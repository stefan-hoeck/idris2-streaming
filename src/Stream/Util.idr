module Stream.Util

import Data.Colist
import Data.SnocList
import Data.Vect
import Stream.Internal

public export
data Of : (v,r : Type) -> Type where
  MkOf : (vals : List v) -> Of v ()

public export
fromOf : Of a b -> List a
fromOf (MkOf vals) = vals

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

total
foldList : (x -> a -> x) -> x -> List a -> x
foldList f y (h :: t) = foldList f (f y h) t
foldList f y []       = y

total
scanList : (x -> a -> x)
         -> x
         -> (x -> b)
         -> SnocList b
         -> List a
         -> (x, List b)
scanList step acc done bs (va :: as) =
  let acc2 = step acc va
   in scanList step acc2 done (bs :< done acc2) as
scanList step acc done bs []         = (acc, bs <>> Nil)

total
mapList : (a -> b) -> SnocList b -> List a -> List b
mapList f bs (va :: as) = mapList f (bs :< f va) as
mapList f bs []         = bs <>> Nil

total
filterList : (a -> Bool) -> SnocList a -> List a -> List a
filterList p sa (x :: xs) =
  if p x then filterList p (sa :< x) xs else filterList p sa xs
filterList p sa []        = sa <>> Nil

total
mapMaybeList : (a -> Maybe b) -> SnocList b -> List a -> List b
mapMaybeList f sb (x :: xs) = case f x of
  Just vb => mapMaybeList f (sb :< vb) xs
  Nothing => mapMaybeList f sb xs
mapMaybeList f sb []        = sb <>> Nil

total
spanList :  (a -> Bool)
         -> SnocList a
         -> List a
         -> Either (List a) (List a, List a)
spanList f sx (x :: xs) =
  if f x
     then Right (sx <>> Nil, x :: xs)
     else spanList f (sx :< x) xs
spanList f sx [] = Left (sx <>> Nil)

total
breakList : (a -> Maybe (a,a))
         -> SnocList a
         -> List a
         -> Maybe (List a, List a)
breakList f sx (x :: xs) = case f x of
  Just (h,t) => Just (sx <>> [h], t :: xs)
  Nothing    => breakList f (sx :< x) xs
breakList f sx [] = Nothing

total
splitList :  Nat
          -> SnocList a
          -> List a
          -> Either Nat (List a, List a)
splitList (S k) sx (x :: xs) = splitList k (sx :< x) xs
splitList (S k) sx []        = Left (S k)
splitList 0     sx xs        = Right (sx <>> Nil, xs)

--------------------------------------------------------------------------------
--          Producers
--------------------------------------------------------------------------------

chunks : Nat
chunks = 512

export %inline
yieldAll : List a -> Stream (Of a) m ()
yieldAll = yields . MkOf 

export %inline
yield : a -> Stream (Of a) m ()
yield v = yieldAll [v]

export %inline
list : List a -> Stream (Of a) m ()
list = yieldAll

streamChunks : Nat -> List a -> Stream a -> Stream (Of a) m Void
streamChunks (S k) xs (h :: t) =
  streamChunks k (h :: xs) t
streamChunks 0 xs ys =
  yieldAll (reverse xs) >> streamChunks chunks Nil ys

export %inline
stream : Stream a -> Stream (Of a) m Void
stream = streamChunks chunks Nil

colistChunks : Nat -> List a -> Colist a -> Stream (Of a) m ()
colistChunks (S k) xs (y :: ys) = colistChunks k (y :: xs) ys
colistChunks (S k) xs [] = yieldAll (reverse xs)
colistChunks 0     xs ys = yieldAll (reverse xs) >> colistChunks chunks Nil ys

export %inline
colist : Colist a -> Stream (Of a) m ()
colist = colistChunks chunks Nil

||| Generates the sequence (ini, f ini, f $ f ini, ...)
export
iterate : (fun : a -> a) -> (ini : a) -> Stream (Of a) m Void
iterate f ini = go chunks Nil ini
  where go : Nat -> List a -> a -> Stream (Of a) m Void
        go (S k) xs x = go k (x :: xs) (f x)
        go 0 xs x = yieldAll (reverse xs) >> go chunks Nil x

export
generate : (s -> (s,a)) -> s -> Stream (Of a) m Void
generate f ini = go chunks Nil ini
  where go : Nat -> List a -> s -> Stream (Of a) m Void
        go 0     xs x = yieldAll (reverse xs) >> go chunks Nil x
        go (S k) xs x = let (vs,va) = f x in go k (va :: xs) vs

export
tillRight : m (Either a r) -> Stream (Of a) m r
tillRight x = lift x >>= next
  where next : Either a r -> Stream (Of a) m r
        next (Left v)  = yield v >> tillRight x
        next (Right r) = pure r

--------------------------------------------------------------------------------
--          Consuming Streams
--------------------------------------------------------------------------------

export
mapM_ : Applicative m => (a -> m x) -> Stream (Of a) m r -> Stream Empty m r
mapM_ f y = case toView y of
  BindP val      w => pure val >>= \v => mapM_ f (w v)
  BindF (MkOf v) w => lift (traverse f v) >>= \_ => mapM_ f (w ())
  BindM act      w => lift act >>= \v => mapM_ f (w v)
  VP val           => pure val
  VF (MkOf v)      => ignore $ lift (traverse f v)
  VM act           => lift act

export %inline
effects : Applicative m => Stream (Of a) m r -> Stream Empty m r
effects = mapM_ (const $ pure ())

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

export
fold :  (x -> a -> x)
     -> x
     -> (x -> b)
     -> Stream (Of a) m r
     -> Stream Empty m (b,r)
fold step ini done x = case toView x of
  BindP val      z => pure val >>= \v => fold step ini done (z v)
  BindF (MkOf v) z => pure () >> fold step (foldList step ini v) done (z ())
  BindM act      z => lift act >>= \v => fold step ini done (z v)
  VP val           => pure (done ini, val)
  VF (MkOf v)      => pure (done $ foldList step ini v, ())
  VM act           => (done ini,) <$> lift act

export %inline
fold_ :  (x -> a -> x)
      -> x
      -> (x -> b)
      -> Stream (Of a) m r
      -> Stream Empty m b
fold_ step ini done = map fst . fold step ini done

export %inline
foldMap : Monoid mo => (a -> mo) -> Stream (Of a) m r -> Stream Empty m (mo,r)
foldMap f = fold (\vmo,va => vmo <+> f va) neutral id

export %inline
foldMap_ : Monoid mo => (a -> mo) -> Stream (Of a) m r -> Stream Empty m mo
foldMap_ f = map fst . foldMap f

export %inline
sum : Num a => Stream (Of a) m r -> Stream Empty m (a,r)
sum = fold (+) 0 id

export %inline
sum_ : Num a => Stream (Of a) m r -> Stream Empty m a
sum_ = map fst . sum

export %inline
product : Num a => Stream (Of a) m r -> Stream Empty m (a,r)
product = fold (*) 0 id

export %inline
product_ : Num a => Stream (Of a) m r -> Stream Empty m a
product_ = map fst . product

export %inline
length : Stream (Of a) m r -> Stream Empty m (Nat,r)
length = fold (\x,_ => S x) 0 id

export %inline
length_ : Stream (Of a) m r -> Stream Empty m Nat
length_ = map fst . length

export %inline
count : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m (Nat,r)
count p = fold (\x,va => if p va then S x else x) 0 id

export %inline
count_ : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m Nat
count_ p = map fst . count p

export %inline
first : Stream (Of a) m r -> Stream Empty m (Maybe a,r)
first = fold (\acc,va => acc <|> Just va) Nothing id

export %inline
first_ : Stream (Of a) m r -> Stream Empty m (Maybe a)
first_ = map fst . first

export %inline
last : Stream (Of a) m r -> Stream Empty m (Maybe a,r)
last = fold (\_,va => Just va) Nothing id

export %inline
last_ : Stream (Of a) m r -> Stream Empty m (Maybe a)
last_ = map fst . last

export %inline
minimum : Ord a => Stream (Of a) m r -> Stream Empty m (Maybe a,r)
minimum = fold (\acc,va => map (min va) acc <|> Just va) Nothing id

export %inline
minimum_ : Ord a => Stream (Of a) m r -> Stream Empty m (Maybe a)
minimum_ = map fst . minimum

export %inline
maximum : Ord a => Stream (Of a) m r -> Stream Empty m (Maybe a,r)
maximum = fold (\acc,va => map (max va) acc <|> Just va) Nothing id

export %inline
maximum_ : Ord a => Stream (Of a) m r -> Stream Empty m (Maybe a)
maximum_ = map fst . maximum

export %inline
all : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m (Bool,r)
all p = fold (\acc,va => acc && p va) True id

export %inline
all_ : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m Bool
all_ p = map fst . all p

export %inline
any : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m (Bool,r)
any p = fold (\acc,va => acc || p va) False id

export %inline
any_ : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m Bool
any_ p = map fst . any p

export %inline
elem : Eq a => a -> Stream (Of a) m r -> Stream Empty m (Bool, r)
elem va = any (va ==)

export %inline
elem_ : Eq a => a -> Stream (Of a) m r -> Stream Empty m Bool
elem_ va = map fst . elem va

export %inline
toSnocList : Stream (Of a) m r -> Stream Empty m (SnocList a, r)
toSnocList = fold (:<) Lin id

export %inline
toSnocList_ : Stream (Of a) m r -> Stream Empty m (SnocList a)
toSnocList_ = map fst . toSnocList

export %inline
toList : Stream (Of a) m r -> Stream Empty m (List a, r)
toList = map (\(sx,vr) => (sx <>> Nil, vr)) . toSnocList

export %inline
toList_ : Stream (Of a) m r -> Stream Empty m (List a)
toList_ = map fst . toList

-- export
-- foldM :  (x -> a -> m x)
--       -> m x
--       -> (x -> m b)
--       -> Stream (Of a) m r
--       -> Stream Empty m (b,r)
-- foldM step ini done x = case toView x of
--   BindF (MkOf v) z => do
--     vx <- lift ini
--     foldM step (step vx v) done (z ())
-- 
--   BindP val      z => pure val >>= \v => foldM step ini done (z v)
--   BindM act      z => lift act >>= \v => foldM step ini done (z v)
-- 
--   VP val        => do
--     vx <- lift ini
--     vb <- lift (done vx)
--     pure (vb, val)
-- 
--   VF (MkOf v)   => do
--     vx  <- lift ini
--     vx2 <- lift (step vx v)
--     vb  <- lift (done vx2)
--     pure (vb,())
-- 
--   VM act        => do
--     vr <- lift act
--     vx <- lift ini
--     vb <- lift (done vx)
--     pure (vb, vr)

export
scan :  (x -> a -> x)
     -> x
     -> (x -> b)
     -> Stream (Of a) m r
     -> Stream (Of b) m r
scan step ini done str = yield (done ini) >>= \_ => go ini str
  where go : x -> Stream (Of a) m r -> Stream (Of b) m r
        go vx s = case toView s of
          BindF (MkOf v) z => 
            let (vx2,bs) = scanList step vx done Lin v
             in yieldAll bs >> go vx2 (z ())
          BindP val      z => pure val >>= \v => go vx (z v)
          BindM act      z => lift act >>= \v => go vx (z v)
          VP val           => pure val
          VF (MkOf v)      => yieldAll (snd $ scanList step vx done Lin v)
          VM act           => lift act

--------------------------------------------------------------------------------
--          Filters and Stream Transformers
--------------------------------------------------------------------------------

export
for : Stream (Of a) m r -> (List a -> Stream f m x) -> Stream f m r
for str fun = case toView str of
  BindF (MkOf va) z => fun va   >>= \_ => for (z ()) fun
  BindP val       z => pure val >>= \v => for (z v) fun
  BindM act       z => lift act >>= \v => for (z v) fun
  VF (MkOf va)      => ignore $ fun va
  VP val            => pure val
  VM act            => lift act

export
forVals : (List a -> List b) -> Stream (Of a) m r -> Stream (Of b) m r
forVals f str = for str (yieldAll . f)

export %inline
mapVals : (a -> b) -> Stream (Of a) m r -> Stream (Of b) m r
mapVals f = forVals (mapList f Lin)

export %inline
castVals : Cast from to => Stream (Of from) m r -> Stream (Of to) m r
castVals = mapVals cast

export
mapValsM : Applicative m => (a -> m b) -> Stream (Of a) m r -> Stream (Of b) m r
mapValsM f str = for str $ \va => lift (traverse f va) >>= yieldAll

export %inline
drain : Stream (Of a) m r -> Stream (Of a) m r
drain = forVals (const [])

export %inline
with_ : Stream (Of a) m r -> (List a -> f x) -> Stream f m r
with_ str fun = for str (yields . fun)

export %inline
subst : (List a -> f x) -> Stream (Of a) m r -> Stream f m r
subst fun str = for str (yields . fun)

export %inline
filter : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m r
filter p = forVals (filterList p Lin)

export %inline
mapMaybe : (a -> Maybe b) -> Stream (Of a) m r -> Stream (Of b) m r
mapMaybe f = forVals (mapMaybeList f Lin)

export
span :  (a -> Bool)
     -> Stream (Of a) m r 
     -> Stream (Of a) m (Stream (Of a) m r)
span p x = case toView x of
  BindF (MkOf vals) z => case spanList p Lin vals of
    Left vs => yieldAll vs >> span p (z ())
    Right (vs,rest) => yieldAll vs $> (yieldAll rest >> z ())
  BindP val z => pure val >>= \v => span p (z v)
  BindM act z => lift act >>= \v => span p (z v)
  VP val      => pure (pure val)
  VF (MkOf v) => case spanList p Lin v of
    Left vs         => yieldAll vs $> pure ()
    Right (vs,rest) => yieldAll vs $> yieldAll rest
  VM act      => pure $ lift act

export %inline
takeUntil : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m ()
takeUntil p = ignore . span p

export %inline
takeWhile : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m ()
takeWhile p = takeUntil (not . p)

export
dropUntil : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m r
dropUntil p str = drain (span p str) >>= id

export
dropWhile : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m r
dropWhile p = dropUntil (not . p)

export
slidingWindow :  (n : Nat)
              -> {auto 0 prf : IsSucc n}
              -> Stream (Of a) m r
              -> Stream (Of $ Vect n a) m r
slidingWindow (S k) =
  mapMaybe sequence .
  scan (\prev,va => Just va :: init prev) (replicate (S k) Nothing) id

export
breakWith :  (a -> Maybe (a,a))
          -> Stream (Of a) m r
          -> Stream (Of a) m (Stream (Of a) m r)
breakWith f x = case toView x of
  BindF (MkOf y) g => case breakList f Lin y of
    Just (yh,yt) => yieldAll yh >>= \v => pure (yieldAll yt >>= \_ => g v)
    Nothing      => yieldAll y >>= \v => breakWith f (g v)
  BindP y g => pure y >>= \v => breakWith f (g v)
  BindM y g => lift y >>= \v => breakWith f (g v)
  VF (MkOf y) => case breakList f Lin y of
    Just (yh,yt) => yieldAll yh $> yieldAll yt
    Nothing      => yieldAll y  $> pure ()
  VP y => pure (pure y)
  VM y => pure (lift y)

export
splitWith :  (a -> Maybe (a,a))
          -> Stream (Of a) m r
          -> Stream (Stream (Of a) m) m r
splitWith f s = F (breakWith f s) >>=
  \case P r => P r
        M y => M y
        x   => splitWith f x

export
splitAt :  Nat
        -> Stream (Of a) m r
        -> Stream (Of a) m (Stream (Of a) m r)
splitAt k x = case toView x of
  BindF (MkOf vs) z => case splitList k Lin vs of
    Left k2     => yieldAll vs >>= \v => splitAt k2 (z v)
    Right (h,t) => yieldAll h $> (yieldAll t >>= \v => (z v))
  BindP val z => Bind (pure val)  (\v => splitAt k (z v))
  BindM act z => Bind (lift act)  (\v => splitAt k (z v))
  VF (MkOf vs) => case splitList k Lin vs of
    Left k2     => yieldAll vs $> pure ()
    Right (h,t) => yieldAll h $> yieldAll t
  VP v         => pure (P v)
  VM v         => pure (M v)

export
take : Nat -> Stream (Of a) m r -> Stream (Of a) m ()
take n = ignore . splitAt n

export
drop : Nat -> Stream (Of a) m r -> Stream (Of a) m r
drop n str = drain (splitAt n str) >>= id
