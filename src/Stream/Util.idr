module Stream.Util

import Data.Colist
import Data.SnocList
import Data.Vect
import Stream.Internal

public export
data Of : (v,r : Type) -> Type where
  MkOf : (val : v) -> Of v ()

public export
fromOf : Of a b -> a
fromOf (MkOf val) = val

--------------------------------------------------------------------------------
--          Producers
--------------------------------------------------------------------------------

export %inline
yield : a -> Stream (Of a) m ()
yield = yields . MkOf

export
list : List a -> Stream (Of a) m ()
list []        = pure ()
list (x :: xs) = yield x >> list xs

export
stream : Stream a -> Stream (Of a) m Void
stream (x :: y) = yield x >> stream y

export
colist : Colist a -> Stream (Of a) m ()
colist []       = pure ()
colist (x :: y) = yield x >> colist y

||| Generates the sequence (ini, f ini, f $ f ini, ...)
export
iterate : (fun : a -> a) -> (ini : a) -> Stream (Of a) m Void
iterate f ini = yield ini >> iterate f (f ini)

export
generate : (s -> (s,a)) -> s -> Stream (Of a) m Void
generate f ini = let (vs,va) = f ini in yield va >> generate f vs

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
mapM_ : (a -> m x) -> Stream (Of a) m r -> Stream Empty m r
mapM_ f y = case toView y of
  BindP val      w => pure val >>= \v => mapM_ f (w v)
  BindF (MkOf v) w => lift (f v) >>= \_ => mapM_ f (w ())
  BindM act      w => lift act >>= \v => mapM_ f (w v)
  VP val           => pure val
  VF (MkOf v)      => ignore $ lift (f v)
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
  BindF (MkOf v) z => pure () >> fold step (step ini v) done (z ())
  BindM act      z => lift act >>= \v => fold step ini done (z v)
  VP val           => pure (done ini, val)
  VF (MkOf v)      => pure (done $ step ini v, ())
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

export
foldM :  (x -> a -> m x)
      -> m x
      -> (x -> m b)
      -> Stream (Of a) m r
      -> Stream Empty m (b,r)
foldM step ini done x = case toView x of
  BindF (MkOf v) z => do
    vx <- lift ini
    foldM step (step vx v) done (z ())

  BindP val      z => pure val >>= \v => foldM step ini done (z v)
  BindM act      z => lift act >>= \v => foldM step ini done (z v)

  VP val        => do
    vx <- lift ini
    vb <- lift (done vx)
    pure (vb, val)

  VF (MkOf v)   => do
    vx  <- lift ini
    vx2 <- lift (step vx v)
    vb  <- lift (done vx2)
    pure (vb,())

  VM act        => do
    vr <- lift act
    vx <- lift ini
    vb <- lift (done vx)
    pure (vb, vr)

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
            let vx2 = step vx v
             in yield (done vx2) >> go vx2 (z ())
          BindP val      z => pure val >>= \v => go vx (z v)
          BindM act      z => lift act >>= \v => go vx (z v)
          VP val           => pure val
          VF (MkOf v)      => yield (done $ step vx v)
          VM act           => lift act

--------------------------------------------------------------------------------
--          Filters and Stream Transformers
--------------------------------------------------------------------------------

export
for : Stream (Of a) m r -> (a -> Stream f m x) -> Stream f m r
for str fun = case toView str of
  BindF (MkOf va) z => fun va   >>= \_ => for (z ()) fun
  BindP val       z => pure val >>= \v => for (z v) fun
  BindM act       z => lift act >>= \v => for (z v) fun
  VF (MkOf va)      => ignore $ fun va
  VP val            => pure val
  VM act            => lift act

export
mapVals : (a -> b) -> Stream (Of a) m r -> Stream (Of b) m r
mapVals f str = for str (yield . f)

export %inline
castVals : Cast from to => Stream (Of from) m r -> Stream (Of to) m r
castVals = mapVals cast

export
mapValsM : (a -> m b) -> Stream (Of a) m r -> Stream (Of b) m r
mapValsM f str = for str $ \va => lift (f va) >>= yield

export
drain : Stream (Of a) m r -> Stream (Of a) m r
drain str = for str (\_ => pure ())

export %inline
with_ : Stream (Of a) m r -> (a -> f x) -> Stream f m r
with_ str fun = for str (yields . fun)

export %inline
subst : (a -> f x) -> Stream (Of a) m r -> Stream f m r
subst fun str = for str (yields . fun)

export
filter : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m r
filter p x = case toView x of
  BindF (MkOf val) z =>
    if p val
       then yield val >> filter p (z ())
       else pure ()   >> filter p (z ())
  BindP val z    => pure val >>= \v => filter p (z v)
  BindM act z    => lift act >>= \v => filter p (z v)
  VP val         => pure val
  VF (MkOf v)    => if p v then yield v else pure ()
  VM act         => lift act

export
mapMaybe : (a -> Maybe b) -> Stream (Of a) m r -> Stream (Of b) m r
mapMaybe f x = case toView x of
  BindF (MkOf val) z => case f val of
    Just vb => yield vb >> mapMaybe f (z ())
    Nothing => pure ()  >> mapMaybe f (z ())
  BindP val z    => pure val >>= \v => mapMaybe f (z v)
  BindM act z    => lift act >>= \v => mapMaybe f (z v)
  VF (MkOf v)    => case f v of
    Just vb => yield vb
    Nothing => pure ()
  VP val         => pure val
  VM act         => lift act

export
span :  (a -> Bool)
     -> Stream (Of a) m r 
     -> Stream (Of a) m (Stream (Of a) m r)
span p x = case toView x of
  BindF (MkOf val) z =>
    if p val
       then pure (yield val >> z ())
       else yield val >> span p (z ())
  BindP val z => pure val >>= \v => span p (z v)
  BindM act z => lift act >>= \v => span p (z v)
  VP val      => pure (pure val)
  VF (MkOf v) => if p v then pure (yield v) else yield v >> (pure $ pure ())
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
drop : Nat -> Stream (Of a) m r -> Stream (Of a) m r
drop n str = drain (splitsAt n str) >>= id

export
slidingWindow :  (n : Nat)
              -> {auto 0 prf : IsSucc n}
              -> Stream (Of a) m r
              -> Stream (Of $ Vect n a) m r
slidingWindow (S k) =
  mapMaybe sequence .
  scan (\prev,va => Just va :: init prev) (replicate (S k) Nothing) id
