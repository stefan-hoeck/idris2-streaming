module Stream.Util

import Data.Colist
import Data.SnocList
import Stream.Internal

public export
data Of : (v,r : Type) -> Type where
  MkOf : (val : v) -> Of v v

public export
fromOf : Of a b -> a
fromOf (MkOf val) = val

--------------------------------------------------------------------------------
--          Producers
--------------------------------------------------------------------------------

export %inline
yield : a -> Stream (Of a) m a
yield = yields . MkOf

export
list : List a -> Stream (Of a) m ()
list []        = pure ()
list (x :: xs) = yield x >>= \_ => list xs

export
stream : Stream a -> Stream (Of a) m Void
stream (x :: y) = yield x >>= \_ => stream y

export
colist : Colist a -> Stream (Of a) m ()
colist []       = pure ()
colist (x :: y) = yield x >>= \_ => colist y

||| Generates the sequence (ini, f ini, f $ f ini, ...)
export
iterate : (fun : a -> a) -> (ini : a) -> Stream (Of a) m Void
iterate f ini = yield ini >>= \_ => iterate f (f ini)

export
generate : (s -> (s,a)) -> s -> Stream (Of a) m Void
generate f ini = let (vs,va) = f ini in yield va >>= \_ => generate f vs

export
tillRight : m (Either a r) -> Stream (Of a) m r
tillRight x = lift x >>= next
  where next : Either a r -> Stream (Of a) m r
        next (Left v)  = yield v >>= \_ => tillRight x
        next (Right r) = pure r

--------------------------------------------------------------------------------
--          Consuming Streams
--------------------------------------------------------------------------------

export
mapM_ : (a -> m x) -> Stream (Of a) m r -> Stream Empty m r
mapM_ f y = case toView y of
  BindP val      w => pure val >>= \v => mapM_ f (w v)
  BindF (MkOf v) w => lift (f v) >>= \_ => mapM_ f (w v)
  BindM act      w => lift act >>= \v => mapM_ f (w v)
  VP val           => pure val
  VF (MkOf v)      => lift (f v) $> v
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
  BindF (MkOf v) z => pure () >> fold step (step ini v) done (z v)
  BindM act      z => lift act >>= \v => fold step ini done (z v)
  VP val           => pure (done ini, val)
  VF (MkOf v)      => pure (done $ step ini v, v)
  VM act           => (done ini,) <$> lift act

export %inline
foldMap : Monoid mo => (a -> mo) -> Stream (Of a) m r -> Stream Empty m (mo,r)
foldMap f = fold (\vmo,va => vmo <+> f va) neutral id

export %inline
sum : Num a => Stream (Of a) m r -> Stream Empty m (a,r)
sum = fold (+) 0 id

export %inline
product : Num a => Stream (Of a) m r -> Stream Empty m (a,r)
product = fold (*) 0 id

export %inline
first : Stream (Of a) m r -> Stream Empty m (Maybe a,r)
first = fold (\acc,va => acc <|> Just va) Nothing id

export %inline
last : Stream (Of a) m r -> Stream Empty m (Maybe a,r)
last = fold (\_,va => Just va) Nothing id

export %inline
minimum : Ord a => Stream (Of a) m r -> Stream Empty m (Maybe a,r)
minimum = fold (\acc,va => map (min va) acc <|> Just va) Nothing id

export %inline
maximum : Ord a => Stream (Of a) m r -> Stream Empty m (Maybe a,r)
maximum = fold (\acc,va => map (max va) acc <|> Just va) Nothing id

export %inline
all : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m (Bool,r)
all p = fold (\acc,va => acc && p va) True id

export %inline
any : (a -> Bool) -> Stream (Of a) m r -> Stream Empty m (Bool,r)
any p = fold (\acc,va => acc || p va) False id

export %inline
elem : Eq a => a -> Stream (Of a) m r -> Stream Empty m (Bool,r)
elem va = any (va ==) 

export %inline
toSnocList : Stream (Of a) m r -> Stream Empty m (SnocList a, r)
toSnocList = fold (:<) Lin id

export %inline
toList : Stream (Of a) m r -> Stream Empty m (List a, r)
toList = map (\(sx,vr) => (sx <>> Nil, vr)) . toSnocList

export
foldM :  (x -> a -> m x)
      -> m x
      -> (x -> m b)
      -> Stream (Of a) m r
      -> Stream Empty m (b,r)
foldM step ini done x = case toView x of
  BindF (MkOf v) z => do
    vx <- lift ini
    foldM step (step vx v) done (z v)

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
    pure (vb,v)

  VM act        => do
    vr <- lift act
    vx <- lift ini
    vb <- lift (done vx)
    pure (vb, vr)

--------------------------------------------------------------------------------
--          Filters and Stream Transformers
--------------------------------------------------------------------------------

export
for : Stream (Of a) m r -> (a -> Stream f m x) -> Stream f m r
for str fun = case toView str of
  BindF (MkOf va) z => fun va   >>= \_ => for (z va) fun
  BindP val       z => pure val >>= \v => for (z v) fun
  BindM act       z => lift act >>= \v => for (z v) fun
  VF (MkOf va)      => fun va $> va
  VP val            => pure val
  VM act            => lift act

export
mapVals : (a -> b) -> Stream (Of a) m r -> Stream (Of b) m r
mapVals f str = for str (yield . f)

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
       then yield val >>= \v => filter p (z v)
       else pure ()   >>   filter p (z val)
  BindP val z    => pure val >>= \v => filter p (z v)
  BindM act z    => lift act >>= \v => filter p (z v)
  VP val         => pure val
  VF (MkOf v)    => if p v then yield v else pure v
  VM act         => lift act

export
span :  (a -> Bool)
     -> Stream (Of a) m r 
     -> Stream (Of a) m (Stream (Of a) m r)
span p x = case toView x of
  BindF (MkOf val) z =>
    if p val
       then pure ()   >> pure (z val)
       else yield val >>= \v => span p (z v)
  BindP val z => pure val >>= \v => span p (z v)
  BindM act z => lift act >>= \v => span p (z v)
  VP val      => pure (pure val)
  VF (MkOf v) => pure $ if p v then yield v else pure v
  VM act      => pure $ lift act

export
takeWhile : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m ()
takeWhile p = ignore . span p

export
dropWhile : (a -> Bool) -> Stream (Of a) m r -> Stream (Of a) m r
dropWhile p str = drain (span p str) >>= id

export
drop : Nat -> Stream (Of a) m r -> Stream (Of a) m r
drop n str = drain (splitsAt n str) >>= id
