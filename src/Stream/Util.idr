module Stream.Util

import Data.Colist
import Data.Fuel
import Data.List.TailRec
import Data.Vect
import Stream.Internal

public export
data Of : (v,r : Type) -> Type where
  MkOf : (vals : List v) -> Of v ()

public export
fromOf : Of a b -> List a
fromOf (MkOf vals) = vals

--------------------------------------------------------------------------------
--          Producers
--------------------------------------------------------------------------------

chunks : Nat
chunks = 512

export %inline
yieldAll : List a -> Stream (Of a) e ()
yieldAll = yields . MkOf 

export %inline
yield : a -> Stream (Of a) e ()
yield v = yieldAll [v]

export %inline
list : List a -> Stream (Of a) e ()
list = yieldAll

streamChunks : Nat -> List a -> Stream a -> Stream (Of a) e Void
streamChunks (S k) xs (h :: t) =
  streamChunks k (h :: xs) t
streamChunks 0 xs ys =
  yieldAll (reverse xs) >> streamChunks chunks Nil ys

export %inline
stream : Stream a -> Stream (Of a) e Void
stream = streamChunks chunks Nil

colistChunks : Nat -> List a -> Colist a -> Stream (Of a) e ()
colistChunks (S k) xs (y :: ys) = colistChunks k (y :: xs) ys
colistChunks (S k) xs [] = yieldAll (reverse xs)
colistChunks 0     xs ys = yieldAll (reverse xs) >> colistChunks chunks Nil ys

export %inline
colist : Colist a -> Stream (Of a) e ()
colist = colistChunks chunks Nil

||| Generates the sequence (ini, f ini, f $ f ini, ...)
export
iterate : (fun : a -> a) -> (ini : a) -> Stream (Of a) e Void
iterate f ini = go chunks Nil ini
  where go : Nat -> List a -> a -> Stream (Of a) m Void
        go (S k) xs x = go k (x :: xs) (f x)
        go 0 xs x = yieldAll (reverse xs) >> go chunks Nil x

export
generate : (s -> (s,a)) -> s -> Stream (Of a) e Void
generate f ini = go chunks Nil ini
  where go : Nat -> List a -> s -> Stream (Of a) m Void
        go 0     xs x = yieldAll (reverse xs) >> go chunks Nil x
        go (S k) xs x = let (vs,va) = f x in go k (va :: xs) vs

export
tillRight : IO (Either a r) -> Stream (Of a) e r
tillRight x = lift x >>= next
  where next : Either a r -> Stream (Of a) m r
        next (Left v)  = yield v >> tillRight x
        next (Right r) = pure r

--------------------------------------------------------------------------------
--          Consuming Streams
--------------------------------------------------------------------------------

export
mapM : (a -> IO b) -> Stream (Of a) e r -> Stream (Of b) e r
mapM f = mapsIO (\(MkOf as) => MkOf <$> traverseIO f as)

export
mapM_ : (a -> IO b) -> Stream (Of a) e r -> Stream Empty e r
mapM_ fun = mapStep (\_ => M . (>>= fun'))
  where fun' : Step (Of a) e s -> IO (Step Empty e s)
        fun' (Yield $ MkOf vs) = traverseIO fun vs $> Done ()
        fun' (Done res)        = pure $ Done res
        fun' (Fail err)        = pure $ Fail err


export %inline
effects : Stream (Of a) m r -> Stream Empty m r
effects = mapM_ (const $ pure ())

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

total export
foldWith :  Fuel
         -> (x -> a -> x)
         -> x
         -> (x -> b)
         -> Stream (Of a) e r
         -> IO (Either e (b, Maybe r))
foldWith fuel step ini done str = fromPrim $ go fuel ini (toView str)
  where go : Fuel -> x -> View (Of a) e r -> PrimIO (Either e (b, Maybe r))
        go (More y) vx (VBind z f) w =
          let MkIORes vz w2 = toPrim z w
           in case vz of
               Yield (MkOf vals)  =>
                 go y (foldl step vx vals) (toView $ f ()) w2
               Done res   => go y vx (toView $ f res) w2
               Fail err   => MkIORes (Left err) w2

        go (More y) vx (VM z)      w =
          let MkIORes vz w2 = toPrim z w
           in case vz of
               Yield (MkOf vals)  =>
                 MkIORes (Right (done (foldl step vx vals), Just ())) w2
               Done res   => MkIORes (Right (done vx, Just res)) w2
               Fail err   => MkIORes (Left err) w2

        go Dry      vx _           w =
          MkIORes (Right (done vx, Nothing)) w


partial export
fold :  (x -> a -> x)
     -> x
     -> (x -> b)
     -> Stream (Of a) e r
     -> IO (Either e (b, r))
fold step ini done str = fromPrim $ go ini (toView str)
  where partial go : x -> View (Of a) e r -> PrimIO (Either e (b,r))
        go vx (VBind z f) w =
          let MkIORes vz w2 = toPrim z w
           in case vz of
               Yield (MkOf vals)  =>
                 go (foldl step vx vals) (toView $ f ()) w2
               Done res   => go vx (toView $ f res) w2
               Fail err   => MkIORes (Left err) w2

        go vx (VM z)      w =
          let MkIORes vz w2 = toPrim z w
           in case vz of
               Yield (MkOf vals)  =>
                 MkIORes (Right (done (foldl step vx vals), ())) w2
               Done res   => MkIORes (Right (done vx, res)) w2
               Fail err   => MkIORes (Left err) w2

partial export
fold_ :  (x -> a -> x)
      -> x
      -> (x -> b)
      -> Stream (Of a) e r
      -> IO (Either e b)
fold_ step ini done str = map fst <$> fold step ini done str

-- export
-- scan :  (x -> a -> x)
--      -> x
--      -> (x -> b)
--      -> Stream (Of a) e r
--      -> Stream (Of b) e r
-- scan step ini done = mapStepSt fun ini
--   where fun : (0 x : _) -> x -> IO (Step (Of a) e x) -> (

--------------------------------------------------------------------------------
--          Filters and Stream Transformers
--------------------------------------------------------------------------------

export
for : Stream (Of a) e r -> (List a -> Stream f e x) -> Stream f e r
for str fun = mapStep (\_ => effect . map fun') str
  where fun' : Step (Of a) e s -> Stream f e s
        fun' (Yield $ MkOf vs) = ignore $ fun vs
        fun' (Done res)        = pure res
        fun' (Fail err)        = fail err

export
forVals : (List a -> List b) -> Stream (Of a) e r -> Stream (Of b) e r
forVals f str = for str (yieldAll . f)

export %inline
mapVals : (a -> b) -> Stream (Of a) e r -> Stream (Of b) e r
mapVals f = forVals (mapTR Lin f)

export %inline
castVals : Cast from to => Stream (Of from) e r -> Stream (Of to) e r
castVals = mapVals cast

export %inline
drain : Stream (Of a) e r -> Stream (Of b) e r
drain = forVals (const [])

export %inline
with_ : Stream (Of a) e r -> (List a -> f x) -> Stream f e r
with_ str fun = for str (yields . fun)

export %inline
subst : (List a -> f x) -> Stream (Of a) e r -> Stream f e r
subst fun str = for str (yields . fun)

export %inline
filter : (a -> Bool) -> Stream (Of a) e r -> Stream (Of a) e r
filter p = forVals (filterTR Lin p)

export %inline
mapMaybe : (a -> Maybe b) -> Stream (Of a) e r -> Stream (Of b) e r
mapMaybe f = forVals (mapMaybeTR Lin f)

splitting :  (s -> List a -> Either s (List a, List a))
          -> s
          -> Stream (Of a) e r 
          -> Stream (Of a) e (Stream (Of a) e r)
splitting fun vs x = case toView x of
  VBind y f => effect $ do
    Yield (MkOf vals) <- y
      | Done res => pure (splitting fun vs $ f res)
      | Fail err => pure (fail err)
    case fun vs vals of
      Right (h,t) => pure (yieldAll h  $> Bind (yieldAll t) f)
      Left vs2    => pure (Bind (yieldAll vals) (splitting fun vs2 . f))

  VM y      => effect $ do
    Yield (MkOf vals) <- y
      | Done res => pure (pure $ pure res)
      | Fail err => pure (fail err)
    case fun vs vals of
      Right (h,t) => pure (yieldAll h    $> yieldAll t)
      Left _      => pure (yieldAll vals $> pure ())

export
span :  (a -> Bool)
     -> Stream (Of a) e r 
     -> Stream (Of a) e (Stream (Of a) e r)
span p = splitting (\_ => spanTR Lin p) ()

export %inline
takeUntil : (a -> Bool) -> Stream (Of a) e r -> Stream (Of a) e ()
takeUntil p = ignore . span p

export %inline
takeWhile : (a -> Bool) -> Stream (Of a) e r -> Stream (Of a) e ()
takeWhile p = takeUntil (not . p)

export
dropUntil : (a -> Bool) -> Stream (Of a) e r -> Stream (Of a) e r
dropUntil p str = drain (span p str) >>= id

export
dropWhile : (a -> Bool) -> Stream (Of a) e r -> Stream (Of a) e r
dropWhile p = dropUntil (not . p)

export
breakWith :  (a -> Maybe (a,a))
          -> Stream (Of a) m r
          -> Stream (Of a) m (Stream (Of a) m r)
breakWith f = splitting (\_ => breakTR Lin f) ()

-- export
-- slidingWindow :  (n : Nat)
--               -> {auto 0 prf : IsSucc n}
--               -> Stream (Of a) m r
--               -> Stream (Of $ Vect n a) m r
-- slidingWindow (S k) =
--   mapMaybe sequence .
--   scan (\prev,va => Just va :: init prev) (replicate (S k) Nothing) id

export
splitWith :  (a -> Maybe (a,a))
          -> Stream (Of a) m r
          -> Stream (Stream (Of a) m) m r
splitWith f s = yields (breakWith f s) >>= splitWith f

export
splitAt :  Nat
        -> Stream (Of a) m r
        -> Stream (Of a) m (Stream (Of a) m r)
splitAt = splitting (splitTR Lin)

export
take : Nat -> Stream (Of a) m r -> Stream (Of a) m ()
take n = ignore . splitAt n

export
drop : Nat -> Stream (Of a) m r -> Stream (Of a) m r
drop n str = drain (splitAt n str) >>= id
