module Data.List.TailRec

import Data.SnocList

%default total

export
chunkSize : Nat
chunkSize = 0xff

--------------------------------------------------------------------------------
--          Generating Lists
--------------------------------------------------------------------------------

export
replicateTR : SnocList a -> Nat -> a -> List a
replicateTR sx (S k) x = replicateTR (sx :< x) k x
replicateTR sx 0 x     = sx <>> Nil

export
iterateTR : SnocList a -> Nat -> (a -> a) -> a -> (List a, a)
iterateTR sx (S k) f x = iterateTR (sx :< x) k f (f x)
iterateTR sx 0     _ x = (sx <>> Nil, x)

export
generateTR : SnocList a -> Nat -> (s -> (a, s)) -> s -> (List a, s)
generateTR sx (S k) f x = let (va,vs) = f x in generateTR (sx :< va) k f vs
generateTR sx 0     _ x = (sx <>> Nil, x)

--------------------------------------------------------------------------------
--          Maps and Traversals
--------------------------------------------------------------------------------

export
mapTR : SnocList b -> (a -> b) -> List a -> List b
mapTR sx f (x :: xs) = mapTR (sx :< f x) f xs
mapTR sx f []        = sx <>> Nil

export
mapMaybeTR : SnocList b -> (a -> Maybe b) -> List a -> List b
mapMaybeTR sx f (x :: xs) = case f x of
  Just vb => mapMaybeTR (sx :< vb) f xs
  Nothing => mapMaybeTR sx f xs
mapMaybeTR sx f []        = sx <>> Nil

export
scanTR : (x -> a -> x)
       -> x
       -> (x -> b)
       -> SnocList b
       -> List a
       -> (x, List b)
scanTR step acc done bs (va :: as) =
  let acc2 = step acc va
   in scanTR step acc2 done (bs :< done acc2) as
scanTR step acc done bs []         = (acc, bs <>> Nil)

export
traverseIO : (a -> IO b) -> List a -> IO (List b) 
traverseIO fun as = fromPrim $ go Lin as
  where go : SnocList b -> List a -> PrimIO (List b)
        go sb (va :: as) w = let MkIORes vb w2 = toPrim (fun va) w
                              in go (sb :< vb) as w2
        go sb Nil        w = MkIORes (sb <>> Nil) w

export
traverseIOE : (a -> IO (Either e b)) -> List a -> IO (Either e $ List b)
traverseIOE fun as = fromPrim $ go Lin as
  where go : SnocList b -> List a -> PrimIO (Either e $ List b)
        go sb (va :: as) w =
          let MkIORes v w2 = toPrim (fun va) w
           in case v of
                Right vb => go (sb :< vb) as w2
                Left  ve => MkIORes (Left ve) w2

        go sb Nil        w = MkIORes (Right $ sb <>> Nil) w

export
traverseIOE_ : (a -> IO (Either e x)) -> List a -> IO (Either e ())
traverseIOE_ fun as = fromPrim $ go as
  where go : List a -> PrimIO (Either e ())
        go (va :: as) w =
          let MkIORes v w2 = toPrim (fun va) w
           in case v of
                Right _  => go as w2
                Left  ve => MkIORes (Left ve) w2

        go Nil        w = MkIORes (Right ()) w

--------------------------------------------------------------------------------
--          Sublists
--------------------------------------------------------------------------------

export
takeTR : SnocList a -> Nat -> List a -> (List a, Nat)
takeTR sx (S k) (x :: xs) = takeTR (sx :< x) k xs
takeTR sx (S k) []        = (sx <>> Nil, S k)
takeTR sx 0     _         = (sx <>> Nil, 0)

export
dropTR : Nat -> List a -> Either (List a) Nat
dropTR (S k) (x :: xs) = dropTR k xs
dropTR 0     xs        = Left xs
dropTR n     []        = Right n

export
filterTR : SnocList a -> (a -> Bool) -> List a -> List a
filterTR sx f (x :: xs) =
  if f x then filterTR (sx :< x) f xs else filterTR sx f xs
filterTR sx f []        = sx <>> Nil

export
spanTR :  SnocList a
       -> (a -> Bool)
       -> List a
       -> Either () (List a, List a)
spanTR sx f (x :: xs) =
  if f x
     then Right (sx <>> Nil, x :: xs)
     else spanTR (sx :< x) f xs
spanTR sx _ [] = Left ()

export
breakTR : SnocList a
        -> (a -> Maybe (a,a))
        -> List a
        -> Either () (List a, List a)
breakTR sx f (x :: xs) = case f x of
  Just (h,t) => Right (sx <>> [h], t :: xs)
  Nothing    => breakTR (sx :< x) f xs
breakTR _ _ [] = Left ()

export
splitTR :  SnocList a
        -> Nat
        -> List a
        -> Either Nat (List a, List a)
splitTR sx (S k) (x :: xs) = splitTR (sx :< x) k xs
splitTR sx 0     xs        = Right (sx <>> Nil, xs)
splitTR sx n     []        = Left n
