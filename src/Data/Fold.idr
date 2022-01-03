module Data.Fold

public export
data Fold : (a,b : Type) -> Type where
  MkFold :  {0 s : _}
         -> (acc : s -> a -> s)
         -> (cur : s)
         -> (res : s -> b)
         -> Fold a b

public export
Functor (Fold a) where
  map f (MkFold acc cur res) = MkFold acc cur (f . res)

public export
Applicative (Fold a) where
  pure v = MkFold const () (const v)
  MkFold acc1 cur1 res1 <*> MkFold acc2 cur2 res2 =
    MkFold
    (\(s1,s2),va => (acc1 s1 va, acc2 s2 va))
    (cur1,cur2)
    (\(s1,s2) => res1 s1 (res2 s2))

public export %inline
Semigroup b => Semigroup (Fold a b) where
  x <+> y = [| x <+> y |]

public export %inline
Monoid b => Monoid (Fold a b) where
  neutral = pure neutral

public export %inline
Num b => Num (Fold a b) where
  x + y = [| x + y |]
  x * y = [| x * y |]
  fromInteger = pure . fromInteger

public export %inline
Neg b => Neg (Fold a b) where
  x - y  = [| x - y |]
  negate = map negate

public export %inline
Integral b => Integral (Fold a b) where
  mod x y = [| mod x y |]
  div x y = [| div x y |]

public export %inline
Fractional b => Fractional (Fold a b) where
  x / y  = [| x / y |]

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

export
fold1 : (a -> a -> a) -> Fold a (Maybe a)
fold1 f = MkFold (\ma,va => Just $ maybe va (\x => f x va) ma) Nothing id

export %inline
appendTo : Semigroup a => (ini : a) -> Fold a a
appendTo ini = MkFold (<+>) ini id

export %inline
concat : Monoid a => Fold a a
concat = appendTo neutral

export
foldMap : Monoid w => (a -> w) -> (w -> b) -> Fold a b
foldMap f = MkFold (\vw,va => vw <+> f va) neutral

export %inline
head : Fold a (Maybe a)
head = fold1 const

export %inline
last : Fold a (Maybe a)
last = fold1 (flip const)

export %inline
minimum : Ord a => Fold a (Maybe a)
minimum = fold1 min

export %inline
maximum : Ord a => Fold a (Maybe a)
maximum = fold1 max

export %inline
snocList : Fold a (SnocList a)
snocList = MkFold (:<) Lin id

export %inline
length : Fold a Nat
length = MkFold (\n,_ => S n) 0 id

export %inline
sum : Num a => Fold a a
sum = MkFold (+) 0 id

export %inline
product : Num a => Fold a a
product = MkFold (*) 1 id

export %inline
and : Fold Bool Bool
and = MkFold (\x,y => x && y) True id

export %inline
or : Fold Bool Bool
or = MkFold (\x,y => x || y) False id

export %inline
any : (a -> Bool) -> Fold a Bool
any f = MkFold (\x,y => x || f y) False id

export %inline
all : (a -> Bool) -> Fold a Bool
all f = MkFold (\x,y => x && f y) True id

export %inline
elem : Eq a => a -> Fold a Bool
elem v = any (v ==)

--------------------------------------------------------------------------------
--          Transformed Folds
--------------------------------------------------------------------------------

export %inline
premap : (c -> a) -> Fold a b -> Fold c b
premap f (MkFold acc cur res) = MkFold (\vs => acc vs . f) cur res

export %inline
prefilter : (a -> Bool) -> Fold a b -> Fold a b
prefilter f (MkFold acc cur res) =
  MkFold (\vs,va => if f va then acc vs va else vs) cur res

export %inline
premapMaybe : (c -> Maybe a) -> Fold a b -> Fold c b
premapMaybe f (MkFold acc cur res) =
  MkFold (\vs => maybe vs (acc vs) . f) cur res

export
drop : Nat -> Fold a b -> Fold a b
drop n (MkFold {s} acc cur res) = MkFold acc' (cur,n) (res . fst)
  where acc' : (s,Nat) -> a -> (s,Nat)
        acc' (x, 0)     y = (acc x y, 0)
        acc' (x, (S k)) _ = (x, k)

export %inline
tail : Fold a b -> Fold a b
tail = drop 1

export
predropWhile : (a -> Bool) -> Fold a b -> Fold a b
predropWhile f (MkFold {s} acc cur res) = MkFold acc' (cur,True) (res . fst)
  where acc' : (s,Bool) -> a -> (s,Bool)
        acc' (x, b) y = if b && f y then (x,True) else (acc x y, False)
