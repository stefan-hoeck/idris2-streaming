module Stream.Result

||| Single step evaluation result of a `Source`.
||| This can either be a new value (to be consumed
||| by a sink), a final result signalling that the
||| will produce no more values, or an error.
public export
data Result : (err,val,res : Type) -> Type where
  Done  : (result : res) -> Result err val res
  Error : (error : err)  -> Result err val res
  Value : (value : val)  -> Result err val res

public export
fold :  Lazy (err -> x)
     -> Lazy (val -> x)
     -> Lazy (res -> x)
     -> Result err val res
     -> x
fold _ g _  (Value value) = g value
fold _ _ h (Done result)  = h result
fold f _ _  (Error error) = f error

public export
mapRes :  Lazy (err -> err2)
       -> Lazy (val -> val2)
       -> Lazy (res -> res2)
       -> Result err val res
       -> Result err2 val2 res2
mapRes _ g _ (Value value) = Value $ g value
mapRes _ _ h (Done result) = Done  $ h result
mapRes f _ _ (Error error) = Error $ f error

public export
traverseRes :  Applicative f
            => Lazy (err -> f err2)
            -> Lazy (val -> f val2)
            -> Lazy (res -> f res2)
            -> Result err val res
            -> f (Result err2 val2 res2)
traverseRes _ h _ (Value value) = Value <$> h value
traverseRes _ _ i (Done result) = Done  <$> i result
traverseRes g _ _ (Error error) = Error <$> g error

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export
Eq err => Eq val => Eq res => Eq (Result err val res) where
  Value x == Value y = x == y 
  Done  x == Done  y = x == y 
  Error x == Error y = x == y 
  _       == _       = False

export
Show err => Show val => Show res => Show (Result err val res) where
  showPrec p (Value x) = showCon p "Value" $ showArg x
  showPrec p (Done x)  = showCon p "Done"  $ showArg x
  showPrec p (Error x) = showCon p "Error" $ showArg x

export %inline
Functor (Result err val) where
  map f = mapRes id id f

export
Foldable (Result err val) where
  foldr f acc (Done res) = f res acc
  foldr _ acc _          = acc

  foldl f acc (Done res) = f acc res
  foldl _ acc _          = acc

  foldMap f (Done res) = f res
  foldMap _ _          = neutral

export %inline
Traversable (Result err val) where
  traverse f = traverseRes pure pure f

export %inline
Bifunctor (Result err) where
  bimap f g = mapRes id f g

export
Bifoldable (Result err) where
  bifoldr f g acc (Done  res) = g res acc
  bifoldr f g acc (Value res) = f res acc
  bifoldr _ _ acc (Error _)   = acc

export %inline
Bitraversable (Result err) where
  bitraverse f g = traverseRes pure f g
