module Stream.Result

||| Single step evaluation result of a `Source`.
||| This can either be a new value (to be consumed
||| by a sink), a final result signalling that the source
||| will produce no more values, or an error.
public export
data Result : (err,val : Type) -> Type where
  Done  : (result : val) -> Result err val
  Error : (error : err)  -> Result err val
  Value : (value : val)  -> Result err val

public export
fold :  Lazy (err -> x)
     -> Lazy (val -> x)
     -> Result err val
     -> x
fold _ g  (Value value) = g value
fold _ g  (Done result) = g result
fold f _  (Error error) = f error

public export
mapRes :  Lazy (err -> err2)
       -> Lazy (val -> val2)
       -> Result err val
       -> Result err2 val2
mapRes _ g (Value value) = Value $ g value
mapRes _ g (Done result) = Done $ g result
mapRes f _ (Error error) = Error $ f error

public export
traverseRes :  Applicative f
            => Lazy (err -> f err2)
            -> Lazy (val -> f val2)
            -> Result err val
            -> f (Result err2 val2)
traverseRes _ h (Value value) = Value <$> h value
traverseRes _ h (Done result) = Done <$> h result
traverseRes g _ (Error error) = Error <$> g error

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export
Eq err => Eq val => Eq (Result err val) where
  Value x == Value y = x == y 
  Done  x == Done  y = x == y
  Error x == Error y = x == y 
  _       == _       = False

export
Show err => Show val => Show (Result err val) where
  showPrec p (Value x) = showCon p "Value" $ showArg x
  showPrec p (Done x)  = showCon p "Done" $ showArg x
  showPrec p (Error x) = showCon p "Error" $ showArg x

export %inline
Functor (Result err) where
  map f = mapRes id f

export
Foldable (Result err) where
  foldr f acc (Value val) = f val acc
  foldr f acc (Done val)  = f val acc
  foldr _ acc _           = acc

  foldl f acc (Value val) = f acc val
  foldl f acc (Done val)  = f acc val
  foldl _ acc _           = acc

  foldMap f (Value val) = f val
  foldMap f (Done val)  = f val
  foldMap _ _           = neutral

export %inline
Traversable (Result err) where
  traverse f = traverseRes pure f

export %inline
Bifunctor Result where
  bimap f g = mapRes f g

export
Bifoldable Result where
  bifoldr _ g acc (Done val)  = g val acc
  bifoldr _ g acc (Value val) = g val acc
  bifoldr f _ acc (Error err) = f err acc

export %inline
Bitraversable Result where
  bitraverse f g = traverseRes f g
