||| Stack-safe, potentially infinite streams of effectful
||| computations.
|||
||| Streams are freer monad transformers, taking three type parameters:
|||
|||  f : The effect type, in which values are wrapped. In most cases,
|||      this is `Of a` for some value type `a`.
|||
|||  m : The effect type, in which computations are run. This is
|||      typically `IO`.
|||
|||  r : The return type of a stream if it is being run to completion.
|||      for provably infinite streams, this is set to `Void`.
|||
||| As an example, a stream reading lines from a file returning
||| the total number of lines read might be of
||| type `Stream (Of String) IO Nat`.
module Stream.Internal

import Control.WellFounded
import Data.Fuel
import Data.Nat

%default total

public export
I : Type -> Type
I ty = ty

public export
data Stream : (m : Type -> Type) -> (a,r : Type) -> Type where
  Pure  : r -> Stream m a r
  Yield : (val : a) -> Inf (Stream m a r) -> Stream m a r
  Del   : Inf (Stream m a r) -> Stream m a r
  Bind  : m r -> (r -> Stream m a s) -> Stream m a s

--------------------------------------------------------------------------------
--          Lifting Values
--------------------------------------------------------------------------------

export %inline
effect : m (Stream m a r) -> Stream m a r
effect v = Bind v id

export %inline
yield : a -> Stream m a ()
yield v = Yield v (Pure ())

export %inline
yieldM : m a -> Stream m a ()
yieldM v = Bind v yield

export %inline
lift : m r -> Stream m a r
lift v = Bind v Pure

--------------------------------------------------------------------------------
--          Interfaces
-----------------------------------------------------------------------------

bind : Stream m a r -> (r -> Stream m a s) -> Stream m a s
bind (Pure x) f      = f x
bind (Yield val x) f = Yield val (bind x f)
bind (Del x) f       = Del (bind x f)
bind (Bind x g) f    = Bind x (\v => bind (g v) f)

export
Functor (Stream m a) where
  map f s = bind s (Pure . f)

export %inline
Applicative (Stream m a) where
  pure      = Pure
  fn <*> fk = bind fn (\fun => map (fun $ ) fk)

export %inline
Monad (Stream m a) where
  (>>=) = bind

export %inline
HasIO io => HasIO (Stream io a) where
  liftIO = lift . liftIO

--------------------------------------------------------------------------------
--          Running Streams
--------------------------------------------------------------------------------

export
runWith : Fuel -> Stream IO Void r -> IO (Maybe r)
runWith fuel s = fromPrim $ go fuel s
  where go : Fuel -> Stream IO Void r -> (1 w : %World) -> IORes (Maybe r)
        go (More x) (Del y)       w = go x y w
        go (More x) (Bind y f)    w =
          let MkIORes v w2 = toPrim y w in go x (f v) w2
        go (More x) (Pure y)      w = MkIORes (Just y) w
        go Dry _                  w = MkIORes Nothing w


export
runPure : Fuel -> Stream I Void r -> Maybe r
runPure fuel s = go fuel s
  where go : Fuel -> Stream I Void r -> Maybe r
        go (More x) (Pure y)    = Just y
        go (More x) (Del y)     = go x y
        go (More x) (Bind y f)  = go x (f y)
        go Dry _                = Nothing

export %inline
runWith_ : Fuel -> Stream IO Void r -> IO ()
runWith_ f = ignore . runWith f

export covering
run : Stream IO Void r -> IO r
run s = fromPrim $ go s
  where go : Stream IO Void r -> (1 w : %World) -> IORes r
        go (Del y)       w = go y w
        go (Bind y f)    w =
          let MkIORes v w2 = toPrim y w in go (f v) w2
        go (Pure y)      w = MkIORes y w

export covering %inline
run_ : Stream IO Void r -> IO ()
run_ = ignore . run

export covering
concat : Stream m (Stream m a ()) r -> Stream m a r
concat (Pure x)      = Pure x
concat (Yield val x) = val >> concat x
concat (Del x)       = Del (concat x)
concat (Bind x f)    = Bind x (\v => concat (f v))

--------------------------------------------------------------------------------
--          Creating Streams
--------------------------------------------------------------------------------

export
unfold : (s -> m (Either r (a,s))) -> s -> Stream m a r
unfold fun vs = lift (fun vs) >>= go
  where go : Either r (a,s) -> Stream m a r
        go (Left x)        = Pure x
        go (Right (va,vs)) = Yield va (unfold fun vs)

export
repeat : a -> Stream m a Void
repeat v = Yield v (repeat v)

export
replicate : Nat -> a -> Stream m a ()
replicate 0     _ = Pure ()
replicate (S k) v = Yield v (replicate k v)

--------------------------------------------------------------------------------
--          Splitting Streams
--------------------------------------------------------------------------------

export covering
splitAt : Nat -> Stream m a r -> Stream m a (Stream m a r)
splitAt 0     x = Pure x
splitAt (S k) (Pure x)      = Pure (Pure x)
splitAt (S k) (Yield val x) = Yield val (splitAt k x)
splitAt (S k) (Del x)       = Del (splitAt (S k) x)
splitAt (S k) (Bind x f)    = Bind x (\v => splitAt (S k) (f v))

export covering
take : Nat -> Stream f m r -> Stream f m ()
take n = ignore . splitAt n
