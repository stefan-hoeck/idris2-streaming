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

||| A lifte value.
public export
data PFM : (f,m : Type -> Type) -> (r : Type) -> Type where
  P : (val : r)   -> PFM f m r
  F : (eff : f r) -> PFM f m r
  M : (act : m r) -> PFM f m r

public export
data Stream : (f,m : Type -> Type) -> (r : Type) -> Type where
  Lift : PFM f m r -> Stream f m r
  Bind :  Stream f m r -> (r -> Stream f m s) -> Stream f m s

||| Calculates the number of left-nested binds in a `Stream`.
public export
depth : Stream f m r -> Nat
depth (Lift x)   = 0
depth (Bind x y) = S $ depth x

public export
Sized (Stream f m r) where
  size = depth

||| A view on a `Stream` with left-nested binds reassociated.
public export
data View : (f,m : Type -> Type) -> (r : Type) -> Type where
  VLift : PFM f m r -> View f m r
  VBind : PFM f m r -> (r -> Stream f m s) -> View f m s

view_ : (s : Stream f m r) -> (0 _ : SizeAccessible s) -> View f m r
view_ (Bind x y) (Access rec) = case x of
  Lift v   => VBind v y
  Bind z w => view_ (Bind z $ \v => Bind (w v) y) (rec _ reflexive)
view_ (Lift v) _ = VLift v

export %inline
toView : (s : Stream f m r) -> View f m r
toView s = view_ s (sizeAccessible s)

export %inline
fromView : View f m r -> Stream f m r
fromView (VLift x)   = Lift x
fromView (VBind x y) = Bind (Lift x) y

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (Stream f m) where
  map f s = Bind s (Lift . P . f)

export %inline
Applicative (Stream f m) where
  pure      = Lift . P
  fn <*> fk = Bind fn (\fun => map (fun $ ) fk)

export %inline
Monad (Stream f m) where
  (>>=) = Bind

export %inline
HasIO io => HasIO (Stream f io) where
  liftIO = Lift . M . liftIO

--------------------------------------------------------------------------------
--          Lifting Values
--------------------------------------------------------------------------------

export %inline
wrap : f (Stream f m r) -> Stream f m r
wrap v = Bind (Lift $ F v) id

export %inline
effect : m (Stream f m r) -> Stream f m r
effect v = Bind (Lift $ M v) id

export %inline
yields : f r -> Stream f m r
yields = Lift . F

export %inline
yieldsM : m (f r) -> Stream f m r
yieldsM v = Bind (Lift $ M v) (Lift . F)

export %inline
lift : m r -> Stream f m r
lift = Lift . M

--------------------------------------------------------------------------------
--          Running Streams
--------------------------------------------------------------------------------

public export
data Empty : Type -> Type where

export
runWith : Fuel -> Stream Empty IO r -> IO (Maybe r)
runWith fuel s = fromPrim $ go fuel (toView s)
  where go : Fuel -> View Empty IO r -> (1 w : %World) -> IORes (Maybe r)
        go Dry _                w = MkIORes Nothing w
        go (More x) (VBind y z) w = case y of
          P val => go x (toView $ z val) w
          M act =>
            let MkIORes val w2 = toPrim act w
             in go x (toView $ z val) w2
        go (More x) (VLift $ P r) w = MkIORes (Just r) w
        go (More x) (VLift $ M r)      w =
            let MkIORes val w2 = toPrim r w
             in MkIORes (Just val) w2

export
runPure : Fuel -> Stream Empty Empty r -> Maybe r
runPure fuel s = go fuel (toView s)
  where go : Fuel -> View Empty Empty r -> Maybe r
        go Dry _                = Nothing
        go (More x) (VBind y z) = case y of
          P val => go x (toView $ z val)
          M act impossible
          F eff impossible
        go (More x) (VLift $ P r) = Just r
        go (More x) (VLift $ M r) impossible
        go (More x) (VLift $ F r) impossible

export %inline
runWith_ : Fuel -> Stream Empty IO r -> IO ()
runWith_ f = ignore . runWith f

export partial %inline
run : Stream Empty IO r -> IO (Maybe r)
run = runWith forever

export partial %inline
run_ : Stream Empty IO r -> IO ()
run_ = runWith_ forever

export
concat : Stream (Stream f m) m r -> Stream f m r
concat s = case toView s of
  VBind (P val) y => pure val >>= \v => concat (y v)
  VBind (F eff) y => eff      >>= \v => concat (y v)
  VBind (M act) y => lift act >>= \v => concat (y v)
  VLift (P val)   => pure val
  VLift (F eff)   => eff
  VLift (M act)   => lift act

--------------------------------------------------------------------------------
--          Mapping Values
--------------------------------------------------------------------------------

maps_ : ((0 x : _) -> f x -> g x) -> Stream f m r -> Stream g m r
maps_ fun fn = case toView fn of
  VBind (P val) fu => pure val >>= \x => maps_ fun (fu x)
  VBind (F eff) fu => yields (fun _ eff) >>= \x => maps_ fun (fu x)
  VBind (M act) fu => lift act >>= \x => maps_ fun (fu x)
  VLift (P val)    => pure val
  VLift (F eff)    => yields $ fun _ eff
  VLift (M act)    => lift act

mapsM_ : ((0 x : _) -> f x -> m (g x)) -> Stream f m r -> Stream g m r
mapsM_ fun fn = case toView fn of
  VBind (P val) fu => pure val >>= \x => mapsM_ fun (fu x)
  VBind (F eff) fu => lift (fun _ eff) >>= yields >>= \v => mapsM_ fun (fu v)
  VBind (M act) fu => lift act >>= \x => mapsM_ fun (fu x)
  VLift (P val)    => pure val
  VLift (F eff)    => Bind (lift $ fun _ eff) yields
  VLift (M act)    => lift act

export %inline
maps : (forall x . f x -> g x) -> Stream f m r -> Stream g m r
maps fun = maps_ (\_ => fun)

export %inline
mapsM : (forall x . f x -> m (g x)) -> Stream f m r -> Stream g m r
mapsM fun = mapsM_ (\_ => fun)

--------------------------------------------------------------------------------
--          Creating Streams
--------------------------------------------------------------------------------

export
unfold : (s -> m (Either r (f s))) -> s -> Stream f m r
unfold fun vs = lift (fun vs) >>= go
  where go : Either r (f s) -> Stream f m r
        go (Left x)  = pure x
        go (Right x) = yields x >>= unfold fun

export
repeat : f () -> Stream f m Void
repeat v = yields v >> repeat v

export
replicate : Nat -> f () -> Stream f m ()
replicate 0     _ = pure ()
replicate (S k) v = yields v >> replicate k v

--------------------------------------------------------------------------------
--          Splitting Streams
--------------------------------------------------------------------------------

export
splitsAt : Nat -> Stream f m r -> Stream f m (Stream f m r)
splitsAt 0     x = pure x
splitsAt (S k) x = case toView x of
  VLift y         => pure (Lift y)
  VBind (P val) z => Bind (pure val)   (\v => splitsAt (S k) (z v))
  VBind (F eff) z => Bind (yields eff) (\v => splitsAt k (z v))
  VBind (M act) z => Bind (lift act)   (\v => splitsAt (S k) (z v))

export
take : Nat -> Stream f m r -> Stream f m ()
take n = ignore . splitsAt n
