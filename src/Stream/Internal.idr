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

public export
data Stream : (f,m : Type -> Type) -> (r : Type) -> Type where
  Bind : Stream f m r -> (r -> Stream f m s) -> Stream f m s
  P    : r -> Stream f m r
  F    : f r -> Stream f m r
  M    : m r -> Stream f m r

||| Calculates the number of left-nested binds in a `Stream`.
public export
depth : Stream f m r -> Nat
depth (Bind x y) = S $ depth x
depth (P x)      = 0
depth (F x)      = 0
depth (M x)      = 0

public export
Sized (Stream f m r) where
  size = depth

||| A view on a `Stream` with left-nested binds reassociated.
public export
data View : (f,m : Type -> Type) -> (r : Type) -> Type where
  BindP : r   -> (r -> Stream f m s) -> View f m s
  BindF : f r -> (r -> Stream f m s) -> View f m s
  BindM : m r -> (r -> Stream f m s) -> View f m s
  VP    : r   -> View f m r
  VF    : f r -> View f m r
  VM    : m r -> View f m r

view_ : (s : Stream f m r) -> (0 _ : SizeAccessible s) -> View f m r
view_ (Bind x y) (Access rec) = case x of
  F v      => BindF v y
  Bind z w => view_ (Bind z $ \v => Bind (w v) y) (rec _ reflexive)
  P v      => BindP v y
  M v      => BindM v y
view_ (F v) _ = VF v
view_ (P v) _ = VP v
view_ (M v) _ = VM v

export %inline
toView : (s : Stream f m r) -> View f m r
toView s = view_ s (sizeAccessible s)

export %inline
fromView : View f m r -> Stream f m r
fromView (BindP x y) = Bind (P x) y
fromView (BindF x y) = Bind (F x) y
fromView (BindM x y) = Bind (M x) y
fromView (VF x)      = F x
fromView (VP x)      = P x
fromView (VM x)      = M x

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (Stream f m) where
  map f s = Bind s (P . f)

export %inline
Applicative (Stream f m) where
  pure      = P
  fn <*> fk = Bind fn (\fun => map (fun $ ) fk)

export %inline
Monad (Stream f m) where
  (>>=) = Bind

export %inline
HasIO io => HasIO (Stream f io) where
  liftIO = M . liftIO

--------------------------------------------------------------------------------
--          Lifting Values
--------------------------------------------------------------------------------

export %inline
wrap : f (Stream f m r) -> Stream f m r
wrap v = Bind (F v) id

export %inline
effect : m (Stream f m r) -> Stream f m r
effect v = Bind (M v) id

export %inline
yields : f r -> Stream f m r
yields = F

export %inline
yieldsM : m (f r) -> Stream f m r
yieldsM v = Bind (M v) F

export %inline
lift : m r -> Stream f m r
lift = M

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
        go (More x) (BindM y z) w =
          let MkIORes val w2 = toPrim y w
           in go x (toView $ z val) w2
        go (More x) (BindP y z) w = go x (toView $ z y) w

        go (More x) (VM r) w =
            let MkIORes val w2 = toPrim r w
             in MkIORes (Just val) w2
        go (More x) (VP r) w = MkIORes (Just r) w

export
runPure : Fuel -> Stream Empty Empty r -> Maybe r
runPure fuel s = go fuel (toView s)
  where go : Fuel -> View Empty Empty r -> Maybe r
        go (More x) (BindP y z) = go x (toView $ z y)
        go (More x) (VP r)      = Just r
        go Dry _                = Nothing

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
  BindF eff y => eff      >>= \v => concat (y v)
  BindP val y => pure val >>= \v => concat (y v)
  BindM act y => lift act >>= \v => concat (y v)
  VF eff      => eff
  VP val      => pure val
  VM act      => lift act

--------------------------------------------------------------------------------
--          Mapping Values
--------------------------------------------------------------------------------

maps_ : ((0 x : _) -> f x -> g x) -> Stream f m r -> Stream g m r
maps_ fun fn = case toView fn of
  BindF eff fu => yields (fun _ eff) >>= \x => maps_ fun (fu x)
  BindP val fu => pure val >>= \x => maps_ fun (fu x)
  BindM act fu => lift act >>= \x => maps_ fun (fu x)
  VP val       => pure val
  VF eff       => yields $ fun _ eff
  VM act       => lift act

mapsM_ : ((0 x : _) -> f x -> m (g x)) -> Stream f m r -> Stream g m r
mapsM_ fun fn = case toView fn of
  BindF eff fu => lift (fun _ eff) >>= yields >>= \v => mapsM_ fun (fu v)
  BindP val fu => pure val >>= \x => mapsM_ fun (fu x)
  BindM act fu => lift act >>= \x => mapsM_ fun (fu x)
  VP val       => pure val
  VF eff       => Bind (lift $ fun _ eff) yields
  VM act       => lift act

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
  BindF eff z => Bind (yields eff) (\v => splitsAt k (z v))
  BindP val z => Bind (pure val)   (\v => splitsAt (S k) (z v))
  BindM act z => Bind (lift act)   (\v => splitsAt (S k) (z v))
  VF v        => pure (F v)
  VP v        => pure (P v)
  VM v        => pure (M v)

export
take : Nat -> Stream f m r -> Stream f m ()
take n = ignore . splitsAt n
