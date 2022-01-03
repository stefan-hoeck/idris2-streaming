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
data Step : (f : Type -> Type) -> (e,r : Type) -> Type where
  Yield : (val : f r) -> Step f e r
  Done  : (res : r) -> Step f e r
  Fail  : (err : e) -> Step f e r

public export
data Stream : (f : Type -> Type) -> (e,r : Type) -> Type where
  Bind : Stream f m r -> (r -> Stream f m s) -> Stream f m s
  M    : IO (Step f e r) -> Stream f e r

||| Calculates the number of left-nested binds in a `Stream`.
public export
depth : Stream f e r -> Nat
depth (Bind x _) = S $ depth x
depth (M _)      = 0

public export
Sized (Stream f e r) where
  size = depth

||| A view on a `Stream` with left-nested binds reassociated.
public export
data View : (f : Type -> Type) -> (e,r : Type) -> Type where
  VBind : IO (Step f e r) -> (r -> Stream f e s) -> View f e s
  VM    : IO (Step f e r) -> View f e r

view_ : (s : Stream f e r) -> (0 _ : SizeAccessible s) -> View f e r
view_ (Bind x y) (Access rec) = case x of
  M v      => VBind v y
  Bind z w => view_ (Bind z $ \v => Bind (w v) y) (rec _ reflexive)
view_ (M v) _ = VM v

export %inline
toView : (s : Stream f e r) -> View f e r
toView s = view_ s (sizeAccessible s)

export %inline
fromView : View f e r -> Stream f e r
fromView (VBind x y) = Bind (M x) y
fromView (VM x)      = M x

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
pureStream : r -> Stream f e r
pureStream = M . pure . Done

export %inline
lift : IO r -> Stream f e r
lift = M . map Done

export
Functor (Stream f e) where
  map f s = Bind s (pureStream . f)

export %inline
Applicative (Stream f m) where
  pure      = pureStream
  fn <*> fk = Bind fn (\fun => map (fun $ ) fk)

export %inline
Monad (Stream f m) where
  (>>=) = Bind

export %inline
HasIO io => HasIO (Stream f e) where
  liftIO = lift . liftIO

--------------------------------------------------------------------------------
--          Lifting Values
--------------------------------------------------------------------------------

export %inline
fail : e -> Stream f e r
fail = M . pure . Fail

export %inline
yields : f r -> Stream f e r
yields = M . pure . Yield

export %inline
wrap : f (Stream f e r) -> Stream f e r
wrap v = Bind (yields v) id

export %inline
effect : IO (Stream f e r) -> Stream f e r
effect v = Bind (lift v) id

export %inline
yieldsM : IO (f r) -> Stream f m r
yieldsM v = Bind (lift v) yields

--------------------------------------------------------------------------------
--          Running Streams
--------------------------------------------------------------------------------

public export
data Empty : Type -> Type where

export
runWith : Fuel -> Stream Empty e r -> IO (Either e $ Maybe r)
runWith fuel s = fromPrim $ go fuel (toView s)
  where go : Fuel -> View Empty e r -> (1 w : %World) -> IORes (Either e $ Maybe r)
        go Dry _                w = MkIORes (Right Nothing) w
        go (More x) (VBind y z) w =
          let MkIORes val w2 = toPrim y w
           in case val of
                Done res => go x (toView $ z res) w2
                Fail err => MkIORes (Left err) w2
                Yield _ impossible

        go (More x) (VM r) w =
            let MkIORes val w2 = toPrim r w
             in case val of
                Done res => MkIORes (Right $ Just res) w2
                Fail err => MkIORes (Left err) w2
                Yield _ impossible

export %inline
runWith_ : Fuel -> Stream Empty e r -> IO ()
runWith_ f = ignore . runWith f

export %inline covering
run : Stream Empty e r -> IO (Either e r)
run s = fromPrim $ go (toView s)
  where covering go : View Empty e r -> (1 w : %World) -> IORes (Either e r)
        go (VBind y z) w =
          let MkIORes val w2 = toPrim y w
           in case val of
                Done res => go (toView $ z res) w2
                Fail err => MkIORes (Left err) w2
                Yield _ impossible

        go (VM r) w =
            let MkIORes val w2 = toPrim r w
             in case val of
                Done res => MkIORes (Right res) w2
                Fail err => MkIORes (Left err) w2
                Yield _ impossible

export %inline covering
run_ : Stream Empty e r -> IO ()
run_ = runWith_ forever

--------------------------------------------------------------------------------
--          Mapping Values
--------------------------------------------------------------------------------

export
mapStepSt :  ((0 x : _) -> st -> Step f e1 x -> (st,Stream g e2 x))
          -> (state : st)
          -> Stream f e1 r
          -> Stream g e2 r
mapStepSt fun st1 s = case toView s of
  VBind x g => assert_total $ effect $ do
    vx <- x
    let (st2,str) = fun _ st1 vx
    pure $ Bind str (\v => mapStepSt fun st2 (g v))
  VM x      => effect $ snd . fun _ st1 <$>  x

export
mapStep :  ((0 x : _) -> IO (Step f e1 x) -> Stream g e2 x)
        -> Stream f e1 r
        -> Stream g e2 r
mapStep fun s = case toView s of
  VBind x g => assert_total $ Bind (fun _ x) (\v => mapStep fun (g v))
  VM x      => fun _ x

joinStep : IO (Step (Stream f e) e r) -> Stream f e r
joinStep io = effect $ do
  st <- io
  case st of
    Yield val => pure val
    Done res  => pure $ pureStream res
    Fail err  => pure $ fail err

export %inline
concat : Stream (Stream f e) e r -> Stream f e r
concat = mapStep (\_,v => joinStep v)

export
maps : (forall x . f x -> g x) -> Stream f e r -> Stream g e r
maps fun = mapStep $ \_ => M . map fun'
  where fun' : Step f e s -> Step g e s
        fun' (Yield val) = Yield (fun val)
        fun' (Done res)  = Done res
        fun' (Fail err)  = Fail err

export
mapsIO : (forall x . f x -> IO (g x)) -> Stream f e r -> Stream g e r
mapsIO fun = mapStep $ \_,v => M $ v >>= fun'
  where fun' : Step f e s -> IO (Step g e s)
        fun' (Yield val) = Yield <$> fun val
        fun' (Done res)  = pure $ Done res
        fun' (Fail err)  = pure $ Fail err

export
handle : (forall x . f x -> IO x) -> Stream f e r -> Stream Empty e r
handle fun = mapStep $ \_,v => M $ v >>= fun'
  where fun' : Step f e s -> IO (Step Empty e s)
        fun' (Yield val) = Done <$> fun val
        fun' (Done res)  = pure $ Done res
        fun' (Fail err)  = pure $ Fail err

export
handleE : (forall x . f x -> IO (Either e x))
        -> Stream f e r
        -> Stream Empty e r
handleE fun = mapStep $ \_,v => M $ v >>= fun'
  where fun' : Step f e s -> IO (Step Empty e s)
        fun' (Yield val) = either Fail Done <$> fun val
        fun' (Done res)  = pure $ Done res
        fun' (Fail err)  = pure $ Fail err

--------------------------------------------------------------------------------
--          Creating Streams
--------------------------------------------------------------------------------

export covering
unfold : (s -> IO (Either r (f s))) -> s -> Stream f Void r
unfold fun vs = lift (fun vs) >>= go
  where go : Either r (f s) -> Stream f Void r
        go (Left x)  = pure x
        go (Right x) = yields x >>= unfold fun

export covering
repeat : f () -> Stream f m Void
repeat v = yields v >> repeat v

export
replicate : Nat -> f () -> Stream f m ()
replicate 0     _ = pure ()
replicate (S k) v = yields v >> replicate k v
