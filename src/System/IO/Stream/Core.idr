module System.IO.Stream.Core

import Control.MonadRec
import Data.IORef
import Data.Maybe
import Data.MVar
import System.Concurrency

%default total

--------------------------------------------------------------------------------
--          Input Streams
--------------------------------------------------------------------------------

public export
record InputStream (a : Type) where
  constructor MkIS
  ||| Try to get a value from an input stream
  read   : IO (Maybe a)
  ||| Push back a value to an input stream
  unReadAt : a -> IO ()

export
unRead : a -> InputStream a -> IO ()
unRead = flip unReadAt

export
peak : InputStream a -> IO (Maybe a)
peak is = do
  ma <- read is
  maybe (pure ()) (unReadAt is) ma
  pure ma

||| Creates an `InputStream` from a value-producing action.
||| 
||| `makeInputStream m` calls the action `m` each time you request a value
||| from the `InputStream`. The given action is extended with the default
||| pushback mechanism.
export
makeInputStream : IO (Maybe a) -> IO (InputStream a)
makeInputStream m = do
    doneRef <- newIORef False
    pbRef   <- newIORef (the (List a) [])

    let grab : IO (Maybe a)
        grab = do
          []      <- readIORef pbRef
            | (x ::xs) => writeIORef pbRef xs $> Just x
          False   <- readIORef doneRef | True => pure Nothing
          Nothing <- m | mv => pure mv
          writeIORef doneRef True $> Nothing

    pure $ MkIS grab (\va => modifyIORef pbRef (va ::))

||| An empty `InputStream` that yields `Nothing` immediately.
export
nullInput : IO (InputStream a)
nullInput = makeInputStream $ pure Nothing

||| Converts an `InputStream` into a thread-safe `InputStream`, at a slight
||| performance penalty.
||| 
||| For performance reasons, this library provides non-thread-safe streams by
||| default. Use the `locking` functions to convert these streams into slightly
||| slower, but thread-safe, equivalents.
|||
||| TODO: Should we keep track of thread-safety at the type level?
export
lockingInputStream : InputStream a -> IO (InputStream a)
lockingInputStream (MkIS g p) = do
    m <- makeMutex
    pure $ MkIS (withMutex m g) (withMutex m . p)

--------------------------------------------------------------------------------
--          Output Streams
--------------------------------------------------------------------------------

public export
record OutputStream (a : Type) where
  constructor MkOS
  writeTo : Maybe a -> IO ()

||| Flipped version of `writeTo`.
export
write : Maybe a -> OutputStream a -> IO ()
write = flip writeTo

||| Creates an `OutputStream` from a value-consuming action.
||| 
||| `makeOutputStream f` runs the computation `f` on each value fed to it.
||| 
||| `makeOutputStream` also ensures that output streams
||| no longer receive data once EOF is received (i.e. you can now assume that
||| makeOutputStream will feed your function @Nothing@ at most once.)
export
makeOutputStream : (Maybe a -> IO ()) -> IO (OutputStream a)
makeOutputStream func = MkOS . go <$> newIORef False
  where go : IORef Bool -> Maybe a -> IO ()
        go closedRef m = do
          False <- readIORef closedRef | True => pure ()
          when (isNothing m) $ writeIORef closedRef True
          func m

||| An empty `OutputStream` that discards any input fed to it.
export
nullOutput : IO (OutputStream a)
nullOutput = makeOutputStream . const $ pure ()

||| `concatInputStreams` concatenates a list of `InputStream`s, analogous to
||| `(++)` for lists.
||| 
||| Subsequent `InputStream`s continue where the previous one `InputStream`
||| ends.
||| 
||| Note: values pushed back to the `InputStream` returned by
||| `concatInputStreams` are not propagated to any of the source
||| `InputStream`s.
export
concatInputStreams : List (InputStream a) -> IO (InputStream a)
concatInputStreams streams = do
    ref <- newIORef streams

    let go : List (InputStream a) -> IO (Maybe a)
        go []       = pure Nothing
        go (h :: t) = do
          Just v <- read h | Nothing => writeIORef ref t >> go t
          pure (Just v)

    makeInputStream (readIORef ref >>= go)

||| `appendInputStream` concatenates two `InputStream`s, analogous to `(++)`
||| for lists.
||| 
||| The second `InputStream` continues where the first `InputStream` ends.
||| 
||| Note: values pushed back to `appendInputStream` are not propagated to either
||| wrapped `InputStream`.
export
appendInputStream : InputStream a -> InputStream a -> IO (InputStream a)
appendInputStream s1 s2 = concatInputStreams [s1, s2]

||| Checks if an 'InputStream' is at end-of-stream.
export
atEOF : InputStream a -> IO Bool
atEOF s = read s >>= maybe (pure True) (\k => unRead k s $> False)

||| Converts an `OutputStream` into a thread-safe `OutputStream`, at a slight
||| performance penalty.
||| 
||| For performance reasons, this library provides non-thread-safe streams by
||| default. Use the `locking` functions to convert these streams into slightly
||| slower, but thread-safe, equivalents.
|||
||| TODO: Should we keep track of thread-safety at the type level?
export
lockingOutputStream : OutputStream a -> IO (OutputStream a)
lockingOutputStream (MkOS f) = do
    m <- makeMutex
    makeOutputStream $ withMutex m . f

--------------------------------------------------------------------------------
--          Connecting Streams
--------------------------------------------------------------------------------

||| Feeds input from an `InputStream` to an `OutputStream` until
||| either it returns `Nothing` or the `Fuel` runs dry.
export
connectWith : Fuel -> InputStream a -> OutputStream a -> IO ()
connectWith f is os = trSized step f ()
  where step : (f : Fuel) -> () -> IO (Step Smaller f () ())
        step Dry      _ = writeTo os Nothing $> Done ()
        step (More y) _ = do
          Just v <- read is | Nothing => writeTo os Nothing $> Done ()
          writeTo os (Just v) $> Cont y (reflexive {rel = LTE}) ()

||| Flipped version of `connectWith`. Useful for writing
||| expressions like `fromList [1,2,3] >>= connectTo (limit 100) foo`.
export %inline
connectTo : Fuel -> OutputStream a -> InputStream a -> IO ()
connectTo = flip . connectWith

||| Partial version of `connectWith`, which potentially runs forever.
export partial %inline
connect : InputStream a -> OutputStream a -> IO ()
connect = connectWith forever

||| Connects an `InputStream` to an `OutputStream` without passing the
||| end-of-stream notification through to the `OutputStream`.
||| 
||| Use this to supply an `OutputStream` with multiple `InputStream`s and use
||| `connect` for the final `InputStream` to finalize the `OutputStream`, like
||| so:
||| 
||| ```idris2 example
||| do supplyWith  fuel input1 output
|||    supplyWith  fuel input2 output
|||    connectWith fuel input3 output
||| ```
||| 
export
supplyWith : Fuel -> InputStream a -> OutputStream a -> IO ()
supplyWith f is os = trSized step f ()
  where step : (f : Fuel) -> () -> IO (Step Smaller f () ())
        step Dry      _ = pure $ Done ()
        step (More y) _ = do
          Just v <- read is | Nothing => pure $ Done ()
          writeTo os (Just v) $> Cont y (reflexive {rel = LTE}) ()

||| Flipped version of `supplyWith`. Useful for writing
||| expressions like `fromList [1,2,3] >>= supplyTo (limit 100) foo`.
export %inline
supplyTo : Fuel -> OutputStream a -> InputStream a -> IO ()
supplyTo = flip . supplyWith

||| Partial version of `supplyWith`, which potentially runs forever.
export partial %inline
supply : InputStream a -> OutputStream a -> IO ()
supply = supplyWith forever

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

||| A `Generator` is a coroutine monad that can be used to define complex
||| `InputStream`s. You can cause a value of type @Just r@ to appear when the
||| `InputStream` is read by calling `yield`:
||| 
||| ```idris2 example
||| g : Generator Int ()
||| g = do
|||     yield 1
|||     yield 2
|||     yield 3
||| ```
||| 
||| A `Generator` can be turned into an `InputStream` by calling
||| `fromGenerator`:
||| 
||| ```idris2 example
||| m : IO (List Int)
||| m = fromGenerator g >>= System.IO.Streams.toList
||| ```
||| 
||| As a general rule, you should not acquire resources that need to be freed
||| from a `Generator`, because there is no guarantee the coroutine continuation
||| will ever be called, nor can you catch an exception from within a
||| `Generator`.
public export
record Generator r a where
  constructor MkGen
  unG : IO (Either (r, Generator r a) a)

genBind : Generator r a -> (a -> Generator r b) -> Generator r b
genBind (MkGen m) f = MkGen (m >>= either step (unG . f))
  where step : (r, Generator r a) -> IO (Either (r, Generator r b) b)
        step (v,g) = assert_total (pure . Left . (v,) $ genBind g f)

export
Functor (Generator r) where
  map f (MkGen m) = MkGen (m >>= either step (pure . Right . f))
  where step : (r, Generator r a) -> IO (Either (r, Generator r b) b)
        step (v,g) = assert_total (pure . Left . (v,) $ map f g)

export
Applicative (Generator r) where
  pure = MkGen . pure . Right
  m <*> n = genBind m (\fun => apply fun <$> n)

export %inline
Monad (Generator r) where
  (>>=) = genBind

export
HasIO (Generator r) where
  liftIO m = MkGen $ Right <$> m

export
yield : r -> Generator r ()
yield vr = MkGen . pure $ Left (vr, pure ())

||| Turns a `Generator` into an `InputStream`.
export
fromGenerator : Generator r a -> IO (InputStream r)
fromGenerator (MkGen m) = do
    ref <- newIORef m

    let go : IO (Maybe r)
        go = do
          Left (v,MkGen n) <- join (readIORef ref) | Right _ => pure Nothing
          writeIORef ref n 
          pure (Just v)

    makeInputStream go

--------------------------------------------------------------------------------
--          Consumers
--------------------------------------------------------------------------------

public export
record Consumer c a where
  constructor MkCon
  unC : IO (Either (Maybe c -> Consumer c a) a)

conBind : Consumer c a -> (a -> Consumer c b) -> Consumer c b
conBind (MkCon m) f = MkCon (m >>= either step (unC . f))
  where step :  (Maybe c -> Consumer c a)
             -> IO (Either (Maybe c -> Consumer c b) b)
        step g = assert_total (pure . Left $ ((`conBind` f) . g))

export
Functor (Consumer r) where
  map f (MkCon m) = MkCon (m >>= either step (pure . Right . f))
  where step :  (Maybe c -> Consumer c a)
             -> IO (Either (Maybe c -> Consumer c b) b)
        step g = assert_total (pure . Left $ map f . g)

export
Applicative (Consumer r) where
  pure = MkCon . pure . Right
  m <*> n = conBind m (\fun => apply fun <$> n)

export %inline
Monad (Consumer r) where
  (>>=) = conBind

export
HasIO (Consumer r) where
  liftIO m = MkCon $ Right <$> m

export
await : Consumer r (Maybe r)
await = MkCon $ pure (Left pure)

export
fromConsumer : Consumer r a -> IO (OutputStream r)
fromConsumer c0 = newIORef c0 >>= makeOutputStream . go
  where
    go : IORef (Consumer r a) -> Maybe r -> IO ()
    go ref mr = do
       c  <- readIORef ref
       c' <- c.unC >>= either step (const $ pure c)
       writeIORef ref c'

     where step : (Maybe r -> Consumer r a) -> IO (Consumer r a)
           step g = MkCon . pure <$> unC (g mr)
