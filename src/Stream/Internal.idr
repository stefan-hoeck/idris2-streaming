module Stream.Internal

import Data.IORef
import Data.List1

--------------------------------------------------------------------------------
--          Input Streams
--------------------------------------------------------------------------------

||| Input from an `InputStream`.
|||
||| This is parameterized over error type `err` and value
||| type `a`.
public export
data Input : (err, a : Type) -> Type where
  Error  : (error : err)  -> Input err a
  Values : (v : a) -> (vs : List a) -> Input err a
  Done   : Input err a

||| An input stream produces effectful chunks of
||| input of type `a` possibly resuliting in errors of
||| type `err`.
|||
||| We can pull (`read`) values from an input stream
||| and push (`unRead`) non-empty chunks of values to an input Stream.
public export
record InputStream err a where
  constructor IS
  read   : IO (Input err a)
  unRead : List1 a -> IO ()

||| Peeks the next piece of input from an input stream.
||| All peeked values are written back to the input stream's
||| buffer.
export
peek : InputStream err a -> IO (Input err a)
peek is = do
  Values v vs <- read is | ip => pure ip
  unRead is (v ::: vs)
  pure $ Values v vs

export
makeInputStream : IO (Input err a) -> IO (InputStream err a)
makeInputStream io = do
  ref  <- newIORef (the (List a) [])
  done <- newIORef False
  let rd : IO (Input err a)
      rd = do
        False <- readIORef done | True => pure Done
        []    <- readIORef ref
          | (h :: t) => writeIORef ref [] $> Values h t
        v <- io
        case v of
          Done    => writeIORef done True $> v
          Error _ => writeIORef done True $> v
          _       => pure v

  pure $ IS rd $ \vs => modifyIORef ref (forget vs ++)


runConcat :  IORef (List $ InputStream err a)
          -> List (InputStream err a)
          -> PrimIO (Input err a)
runConcat ref (x :: xs) w =
  let MkIORes res w2 = toPrim (read x) w
   in case res of
        Values _ _ => toPrim (writeIORef ref (x :: xs) $> res) w2
        Done       => runConcat ref xs w2
        Error _    => toPrim (writeIORef ref [] $> res) w2
runConcat ref [] w = toPrim (writeIORef ref [] $> Done) w

export
concat : List (InputStream err a) -> IO (InputStream err a)
concat ss = do
  ref <- newIORef ss
  makeInputStream $ do
    (h :: t) <- readIORef ref | [] => pure Done 
    res <- read h
    case res of
      Values _ _ => pure res
      Done       => fromPrim $ runConcat ref t
      Error err  => writeIORef ref [] $> Error err

export
append : InputStream err a -> InputStream err a -> IO (InputStream err a)
append i1 i2 = concat [i1,i2]
