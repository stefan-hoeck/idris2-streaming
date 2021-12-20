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
data Input : (e, a, r : Type) -> Type where
  Val : (val : a) -> Input e a r
  Err : (err : e) -> Input e a r
  Res : (res : r) -> Input e a r

||| An input stream produces effectful chunks of
||| input of type `a` possibly resulting in errors of
||| type `e` and ending with a result of type `r`.
|||
||| We can pull (`read`) values from an input stream
||| and push (`unRead`) non-empty chunks of values to an input Stream.
public export
record InputStream e a r where
  constructor IS
  read   : IO (Input e (List1 a) r)
  unRead : List1 a -> IO ()

||| Peeks the next piece of input from an input stream.
||| All peeked values are written back to the input stream's
||| buffer.
export
peek : InputStream e a r -> IO (Input e (List1 a) r)
peek is = do
  Val vs <- read is | ip => pure ip
  unRead is vs
  pure $ Val vs

export
makeInputStream : IO (Input e (List1 a) r) -> IO (InputStream e a r)
makeInputStream io = do
  ref  <- newIORef (the (List a) [])
  done <- newIORef (the (Input e () r) $ Val ())

  let rd : IO (Input e (List1 a) r)
      rd = do
        Val _  <- readIORef done
          | Err err => pure $ Err err
          | Res res => pure $ Res res

        []      <- readIORef ref
          | (h :: t) => writeIORef ref [] $> Val (h ::: t)

        v <- io
        case v of
          Res res => writeIORef done (Res res) $> v
          Err err => writeIORef done (Err err) $> v
          _       => pure v

  pure $ IS rd $ \vs => modifyIORef ref (forget vs ++)

--------------------------------------------------------------------------------
--          Sequencing Input Streams
--------------------------------------------------------------------------------

public export
data HSeq : (f : Type -> Type) -> (i,o : Type) -> Type where
  Nil  : HSeq f i i
  (::) : {0 x : _} -> (fun : i -> f x) -> HSeq f x o -> HSeq f i o

public export
data StreamSeq : (e,a,r : Type) -> Type where
  Seq :  {0 x : _}
      -> (current : InputStream e a x)
      -> (seq     : HSeq (InputStream e a) x r)
      -> StreamSeq e a r

runSeq :  IORef (StreamSeq e a r)
       -> InputStream e a x
       -> HSeq (InputStream e a) x r
       -> PrimIO (Input e (List1 a) r)
runSeq ref sx fs w =
  let MkIORes res w2 = toPrim (writeIORef ref (Seq sx fs) >> read sx) w
   in case res of
        Val vs => MkIORes (Val vs) w2
        Err ve => MkIORes (Err ve) w2
        Res vx => case fs of
          f :: fs => runSeq ref (f vx) fs w2
          []      => MkIORes (Res vx) w2

export
seq :  InputStream e a x
    -> HSeq (InputStream e a) x r
    -> IO (InputStream e a r)
seq is ss = do
  ref <- newIORef (Seq is ss)
  makeInputStream $ do
    Seq sx fs <- readIORef ref
    fromPrim $ runSeq ref sx fs

export
concat : List (InputStream e a ()) -> IO (InputStream e a ())
concat []        = makeInputStream (pure $ Res ())
concat (s :: ss) = seq s $ hseq (reverse ss) Nil
  where hseq :  List (InputStream e a ())
             -> HSeq (InputStream e a) () ()
             -> HSeq (InputStream e a) () ()
        hseq (x :: xs) ss = hseq xs ((\_ => x) :: ss)
        hseq []        ss = ss


export
append : InputStream e a () -> InputStream e a () -> IO (InputStream e a ())
append i1 i2 = concat [i1,i2]

--------------------------------------------------------------------------------
--          Output Stream
--------------------------------------------------------------------------------

public export
record OutputStream e a r where
  constructor OS
  write : Maybe (List1 a) -> IO (Input e () r)
