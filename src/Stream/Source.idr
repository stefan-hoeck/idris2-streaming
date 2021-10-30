module Stream.Source

import Data.ByteString
import Data.Colist
import Data.Fuel
import Data.Iterable
import Data.SOP
import System.File

%default total

--------------------------------------------------------------------------------
--          Source
--------------------------------------------------------------------------------

public export
data Source : (err,val,res : Type) -> Type

public export
data ParList : (err,res : Type) -> (vals : List Type) -> Type where
  Nil  :  ParList err res []
  (::) :  (src  : Source err val res)
       -> (srcs : ParList err res vals)
       -> ParList err res (val :: vals)

||| Single step evaluation result of a `Source`.
||| This can either be a new value (to be consumed
||| by a sink), a final result signalling that the
||| will produce no more values, or an error.
public export
data Result : (err,val,res : Type) -> Type where
  Done  : (result : res) -> Result err val res
  Error : (error : err)  -> Result err val res
  Value : (value : val)  -> Result err val res

||| Potentially infinite effectful data source.
|||
||| In a total program, querying a `Source` for new data *must* lead
||| to a `Result` in a finite amount of time.
|||
||| Having a large number of constructors may seem cumbersome
||| compared to the elegant solutions found in similar
||| Haskell libraries. It comes with a big advantage,
||| however: We can recursively traverse a `Source` tree
||| cleaning up all active resources along the way.
public export
data Source : (err,val,res : Type) -> Type where
  ||| A pure, stateful source. Use this to create a source
  ||| from a stateful computation, for instance
  ||| an iterative calculation or the elements
  ||| from a `List` or `Stream` of values.
  ST   :  (state : st)
       -> (fun   : st -> Result err (st,val) res)
       -> Source err val res

  ||| A system resource such as a file or a socket.
  ||| This comes with instructions how to clean up
  ||| the source, once it can no longer produce any
  ||| values or is no longer needed.
  Sys  :  (next : IO (Result err val res))
       -> (release : IO ())
       -> Source err val res

  ||| An empty `Source`, throwing an error.
  Fail : (error : err) -> Source err val res

  ||| An empty `Source`, producing only a result.
  Pure : (result : res) -> Source err val res

  ||| Sequential composition of sources.
  |||
  ||| A new source is created from an existing on, once
  ||| the latter has spent all its values.
  Bind :  Source err val res
       -> (res -> IO (Source err val res2))
       -> Source err val res2

  ||| Parallel composition (zipping) of sources.
  |||
  ||| The list of sources generates values until the
  ||| first one is spent.
  Par  : (sources : ParList err res vals)
       -> Source err (NP I vals) res

  ||| A `Source` of `Source`s.
  |||
  ||| Creates a child source from each value of a parent
  ||| source, consuming the child until it is exhaused.
  ||| This can for instance be used to read all data
  ||| from a list of files (or a directory).
  |||
  ||| Note: The `parent` decides, when this source is spent.
  |||       Once a child terminates with a `val2`, a new child
  |||       is generated (if possible).
  |||
  |||       It is important that a child terminates with a
  |||       result of the same type as the values it produces,
  |||       to keep single step evaluation deterministic.
  Fan  :  (parent       : Source err val res)
       -> (mkChild      : val -> IO (Source err val2 val2))
       -> (currentChild : Source err val2 val2)
       -> Source err val2 res

export %inline
Functor (Source err val) where
  map f sr = Bind sr (pure . Pure . f)

export
Applicative (Source err val) where
  pure = Pure
  sf <*> sa = Bind sf (\fun => pure $ apply fun <$> sa)

export %inline
Monad (Source err val) where
  s >>= f = Bind s (pure . f)

||| Sequential composition of `Source`s.
export
Semigroup (Source err val res) where
  sa <+> sb = Bind sa (pure . const sb)

export
Monoid res => Monoid (Source err val res) where
  neutral = Pure neutral

--------------------------------------------------------------------------------
--          Single Step Evaluation
--------------------------------------------------------------------------------

mutual
  releaseList : ParList err res vals -> IO ()
  releaseList []            = pure ()
  releaseList (src :: srcs) = release src >> releaseList srcs

  ||| Recursively release all open resources of
  ||| the given `Source`.
  export
  release : Source err val res -> IO ()
  release (ST _ _)    = pure ()
  release (Sys _ rel) = rel
  release (Pure _)    = pure ()
  release (Fail _)    = pure ()
  release (Bind x _)  = release x
  release (Par srcs)  = releaseList srcs
  release (Fan p _ c) = release p >> release c

mutual
  stepList :  ParList err res vals
           -> IO (Result err (NP I vals, ParList err res vals) res)
  stepList []            = pure $ Value ([],[])
  stepList (src :: srcs) = do
    Value (v,s) <- step src
      | Done  res => releaseList srcs $> Done res
      | Error err => releaseList srcs $> Error err

    Value (vs,ss) <- stepList srcs
      | Done  res => pure $ Done res
      | Error err => pure $ Error err

    pure $ Value (v :: vs, s :: ss)

  ||| Single step evaluation of a `Source`.
  |||
  ||| This either yields a `val` together with the next
  ||| source, fails with an error, or returns a result.
  ||| In the latter two cases, all internal sources are
  ||| cleaned up by invoking `release`.
  export
  step :  Source err val res
       -> IO (Result err (val, Source err val res) res)
  step (ST state fun) = case fun state of
    Done result       => pure $ Done result
    Error error       => pure $ Error error
    Value (state2, v) => pure $ Value (v, ST state2 fun)

  step (Sys next release) = do
    Value v <- next
      | Done  result => release $> Done result
      | Error err    => release $> Error err
    pure $ Value (v, Sys next release)
  
  step (Pure result) = pure $ Done result

  step (Bind src f) = do
    Value (v,src2) <- step src
      | Done result => assert_total (f result >>= step)
      | Error err   => pure $ Error err
    pure $ Value (v, Bind src2 f)

  step (Par sources) = do
    Value (vs, sources2) <- stepList sources
      | Error err => pure $ Error err
      | Done res  => pure $ Done res
    pure $ Value (vs, Par sources2)

  step (Fan parent mkChild child) = do
    Done v2           <- step child
      | Error err        => release parent $> Error err
      | Value (v,child2) => pure $ Value (v, Fan parent mkChild child2)

    Value (v,parent2) <- step parent
      | Error err        => pure $ Error err
      | Done res         => pure $ Value (v2, Pure res)

    child2            <- mkChild v
    pure $ Value (v2, Fan parent2 mkChild child2)

  step (Fail err) = pure (Error err)

--------------------------------------------------------------------------------
--          Sink
--------------------------------------------------------------------------------

public export
record Sink (a : Type) where
  constructor MkSink
  sink : a -> IO ()

export
filter : (a -> Bool) -> Sink a -> Sink a
filter f (MkSink sink) = MkSink $ \va => when (f va) (sink va)

--------------------------------------------------------------------------------
--          Driver
--------------------------------------------------------------------------------

public export
data Res : (err, res : Type) -> Type where
  SinkFull    : Res err res
  SourceEmpty : (result : res) -> Res err res
  Err         : (error : err) -> Res err res
  NoMoreFuel  : Res err res

drive :  Sink val
      -> (v : Fuel)
      -> Source err val res
      -> IO (Step Smaller v (Source err val res) (Res err res))
drive si (More x) src = do
  Value (v,src2) <- step src
    | Error err => pure (Done $ Err err)
    | Done  res => pure (Done $ SourceEmpty res)
  si.sink v $> Cont x (reflexive {rel = LTE}) src2
drive si Dry      src = release src $> Done NoMoreFuel

||| Connect a `Source` with a `Sink` an feed values
||| from the source to the sink until one of the
||| following situation occurs:
|||
|||   * The `Fuel` runs dry. The result will be `NoMoreFuel`.
|||
|||   * An error occured either in the `Sink` or the `Source`.
|||     The result will hold the error that was thrown.
|||
|||   * The `Sink` is full. The result will be `SinkFull`.
|||
|||   * The `Source` is empty.  The result will be `SourceEmpty`.
|||
||| No matter the final result: All system resources will be
||| properly released.
export
run : Fuel -> Source err val res -> Sink val -> IO (Res err res)
run f so si = trSized (drive si) f so

--------------------------------------------------------------------------------
--          Pure Sources
--------------------------------------------------------------------------------

export
fromList : List a -> Source err a ()
fromList xs = ST xs $ \case (h :: t) => Value (t,h)
                            Nil      => Done ()

export
fromStream : Stream a -> Source err a ()
fromStream xs = ST xs $ \(h :: t) => Value (t,h)

export
fromColist : Colist a -> Source err a ()
fromColist xs = ST xs $ \case (h :: t) => Value (t,h)
                              Nil      => Done ()

--------------------------------------------------------------------------------
--          Files
--------------------------------------------------------------------------------

export
chars : Bits32 -> File -> Source FileError String ()
chars n h = Sys read (closeFile h)
  where read : IO (Result FileError String ())
        read = do
          False   <- fEOF h | True => pure (Done ())
          Right s <- fGetChars h (cast n) | Left err => pure (Error err)
          pure (Value s)

export
bytes : Bits32 -> File -> Source FileError ByteString ()
bytes n h = Sys read (closeFile h)
  where read : IO (Result FileError ByteString ())
        read = do
          False   <- fEOF h | True => pure (Done ())
          Right s <- readChunk n h | Left err => pure (Error err)
          pure (Value s)

export
getLine : Source err String res
getLine = Sys (Value <$> getLine) (pure ())

export
putStrLn : Sink String
putStrLn = MkSink putStrLn

export
putStr : Sink String
putStr = MkSink putStr

export
printLn : Show a => Sink a
printLn = MkSink printLn

export
print : Show a => Sink a
print = MkSink print

export
writeBytes : File -> Sink ByteString
writeBytes h = MkSink (ignore . write h)
