module Stream.Source

import Data.Colist
import Data.SOP
import Stream.Result

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

  ||| Effectful, stateful source.
  STIO :  (state   : st)
       -> (fun     : st -> IO (Result err (st,val) res))
       -> (cleanup : st -> IO ())
       -> Source err val res

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
  release (ST _ _)       = pure ()
  release (STIO st _ cl) = cl st
  release (Sys _ rel)    = rel
  release (Pure _)       = pure ()
  release (Fail _)       = pure ()
  release (Bind x _)     = release x
  release (Par srcs)     = releaseList srcs
  release (Fan p _ c)    = release p >> release c

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

  step (STIO state fun cleanup) = do
    Value (state2,v) <- fun state
      | Done result       => pure $ Done result
      | Error error       => pure $ Error error
    pure $ Value (v, STIO state2 fun cleanup)

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
