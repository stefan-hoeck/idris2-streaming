module Stream.Source

import Data.Colist
import Data.SOP
import Stream.Result

%default total

--------------------------------------------------------------------------------
--          Source
--------------------------------------------------------------------------------

public export
data Source : (err,val : Type) -> Type

public export
data ParList : (err : Type) -> (vals : List Type) -> Type where
  Nil  :  ParList err []
  (::) :  (src  : Source err val)
       -> (srcs : ParList err vals)
       -> ParList err (val :: vals)

||| Potentially infinite, effectful, non-empty data source.
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
data Source : (err,val : Type) -> Type where
  ||| A pure, stateful source. Use this to create a source
  ||| from a stateful computation, for instance
  ||| an iterative calculation or the elements
  ||| from a `List` or `Stream` of values.
  ST   : (state : st) -> (fun   : st -> Result err (st,val)) -> Source err val

  ||| A system resource such as a file or a socket.
  ||| This comes with instructions how to clean up
  ||| the source, once it can no longer produce any
  ||| values or is no longer needed.
  Sys  : (next : IO (Result err val)) -> (release : IO ()) -> Source err val

  ||| An empty `Source`, throwing an error.
  Fail : (error : err) -> Source err val

  ||| Sequential composition of sources.
  |||
  ||| A new source is created after an existing on, once
  ||| the latter has spent all its values.
  Seq  : Source err val -> IO (Source err val) -> Source err val

  ||| Parallel composition (zipping) of sources.
  |||
  ||| The list of sources generates values until the
  ||| first one is spent.
  Par  : (sources : ParList err vals) -> Source err (NP I vals)

  ||| A `Source` of `Source`s.
  |||
  ||| Creates a child source from each value of a parent
  ||| source, consuming the child until it is exhaused.
  ||| This can for instance be used to read all data
  ||| from a list of files (or a directory).
  |||
  ||| Note: The `parent` decides, when this source is spent.
  |||       Once a child terminates, a new child
  |||       is generated (if possible).
  Fan  :  (parent       : Source err val)
       -> (mkChild      : val -> IO (Source err val2))
       -> (currentChild : Source err val2)
       -> Source err val2

  ||| Effectful, stateful source.
  STIO :  (state   : st)
       -> (fun     : st -> IO (Result err (st,val)))
       -> (cleanup : st -> IO ())
       -> Source err val

-- export
-- Functor (Source err val) where
--   map f sr = Fan sr (pure . Pure . f)

-- export
-- Applicative (Source err val) where
--   pure = Pure
--   sf <*> sa = Bind sf (\fun => pure $ apply fun <$> sa)
-- 
-- export %inline
-- Monad (Source err val) where
--   s >>= f = Bind s (pure . f)
-- 
-- ||| Sequential composition of `Source`s.
-- export
-- Semigroup (Source err val res) where
--   sa <+> sb = Bind sa (pure . const sb)
-- 
-- export
-- Monoid res => Monoid (Source err val res) where
--   neutral = Pure neutral
-- 
-- --------------------------------------------------------------------------------
-- --          Single Step Evaluation
-- --------------------------------------------------------------------------------
-- 
-- mutual
--   releaseList : ParList err res vals -> IO ()
--   releaseList []            = pure ()
--   releaseList (src :: srcs) = release src >> releaseList srcs
-- 
--   ||| Recursively release all open resources of
--   ||| the given `Source`.
--   export
--   release : Source err val res -> IO ()
--   release (ST _ _)       = pure ()
--   release (STIO st _ cl) = cl st
--   release (Sys _ rel)    = rel
--   release (Pure _)       = pure ()
--   release (Fail _)       = pure ()
--   release (Bind x _)     = release x
--   release (Par srcs)     = releaseList srcs
--   release (Fan p _ c)    = release p >> release c
-- 
-- mutual
--   stepList :  ParList err res vals
--            -> IO (Result err (NP I vals, ParList err res vals) res)
--   stepList []            = pure $ Value ([],[])
--   stepList (src :: srcs) = do
--     Value (v,s) <- step src
--       | Done  res => releaseList srcs $> Done res
--       | Error err => releaseList srcs $> Error err
-- 
--     Value (vs,ss) <- stepList srcs
--       | Done  res => pure $ Done res
--       | Error err => pure $ Error err
-- 
--     pure $ Value (v :: vs, s :: ss)
-- 
--   ||| Single step evaluation of a `Source`.
--   |||
--   ||| This either yields a `val` together with the next
--   ||| source, fails with an error, or returns a result.
--   ||| In the latter two cases, all internal sources are
--   ||| cleaned up by invoking `release`.
--   export
--   step :  Source err val res
--        -> IO (Result err (val, Source err val res) res)
--   step (ST state fun) = case fun state of
--     Done result       => pure $ Done result
--     Error error       => pure $ Error error
--     Value (state2, v) => pure $ Value (v, ST state2 fun)
-- 
--   step (STIO state fun cleanup) = do
--     Value (state2,v) <- fun state
--       | Done result       => pure $ Done result
--       | Error error       => pure $ Error error
--     pure $ Value (v, STIO state2 fun cleanup)
-- 
--   step (Sys next release) = do
--     Value v <- next
--       | Done  result => release $> Done result
--       | Error err    => release $> Error err
--     pure $ Value (v, Sys next release)
--   
--   step (Pure result) = pure $ Done result
-- 
--   step (Bind src f) = do
--     Value (v,src2) <- step src
--       | Done result => assert_total (f result >>= step)
--       | Error err   => pure $ Error err
--     pure $ Value (v, Bind src2 f)
-- 
--   step (Par sources) = do
--     Value (vs, sources2) <- stepList sources
--       | Error err => pure $ Error err
--       | Done res  => pure $ Done res
--     pure $ Value (vs, Par sources2)
-- 
--   step (Fan parent mkChild child) = do
--     Done v2           <- step child
--       | Error err        => release parent $> Error err
--       | Value (v,child2) => pure $ Value (v, Fan parent mkChild child2)
-- 
--     Value (v,parent2) <- step parent
--       | Error err        => pure $ Error err
--       | Done res         => pure $ Value (v2, Pure res)
-- 
--     child2            <- mkChild v
--     pure $ Value (v2, Fan parent2 mkChild child2)
-- 
--   step (Fail err) = pure (Error err)
