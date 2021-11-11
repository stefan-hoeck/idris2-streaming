module Stream.Driver

import Data.Fuel
import Data.Iterable
import Stream.Result
import Stream.Sink
import Stream.Source

--------------------------------------------------------------------------------
--          Driver
--------------------------------------------------------------------------------

-- public export
-- data Res : (err, res : Type) -> Type where
--   SinkFull    : Res err res
--   SourceEmpty : (result : res) -> Res err res
--   Err         : (error : err) -> Res err res
--   NoMoreFuel  : Res err res
-- 
-- drive :  Sink val
--       -> (v : Fuel)
--       -> Source err val res
--       -> IO (Step Smaller v (Source err val res) (Res err res))
-- drive si (More x) src = do
--   Value (v,src2) <- step src
--     | Error err => pure (Done $ Err err)
--     | Done  res => pure (Done $ SourceEmpty res)
--   si.sink v $> Cont x (reflexive {rel = LTE}) src2
-- drive si Dry      src = release src $> Done NoMoreFuel
-- 
-- ||| Connect a `Source` with a `Sink` an feed values
-- ||| from the source to the sink until one of the
-- ||| following situation occurs:
-- |||
-- |||   * The `Fuel` runs dry. The result will be `NoMoreFuel`.
-- |||
-- |||   * An error occured either in the `Sink` or the `Source`.
-- |||     The result will hold the error that was thrown.
-- |||
-- |||   * The `Sink` is full. The result will be `SinkFull`.
-- |||
-- |||   * The `Source` is empty.  The result will be `SourceEmpty`.
-- |||
-- ||| No matter the final result: All system resources will be
-- ||| properly released.
-- export
-- run : Fuel -> Source err val res -> Sink val -> IO (Res err res)
-- run f so si = trSized (drive si) f so
