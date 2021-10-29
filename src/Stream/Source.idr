module Stream.Source

import Data.ByteString
import Data.Fuel
import Data.Iterable
import System.File

%default total

--------------------------------------------------------------------------------
--          Source
--------------------------------------------------------------------------------

||| Potentially infinite effectful data source.
||| It is not possible to fully consume such a value in the general
||| case. Therefore, all streaming combinators in typical
||| Haskell libraries telling you otherwise are a lie and
||| may loop forever.
|||
||| Likewise, it is not totally safe to "filter" a data source
||| according to a boolean predicate for instance. Nor is
||| it safe to group values according to a given boolean predicate.
||| Consider for instance a `Source` reading byte strings from a file,
||| grouping them into lines of strings. Reading data from such a
||| `Source` might never terminate: The file in question might hold
||| an infinite amount of data (`/dev/urandom` for instance) without
||| a single new-line character.
public export
data Source : (a,r : Type) -> Type where
  More  : (val : a) -> Inf (Source a r) -> Source a r
  Done  : (result : r) -> Source a r
  Eff   : IO (Source a r) -> Source a r
  Run   : IO (Either a r) -> Source a r
  Bind  : Inf (Source a r) -> (r -> Source a s) -> Source a s

export %inline
Functor (Source a) where
  map f sr = Bind sr (Done . f)

export
Applicative (Source a) where
  pure = Done
  sf <*> sa = Bind sf (\fun => apply fun <$> sa)

export %inline
Monad (Source a) where
  s >>= f = Bind s f

export
Semigroup (Source a r) where
  sa <+> sb = Bind sa (const sb)

export
Monoid r => Monoid (Source a r) where
  neutral = Done neutral

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

step :  Sink a
     -> (v : Fuel)
     -> Source a b
     -> IO (Step Smaller v (Source a b) (Maybe b))
step si (More v) (More val x) =
  si.sink val $> Cont v refl x

step _  (More v) (Done vr) =
  pure . Done $ Just vr

step si (More v) (Run m) = do
  Left va <- m | Right vr => pure . Done $ Just vr
  si.sink va $> Cont v refl (Run m)

step _  (More v) (Eff g) =
  Cont v refl <$> g

step si (More v) (Bind y f) = do
  Just r <- assert_total (trSized (step si) v y)
    | Nothing => pure (Done Nothing)
  pure $ Cont v refl (f r)

step _  Dry _ = pure $ Done Nothing

||| Connect a `Source` with a `Sink` an run until the fuel runs dry.
export
run : Fuel -> Source a r -> Sink a -> IO (Maybe r)
run f so si = trSized (step si) f so

--------------------------------------------------------------------------------
--          Files
--------------------------------------------------------------------------------

export
chars : Bits32 -> File -> Source String ()
chars n h = Run $ do
  False   <- fEOF h | True => pure (Right ())
  Right s <- fGetChars h (cast n) | Left _ => pure (Right ())
  pure (Left s)

export
bytes : Bits32 -> File -> Source ByteString ()
bytes n h = Run $ do
  False    <- fEOF h | True => pure (Right ())
  Right bs <- readChunk n h | Left _ => pure (Right ())
  pure (Left bs)

export
getLine : Source String ()
getLine = Run (Left <$> getLine)

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
