module Stream.File

import Data.ByteString
import Stream.Result
import Stream.Sink
import Stream.Source
import System.File

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
