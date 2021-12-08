module Stream.File

import Data.ByteString
import Stream.Internal
import Stream.Util
import System.File

export
chars : HasIO io => Bits32 -> File -> Stream (Of String) io (Maybe FileError)
chars n h = tillRight $ do
  False <- fEOF h | True => pure (Right Nothing)
  Right s <- fGetChars h (cast n) | Left err => pure (Right $ Just err)
  pure (Left s)

export
bytes :  HasIO io
      => Bits32
      -> File
      -> Stream (Of ByteString) io (Maybe FileError)
bytes n h = tillRight $ do
  False <- fEOF h | True => pure (Right Nothing)
  Right s <- readChunk n h | Left err => pure (Right $ Just err)
  pure (Left s)

-- export
-- putStrLn : Sink String
-- putStrLn = MkSink putStrLn
-- 
-- export
-- putStr : Sink String
-- putStr = MkSink putStr
-- 
-- export
-- printLn : Show a => Sink a
-- printLn = MkSink printLn
-- 
-- export
-- print : Show a => Sink a
-- print = MkSink print
-- 
-- export
-- writeBytes : File -> Sink ByteString
-- writeBytes h = MkSink (ignore . write h)
