module Stream.File

import Data.ByteString
import Stream.Internal
import Stream.Util
import System.File

-- export
-- chars : HasIO io => Bits32 -> File -> Stream (Of String) io (Maybe FileError)
-- chars n h = tillRight $ do
--   False <- fEOF h | True => pure (Right Nothing)
--   Right s <- fGetChars h (cast n) | Left err => pure (Right $ Just err)
--   pure (Left s)
-- 
-- export
-- lines : HasIO io => File -> Stream (Of String) io (Maybe FileError)
-- lines h = tillRight $ do
--   False <- fEOF h | True => pure (Right Nothing)
--   Right s <- fGetLine h | Left err => pure (Right $ Just err)
--   pure (Left s)
-- 
-- export
-- withLines :  HasIO io
--           => String
--           -> (Stream (Of String) io (Maybe FileError) -> io res)
--           -> io (Either FileError res)
-- withLines s f = withFile s Read (pure . id) (\h => Right <$> f (lines h))
-- 
-- export
-- stdinLn : HasIO io => Stream (Of String) io r
-- stdinLn = tillRight $ Left <$> getLine
-- 
-- export
-- bytes :  HasIO io
--       => Bits32
--       -> File
--       -> Stream (Of ByteString) io (Maybe FileError)
-- bytes n h = tillRight $ do
--   False <- fEOF h | True => pure (Right Nothing)
--   Right s <- readChunk n h | Left err => pure (Right $ Just err)
--   pure (Left s)
-- 
-- export
-- withBytes :  HasIO io
--           => String
--           -> Bits32
--           -> (Stream (Of ByteString) io (Maybe FileError) -> io res)
--           -> io (Either FileError res)
-- withBytes s n f = withFile s Read (pure . id) (\h => Right <$> f (bytes n h))
-- 
-- export
-- stdoutLn : HasIO io => Stream (Of String) io r -> Stream Empty io r
-- stdoutLn = mapM_ putStrLn
-- 
-- export
-- printLn : HasIO io => Show a => Stream (Of a) io r -> Stream Empty io r
-- printLn = mapM_ printLn
-- 
-- export
-- writeBytes :  HasIO io
--            => File
--            -> Stream (Of ByteString) io r
--            -> Stream Empty io r
-- writeBytes = mapM_ . write
