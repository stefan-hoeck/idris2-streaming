import Stream

import Data.ByteString
import Data.Fuel

import System
import System.File

main : IO ()

-- bytes : Bits32 -> String -> IO (Source FileError ByteString ByteString)
-- bytes n s = do
--   Right h <- openFile s Read | Left err => pure (Fail err)
--   pure (bytes n h $> empty)
-- 
-- main : IO ()
-- main = do
--   (_ :: fs) <- getArgs | _ => putStrLn "Missing arguments"
--   res <- run
--            (limit 10000000000)
--            (Fan (fromList fs) (bytes 65536) (Pure empty))
--            (writeBytes stdout)
-- 
--   case res of
--     SinkFull             => putStrLn "sink overflow"
--     (SourceEmpty result) => pure ()
--     (Err error)          => putStrLn "Error: \{show error}"
--     NoMoreFuel           => putStrLn "running on empty"
