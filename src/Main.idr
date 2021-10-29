import Stream.Source

import Data.ByteString
import Data.Fuel
import Control.Monad.Either
import System
import System.File

tryOpen : Mode -> List String -> IO (List File)
tryOpen _ []        = pure []
tryOpen m (p :: ps) = do
  Right h <- openFile p m
    | Left err => putStrLn "Error when opening file \{p}: \{show err}"
               >> tryOpen m ps
  (h ::) <$> tryOpen m ps

main : IO ()
main = do
  (_ :: fs) <- getArgs | _ => putStrLn "Missing arguments"
  hs <- tryOpen Read fs
  _  <- run (limit 10000000000) (foldMap (bytes 65536) hs) (writeBytes stdout)
  traverse_ closeFile hs
