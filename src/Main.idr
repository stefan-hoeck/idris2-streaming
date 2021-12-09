import Stream

import Data.String
import System
import System.File

zipWithTail : Stream (Of a) m r -> Stream (Of (a,a)) m r
zipWithTail = mapMaybe (\(mx,my) => [| (,) mx my |])
            . scan (\p,vn => (Just vn, fst p)) (Nothing,Nothing) id

main : IO ()
main = do
  res <- run 
       . map fst
       . count (\(x,y) => x > y)
       . zipWithTail
       . mapVals (cast {to = Nat} . trim)
       $ lines stdin
  putStrLn "Result: \{show res}"
