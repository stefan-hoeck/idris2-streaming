module Examples.AOC1

import Data.String
import Data.Vect

import Stream
import System
import System.File

export
part1 : IO ()
part1 = ignore $ withLines "resources/aoc1a" $ \ls => do
  res <- run 
       . count_ (\[x,y] => x > y)
       . slidingWindow 2
       $ mapVals (cast {to = Nat} . trim) ls
  putStrLn "Day1, Result A: \{show res}"

export
part2 : IO ()
part2 = ignore $ withLines "resources/aoc1a" $ \ls => do
  res <- run 
       . count_ (\[x,y] => sum x > sum y)
       . slidingWindow 2
       . slidingWindow 3
       $ mapVals (cast {to = Nat} . trim) ls
  putStrLn "Day1, Result B: \{show res}"
