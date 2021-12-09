module Examples.AOC3

import Data.String
import Data.List
import Data.Nat

import Stream
import System
import System.File

accum : List Int32 -> String -> List Int32
accum xs s = case trim s of
  "" => xs
  s2 => zipWith (+) xs (map dec $ unpack s2)
  where dec : Char -> Int32
        dec '0' = -1
        dec _   = 1

encode : List Int32 -> Bits32
encode = foldl (\acc,x => 2 * acc + (if x > 0 then 1 else 0)) 0

export
part1 : IO ()
part1 = ignore $ withLines "resources/aoc3a" $ \ls => do
  cs <- run $ fold_ accum (replicate 200 0) id ls
  let g = encode cs
      e = encode (map negate cs)
  putStrLn "Day3, Result A: \{show $ g * e} (g: \{show g}, e: \{show e}, acc: \{show cs})"

export
part2 : IO ()
part2 = pure ()
