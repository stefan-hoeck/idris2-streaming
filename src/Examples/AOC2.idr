module Examples.AOC2

import Data.String
import Data.Nat

import Stream
import System
import System.File

record Pos where
  constructor MkPos
  aim        : Int32
  depth      : Int32
  horizontal : Int32

initialPos : Pos
initialPos = MkPos 0 0 0

adjustPos : Pos -> String -> Pos
adjustPos (MkPos a d h) s = case words $ trim s of
  ["forward",v] => MkPos a d (h + cast v)
  ["down",v]    => MkPos a (d + cast v) h
  ["up",v]      => MkPos a (d - cast v) h
  _             => MkPos a d h

adjustPos2 : Pos -> String -> Pos
adjustPos2 (MkPos a d h) s = case words $ trim s of
  ["forward",v] => MkPos a (d + a * cast v) (h + cast v)
  ["down",v]    => MkPos (a + cast v) d h
  ["up",v]      => MkPos (a - cast v) d h
  _             => MkPos a d h

export
part1 : IO ()
part1 = ignore $ withLines "resources/aoc2a" $ \ls => do
  MkPos a d h <- run $ fold_ adjustPos initialPos id ls
  putStrLn "Day2, Result A: \{show $ d * h} (Depth: \{show d}, Pos: \{show h})"

export
part2 : IO ()
part2 = ignore $ withLines "resources/aoc2a" $ \ls => do
  MkPos a d h <- run $ fold_ adjustPos2 initialPos id ls
  putStrLn "Day2, Result B: \{show $ d * h} (Depth: \{show d}, Pos: \{show h})"
