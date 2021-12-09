module Examples.Main

import Examples.AOC1
import Examples.AOC2

main : IO ()
main =  AOC1.part1 >> AOC1.part2
     >> AOC2.part1 >> AOC2.part2
