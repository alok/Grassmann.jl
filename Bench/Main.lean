import Bench

/-- Benchmark driver: `lake exe bench [--smoke] [suite …]` (suites: `math`). -/
def main (args : List String) : IO UInt32 := do
  let smoke := args.contains "--smoke"
  let chosen := args.filter (· != "--smoke")
  if chosen.isEmpty || chosen.contains "math" then Bench.Math.run smoke
  return 0
