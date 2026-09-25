import Bench

/-- Benchmark driver: `lake exe bench [--smoke] [suite …]`. -/
def main (_args : List String) : IO UInt32 := do
  IO.println "bench: no suites registered yet"
  return 0
