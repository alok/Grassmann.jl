import Tests

/-- Test driver: `lake test` / `lake exe tests [suite …]`. Suites register in `Tests/Main.lean`. -/
def main (_args : List String) : IO UInt32 := do
  IO.println "tests: no suites registered yet"
  return 0
