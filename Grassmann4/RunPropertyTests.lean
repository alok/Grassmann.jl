/-
  RunPropertyTests.lean - Execute Plausible property tests
-/
import Grassmann.PropertyTests

def main : IO Unit := Grassmann.PropertyTests.runPropertyTests
