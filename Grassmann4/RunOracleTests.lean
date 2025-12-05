/-
  RunOracleTests.lean - Execute the Julia oracle verification suite
-/
import Grassmann.JuliaOracle

def main : IO Unit := Grassmann.JuliaOracle.runAllTests
