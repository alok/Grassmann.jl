import Tests.Cartan.Ranges

/-!
Cartan test aggregator.

`Tests.Cartan.run` compares the port with the Julia oracle (`oracle/golden/cartan/*`, regenerated
by `oracle/cartan/gen.jl`) and runs the unit and property checks.
-/

open Tests.Small

namespace Tests.Cartan

/-- Run every Cartan suite; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := runSuite "Cartan" do
  Tests.CartanTests.Ranges.run

end Tests.Cartan
