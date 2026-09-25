import Tests.Cartan.Ranges
import Tests.Cartan.Field2d
import Tests.Cartan.Field1d
import Tests.Cartan.Grids
import Tests.Cartan.Slices
import Tests.Cartan.Mesh

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
  Tests.CartanTests.Field2d.run
  Tests.CartanTests.Field1d.run
  Tests.CartanTests.Grids.run
  Tests.CartanTests.Slices.run
  Tests.CartanTests.Mesh.run

end Tests.Cartan
