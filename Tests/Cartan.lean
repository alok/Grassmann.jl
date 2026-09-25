import Tests.Cartan.Ranges
import Tests.Cartan.Field2d
import Tests.Cartan.Field1d
import Tests.Cartan.Grids
import Tests.Cartan.Slices
import Tests.Cartan.Mesh
import Tests.Cartan.Props
import Tests.Cartan.Eval
import Tests.Cartan.Misc
import Tests.Cartan.Unit
import Tests.Cartan.Operators
import Tests.Cartan.Solve
import Tests.Cartan.Element
import Tests.Cartan.FFT
import Tests.Cartan.Spectral

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
  Tests.CartanTests.Props.run
  Tests.CartanTests.Eval.run
  Tests.CartanTests.MiscTests.run
  Tests.CartanTests.Unit.run
  Tests.CartanTests.Operators.run
  Tests.CartanTests.SolveTests.run
  Tests.CartanTests.ElementTests.run
  Tests.CartanTests.FFTTests.run
  Tests.CartanTests.SpectralTests.run

end Tests.Cartan
