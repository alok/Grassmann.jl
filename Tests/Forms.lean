import Tests.Forms.Common
import Tests.Forms.Exact
import Tests.Forms.Float
import Tests.Forms.Spectral
import Tests.Forms.Diag
import Tests.Forms.Geometry
import Tests.Forms.Props
import Tests.Forms.Types

/-!
# Forms test aggregator

`Tests.Forms.run` returns `(passed, failed)` over the linear algebra of Grassmann
elements (`Grassmann.Forms`): the Julia goldens in `oracle/golden/forms/`
(`oracle/forms/gen.jl`), property tests and static-type checks.

| suite | content |
|---|---|
| `forms/exact` | integer operators `n ≤ 6`: determinant family, outermorphisms, products, display |
| `forms/float` | real operators: Cramer inverse and solves, characteristic polynomials, spectra, `exp` |
| `forms/spectral` | LAPACK eigen-decompositions (residuals), matrix `log`, polynomial roots |
| `forms/diag+rect` | diagonal operators and non-square operators |
| `forms/geometry` | simplices, metric tensors, sandwich operators, Cayley/TeX, rank-one forms, evaluation, element spectra |
| `forms/props` | Cauchy–Binet, adjugates, exact inverses, Newton's identities, Pfaffians, eigen residuals, `exp`/`log` |
| `forms/types` | static result types and the worked examples through the notation |
-/

namespace Tests.Forms

open Tests.FormsTests

/-- Run every Forms suite; returns `(passed, failed)`. -/
def run : IO (Nat × Nat) := do
  IO.println "Forms"
  let suites : List (IO Tally) :=
    [Exact.suite, FloatSuite.suite, SpectralSuite.suite, DiagSuite.suite, GeometrySuite.suite,
     Props.suite, Types.suite]
  let mut pass := 0
  let mut fail := 0
  for suite in suites do
    let t0 ← IO.monoMsNow
    let t ← suite
    let t1 ← IO.monoMsNow
    let (p, f) ← ({ t with s := { t.s with name := s!"{t.s.name} ({t1 - t0} ms)" } } : Tally).report
    pass := pass + p
    fail := fail + f
  return (pass, fail)

end Tests.Forms
