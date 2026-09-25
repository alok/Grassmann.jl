import MeasureSystems.Measurement
import MeasureSystems.Measures
import MeasureSystems.Derived

/-!
# MeasureSystems

Lean port of `chakravala/MeasureSystems.jl` (v0.2.2): UnitSystems and
Similitude with CODATA/IAU uncertainties.

* `Measurement` (`Measurement`): Measurements.jl's linear error propagation with
  correlation tracking (each result carries its derivatives with respect to the
  independent measurements), parsing `measurement("v(e)[eN]")`, `show`, and
  MeasureSystems' concise `print_special`/`special_print`.
* `productM`, `showMeasures`, `MValue` (`Measures`): `Group{:Measures}` is the
  exact constants group of Similitude with 13 measured generators, so every
  unit-system constant and conversion ratio reuses Similitude's exact value and
  is evaluated with propagated uncertainty
  (`boltzmann(Metric) = 1.38064899953(43) × 10⁻²³ [J⋅K⁻¹] Metric`); quantities
  are Similitude's typed `Quantity U d MValue`.

Differences from Julia (documented in `docs/port-notes/similitude-fieldalgebra-measure.md`):
measured constants carry fixed tags, so separate evaluations that share a
constant are correlated (Julia's fresh tags make them independent), and a
measurement multiplied by a group is evaluated rather than kept as a group
with a measured coefficient. The `Measure{N}` interning cache is unnecessary.
-/
