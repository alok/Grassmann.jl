import Bench.Harness
import Similitude

/-!
# `unitsystems`: conversion factors and dimension arithmetic

Julia twin: `oracle/bench/unitsystems.jl` (UnitSystems 0.3 / Similitude).

* `convert_pairs`: all 131 conversion quantities `q(U, S)` between six pairs of the 48 systems,
  evaluated at runtime on `Num` values (Julia: `q(U, S)` with `q` and the systems taken from
  vectors, i.e. dynamic dispatch onto the specializations Julia compiles per system pair).
* `natural_systems`: the one-argument form `q(U) = q(Natural, U)` over eight systems.
* `dim_products`: Similitude dimension arithmetic: the product of every pair of the 131 USQ
  dimension groups (`Group{:USQ}` in Julia).

Checks are sums of the factors (resp. of the length exponents), equal when bit-exact.
-/

namespace Bench.UnitSystems

open _root_.UnitSystems FieldConstants FieldAlgebra Similitude Bench

/-- The system pairs of `convert_pairs` (Julia `IAU` is `IAU☉`). -/
def pairs : List (Sys × Sys) :=
  [(.Metric, .English), (.English, .Metric), (.SI2019, .Gauss), (.Planck, .Metric),
   (.Hartree, .SI2019), (.IAU, .Metric)]

/-- The systems of `natural_systems`. -/
def naturals : List Sys :=
  [.Metric, .English, .Gauss, .Planck, .Hartree, .IAU, .Stoney, .QCD]

/-- `∑ q(U, S)` over every quantity and pair. -/
def convertAll (ps : Array (UnitSystem Num × UnitSystem Num)) : Float :=
  Conv.all.foldl (fun acc q => ps.foldl (fun acc (U, S) => acc + (q.factor U S).toFloat) acc) 0

/-- `∑ q(U)` over every quantity and system. -/
def naturalAll (us : Array (UnitSystem Num)) : Float :=
  Conv.all.foldl (fun acc q => us.foldl (fun acc U => acc + (q.natural U).toFloat) acc) 0

/-- `∑ L-exponent (a * b)` over all pairs. -/
def dimProducts (ds : Array USQGroup) : Float :=
  ds.foldl (fun acc a => ds.foldl (fun acc b => acc + (a * b).v.getFloat ⟨2, by decide⟩) acc) 0

/-- The suite. -/
def suite : Suite := ⟨"unitsystems", do
  let ps := (pairs.map fun (u, s) => (u.sys Num, s.sys Num)).toArray
  bench "convert_pairs" (ops := 131 * ps.size) (param := s!"131×{ps.size}") fun s =>
    convertAll (blackBox s ps)
  let us := (naturals.map (·.sys Num)).toArray
  bench "natural_systems" (ops := 131 * us.size) (param := s!"131×{us.size}") fun s =>
    naturalAll (blackBox s us)
  let ds : Array USQGroup := Conv.all.toArray.map (·.dim.toGroup)
  bench "dim_products" (ops := ds.size * ds.size) (param := s!"{ds.size}²") fun s =>
    dimProducts (blackBox s ds)⟩

end Bench.UnitSystems
