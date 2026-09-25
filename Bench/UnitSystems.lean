import Bench.Harness
import Similitude

/-!
# `unitsystems`: conversion factors and dimension arithmetic

Julia twin: `oracle/bench/unitsystems.jl` (UnitSystems 0.3 / Similitude).

* `convert_pairs`: all 131 conversion quantities `q(U, S)` between six pairs of the 48 systems,
  evaluated at runtime on `Num` values (Julia: `q(U, S)` with `q` and the systems taken from
  vectors, i.e. dynamic dispatch onto the specializations Julia compiles per system pair).
* `convert_pairs_sys`: the same factors for named systems chosen at run time (`Sys`), read from
  the per-pair tables (`Conv.factorSys`; Julia: the same code as `convert_pairs`).
* `convert_pairs_numf`: the same chains over unboxed `NumF` (the path for systems built at run
  time; Julia: the same code as `convert_pairs`).
* `convert_literal`: `energy(v, English, Metric)` for `10⁴` plain `Float64` values, with the
  systems written as literals (Julia folds the factor into a constant; Lean hoists it as a
  closed term, `Conv.convertF`).
* `convert_any`: `energy(U, Metric)` with `U` chosen at run time among four `UnitSystem Num`
  values (Julia: dynamic dispatch; Lean: `Conv.factorAny`, which recognises named systems).
* `natural_systems`: the one-argument form `q(U) = q(Natural, U)` over eight systems;
  `natural_systems_sys` reads the per-pair tables (`Conv.naturalSys`).
* `dim_products`: Similitude dimension arithmetic: the product of every pair of the 131 USQ
  dimension groups (`Group{:USQ}` in Julia).
* `ratio_runtime`: Similitude's exact conversion factor `ratio(d, U, S)` of every quantity's
  dimension for the six pairs of `convert_pairs`, evaluated at run time (Lean caches the eleven
  constant ratios per pair of systems; Julia recomputes them).

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

/-- `∑ q(U, S)` over every quantity and pair, from the per-pair tables. -/
def convertAllSys (ps : Array (Sys × Sys)) : Float :=
  Conv.all.foldl (fun acc q => ps.foldl (fun acc (U, S) => acc + (q.factorSys U S).toFloat) acc) 0

/-- `∑ q(U, S)` over every quantity and pair, on unboxed chains. -/
def convertAllF (ps : Array (UnitSystem NumF × UnitSystem NumF)) : Float :=
  Conv.all.foldl (fun acc q => ps.foldl (fun acc (U, S) => acc + (q.factor U S).x) acc) 0

/-- `∑ energy(v, English, Metric)` over a grid of values. -/
def convertLiteral (xs : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < xs.size then
    convertLiteral xs (i + 1) (acc + Conv.convertF .energy (xs[i]'h) (English Num) (Metric Num))
  else acc
termination_by xs.size - i

/-- `∑ energy(U, Metric)` over systems chosen at run time. -/
def convertAny (us : Array (UnitSystem Num)) : Float :=
  us.foldl (fun acc U => acc + (Conv.factorAny .energy U (Metric Num)).toFloat) 0

/-- `∑ q(U)` over every quantity and system. -/
def naturalAll (us : Array (UnitSystem Num)) : Float :=
  Conv.all.foldl (fun acc q => us.foldl (fun acc U => acc + (q.natural U).toFloat) acc) 0

/-- `∑ q(U)` over every quantity and system, from the per-pair tables. -/
def naturalAllSys (us : Array Sys) : Float :=
  Conv.all.foldl (fun acc q => us.foldl (fun acc U => acc + (q.naturalSys U).toFloat) acc) 0

/-- `∑ ratio(d, U, S)` (Similitude's exact factor, as a `Float64`) over every
quantity's dimension and pair. -/
def ratioAll (ds : Array USQGroup) (ps : Array (Sys × Sys)) : Float :=
  ds.foldl (fun acc d => ps.foldl (fun acc (U, S) => acc + (Similitude.ratio d.v U S).toFloat) acc) 0

/-- `∑ L-exponent (a * b)` over all pairs. -/
def dimProducts (ds : Array USQGroup) : Float :=
  ds.foldl (fun acc a => ds.foldl (fun acc b => acc + (a * b).v.getFloat ⟨2, by decide⟩) acc) 0

/-- `n` values `1 + i/n` (Julia `1 .+ (0:n-1) ./ n`). -/
def values (n : Nat) : FloatArray :=
  (List.range n).foldl (fun acc i => acc.push (1.0 + i.toUInt64.toFloat / n.toUInt64.toFloat))
    (FloatArray.emptyWithCapacity n)

/-- The suite. -/
def suite : Suite := ⟨"unitsystems", do
  let ps := (pairs.map fun (u, s) => (u.sys Num, s.sys Num)).toArray
  bench "convert_pairs" (ops := 131 * ps.size) (param := s!"131×{ps.size}") fun s =>
    convertAll (blackBox s ps)
  let pss := pairs.toArray
  bench "convert_pairs_sys" (ops := 131 * pss.size) (param := s!"131×{pss.size}") fun s =>
    convertAllSys (blackBox s pss)
  let psf := (pairs.map fun (u, s) => (u.sys NumF, s.sys NumF)).toArray
  bench "convert_pairs_numf" (ops := 131 * psf.size) (param := s!"131×{psf.size}") fun s =>
    convertAllF (blackBox s psf)
  let n ← size 10000 100
  let xs := values n
  bench "convert_literal" (ops := n) (param := s!"n={n}") fun s =>
    convertLiteral (blackBox s xs) 0 0.0
  let ua := #[English Num, Gauss Num, Planck Num, Hartree Num]
  bench "convert_any" (ops := ua.size) (param := s!"{ua.size}") fun s => convertAny (blackBox s ua)
  let us := (naturals.map (·.sys Num)).toArray
  bench "natural_systems" (ops := 131 * us.size) (param := s!"131×{us.size}") fun s =>
    naturalAll (blackBox s us)
  let uss := naturals.toArray
  bench "natural_systems_sys" (ops := 131 * uss.size) (param := s!"131×{uss.size}") fun s =>
    naturalAllSys (blackBox s uss)
  let ds : Array USQGroup := Conv.all.toArray.map (·.dim.toGroup)
  bench "dim_products" (ops := ds.size * ds.size) (param := s!"{ds.size}²") fun s =>
    dimProducts (blackBox s ds)
  bench "ratio_runtime" (ops := ds.size * pss.size) (param := s!"{ds.size}×{pss.size}") fun s =>
    ratioAll (blackBox s ds) pss⟩

end Bench.UnitSystems
