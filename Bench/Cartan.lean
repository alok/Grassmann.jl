import Bench.Harness
import Cartan

/-!
# `cartan`: tensor-field kernels

Julia twin: `oracle/bench/cartan.jl` (Cartan 0.4.16). Every case works on the fields of the old
`Tests/Cartan/Bench.lean`: a `1000×1000` grid `range(0, 1, length = 1000)²` (smoke: `20×20`), the
`Chain ℝ3` fields `v = (x, y, 1)` and `w = (1, -y, x)` on it, the scalar field `a = x + 2y`, and
the interval `range(0, 10, length = 10⁶)` with its identity field `t` and `s = sin(t)`. Times are
**ns per grid point** (`ops` = the number of points).

The check of a field is `data[0] + data[n/2] + data[n-1]` of its flat fibers (Julia: the same
entries of `reinterpret(Float64, fiber(t))`), cheap enough not to perturb the timing.
-/

namespace Bench.Cartan

open _root_.Cartan Grassmann Bench

/-- The check of a flat array: three of its entries. -/
def fieldCheck (a : FloatArray) : Float :=
  if a.size == 0 then 0 else a.get! 0 + a.get! (a.size / 2) + a.get! (a.size - 1)

/-- The check of a field (`fieldCheck` of its data). -/
@[inline] def chk {M F : Type} [FrameBundle M] [FlatFiber F] {m : M} (t : TensorField m F) : Float :=
  fieldCheck t.data

/-- A `Chain ℝ3` from three coordinates. -/
@[inline] def chain3 (x y z : Float) : Chain ℝ3 1 Float :=
  Chain.ofFn fun i => if i.1 = 0 then x else if i.1 = 1 then y else z

/-- Julia `torus(x) = (r = 3 + cos(x[2]); Chain(r cos x[1], r sin x[1], sin x[2]))`. -/
@[inline] def torusPoint (u v : Float) : Chain ℝ3 1 Float :=
  let r := 3 + Float.cos v
  chain3 (r * Float.cos u) (r * Float.sin u) (Float.sin v)

/-- The suite. -/
def suite : Suite := ⟨"cartan", do
  let n ← size 1000 20
  let pts := n * n
  let p := s!"{n}×{n}"
  let ps : ProductSpace 2 := .ofAxes #v[Axis.range 0 1 n, Axis.range 0 1 n]
  let g := GridBundle.ofSpace ps
  let line := Axis.range 0 10 pts
  let lb := GridBundle.ofAxis line
  let lp := s!"{pts}"
  -- building fields
  bench "tabulate_chain3" (ops := pts) (param := p) fun s =>
    chk <| TensorField.tabulatePoint (blackBox s g) fun x => chain3 (x.get! 0) (x.get! 1) 1
  bench "tabulate_w" (ops := pts) (param := p) fun s =>
    chk <| TensorField.tabulatePoint (blackBox s g) fun x => chain3 1 (-x.get! 1) (x.get! 0)
  bench "tabulate_scalar" (ops := pts) (param := p) fun s =>
    chk <| TensorField.tabulatePoint (blackBox s g) fun x => x.get! 0 + 2 * x.get! 1
  bench "tabulate2_chain3" (ops := pts) (param := p) fun s =>
    chk <| TensorField.tabulate2 (blackBox s g) fun x y => chain3 x y 1
  bench "tabulate2_scalar" (ops := pts) (param := p) fun s =>
    chk <| TensorField.tabulate2 (blackBox s g) fun x y => x + 2 * y
  bench "identity_range" (ops := pts) (param := lp) fun s =>
    chk <| TensorField.ofAxis (blackBox s line)
  let v := ((TensorField.tabulatePoint g fun x => chain3 (x.get! 0) (x.get! 1) 1).rebase? g).get!
  let w := ((TensorField.tabulatePoint g fun x => chain3 1 (-x.get! 1) (x.get! 0)).rebase? g).get!
  let a := ((TensorField.tabulatePoint g fun x => x.get! 0 + 2 * x.get! 1).rebase? g).get!
  let t := ((TensorField.ofAxis line).rebase? lb).get!
  let sn := t.sin
  -- scalar functions and linear operations
  bench "sin" (ops := pts) (param := lp) fun s => chk (blackBox s t).sin
  bench "exp" (ops := pts) (param := lp) fun s => chk (blackBox s t).exp
  bench "add_ts" (ops := pts) (param := lp) fun s => chk (blackBox s t + sn)
  bench "scale_s2" (ops := pts) (param := lp) fun s => chk (blackBox s sn * (2 : Float))
  bench "mul_st" (ops := pts) (param := lp) fun s => chk (blackBox s sn * t)
  bench "add_vw" (ops := pts) (param := p) fun s => chk (blackBox s v + w)
  bench "scale_2v" (ops := pts) (param := p) fun s => chk ((2 : Float) * blackBox s v)
  bench "mul_av" (ops := pts) (param := p) fun s => chk (blackBox s a * v)
  -- Grassmann products
  bench "wedge_vw" (ops := pts) (param := p) fun s => chk (blackBox s v ∧ w)
  bench "geom_vw" (ops := pts) (param := p) fun s => chk (blackBox s v * w)
  bench "dot_vw" (ops := pts) (param := p) fun s => chk (blackBox s v ⋅ w)
  bench "hodge_v" (ops := pts) (param := p) fun s => chk (⋆(blackBox s v))
  bench "norm_v" (ops := pts) (param := p) fun s => chk (blackBox s v).norm
  let h := n / 2
  bench "resample_a" (ops := h * h) (param := s!"{h}×{h}") fun s =>
    chk ((blackBox s a).resample #v[h, h])
  -- reductions
  bench "sum_s" (ops := pts) (param := lp) fun s => (blackBox s sn).sumF
  bench "supnorm_v" (ops := pts) (param := p) fun s => (blackBox s v).supnorm
  -- a parametrized surface (Julia `torus.(TorusParameter(n, n))`)
  let T := Parameter.torus #v[n, n]
  bench "torus" (ops := pts) (param := p) fun s =>
    chk <| (blackBox s T).map fun q => torusPoint (q.get! 0) (q.get! 1)⟩

end Bench.Cartan
