import Bench.Harness
import Cartan
import Cartan.Element
import Cartan.Spectral

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

/-- The check of a flat array (`fieldCheck`). -/
@[inline] def chkA (a : FloatArray) : Float := fieldCheck a

/-- Julia `gridmesh(a, b)` of the twin: the unit square in `2ab` triangles on the points
`(i/a, j/b)` (node `k = i + (a+1) j`, 0-based). -/
def gridMesh (a b : Nat) : SimplexBundle 3 (HPoint ℝ3) :=
  let pts : Array (HPoint ℝ3) := (Array.range ((a + 1) * (b + 1))).map fun k =>
    let i := k % (a + 1)
    let j := k / (a + 1)
    Chain.ofFn fun c => if c.1 = 0 then 1 else if c.1 = 1 then Float.ofNat i / Float.ofNat a
      else Float.ofNat j / Float.ofNat b
  let node (i j : Nat) : Nat := 1 + i + (a + 1) * j
  let els := (Array.range (a * b)).flatMap fun q =>
    let i := q % a
    let j := q / a
    #[#v[node i j, node (i + 1) j, node (i + 1) (j + 1)], #v[node i j, node (i + 1) (j + 1), node i (j + 1)]]
  SimplexBundle.ofPoints pts els

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
    chk <| (blackBox s T).map fun q => torusPoint (q.get! 0) (q.get! 1)
  -- evaluation at scattered points (Julia `a(x, y)`)
  let K ← size 100000 100
  let xs : FloatArray := ⟨(Array.range K).map fun k => Float.ofNat (k * 7919 % 100003) / 100003⟩
  let ys : FloatArray := ⟨(Array.range K).map fun k => Float.ofNat (k * 104729 % 100019) / 100019⟩
  bench "eval_a" (ops := K) (param := s!"{K}") fun s =>
    let a' := blackBox s a
    chkA (buildFlat (F := Float) K fun k => a'.eval2 (xs.get! k) (ys.get! k))
  -- finite elements on a structured triangulation (Julia `volumes`, `gradienthat`, `gradient`,
  -- `assembleload`); ns per element (per node for the load)
  let mm ← size 300 10
  let mesh := gridMesh mm mm
  let ne := 2 * mm * mm
  let np := (mm + 1) * (mm + 1)
  let u : FloatArray := ⟨(Array.range np).map fun k =>
    let x := Float.ofNat (k % (mm + 1)) / Float.ofNat mm
    let y := Float.ofNat (k / (mm + 1)) / Float.ofNat mm
    x * x + 2 * y⟩
  let mp := s!"{mm}×{mm}"
  bench "mesh_volumes" (ops := ne) (param := mp) fun s => chk (blackBox s mesh).volumes
  bench "mesh_gradienthat" (ops := ne) (param := mp) fun s => chk (blackBox s mesh).gradienthat
  bench "mesh_gradient" (ops := ne) (param := mp) fun s => chk ((blackBox s mesh).gradient2 u)
  bench "mesh_load" (ops := np) (param := mp) fun s => chkA (blackBox s mesh).assembleload
  -- FFT of 2^16 complex points (Julia FFTW `fft`)
  let nf ← size 65536 64
  let z : Spectral.CVec := ⟨(Array.range (2 * nf)).map fun k => Float.sin (Float.ofNat k * 0.001)⟩
  bench "fft_c" (ops := nf) (param := s!"{nf}") fun s => chkA (Spectral.fft (blackBox s z))
  bench "rfft_r" (ops := nf) (param := s!"{nf}") fun s =>
    chkA (Spectral.rfft (blackBox s ⟨(Array.range nf).map fun k => z.get! (2 * k)⟩))⟩

end Bench.Cartan
