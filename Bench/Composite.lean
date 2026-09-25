import Bench.Harness
import Grassmann
import Grassmann.Kernel.Generated

/-!
# `composite`: transcendental functions of Grassmann elements, `↑`/`↓`, the README curves

Julia twin: `oracle/bench/composite.jl` (Grassmann 0.8.46, `const` basis globals: with
`@basis`'s non-constant globals Julia is two orders of magnitude slower). ns per element
function over a grid of `n` arguments `x` (the midpoints of `[0, 1)`, identical on both sides:
`x = 0` would hit Julia's zero-angle and parabolic `exp` defects), every coefficient of every
result summed into the checksum (Julia would otherwise drop the unread lanes of its isbits
results):

* `ℝ3/…`: `exp`, `log`, `sqrt`, `cosh` of couples and terms; `exp`, `cos` of a bivector
  chain `x(0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃)`; `exp`, `log`, `sqrt` of the quaternion
  `1 + x(…)`; `exp`, `log`, `sqrt`, `^3` of a dense multivector; the input constructions
  alone (`input_*`, the floor of every case);
* `PGA3/Chain.exp` (a motor), `CGA3/Chain.exp` (a translator);
* `Inf3/…`, `CGA3/…` (`S"∞+++"`, `S"∞∅+++"`, generated kernels as `basis!` emits them):
  `↑`, `↓`, the README torus, orbit and helix curves per sample, and the `orb` field
  (`chainfield`) per point.
-/

namespace Bench.Composite

open _root_.Grassmann DirectSum StaticVectors AbstractTensors Bench JuliaBase

/-- The Riemann sphere over `ℝ³` (the README curves). -/
abbrev Inf3 : TensorBundle := S!"∞+++"

namespace K
grassmann_kernels Inf3
end K

/-- Sum `f` over a grid (tail-recursive, unboxed). -/
@[specialize] def loopF (f : Float → Float) (xs : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < xs.size then loopF f xs (i + 1) (acc + f (xs[i]'h)) else acc
termination_by xs.size - i

/-- The sum of every coefficient (so no output of a result is dead code). -/
@[inline] def tot {n : Nat} (v : Values Float n) : Float := v.data.foldl (· + ·) 0

/-- `n` points `a + i·d`. -/
def grid (n : Nat) (a d : Float) : FloatArray :=
  (List.range n).foldl (fun acc i => acc.push (a + i.toUInt64.toFloat * d)) (FloatArray.emptyWithCapacity n)

/-- `0.0` as a module constant. -/
def z0 : Float := f64! 0.0

/-- Bench input coefficients at a literal size `k` (`h : k = n` by `rfl`), so no layout
size (a `Nat` power in DirectSum's `Layout.size`) is computed per call. -/
@[inline] def vs {n : Nat} (k : Nat) (h : k = n) (f : Fin k → Float) : Values Float n :=
  (Values.ofFn f).cast h

/-! ## ℝ3 elements -/

/-- The bivector chain `x(0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃)`. -/
@[inline] def biv (x : Float) : Chain ℝ3 2 Float :=
  ⟨vs 3 rfl fun i => match i.1 with | 0 => (f64! 0.3) * x | 1 => (f64! 0.2) * x | _ => (f64! 0.4) * x⟩

/-- The quaternion `1 + x(0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃)`. -/
@[inline] def quat (x : Float) : Spinor ℝ3 Float :=
  ⟨vs 4 rfl fun i => match i.1 with | 0 => (f64! 1.0) | 1 => (f64! 0.3) * x | 2 => (f64! 0.2) * x | _ => (f64! 0.4) * x⟩

/-- The dense multivector `0.1x·(1, 2, …, 8)`. -/
@[inline] def mvx (x : Float) : Multivector ℝ3 Float :=
  ⟨vs 8 rfl fun i => ((f64! 0.1) * x) * (i.1.toUInt64.toFloat + 1)⟩

/-- The quaternion `1 + x(0.3v₁₂ + 0.2v₁₃ + 0.4v₂₃)` stored as a dense multivector (Julia's
`log`/`sqrt` of a multivector need `inv(t + 1)`, defined when `(~m)m` is a scalar). -/
@[inline] def mvq (x : Float) : Multivector ℝ3 Float :=
  ⟨vs 8 rfl fun i => match i.1 with | 0 => (f64! 1.0) | 4 => (f64! 0.3) * x | 5 => (f64! 0.2) * x | 6 => (f64! 0.4) * x | _ => z0⟩

/-- A PGA3 bivector (a motor generator): `x(0.3, 0.2, 0.4, 0.1, 0.5, 0.6)`. -/
@[inline] def pgaBiv (x : Float) : Chain PGA3 2 Float :=
  ⟨vs 6 rfl fun i => x * (match i.1 with | 0 => (f64! 0.3) | 1 => (f64! 0.2) | 2 => (f64! 0.4) | 3 => (f64! 0.1) | 4 => (f64! 0.5) | _ => (f64! 0.6))⟩

/-- A CGA3 translator generator `x(v∞₁ + 0.5v∞₂ - 0.25v∞₃)` (null: `exp = 1 + t`). -/
@[inline] def cgaTrans (x : Float) : Chain CGA3 2 Float :=
  ⟨vs 10 rfl fun i => match i.1 with | 1 => x | 2 => (f64! 0.5) * x | 3 => -(f64! 0.25) * x | _ => z0⟩

/-! ## The README curves -/

/-- `π` (Julia's `Float64(π)`). -/
def pi : Float := f64! 3.141592653589793

/-- A vector of `Inf3` from its coefficients `(v∞, v₁, v₂, v₃)`. -/
@[inline] def v3 (a b c d : Float) : Chain Inf3 1 Float :=
  ⟨vs 4 rfl fun i => match i.1 with | 0 => a | 1 => b | 2 => c | _ => d⟩

/-- `(3/7)v₁₂ + v∞₃` in `Inf3`. -/
def torusBiv : Chain Inf3 2 Float :=
  ⟨vs 6 rfl fun i => match i.1 with | 2 => (f64! 1.0) | 3 => (3 : Float) / 7 | _ => z0⟩

/-- `v1 + v2 + v3`. -/
def p111 : Chain Inf3 1 Float := v3 0 1 1 1

/-- `v1 + v2 - v3`. -/
def p11m : Chain Inf3 1 Float := v3 0 1 1 (-1)

/-- The torus curve `↓(exp(π t((3/7)v₁₂ + v∞₃)) >>> ↑(v1+v2+v3))`. -/
@[inline] def torus (t : Float) : Chain Inf3 1 Float :=
  Chain.down (Chain.expEven ((pi * t) * torusBiv) >>> Chain.up p111)

/-- `sin(3t)·3v1 + cos(2t)·7v2 - sin(5t)·4v3`. -/
@[inline] def wobble (t : Float) : Chain Inf3 1 Float :=
  v3 0 (F64.sin (3 * t) * 3) (F64.cos (2 * t) * 7) (-(F64.sin (5 * t) * 4))

/-- `v∞ ⟑ (x·w)` as a spinor. -/
@[inline] def infTimes (x : Float) (w : Chain Inf3 1 Float) : Spinor Inf3 Float :=
  (v3 x 0 0 0 * w : Half Inf3 ((1 + 1) % 2 == 1) Float)

/-- The `orbit-2` curve `↓(exp(t v∞ (…)/2) >>> ↑(v1+v2-v3))`. -/
@[inline] def orbit2 (t : Float) : Chain Inf3 1 Float :=
  Chain.down (Half.exp (infTimes t (wobble t) / (2 : Float)) >>> Chain.up p11m)

/-- `v₁₂` as a spinor of `Inf3`. -/
def v12S : Spinor Inf3 Float := ⟨vs 8 rfl fun i => if i.1 = 4 then (f64! 1.0) else z0⟩

/-- The `orbit-4` curve `↓(exp(t(v12 + 0.07v∞(…)/2)) >>> ↑(v1+v2-v3))`. -/
@[inline] def orbit4 (t : Float) : Chain Inf3 1 Float :=
  let B : Spinor Inf3 Float := v12S + infTimes (f64! 0.07) (wobble t) / (2 : Float)
  Chain.down (Half.exp (t * B) >>> Chain.up p11m)

/-- `(3/7)v₁₂ + v∞₃` in `CGA3`. -/
def helixBiv : Chain CGA3 2 Float :=
  ⟨vs 10 rfl fun i => match i.1 with | 3 => (f64! 1.0) | 7 => (3 : Float) / 7 | _ => z0⟩

/-- `v1 + v2 + v3` in `CGA3`. -/
def c111 : Chain CGA3 1 Float := ⟨vs 5 rfl fun i => if i.1 ≥ 2 then (f64! 1.0) else z0⟩

/-- The helix curve (the torus expression in `CGA3`). -/
@[inline] def helix (t : Float) : Chain CGA3 1 Float :=
  Chain.down (Chain.expEven ((pi * t) * helixBiv) >>> Chain.up c111)

/-- The `orb` versor `exp((π/4)(v₁₂ + v∞₃))`. -/
def orbVersor : Spinor Inf3 Float :=
  Chain.expEven ((pi / (4 : Float)) * (⟨vs 6 rfl fun i => match i.1 with | 2 => (f64! 1.0) | 3 => (f64! 1.0) | _ => z0⟩ : Chain Inf3 2 Float))

/-- The subspace `V(2,3,4)` of `Inf3`. -/
def sub234 : SubSpace Inf3 := TensorBundle.sub Inf3 [2, 3, 4]

/-- The grid of arguments and its parameter string. -/
def setup : BenchM (Nat × String × FloatArray) := do
  let n ← size 1000 20
  let d := (f64! 1.0) / n.toUInt64.toFloat
  return (n, s!"n={n}", grid n ((f64! 0.5) * d) d)

/-- Inputs, couples and terms. -/
def casesScalar : BenchM Unit := do
  let (n, p, xs) ← setup
  bench "ℝ3/input_biv" (ops := n) (param := p) fun s => loopF (fun x => tot (biv x).v) (blackBox s xs) 0 0
  bench "ℝ3/input_quat" (ops := n) (param := p) fun s => loopF (fun x => tot (quat x).v) (blackBox s xs) 0 0
  bench "ℝ3/Couple.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => (let z := Couple.exp (⟨3, (f64! 0.1), x⟩ : Couple ℝ3 Float); z.re + z.im)) (blackBox s xs) 0 0
  bench "ℝ3/Single.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => (let z := Single.exp (⟨3, x⟩ : Single ℝ3 2 Float); z.re + z.im)) (blackBox s xs) 0 0
  bench "ℝ3/Couple.log" (ops := n) (param := p) fun s =>
    loopF (fun x => (let z := Couple.log (⟨3, (f64! 1.0), x⟩ : Couple ℝ3 Float); z.re + z.im)) (blackBox s xs) 0 0
  bench "ℝ3/Couple.sqrt" (ops := n) (param := p) fun s =>
    loopF (fun x => (let z := Couple.sqrt (⟨3, (f64! 1.0), x⟩ : Couple ℝ3 Float); z.re + z.im)) (blackBox s xs) 0 0
  bench "ℝ3/Couple.cosh" (ops := n) (param := p) fun s =>
    loopF (fun x => (let z := Couple.cosh (⟨1, (f64! 0.5), x⟩ : Couple ℝ3 Float); z.re + z.im)) (blackBox s xs) 0 0

/-- Bivector chains and quaternions of `ℝ3`. -/
def casesEven : BenchM Unit := do
  let (n, p, xs) ← setup
  bench "ℝ3/Chain.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (biv x).expEven.v) (blackBox s xs) 0 0
  bench "ℝ3/Chain.exp_mv" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (biv x).exp.v) (blackBox s xs) 0 0
  bench "ℝ3/Chain.cos" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (biv x).cos.v) (blackBox s xs) 0 0
  bench "ℝ3/Spinor.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (quat x).exp.v) (blackBox s xs) 0 0
  bench "ℝ3/Spinor.log" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (quat x).log.v) (blackBox s xs) 0 0
  bench "ℝ3/Spinor.sqrt" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (quat x).sqrt.v) (blackBox s xs) 0 0

/-- Dense multivectors of `ℝ3` and bivectors of other spaces. -/
def casesDense : BenchM Unit := do
  let (n, p, xs) ← setup
  bench "ℝ3/Multivector.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (mvx x).exp.v) (blackBox s xs) 0 0
  bench "ℝ3/Multivector.log" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (mvq (x + (f64! 0.1))).log.v) (blackBox s xs) 0 0
  bench "ℝ3/Multivector.sqrt" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (mvq (x + (f64! 0.1))).sqrt.v) (blackBox s xs) 0 0
  bench "ℝ3/Multivector.pow3" (ops := n) (param := p) fun s =>
    loopF (fun x => tot ((mvx x).pow 3).v) (blackBox s xs) 0 0
  bench "PGA3/Chain.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (pgaBiv x).expEven.v) (blackBox s xs) 0 0
  bench "CGA3/Chain.exp" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (cgaTrans x).expEven.v) (blackBox s xs) 0 0

/-- A vector of `CGA3` from `(v1, v2, v3)` and its null parts. -/
@[inline] def c3 (a b c d e : Float) : Chain CGA3 1 Float :=
  ⟨vs 5 rfl fun i => match i.1 with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e⟩

/-- `↑`, `↓`. -/
def casesUpDown : BenchM Unit := do
  let (n, p, xs) ← setup
  bench "Inf3/up" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (Chain.up (v3 0 x (f64! 0.5) (-x))).v) (blackBox s xs) 0 0
  bench "Inf3/down" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (Chain.down (v3 (f64! 0.25) x (f64! 0.5) (-x))).v) (blackBox s xs) 0 0
  bench "CGA3/up" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (Chain.up (c3 0 0 x (f64! 0.5) (-x))).v) (blackBox s xs) 0 0
  bench "CGA3/down" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (Chain.down (c3 ((f64! 0.5) + x * x) 1 x (f64! 0.5) (-x))).v) (blackBox s xs) 0 0

/-- The README curves per sample and the `orb` field per point. -/
def casesCurves : BenchM Unit := do
  let (n, p, xs) ← setup
  bench "Inf3/torus" (ops := n) (param := p) fun s => loopF (fun t => tot (torus t).v) (blackBox s xs) 0 0
  bench "Inf3/orbit2" (ops := n) (param := p) fun s => loopF (fun t => tot (orbit2 t).v) (blackBox s xs) 0 0
  bench "Inf3/orbit4" (ops := n) (param := p) fun s => loopF (fun t => tot (orbit4 t).v) (blackBox s xs) 0 0
  bench "CGA3/helix" (ops := n) (param := p) fun s => loopF (fun t => tot (helix t).v) (blackBox s xs) 0 0
  bench "Inf3/chainfield" (ops := n) (param := p) fun s =>
    loopF (fun x => tot (Fields.chainfield orbVersor sub234 sub234
      ⟨vs 3 rfl fun i => match i.1 with | 0 => x | 1 => (f64! 0.5) | _ => -x⟩).v) (blackBox s xs) 0 0

/-- The suite. -/
def suite : Suite := ⟨"composite", do
  casesScalar
  casesEven
  casesDense
  casesUpDown
  casesCurves⟩

end Bench.Composite
