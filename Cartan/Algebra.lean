import Cartan.Kernel

/-!
# The lifted algebra of tensor fields

Every operation on fields is the pointwise lift of the fiber operation; the result lives over the
same base (Julia `TensorField(base(a), op.(fiber(a), fiber(b)))`, `Cartan.jl:345-456`; port notes
§2.7, §4.3). Because the base is in the type, both operands of a binary operation are over the
same base by construction (Julia checks it at runtime for group A only).

* **Linear operations** (`+ - neg`, scaling by a `Float`) on fibers whose encoding is linear
  (`LinearFiber`: `Float`, `Complex`, `Chain`, `Spinor`, `Multivector`, `AffinePoint`) run as one
  loop over the flat arrays. `Float` fields follow Julia's lazy ranges (`Axis.neg`, `scale`,
  `div`, `add`, `sub`), so `2 .* t`, `t ./ 3`, `-t`, `t + t` keep `TwicePrecision` elements.
* **Every other operation** is the generic lift of a fiber instance: `*` (geometric product, or
  the scalar products of Julia's `Real`/`Complex` methods), `/`, `∧`, `∨`, `⋅` (contraction), `⟑`,
  `×`, `⊘`, `⋆`, `!`, `~`, involutions, grade projections, and `+ -` between different fiber types
  or with a scalar (Julia's `t + 1` materializes: `Ref(1)` blocks the range method).
* **Scalar functions** of `Float`/`Complex` fibers (`Analytic`): Julia's own `exp`/`log`/`^` bit
  for bit (JuliaBase kernels), `libm` for the trigonometric functions; the metric argument Julia
  threads through them (`f(x, g) = f(x)` for numbers, AbstractTensors.jl:394-401) has no effect.
* **Metrics.** Julia passes the base metric to `*`, `⋅`, `⋆`, `abs`, …; for the induced metric
  that is the fiber algebra's own product, which is what the Grassmann instances compute. Metric
  extensors that differ from the algebra's (Julia `Outermorphism` metrics from `intrinsicmetric`)
  are not modelled by the Grassmann port and are not threaded here.
* **Reductions** (`sum`, `prod`, `cumsum`, `maximum`, `supnorm`, `findroot`, …) with Julia's
  association order where it fixes the rounding.

`<` on fields is Julia's *contraction* `a < b = contraction(b, a)` (not an order), provided as
`lt`.
-/

namespace Cartan

open Grassmann DirectSum StaticVectors AbstractTensors JuliaBase MeshTopology

/-! ## Flat loops -/

/-- `out[j] := f a[j] b[j]` for `j ∈ [i, i+k)` (tail recursive; `out` is written in place once
unshared). -/
@[specialize] def zipFloatsLoop (f : Float → Float → Float) (a b : FloatArray) :
    (k i : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, i, out => zipFloatsLoop f a b k (i + 1) (out.set! i (f (a.get! i) (b.get! i)))

theorem size_zipFloatsLoop (f : Float → Float → Float) (a b : FloatArray) :
    ∀ (k i : Nat) (out : FloatArray), (zipFloatsLoop f a b k i out).size = out.size
  | 0, _, _ => rfl
  | k + 1, i, out => by rw [zipFloatsLoop, size_zipFloatsLoop f a b k (i + 1), FloatArray.size_set!']

/-- `[f a[i] b[i] | i < a.size]`, written over a copy of `a` (one allocation, no pushes). -/
@[inline] def zipFloats (f : Float → Float → Float) (a b : FloatArray) : FloatArray :=
  zipFloatsLoop f a b a.size 0 a

@[simp] theorem size_zipFloats (f : Float → Float → Float) (a b : FloatArray) :
    (zipFloats f a b).size = a.size := size_zipFloatsLoop f a b _ _ _

/-- `out[j] := f a[j]` for `j ∈ [i, i+k)` (tail recursive, in place once unshared). -/
@[specialize] def mapFloatsLoop (f : Float → Float) (a : FloatArray) :
    (k i : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, i, out => mapFloatsLoop f a k (i + 1) (out.set! i (f (a.get! i)))

theorem size_mapFloatsLoop (f : Float → Float) (a : FloatArray) :
    ∀ (k i : Nat) (out : FloatArray), (mapFloatsLoop f a k i out).size = out.size
  | 0, _, _ => rfl
  | k + 1, i, out => by rw [mapFloatsLoop, size_mapFloatsLoop f a k (i + 1), FloatArray.size_set!']

/-- `[f a[i] | i < a.size]`, written over a copy of `a`. -/
@[inline] def mapFloats (f : Float → Float) (a : FloatArray) : FloatArray :=
  mapFloatsLoop f a a.size 0 a

@[simp] theorem size_mapFloats (f : Float → Float) (a : FloatArray) :
    (mapFloats f a).size = a.size := size_mapFloatsLoop f a _ _ _

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {F F' F'' : Type}
  [FlatFiber F] [FlatFiber F'] [FlatFiber F'']

/-! ## Linear operations on the flat encoding -/

section Linear

variable [LinearFiber F]

/-- Componentwise combination of the flat arrays (`LinearFiber` operations). -/
@[inline] def zipFlat (f : Float → Float → Float) (a b : TensorField m F) : TensorField m F :=
  ⟨zipFloats f a.data b.data, by rw [size_zipFloats, a.size_data], none⟩

/-- Componentwise map of the flat array (`LinearFiber` operations). -/
@[inline] def mapFlat (f : Float → Float) (a : TensorField m F) : TensorField m F :=
  ⟨mapFloats f a.data, by rw [size_mapFloats, a.size_data], none⟩

/-- Julia `a + b` (group A, `Cartan.jl:346-354`). -/
instance : Add (TensorField m F) := ⟨zipFlat (· + ·)⟩
/-- Julia `a - b`. -/
instance : Sub (TensorField m F) := ⟨zipFlat (· - ·)⟩
/-- Julia `-t` (`Cartan.jl:395`). -/
instance : Neg (TensorField m F) := ⟨mapFlat (- ·)⟩
/-- Julia `x * t` (`Grassmann.:*.(x, fiber(t))`, `Cartan.jl:389`). -/
instance : HMul Float (TensorField m F) (TensorField m F) := ⟨fun x t => mapFlat (x * ·) t⟩
/-- Julia `t * x`. -/
instance : HMul (TensorField m F) Float (TensorField m F) := ⟨fun t x => mapFlat (· * x) t⟩
/-- Julia `t / x`: componentwise for numbers, `t * (1/x)` for Grassmann fibers
(`LinearFiber.recipDiv`, Grassmann `src/algebra.jl:704`). -/
@[inline] def divScalar (t : TensorField m F) (x : Float) : TensorField m F :=
  if LinearFiber.recipDiv F then
    let r := (1 : Float) / x
    mapFlat (· * r) t
  else mapFlat (· / x) t

instance : HDiv (TensorField m F) Float (TensorField m F) := ⟨divScalar⟩

/-- `out[k] = f a[k] s[k / w]`: each point's `w` floats combined with that point's scalar. -/
@[specialize] def zipScalarLoop (f : Float → Float → Float) (a s : FloatArray) (w : Nat) :
    (k i : Nat) → FloatArray → FloatArray
  | 0, _, out => out
  | k + 1, i, out => zipScalarLoop f a s w k (i + 1) (out.set! i (f (a.get! i) (s.get! (i / w))))

theorem size_zipScalarLoop (f : Float → Float → Float) (a s : FloatArray) (w : Nat) :
    ∀ (k i : Nat) (out : FloatArray), (zipScalarLoop f a s w k i out).size = out.size
  | 0, _, _ => rfl
  | k + 1, i, out => by
    rw [zipScalarLoop, size_zipScalarLoop f a s w k (i + 1), FloatArray.size_set!']

/-- Combine every component of `t` with the scalar field `s` at its point. -/
@[inline] def zipScalar (f : Float → Float → Float) (t : TensorField m F) (s : TensorField m Float) :
    TensorField m F :=
  ⟨zipScalarLoop f t.data s.data (FlatFiber.width F) t.data.size 0 t.data,
    by rw [size_zipScalarLoop, t.size_data], none⟩

/-- Julia `a / b` with a scalar field `b` (`./(fiber(a), fiber(b))`, `Cartan.jl:371`): each fiber
divided by the scalar at its point, as `a * (1/b)` for Grassmann fibers. -/
@[inline] def divField (t : TensorField m F) (s : TensorField m Float) : TensorField m F :=
  if LinearFiber.recipDiv F then zipScalar (fun x y => x * ((1 : Float) / y)) t s
  else zipScalar (· / ·) t s

instance (priority := default + 1) : HDiv (TensorField m F) (TensorField m Float) (TensorField m F) :=
  ⟨divField⟩

/-- Julia `a * t` for a scalar field `a` (`fiber(a) .* fiber(t)`, `Cartan.jl:367`): every fiber
scaled by the scalar at its point (`a * x`, Grassmann's `Real * Chain`). -/
instance (priority := default + 5) : HMul (TensorField m Float) (TensorField m F) (TensorField m F) :=
  ⟨fun s t => zipScalar (fun x y => y * x) t s⟩

/-- Julia `t * a` for a scalar field `a` (`Cartan.jl:369`). -/
instance (priority := default + 5) : HMul (TensorField m F) (TensorField m Float) (TensorField m F) :=
  ⟨fun t s => zipScalar (· * ·) t s⟩

end Linear

/-! ## `Float` fields: Julia's lazy range arithmetic -/

section Ranges

/-- A `Float` field whose fibers are the range `r` (materialized, and tagged). -/
def ofRange (m : M) (r : Axis) : TensorField m Float := { ofFn m r.get with range? := some r }

/-- The field `r` when the range operation `op` is defined on the tags, else `eager`. -/
@[inline] def rangeOr (m : M) (r : Option Axis) (eager : Unit → TensorField m Float) :
    TensorField m Float :=
  match r with
  | some r => ofRange m r
  | none => eager ()

/-- Julia `a + b` for `Float` fields: two range fibers add as ranges (`r₁ + r₂`,
`base/twiceprecision.jl:625`), anything else pointwise. -/
def addF (a b : TensorField m Float) : TensorField m Float :=
  rangeOr m (do Axis.add (← a.range?) (← b.range?)) fun _ => zipFlat (· + ·) a b

/-- Julia `a - b` for `Float` fields (`r₁ - r₂ = r₁ + (-r₂)`). -/
def subF (a b : TensorField m Float) : TensorField m Float :=
  rangeOr m (do Axis.sub (← a.range?) (← b.range?)) fun _ => zipFlat (· - ·) a b

/-- Julia `-t` for a `Float` field (`-.(r)` stays a range). -/
def negF (t : TensorField m Float) : TensorField m Float :=
  rangeOr m (t.range? >>= Axis.neg) fun _ => mapFlat (- ·) t

/-- Julia `x * t` / `t * x` for a `Float` field (`x .* r` stays a range). -/
def scaleF (x : Float) (t : TensorField m Float) : TensorField m Float :=
  rangeOr m (t.range? >>= Axis.scale x) fun _ => mapFlat (x * ·) t

/-- Julia `t / x` for a `Float` field (`r ./ x` stays a range). -/
def divF (t : TensorField m Float) (x : Float) : TensorField m Float :=
  rangeOr m (t.range? >>= Axis.div x) fun _ => mapFlat (· / x) t

instance (priority := high) : Add (TensorField m Float) := ⟨addF⟩
instance (priority := high) : Sub (TensorField m Float) := ⟨subF⟩
instance (priority := high) : Neg (TensorField m Float) := ⟨negF⟩
instance (priority := high) : HMul Float (TensorField m Float) (TensorField m Float) := ⟨scaleF⟩
instance (priority := high) : HMul (TensorField m Float) Float (TensorField m Float) :=
  ⟨fun t x => scaleF x t⟩
instance (priority := high) : HDiv (TensorField m Float) Float (TensorField m Float) := ⟨divF⟩

end Ranges

/-! ## Generic lifts of fiber operations -/

/-- Julia `a + b` between different fiber types (Julia promotes; e.g. a scalar field plus a
spinor field). -/
instance (priority := low) [HAdd F F' F''] : HAdd (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith (· + ·)⟩
/-- Julia `a - b` between different fiber types. -/
instance (priority := low) [HSub F F' F''] : HSub (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith (· - ·)⟩
/-- Julia `a * b`: the fiber product (geometric product of Grassmann fibers, `wedgedot_metric`
with the induced metric; plain `.*` when a side is `Real`/`Complex`, `Cartan.jl:363-370`). -/
instance [HMul F F' F''] : HMul (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith (· * ·)⟩
/-- Julia `a / b` (`Cartan.jl:371-372, 387-394`). -/
instance [HDiv F F' F''] : HDiv (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith (· / ·)⟩

/-- Julia `t + x` with a scalar (`+.(fiber(t), Ref(x))`, never lazy). -/
instance (priority := low) [HAdd F Float F'] : HAdd (TensorField m F) Float (TensorField m F') :=
  ⟨fun t x => t.map (· + x)⟩
/-- Julia `x + t` with a scalar. -/
instance (priority := low) [HAdd Float F F'] : HAdd Float (TensorField m F) (TensorField m F') :=
  ⟨fun x t => t.map (x + ·)⟩
/-- Julia `t - x` with a scalar. -/
instance (priority := low) [HSub F Float F'] : HSub (TensorField m F) Float (TensorField m F') :=
  ⟨fun t x => t.map (· - x)⟩
/-- Julia `x - t` with a scalar. -/
instance (priority := low) [HSub Float F F'] : HSub Float (TensorField m F) (TensorField m F') :=
  ⟨fun x t => t.map (x - ·)⟩
/-- Julia `x * t` with a scalar, for fibers without a linear flat encoding. -/
instance (priority := low) [HMul Float F F'] : HMul Float (TensorField m F) (TensorField m F') :=
  ⟨fun x t => t.map (x * ·)⟩
/-- Julia `t * x` with a scalar, for fibers without a linear flat encoding. -/
instance (priority := low) [HMul F Float F'] : HMul (TensorField m F) Float (TensorField m F') :=
  ⟨fun t x => t.map (· * x)⟩
/-- Julia `t / x` with a scalar, for fibers without a linear flat encoding. -/
instance (priority := low) [HDiv F Float F'] : HDiv (TensorField m F) Float (TensorField m F') :=
  ⟨fun t x => t.map (· / x)⟩

/-- Julia `a ∧ b` (group A). -/
instance [Wedge F F' F''] : Wedge (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith wedge⟩
/-- Julia `a ∨ b` (group A). -/
instance [Vee F F' F''] : Vee (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith vee⟩
/-- Julia `a ⋅ b` = `contraction(a, b)` (`contraction_metric`, group B). -/
instance [Contraction F F' F''] :
    Contraction (TensorField m F) (TensorField m F') (TensorField m F'') := ⟨zipWith contraction⟩
/-- Julia `wedgedot(a, b)` = `a ⟑ b` (group B). -/
instance [WedgeDot F F' F''] : WedgeDot (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith wedgedot⟩
/-- Julia `veedot(a, b)` = `a ⟇ b` (group B). -/
instance [VeeDot F F' F''] : VeeDot (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith veedot⟩
/-- Julia `a ⊘ b` (group B). -/
instance [Sandwich F F' F''] : Sandwich (TensorField m F) (TensorField m F') (TensorField m F'') :=
  ⟨zipWith sandwich⟩
/-- Julia `a >>> b` (group B). -/
instance [HShiftRight F F' F''] :
    HShiftRight (TensorField m F) (TensorField m F') (TensorField m F'') := ⟨zipWith (· >>> ·)⟩

/-- Julia `⋆t` (group D; the induced metric's Hodge complement). -/
instance [Hodge F F'] : Hodge (TensorField m F) (TensorField m F') := ⟨map hodge⟩
/-- Julia `!t` = `complementright(t)`. -/
instance [ComplementRight F F'] : ComplementRight (TensorField m F) (TensorField m F') :=
  ⟨map complementRight⟩
/-- Julia `complementleft(t)` (group C). -/
instance [ComplementLeft F F'] : ComplementLeft (TensorField m F) (TensorField m F') :=
  ⟨map complementLeft⟩
/-- Julia `~t` = `reverse(t)` (group C). -/
instance [Reverse F] : Reverse (TensorField m F) := ⟨map Reverse.reverse⟩
/-- Julia `involute(t)`. -/
instance [Involute F] : Involute (TensorField m F) := ⟨map involute⟩
/-- Julia `clifford(t)` (group C). -/
instance [Clifford F] : Clifford (TensorField m F) := ⟨map clifford⟩
/-- Julia `even(t)` (group C). -/
instance [Even F F'] : Even (TensorField m F) (TensorField m F') := ⟨map even⟩
/-- Julia `odd(t)` (group C). -/
instance [Odd F F'] : Odd (TensorField m F) (TensorField m F') := ⟨map odd⟩
/-- Julia `scalar(t)`, `vector(t)`, … (group C). -/
instance {G : Nat} [GradeProj F G F'] : GradeProj (TensorField m F) G (TensorField m F') :=
  ⟨map (GradeProj.proj (G := G))⟩
/-- Julia `pseudoscalar(t)` = `volume(t)` (group C). -/
instance [Volume F F'] : Volume (TensorField m F) (TensorField m F') := ⟨map volume⟩
/-- Julia `inv(t)` (group D). -/
instance [Inv F] : Inv (TensorField m F) := ⟨map Inv.inv⟩

/-- Julia `a < b` for fields = `contraction_metric(b, a)` (`Cartan.jl:383`): a contraction with
the arguments swapped, not a comparison. -/
@[inline] def lt [Contraction (TensorField m F') (TensorField m F) (TensorField m F'')]
    (a : TensorField m F) (b : TensorField m F') : TensorField m F'' := contraction b a

/-- Julia `a << b = contraction(b, ~a)` (`Cartan.jl:357`). -/
@[inline] def shiftl [Reverse (TensorField m F)]
    [Contraction (TensorField m F') (TensorField m F) (TensorField m F'')]
    (a : TensorField m F) (b : TensorField m F') : TensorField m F'' := contraction b (Reverse.reverse a)

/-- Julia `a >> b = contraction(~a, b)` (`Cartan.jl:358`). -/
@[inline] def shiftr [Reverse (TensorField m F)]
    [Contraction (TensorField m F) (TensorField m F') (TensorField m F'')]
    (a : TensorField m F) (b : TensorField m F') : TensorField m F'' := contraction (Reverse.reverse a) b

/-! ## Planned Grassmann products (`Cartan.Kernel`)

For fibers with a dense `Float` layout the products and linear maps run the Grassmann plan over
the whole field (bit-identical to the pointwise lift, which they take precedence over). `×` is
AbstractTensors' `⋆(a ∧ b)` on the field level, so it is planned too. -/

section Planned

variable {V : TensorBundle} {X Y Z : Type} [FlatFiber X] [FlatFiber Y] [FlatFiber Z]
  [DenseLayout X V Float] [DenseLayout Y V Float] [DenseLayout Z V Float]

instance (priority := default + 10) [HMul X Y Z] :
    HMul (TensorField m X) (TensorField m Y) (TensorField m Z) := ⟨planZip .mul (· * ·)⟩
instance (priority := default + 10) [WedgeDot X Y Z] :
    WedgeDot (TensorField m X) (TensorField m Y) (TensorField m Z) := ⟨planZip .mul wedgedot⟩
instance (priority := default + 10) [Wedge X Y Z] :
    Wedge (TensorField m X) (TensorField m Y) (TensorField m Z) := ⟨planZip .wedge wedge⟩
instance (priority := default + 10) [Vee X Y Z] :
    Vee (TensorField m X) (TensorField m Y) (TensorField m Z) := ⟨planZip .vee vee⟩
instance (priority := default + 10) [Contraction X Y Z] :
    Contraction (TensorField m X) (TensorField m Y) (TensorField m Z) :=
  ⟨planZip .contraction contraction⟩
instance (priority := default + 10) [Hodge X Z] : Hodge (TensorField m X) (TensorField m Z) :=
  ⟨planMap .complementrighthodge hodge⟩
instance (priority := default + 10) [ComplementRight X Z] :
    ComplementRight (TensorField m X) (TensorField m Z) := ⟨planMap .complementright complementRight⟩
instance (priority := default + 10) [ComplementLeft X Z] :
    ComplementLeft (TensorField m X) (TensorField m Z) := ⟨planMap .complementleft complementLeft⟩
instance (priority := default + 10) [Reverse X] : Reverse (TensorField m X) :=
  ⟨planMap .reverse Reverse.reverse⟩
instance (priority := default + 10) [Involute X] : Involute (TensorField m X) :=
  ⟨planMap .involute involute⟩
instance (priority := default + 10) [Clifford X] : Clifford (TensorField m X) :=
  ⟨planMap .clifford clifford⟩

end Planned

/-! ## Norms -/

/-- The norm `√(x₀² + x₁² + …)` of the flat encoding at point `i` (StaticVectors `norm`: the sum
of squares left to right from the first). -/
@[inline] def flatNormAt (t : TensorField m F) (i : Nat) : Float :=
  let w := FlatFiber.width F
  let o := i * w
  if w == 0 then 0 else
  let x0 := t.data.get! o
  Float.sqrt (go o w (x0 * x0) 1)
where
  /-- Accumulate the squares of components `j, …, w-1`. -/
  go (o w : Nat) (s : Float) : Nat → Float
    | j => if j < w then go o w (s + t.data.get! (o + j) * t.data.get! (o + j)) (j + 1) else s
  termination_by j => w - j

/-- Julia `norm(t)` (`Cartan.jl:450`): the pointwise norm, a scalar field (on the flat arrays for
Grassmann and point fibers). -/
@[inline] def norm [FiberNorm F] (t : TensorField m F) : TensorField m Float :=
  if FiberNorm.flat F then ofFn m t.flatNormAt else t.map fnorm

/-- Julia `abs(t)` (group D): the pointwise absolute value / norm (Julia returns a `Single`
scalar for a `Chain` fiber; the value is the same). -/
@[inline] def abs [FiberNorm F] (t : TensorField m F) : TensorField m Float := t.norm

/-- Julia `unit(t) = t / abs(t)` (group D): each fiber divided by its norm (as `x * (1/|x|)` for
Grassmann fibers, whose `abs` is a scalar `Single`). -/
@[inline] def unit [FiberNorm F] [LinearFiber F] (t : TensorField m F) : TensorField m F :=
  divField t t.norm

/-- Julia `abs2(t)` of a scalar field. -/
@[inline] def abs2F (t : TensorField m Float) : TensorField m Float := t.map fun x => x * x

/-- Julia `abs2(t)` of a `Chain` field: the grade-0 chain `t ⋅ ~t` (Grassmann `abs2`). -/
@[inline] def abs2Chain {V : TensorBundle} {G : Nat} (t : TensorField m (Chain V G Float)) :
    TensorField m (Chain V 0 Float) := t.map Chain.abs2

/-- Julia `inv(a::Chain)` (Grassmann `src/algebra.jl:482-485`): `~a / value(scalar(abs2(a)))`,
which Grassmann evaluates as `~a * (1/abs2)`. -/
@[inline] def invChain {V : TensorBundle} {G : Nat} (c : Chain V G Float) : Chain V G Float :=
  c.reverse * ((1 : Float) / getD (Chain.abs2 c).v 0)

/-- Julia `inv(t)` of a `Chain` field (group D). -/
instance (priority := default + 1) {V : TensorBundle} {G : Nat} :
    Inv (TensorField m (Chain V G Float)) := ⟨map invChain⟩

/-- Julia `supnorm(t) = maximum(norm, fiber(t))` (`Cartan.jl:513`). -/
def supnorm [FiberNorm F] (t : TensorField m F) : Float :=
  let nt := t.norm
  foldRange (fun acc i => F64.max acc (nt.data.get! i)) (card m) 0 (-(1 : Float) / 0)

/-- Julia `infnorm(t) = minimum(norm, fiber(t))` (`Cartan.jl:514`). -/
def infnorm [FiberNorm F] (t : TensorField m F) : Float :=
  let nt := t.norm
  foldRange (fun acc i => F64.min acc (nt.data.get! i)) (card m) 0 ((1 : Float) / 0)

/-! ## Scalar functions (`Analytic` fibers: `Float`, `Complex`) -/

section Analytic

variable [Analytic F]

/-- Julia `exp(t)`. -/ @[inline] def exp (t : TensorField m F) : TensorField m F := t.map Analytic.exp
/-- Julia `expm1(t)`. -/ @[inline] def expm1 (t : TensorField m F) : TensorField m F := t.map Analytic.expm1
/-- Julia `log(t)` (`log_metric` = `log` for numbers). -/
@[inline] def log (t : TensorField m F) : TensorField m F := t.map Analytic.log
/-- Julia `log1p(t)`. -/ @[inline] def log1p (t : TensorField m F) : TensorField m F := t.map Analytic.log1p
/-- Julia `sqrt(t)` (not `t^0.5`, which differs in the last bit). -/
@[inline] def sqrt (t : TensorField m F) : TensorField m F := t.map Analytic.sqrt
/-- Julia `cbrt(t)`. -/ @[inline] def cbrt (t : TensorField m F) : TensorField m F := t.map Analytic.cbrt
/-- Julia `sin(t)`. -/ @[inline] def sin (t : TensorField m F) : TensorField m F := t.map Analytic.sin
/-- Julia `cos(t)`. -/ @[inline] def cos (t : TensorField m F) : TensorField m F := t.map Analytic.cos
/-- Julia `tan(t)`. -/ @[inline] def tan (t : TensorField m F) : TensorField m F := t.map Analytic.tan
/-- Julia `asin(t)`. -/ @[inline] def asin (t : TensorField m F) : TensorField m F := t.map Analytic.asin
/-- Julia `acos(t)`. -/ @[inline] def acos (t : TensorField m F) : TensorField m F := t.map Analytic.acos
/-- Julia `atan(t)`. -/ @[inline] def atan (t : TensorField m F) : TensorField m F := t.map Analytic.atan
/-- Julia `sinh(t)`. -/ @[inline] def sinh (t : TensorField m F) : TensorField m F := t.map Analytic.sinh
/-- Julia `cosh(t)`. -/ @[inline] def cosh (t : TensorField m F) : TensorField m F := t.map Analytic.cosh
/-- Julia `tanh(t)`. -/ @[inline] def tanh (t : TensorField m F) : TensorField m F := t.map Analytic.tanh
/-- Julia `asinh(t)`. -/ @[inline] def asinh (t : TensorField m F) : TensorField m F := t.map Analytic.asinh
/-- Julia `acosh(t)`. -/ @[inline] def acosh (t : TensorField m F) : TensorField m F := t.map Analytic.acosh
/-- Julia `atanh(t)`. -/ @[inline] def atanh (t : TensorField m F) : TensorField m F := t.map Analytic.atanh
/-- Julia `t ^ x` for a real exponent (`Cartan.jl:386`): Julia's `^(::Float64, ::Float64)`. -/
@[inline] def pow (t : TensorField m F) (x : F) : TensorField m F := t.map (Analytic.pow · x)

end Analytic

/-- Julia `t ^ n` for an integer exponent (`Cartan.jl:345`): Julia's `^(::Float64, ::Int)`
(compensated power by squaring). -/
@[inline] def powInt (t : TensorField m Float) (n : Int) : TensorField m Float := t.map (F64.powInt · n)

/-- Julia `exp2(t)`. -/ @[inline] def exp2 (t : TensorField m Float) : TensorField m Float := t.map F64.exp2
/-- Julia `exp10(t)`. -/ @[inline] def exp10 (t : TensorField m Float) : TensorField m Float := t.map F64.exp10
/-- Julia `log2(t)`. -/ @[inline] def log2 (t : TensorField m Float) : TensorField m Float := t.map F64.log2
/-- Julia `log10(t)`. -/ @[inline] def log10 (t : TensorField m Float) : TensorField m Float := t.map F64.log10
/-- Julia `inv(t)` of a scalar field (`Cartan.jl:361`: `one(x)/x`). -/
@[inline] def invF (t : TensorField m Float) : TensorField m Float := t.map ((1 : Float) / ·)
/-- Julia `sign(t)` (`Cartan.jl:360`). -/ @[inline] def sign (t : TensorField m Float) : TensorField m Float := t.map F64.sign
/-- Julia `round(t)` (group C: round half to even). -/
@[inline] def round (t : TensorField m Float) : TensorField m Float := t.map F64.round
/-- Julia `floor(t)`. -/ @[inline] def floor (t : TensorField m Float) : TensorField m Float := t.map Float.floor
/-- Julia `ceil(t)`. -/ @[inline] def ceil (t : TensorField m Float) : TensorField m Float := t.map Float.ceil
/-- Julia `max(t, x)` (group A, Julia's NaN/`-0.0` rules). -/
@[inline] def maxF (t : TensorField m Float) (x : Float) : TensorField m Float := t.map (F64.max · x)
/-- Julia `min(t, x)` (group A). -/
@[inline] def minF (t : TensorField m Float) (x : Float) : TensorField m Float := t.map (F64.min · x)
/-- Julia `max(a, b)` of two scalar fields (group A). -/
@[inline] def max2 (a b : TensorField m Float) : TensorField m Float := zipWith F64.max a b
/-- Julia `min(a, b)` of two scalar fields (group A). -/
@[inline] def min2 (a b : TensorField m Float) : TensorField m Float := zipWith F64.min a b
/-- Julia `mod(t, x)` (group A: floored, sign of `x`). -/
@[inline] def mod (t : TensorField m Float) (x : Float) : TensorField m Float := t.map (F64.mod · x)
/-- Julia `rem(t, x)` (group A: truncated, sign of `t`). -/
@[inline] def rem (t : TensorField m Float) (x : Float) : TensorField m Float := t.map (F64.rem · x)
/-- Julia `iszero(t)` → `0.0`/`1.0` (group C and C7). -/
@[inline] def iszero (t : TensorField m Float) : TensorField m Float := t.mapPred (· == 0)
/-- Julia `isnan(t)` → `0.0`/`1.0`. -/
@[inline] def isnan (t : TensorField m Float) : TensorField m Float := t.mapPred Float.isNaN

/-- Julia `real(z)` of a complex field. -/
@[inline] def re (t : TensorField m (Complex Float)) : TensorField m Float := t.map (·.re)
/-- Julia `imag(z)` of a complex field. -/
@[inline] def im (t : TensorField m (Complex Float)) : TensorField m Float := t.map (·.im)
/-- Julia `conj(z)` of a complex field. -/
@[inline] def conj (t : TensorField m (Complex Float)) : TensorField m (Complex Float) :=
  t.map Complex.conj
/-- Julia `angle(z)` of a complex field (Julia's metric form has no method, B25; this is
`angle(z)`). -/
@[inline] def angle (t : TensorField m (Complex Float)) : TensorField m Float := t.map ComplexF64.angle

/-! ## Reductions -/

/-- Julia `sum(v::Vector{Float64})`, bit for bit (`JuliaBase.F64.sum`). -/
@[inline] def sumFloats (a : FloatArray) : Float := F64.sum a

/-- One block of Julia's pairwise `prod(::Vector{Float64})` (`base/reduce.jl:252-277`), as LLVM
vectorizes the `@simd` loop on aarch64: `v = a[i0] * a[i0+1]`, then 2 lanes × 4 accumulators over
groups of 8 (`1.0` in the unused lanes), combined, then the scalar tail. -/
def prodBlock (a : FloatArray) (i0 i1 : Nat) : Float :=
  let v := a[i0]! * a[i0 + 1]!
  let r0 := i0 + 2
  let len := i1 + 1 - r0
  let nvec := len / 8 * 8
  let one : Float := 1
  let s := if nvec == 0 then v else vec 0 v one one one one one one one (nvec / 8)
  tail (r0 + nvec) s (len - nvec)
where
  /-- The vector loop over groups of 8. -/
  vec (j : Nat) (a00 a01 a10 a11 a20 a21 a30 a31 : Float) : Nat → Float
    | 0 =>
      let b0 := ((a00 * a10) * a20) * a30
      let b1 := ((a01 * a11) * a21) * a31
      b0 * b1
    | k + 1 =>
      let b := i0 + 2 + 8 * j
      vec (j + 1) (a00 * a[b]!) (a01 * a[b + 1]!) (a10 * a[b + 2]!) (a11 * a[b + 3]!)
        (a20 * a[b + 4]!) (a21 * a[b + 5]!) (a30 * a[b + 6]!) (a31 * a[b + 7]!) k
  /-- Scalar remainder. -/
  tail (i : Nat) (s : Float) : Nat → Float
    | 0 => s
    | k + 1 => tail (i + 1) (s * a[i]!) k

/-- Julia `prod(v::Vector{Float64})` (pairwise with blocks of 1024, `base/reduce.jl`): fewer than
16 elements left to right, otherwise halved until blocks are shorter than 1024. -/
def prodFloats (a : FloatArray) : Float :=
  let n := a.size
  if n == 0 then 1
  else if n == 1 then a[0]!
  else if n < 16 then seq 2 (a[0]! * a[1]!) (n - 2)
  else impl 0 (n - 1) n
where
  /-- Left-to-right accumulation. -/
  seq (i : Nat) (s : Float) : Nat → Float
    | 0 => s
    | k + 1 => seq (i + 1) (s * a[i]!) k
  /-- Pairwise recursion (fuelled by the length). -/
  impl (i0 i1 : Nat) : Nat → Float
    | 0 => prodBlock a i0 i1
    | fuel + 1 =>
      if i0 == i1 then a[i0]!
      else if i1 - i0 < 1024 then prodBlock a i0 i1
      else
        let imid := i0 + (i1 - i0) / 2
        impl i0 imid fuel * impl (imid + 1) i1 fuel

/-- Julia `top_set_bit(x)`: the number of bits of `x` (`0` for `0`). -/
def topSetBit (x : Nat) : Nat := if x == 0 then 0 else Nat.log2 x + 1

/-- Julia `*(x::TwicePrecision{Float64}, v::Integer)` (`base/twiceprecision.jl:310-315`). -/
def tpMulInt (x : TwicePrecision) (v : Int) : TwicePrecision :=
  if v == 0 then ⟨x.hi * 0, x.lo * 0⟩
  else
    let nb := topSetBit (v.natAbs - 1)
    let u := TwicePrecision.truncbits x.hi nb
    TwicePrecision.canonicalize2 (u * Float.ofInt v) (((x.hi - u) + x.lo) * Float.ofInt v)

/-- Julia `sumpair(n)` (`base/twiceprecision.jl:623`). -/
def sumpair (n : Int) : Int × Int := if n % 2 == 0 then (n + 1, n / 2) else (n, (n + 1) / 2)

/-- Julia `sum(r::StepRangeLen{<:Any,<:TwicePrecision,<:TwicePrecision})`
(`base/twiceprecision.jl:604-620`): the closed form in double-double. -/
def sumStepRangeLen (r : StepRangeLen) : Float :=
  let l : Int := r.len
  let np := l - r.offset
  let nn := r.offset - 1
  let sp := sumpair np
  let sn := sumpair nn
  let tp := tpMulInt (tpMulInt r.step sp.1) sp.2
  let tn := tpMulInt (tpMulInt r.step sn.1) sn.2
  -- Julia computes `s_lo += tp.lo - tn.lo` and then never reads it: the low parts of the step
  -- contribution are dropped, and so they are here.
  let s := TwicePrecision.add12 tp.hi (-tn.hi)
  let ref := tpMulInt r.ref l
  let sm := TwicePrecision.add12 s.hi ref.hi
  (TwicePrecision.add12 sm.hi (sm.lo + ref.lo)).hi

/-- Julia `sum(r::AbstractRange{<:Real})` (`base/range.jl:1436-1441`). -/
def sumGenericRange (l : Nat) (first step : Float) : Float :=
  let lf := Float.ofNat l
  lf * first + (if l % 2 == 0 then (step * Float.ofNat (l - 1)) * Float.ofNat (l / 2)
    else (step * lf) * Float.ofNat ((l - 1) / 2))

/-- Julia `sum(t) = sum(fiber(t))` (`Cartan.jl:407`) of a scalar field: the range closed forms
for lazy range fibers, else Julia's pairwise vector sum. -/
def sumF (t : TensorField m Float) : Float :=
  match t.range? with
  | some (.stepLen r) => sumStepRangeLen r
  | some (.lin r) => sumGenericRange r.len r.start r.stepValue
  | _ => sumFloats t.data

/-- Julia `prod(t) = prod(fiber(t))` (`Cartan.jl:408`) of a scalar field. -/
def prodF (t : TensorField m Float) : Float := prodFloats t.data

/-- Julia `sum(fiber(t))` for any fiber with `+`: pairwise with blocks of 1024 like Julia's
`mapreduce_impl`, each block summed left to right (Julia may vectorize blocks of isbits
structs; for fewer than 16 values the order is exactly Julia's). -/
def sum [Add F] (t : TensorField m F) : F :=
  let n := card m
  if n == 0 then FlatFiber.read FloatArray.empty 0
  else if n < 16 then seq 1 (t.get 0) (n - 1)
  else impl 0 (n - 1) n
where
  /-- Left-to-right accumulation. -/
  seq (i : Nat) (s : F) : Nat → F
    | 0 => s
    | k + 1 => seq (i + 1) (s + t.get i) k
  /-- Pairwise recursion. -/
  impl (i0 i1 : Nat) : Nat → F
    | 0 => seq (i0 + 1) (t.get i0) (i1 - i0)
    | fuel + 1 =>
      if i1 - i0 < 1024 then seq (i0 + 1) (t.get i0) (i1 - i0)
      else
        let imid := i0 + (i1 - i0) / 2
        impl i0 imid fuel + impl (imid + 1) i1 fuel

/-- A scan over a field: push the running value `s` (which includes entry `i`), then continue
with `step s (i+1)` (tail recursive). -/
@[specialize] def scanLoop (step : F → Nat → F) : (k i : Nat) → FloatArray → F → FloatArray
  | 0, _, acc, _ => acc
  | 1, _, acc, s => FlatFiber.push acc s
  | k + 2, i, acc, s => scanLoop step (k + 1) (i + 1) (FlatFiber.push acc s) (step s (i + 1))

theorem size_scanLoop (step : F → Nat → F) : ∀ (k i : Nat) (acc : FloatArray) (s : F),
    (scanLoop step k i acc s).size = acc.size + k * FlatFiber.width F
  | 0, _, _, _ => by simp [scanLoop]
  | 1, _, _, _ => by simp [scanLoop]
  | k + 2, i, acc, s => by
    rw [scanLoop, size_scanLoop step (k + 1), FlatFiber.size_push, Nat.succ_mul (k + 1)]; omega

/-- The field of running values `s₀ = t[0]`, `sᵢ = step sᵢ₋₁ i`. -/
@[inline] def scan (t : TensorField m F) (step : F → Nat → F) : TensorField m F :=
  { data := scanLoop step (card m) 0 (FloatArray.emptyWithCapacity (FlatFiber.width F * card m)) (t.get 0)
    size_data := by rw [size_scanLoop, Nat.mul_comm]; exact Nat.zero_add _ }

/-- Julia `cumsum(t)` (`Cartan.jl:411`): running sums, left to right. -/
def cumsum [Add F] (t : TensorField m F) : TensorField m F := t.scan fun s j => s + t.get j

/-- Julia `cumprod(t)` (`Cartan.jl:411`): running products, left to right. -/
def cumprod [Mul F] (t : TensorField m F) : TensorField m F := t.scan fun s j => s * t.get j

/-- The index of the first maximal (`max = true`) or minimal value of a scalar field (Julia
`argmax`/`argmin`: the first extremum, NaN counted as larger than everything). -/
def argExtremum (t : TensorField m Float) (max : Bool) : Nat :=
  foldRange (fun best i =>
    let x := t.get i
    let b := t.get best
    let better := if max then F64.isless b x else F64.isless x b
    if better then i else best) (card m) 0 0

end TensorField

/-! ## Extrema as local tensors -/

namespace TensorField

variable {M : Type} [FrameBundle M] {m : M} {P G : Type} [Coordinates M P G]

/-- Julia `maximum(t) = t[argmax(fiber(t))]` (Cartan `element.jl:119-124`): the local tensor at the
first maximum. -/
def maximum (t : TensorField m Float) : LocalTensor (Coordinate P G) Float := t.localAt (t.argExtremum true)

/-- Julia `minimum(t) = t[argmin(fiber(t))]`. -/
def minimum (t : TensorField m Float) : LocalTensor (Coordinate P G) Float := t.localAt (t.argExtremum false)

/-- Julia `findroot(t) = minimum(norm(t))` (`Cartan.jl:584`). -/
def findroot {F : Type} [FlatFiber F] [FiberNorm F] (t : TensorField m F) :
    LocalTensor (Coordinate P G) Float := t.norm.minimum

/-- Julia `findroot(t, x) = minimum(norm(t - x))` (`Cartan.jl:585`) for a scalar field. -/
def findrootAt (t : TensorField m Float) (x : Float) : LocalTensor (Coordinate P G) Float :=
  (t.map fun y => y - x).norm.minimum

end TensorField

end Cartan
