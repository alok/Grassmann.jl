/-
Vector products and norms over `Values` (Julia `StaticVectors.jl src/linalg.jl`
plus the `LinearAlgebra` fallbacks it relies on).

Evaluation order follows Julia exactly, so `Float` results are bit-identical:
* `dot(a,b) = ((conj(a₁)b₁ + conj(a₂)b₂) + conj(a₃)b₃) + …` (conjugating the
  **left** argument, a left fold that starts from the first term);
* `norm(a) = sqrt((abs2(a₁) + abs2(a₂)) + …)` with **no overflow scaling**
  (`norm(Values(1e200, 1e200)) == Inf`, unlike Julia's `norm(::Vector)`);
* `normalize(a) = inv(norm(a)) * a`, multiplying by the reciprocal.
-/
import StaticVectors.Reduce

universe u

namespace StaticVectors

open Packed JuliaBase

/-- Julia's `dot(x, y)` on elements, returning the inner scalar type `β`:
`conj(x) * y` for numbers, and the recursive `dot` for nested vectors. -/
class JDot (α : Type u) (β : outParam (Type u)) where
  /-- `LinearAlgebra.dot(x, y)` (conjugate-linear in `x`). -/
  dot : α → α → β

/-- Numbers: `dot(x, y) = conj(x) * y`. -/
instance (priority := low) instJDotScalar {α : Type u} [Conj α] [Mul α] : JDot α α :=
  ⟨fun x y => conj x * y⟩

namespace Values

variable {α : Type u} [Packed α] {n : Nat}

/-- Two-vector map-reduce without `init`, starting from `f(a₁, b₁)`; `empty`
when `n = 0`. -/
@[inline] def mapReduce₂ {β γ : Type u} [Packed β] (f : α → β → γ) (op : γ → γ → γ) (empty : γ)
    (a : Values α n) (b : Values β n) : γ :=
  match n, a, b with
  | 0, _, _ => empty
  | k + 1, a, b => foldl₂Loop (fun acc x y => op acc (f x y)) a b k (Nat.le_succ k) (f a.head b.head)

/-- Julia `dot(a, b)` (`SV/linalg.jl:59`): `∑ dot(aᵢ, bᵢ)`, a left fold from
the first term, conjugating the left argument. Julia's `n = 0` value is
`dot(zero, zero)`, which is `0` here. -/
@[inline] def dot {β : Type u} [JDot α β] [Add β] [OfNat β 0] (a b : Values α n) : β :=
  mapReduce₂ JDot.dot (· + ·) 0 a b

/-- Julia `StaticVectors.bilinear_vecdot(a, b)` (`SV/linalg.jl:60`): like `dot`
without conjugation. -/
@[inline] def bilinearDot [Mul α] [Add α] [OfNat α 0] (a b : Values α n) : α :=
  mapReduce₂ (· * ·) (· + ·) 0 a b

/-- Julia `LinearAlgebra.norm_sqr(a)`: `abs2(a₁) + abs2(a₂) + …` as a `Float`
(`0.0` for `n = 0`, where StaticVectors itself is broken, B9). -/
@[inline] def normSqr [JNorm α] (a : Values α n) : Float := a.mapReduce JNorm.abs2 (· + ·) 0

/-- Julia `norm(a)` (`SV/linalg.jl:96`): `sqrt(abs2(a₁) + abs2(a₂) + …)`, no
overflow scaling. -/
@[inline] def norm [JNorm α] (a : Values α n) : Float := Float.sqrt a.normSqr

/-- Julia `norm(a, p)` (`SV/linalg.jl:116`): `p = Inf` gives `maximum(norm.(a))`
with Julia's `max`, `p = 1` gives `∑ |aᵢ|`, `p = 2` gives `norm(a)`, `p = 0`
counts the nonzero entries (broken in StaticVectors, B9), and otherwise
`(∑ |aᵢ|^p)^(1/p)`. `|x|` is `norm(x::Number) = abs(float(x))`. The general
case uses the C `pow`, which may differ from Julia's `^` by an ulp. -/
def normP [JNorm α] (a : Values α n) (p : Float) : Float :=
  if p == Float.inf then a.mapReduce JNorm.norm F64.max 0
  else if p == 1 then a.mapReduce JNorm.norm (· + ·) 0
  else if p == 2 then a.norm
  else if p == 0 then a.mapReduce (fun x => if JNorm.norm x == 0 then 0 else 1) (· + ·) 0
  else if n == 0 then 0
  else Float.pow (a.mapReduce (fun x => Float.pow (JNorm.norm x) p) (· + ·) 0) (1 / p)

/-- Julia `normalize(a)` (`SV/linalg.jl:146`): `inv(norm(a)) * a`, multiplying
each entry by the reciprocal (so `normalize(Values(3.0,4.0)) = [0.6000000000000001, 0.8]`). -/
@[inline] def normalize [JNorm α] [HMul Float α α] (a : Values α n) : Values α n :=
  let s := 1 / a.norm
  a.map (s * ·)

/-- Julia `normalize(a, p)`: `inv(norm(a, p)) * a`. -/
@[inline] def normalizeP [JNorm α] [HMul Float α α] (a : Values α n) (p : Float) : Values α n :=
  let s := 1 / a.normP p
  a.map (s * ·)

/-- Julia `LinearAlgebra.cross(a, b)` on 3-vectors:
`[a₂b₃ - a₃b₂, a₃b₁ - a₁b₃, a₁b₂ - a₂b₁]`. -/
def cross [Mul α] [Sub α] (a b : Values α 3) : Values α 3 :=
  let a1 := a.get 0; let a2 := a.get 1; let a3 := a.get 2
  let b1 := b.get 0; let b2 := b.get 1; let b3 := b.get 2
  ofFn fun i => match i with
    | 0 => a2 * b3 - a3 * b2
    | 1 => a3 * b1 - a1 * b3
    | 2 => a1 * b2 - a2 * b1

/-- Julia `a * b'`: the outer product `aᵢ conj(bⱼ)`, as a vector of rows
(broken for `Values` in StaticVectors, B19). -/
def outer {m : Nat} [Mul α] [Conj α] (a : Values α n) (b : Values α m) : Values (Values α m) n :=
  ofFn fun i => b.map fun y => a.get i * conj y

end Values

/-- Nested vectors: `dot` recurses. -/
instance {α β : Type u} [Packed α] {n : Nat} [JDot α β] [Add β] [OfNat β 0] :
    JDot (Values α n) β := ⟨Values.dot⟩

/-- Nested vectors: `conj` maps. -/
instance {α : Type u} [Packed α] {n : Nat} [Conj α] : Conj (Values α n) := ⟨Values.map conj⟩

/-- Nested vectors: `norm_sqr` and `norm` recurse (Julia `norm_sqr(x::AbstractVector)`). -/
instance {α : Type u} [Packed α] {n : Nat} [JNorm α] : JNorm (Values α n) :=
  ⟨Values.normSqr, Values.norm⟩

/-- Julia `isapprox(x::AbstractArray, y::AbstractArray; atol, rtol, nans)`
(`LinearAlgebra/src/generic.jl:1995`): with `d = norm(x - y)`, if `d` is finite
then `iszero(rtol) ? d ≤ atol : d ≤ max(atol, rtol·max(norm x, norm y))`,
otherwise the elementwise `isapprox` of every pair. -/
instance {α : Type u} [Packed α] {n : Nat} [Sub α] [JNorm α] [JApprox α] : JApprox (Values α n) where
  rtolDefault := JApprox.rtolDefault α
  isapprox x y atol rtol nans :=
    let d := (x - y).norm
    if d.isFinite then
      if rtol == 0 then d ≤ atol
      else d ≤ F64.max atol (rtol * F64.max x.norm y.norm)
    else
      (Values.zipWith (fun a b => JApprox.isapprox a b atol rtol nans) x y : Values Bool n).all id

namespace Values

variable {α : Type u} [Packed α] {n : Nat}

/-- Julia `isapprox(x, y; atol=0, rtol=rtoldefault, nans=false)` on vectors
(`x ≈ y`). The default `rtol` is `√eps` for float entries and `0` for exact
ones, and `0` whenever `atol > 0`. -/
@[inline] def isapprox [Sub α] [JNorm α] [JApprox α] (x y : Values α n) (atol : Float := 0)
    (rtol : Float := if atol > 0 then 0 else JApprox.rtolDefault α) (nans : Bool := false) : Bool :=
  JApprox.isapprox x y atol rtol nans

end Values

end StaticVectors
