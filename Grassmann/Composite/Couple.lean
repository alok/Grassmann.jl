/-
Composite functions of single blades and couples: `Single`, `Couple`, `Phasor`
(Grassmann.jl `src/composite.jl`, `src/multivectors.jl:656-1090`,
`src/algebra.jl:420-470`; port-notes/grassmann-composite.md §4.2-4.5, §4.17,
grassmann-types.md §4.8).

A scaled blade `c·B` and a couple `a + b·B` live in the two-dimensional
commutative algebra `ℝ[B]/(B² = β)` spanned by `1` and `B`, where `β = B ⟑ B`
is a scalar for every blade in every metric. `Composite.BPair` is that algebra;
Julia's generic power series (`expm1`, `cosh`, `sinh`, `qlog`) evaluated on a
`Single` or `Couple` never leave it, so they run on two unboxed floats.

Closed forms, by the sign of `β` (Julia decides it at compile time, the blade
being a type parameter; here the blade is data):

| op | `β = -1` (elliptic) | `β = +1` (hyperbolic) | `β = 0` (parabolic) |
|---|---|---|---|
| `exp` | `eᵃ(cos θ + B sin θ)` | `eᵃ(cosh θ + B sinh θ)` | `eᵃ(1 + bB)` |
| `log`, `log1p`, `sqrt`, `cbrt`, `cosh`, `sinh` | Julia's `ComplexF64` functions | `log(radius) + angle`, `radius^(1/n)·exp(angle/n)`, series | (`angle` undefined: `NaN`) |

with `θ = |b|·√|abs2(B)|`. Result types: a `Single` becomes a `Couple` under
`exp`, `log`, `sqrt` (Julia returns a `Couple`, or a `Single` when the scalar
part is structurally absent; the values agree), while `cosh`/`sinh` of a `Single`
stay single terms (`Single V 0`, `Single V G`), exactly as Julia's series do.

Julia defects fixed here (port-notes §8.3): the parabolic `exp` of a couple
returns `eᵃ(1 + t)` instead of `eᵃ(1 + bB)` (item 1); a zero angle gives
`sin 0/0 = NaN` (item 2); `cbrt` of an elliptic couple has no method (item 8,
here the principal complex cube root); `exp(::Phasor)` uses a wrong formula
(item 11); negative powers of terms return `One` or throw (defect
`term-power-period4`, here `inv(v)^|k|`); blade powers use a period-4 cycle that
is wrong for null and non-unit blades (same defect, here `B^k = β^⌊k/2⌋ B^(k mod 2)`).
-/
import Grassmann.Composite.Series

namespace Grassmann.Composite

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

/-- An element `re + im·B` of the algebra `ℝ[B]/(B² = β)` of one blade (the blade and
`β` are held by the caller). -/
structure BPair where
  /-- The scalar part. -/
  re : Float
  /-- The coefficient of the blade. -/
  im : Float
  deriving Inhabited, Repr

namespace BPair

/-- Sum. -/
@[inline] def add (a b : BPair) : BPair := ⟨a.re + b.re, a.im + b.im⟩

/-- Julia's `Couple ⟑ Couple` on one blade (`src/products.jl:573-575`):
`(a.re·b.re + (a.im·b.im)·β) + (a.re·b.im + a.im·b.re)B`. -/
@[inline] def mul (β : Float) (a b : BPair) : BPair :=
  ⟨a.re * b.re + (a.im * b.im) * β, a.re * b.im + a.im * b.re⟩

/-- Division of both parts by a real number (Julia `t/k`). -/
@[inline] def sdiv (a : BPair) (k : Float) : BPair := ⟨a.re / k, a.im / k⟩

/-- Multiplication of both parts by a real number (Julia `k*t`). -/
@[inline] def smul (k : Float) (a : BPair) : BPair := ⟨k * a.re, k * a.im⟩

/-- Julia `norm(t) = norm(value(t))`: `√(re² + im²)`. -/
@[inline] def norm (a : BPair) : Float := Float.sqrt (a.re * a.re + a.im * a.im)

/-- The unit `1 + 0B`. -/
def one : BPair := ⟨f1, f0⟩

/-- Grassmann's generic `expm1` series (`C:31-51`) in the algebra of one blade. -/
def expm1 (β : Float) (t : BPair) : BPair := expm1Generic add (mul β) sdiv norm t

/-- Grassmann's generic `cosh` series (`C:458-481`): `1 + τ/2 + τ²/4! + …`, `τ = t⟑t`. -/
def cosh (β : Float) (t : BPair) : BPair :=
  let τ := mul β t t
  let S := coshGenericTail add (mul β) sdiv norm τ
  ⟨f1 + S.re, S.im⟩

/-- Grassmann's generic `sinh` series (`C:517-539`): `t + t⟑τ/3! + …`, `τ = t⟑t`. -/
def sinh (β : Float) (t : BPair) : BPair :=
  let τ := mul β t t
  sinhGenericWith add sdiv norm (fun x => mul β x τ) (fun d x => mul β x (sdiv τ (natF d))) t

/-- Grassmann's `qlog(w) = 2 atanh w` series (`C:303-321`). -/
def qlog (β : Float) (w : BPair) : BPair := qlogWith add (mul β) sdiv smul norm w

/-- The inverse `(re - im·B)/(re² - im²·β)` (`nan` parts when not invertible). -/
@[inline] def inv (β : Float) (a : BPair) : BPair :=
  let d := a.re * a.re - (a.im * a.im) * β
  ⟨a.re / d, -a.im / d⟩

end BPair

end Grassmann.Composite

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle}

/-! ## Scaled blades as couples -/

/-- Julia `exp(c·B)` for a scaled blade given by its mask and coefficient
(`src/composite.jl:136-159`, `C:407`): `exp(c)` for the scalar blade; `1` for `c = 0`;
`1 + cB` for a null blade; otherwise `cos θ + B·c·sin θ/θ` (`B² < 0`) or
`cosh θ + B·c·sinh θ/θ` (`B² > 0`) with `θ = √|c²·abs2(B)|`. -/
def Couple.expBlade (V : TensorBundle) (b : UInt64) (c : Float) : Couple V Float :=
  if b == 0 then ⟨0, F64.exp c, f0⟩
  else if c == f0 then ⟨b, f1, f0⟩
  else
    let β := bladeSq V b
    if β == f0 then ⟨b, f1, c⟩
    else
      let θ := Float.sqrt (Float.abs (c * c * bladeAbs2 V b))
      if β < f0 then ⟨b, Float.cos θ, c * sinOver θ⟩
      else ⟨b, Float.cosh θ, c * sinhOver θ⟩

namespace Couple

/-- The couple as an element of its blade algebra. -/
@[inline] def pair (z : Couple V Float) : Composite.BPair := ⟨z.re, z.im⟩

/-- A blade-algebra element as a couple on blade `b`. -/
@[inline] def ofPair (b : UInt64) (p : Composite.BPair) : Couple V Float := ⟨b, p.re, p.im⟩

/-- Julia `Complex(z)` (`src/multivectors.jl:760`): `re + im·i`. -/
@[inline] def toComplex (z : Couple V Float) : Complex Float := ⟨z.re, z.im⟩

/-- Julia `Couple{V,B}(w::Complex)`: a complex number on blade `b`. -/
@[inline] def onBlade (b : UInt64) (w : Complex Float) : Couple V Float := ⟨b, w.re, w.im⟩

/-- `B ⟑ B` for the couple's blade. -/
@[inline] def blSq (z : Couple V Float) : Float := bladeSq V z.bits

/-- Julia `radius(z) = √(re² - im²·value(B ⟑ B))` (`src/multivectors.jl:912`); `NaN`
where Julia throws `DomainError` (outside the light cone of a hyperbolic couple). -/
def radius (z : Couple V Float) : Float :=
  Float.sqrt (z.re * z.re - z.im * z.im * bladeSq V z.bits)

/-- The coefficient of Julia's `angle(z)` (`src/composite.jl:619-627`): `atan(im, re)`
when `B² = -1`, Grassmann's `atanh(im, re)` when `B² = +1`, and `NaN` otherwise (Julia:
`error("Unsupported trigonometric angle")`). -/
def angleCoef (z : Couple V Float) : Float :=
  let β := bladeSq V z.bits
  if β == -f1 then Float.atan2 z.im z.re
  else if β == f1 then atanh2 z.im z.re
  else nan

/-- Julia `angle(z) = θ·B` as the couple `0 + θ·B` (`src/composite.jl:619-627`). -/
@[inline] def angle (z : Couple V Float) : Couple V Float := ⟨z.bits, f0, z.angleCoef⟩

/-- Julia `polarize(z) = Phasor(radius(z), angle(z))` (`src/multivectors.jl:1054-1066`). -/
@[inline] def polarize (z : Couple V Float) : Phasor V Float := ⟨z.radius, z.angle⟩

/-- Julia `complexify(z::Couple) = z` (`src/multivectors.jl:1046-1052`). -/
@[inline] def complexify (z : Couple V Float) : Couple V Float := z

/-- Julia `vectorize(z::Couple{V,B}) = Chain{_subspace(V,B),1}(re, im)`
(`src/multivectors.jl:1068-1077`): the two coordinates of the plane spanned by `1` and
`B` (the subspace itself is not a Lean space, so this returns the coordinates). -/
@[inline] def vectorize {α : Type} [Coeff α] (z : Couple V α) : Values α 2 :=
  Values.ofFn fun i => if i.1 = 0 then z.re else z.im

/-- Julia `exp(z::Couple{V,B})` (`src/composite.jl:99-110`): `eᵃ(cos θ + B sin θ·b/θ)`,
`eᵃ(cosh θ + B sinh θ·b/θ)` or `eᵃ(1 + bB)` by the sign of `B²`, `θ = |b|√|abs2(B)|`
(Julia's parabolic `eᵃ(1 + t)` and `θ = 0` NaN fixed). -/
def exp (z : Couple V Float) : Couple V Float :=
  let β := bladeSq V z.bits
  let er := F64.exp z.re
  if β == f0 then ⟨z.bits, er, er * z.im⟩
  else
    let θ := Float.sqrt (Float.abs (z.im * z.im * bladeAbs2 V z.bits))
    if β < f0 then ⟨z.bits, er * Float.cos θ, er * (z.im * sinOver θ)⟩
    else ⟨z.bits, er * Float.cosh θ, er * (z.im * sinhOver θ)⟩

/-- Julia `expm1(z::Couple)` (`src/composite.jl:31-51`): the complex `expm1` when
`B² = -1`, otherwise Grassmann's generic series. -/
def expm1 (z : Couple V Float) : Couple V Float :=
  let β := z.blSq
  if β == -f1 then onBlade z.bits (ComplexF64.expm1 z.toComplex)
  else ofPair z.bits (BPair.expm1 β z.pair)

/-- Julia `log(z::Couple)` (`src/composite.jl:365`): the complex `log` when `B² = -1`,
otherwise `log(radius(z)) + angle(z)` (`NaN` where Julia throws). -/
def log (z : Couple V Float) : Couple V Float :=
  if z.blSq == -f1 then onBlade z.bits (ComplexF64.log z.toComplex)
  else ⟨z.bits, F64.log z.radius, z.angleCoef⟩

/-- Julia `log1p(z::Couple)` (`src/composite.jl:366`): the complex `log1p` when
`B² = -1`, otherwise `log(1 + z)`. -/
def log1p (z : Couple V Float) : Couple V Float :=
  if z.blSq == -f1 then onBlade z.bits (ComplexF64.log1p z.toComplex)
  else log ⟨z.bits, f1 + z.re, z.im⟩

/-- Julia `sqrt(z::Couple)` (`src/composite.jl:442-445`): the complex `sqrt` when
`B² = -1`, otherwise `√radius(z) · exp(angle(z)/2)`. -/
def sqrt (z : Couple V Float) : Couple V Float :=
  if z.blSq == -f1 then onBlade z.bits (ComplexF64.sqrt z.toComplex)
  else
    let e := expBlade V z.bits (z.angleCoef / f2)
    let s := Float.sqrt z.radius
    ⟨z.bits, s * e.re, s * e.im⟩

/-- Julia `cbrt(z::Couple)` (`src/composite.jl:442-445`): the principal complex cube root
when `B² = -1` (Julia has no `cbrt(::ComplexF64)`, a `MethodError`), otherwise
`∛radius(z) · exp(angle(z)/3)`. -/
def cbrt (z : Couple V Float) : Couple V Float :=
  if z.blSq == -f1 then onBlade z.bits (complexCbrt z.toComplex)
  else
    let e := expBlade V z.bits (z.angleCoef / f3)
    let s := F64.cbrt z.radius
    ⟨z.bits, s * e.re, s * e.im⟩

/-- Julia `cosh(z::Couple)` (`src/composite.jl:458-481`): the complex `cosh` when
`B² = -1`, otherwise Grassmann's generic series. -/
def cosh (z : Couple V Float) : Couple V Float :=
  let β := z.blSq
  if β == -f1 then onBlade z.bits (ComplexF64.cosh z.toComplex)
  else ofPair z.bits (BPair.cosh β z.pair)

/-- Julia `sinh(z::Couple)` (`src/composite.jl:517-539`): the complex `sinh` when
`B² = -1`, otherwise Grassmann's generic series. -/
def sinh (z : Couple V Float) : Couple V Float :=
  let β := z.blSq
  if β == -f1 then onBlade z.bits (ComplexF64.sinh z.toComplex)
  else ofPair z.bits (BPair.sinh β z.pair)

/-- Julia `a / b` of two couples on the same blade (`src/algebra.jl:556-605`): the complex
division when `B² = -1` (Julia's robust `ComplexF64` algorithm), otherwise
`a ⟑ inv(b)` in the blade algebra with the correct inverse (Julia's hyperbolic formula is
defect `couple-inv-hyperbolic`). The blade of `a` is kept; `b` must share it. -/
def divSame (a b : Couple V Float) : Couple V Float :=
  let β := a.blSq
  if β == -f1 then onBlade a.bits (ComplexF64.div a.toComplex b.toComplex)
  else ofPair a.bits (BPair.mul β a.pair (BPair.inv β b.pair))

/-- `tanh z = sinh z / cosh z` (AbstractTensors `tanh`, AT:419). -/
def tanh (z : Couple V Float) : Couple V Float := divSame z.sinh z.cosh

/-- Julia `z ^ k` for a couple (`src/algebra.jl:440-470`): `z` for `k = 1`; the complex
power `Complex(z)^k` (`power_by_squaring`, of `inv(z)` for `k < 0`) when `B² = -1`;
otherwise Julia's repeated/binary multiplication in the blade algebra, and
`inv(z)^|k|` for `k < 0` (Julia returns `One` there). -/
def pow (z : Couple V Float) (k : Int) : Couple V Float :=
  if k == 1 then z
  else
    let β := z.blSq
    if β == -f1 then
      let w := z.toComplex
      onBlade z.bits (if k ≥ 0 then powBySquaring (· * ·) ⟨f1, f0⟩ w k.toNat
        else powBySquaring (· * ·) ⟨f1, f0⟩ (ComplexF64.inv w) k.natAbs)
    else if k ≥ 0 then ofPair z.bits (powJulia (BPair.mul β) BPair.one z.pair k.toNat)
    else ofPair z.bits (powJulia (BPair.mul β) BPair.one (BPair.inv β z.pair) k.natAbs)

/-- Julia `b ^ z = exp(z ⟑ log(b))` for a real base `b` (AbstractTensors `AT:326`). -/
def rpow (b : Float) (z : Couple V Float) : Couple V Float :=
  let l := F64.log b
  exp ⟨z.bits, z.re * l, z.im * l⟩

/-- A real power `z ^ x = exp(x·log z)` (the complex power `Complex(z)^x` when `B² = -1`).
Julia defines no `Couple ^ Real`; this is the principal branch, consistent with `sqrt`
(`x = 1/2`) and `cbrt` (`x = 1/3`) up to rounding. -/
def powf (z : Couple V Float) (x : Float) : Couple V Float :=
  if z.blSq == -f1 then onBlade z.bits (ComplexF64.pow z.toComplex ⟨x, f0⟩)
  else
    let l := z.log
    exp ⟨z.bits, x * l.re, x * l.im⟩

end Couple

/-! ## Single terms -/

namespace Single

variable {G : Nat}

/-- Julia `Couple(t)` of a term (`src/multivectors.jl:699-704`): a scalar `c` becomes
`c + 0·I` on the pseudoscalar, any other term `0 + c·B`. -/
def toCouple (s : Single V G Float) : Couple V Float :=
  if G == 0 then ⟨pseudoMask V, s.val, f0⟩ else ⟨s.bits, f0, s.val⟩

/-- The term as an element of its blade algebra (`0 + cB`, or `c` for a scalar). -/
@[inline] def pair (s : Single V G Float) : Composite.BPair :=
  if G == 0 then ⟨s.val, f0⟩ else ⟨f0, s.val⟩

/-- Julia `exp(t)` of a term (`src/composite.jl:136-159`, `C:407`): `Single(exp c)` for a
scalar, else the closed form of `Couple.expBlade` (for a `⟨1,1,1,0⟩` bivector this is also
the math of Julia's PGA branch, which returns `NaN` for a single blade: port-notes §4.2.5). -/
@[inline] def exp (s : Single V G Float) : Couple V Float :=
  Couple.expBlade V (if G == 0 then 0 else s.bits) s.val

/-- Julia `expm1(t)` of a term (`C:27-51`): `expm1(c)` for a scalar, else Grassmann's
generic series (the result is a couple on the term's blade). -/
def expm1 (s : Single V G Float) : Couple V Float :=
  if G == 0 then ⟨0, F64.expm1 s.val, f0⟩
  else Couple.ofPair s.bits (BPair.expm1 (bladeSq V s.bits) s.pair)

/-- Julia `log(t::TensorTerm) = log(Couple(t))` (`src/composite.jl:362`): a scalar goes
through the couple on the **pseudoscalar** (`log(2.0v) = 0.693 + 0.0v₁₂₃` in `ℝ3`, and a
negative scalar gets the angle `π` when `I² = -1`). -/
@[inline] def log (s : Single V G Float) : Couple V Float := s.toCouple.log

/-- Julia `log1p(t)` of a term: the generic `qlog(t/(t+2))` series (`C:370`; there is no
term method, so even `log1p(1.0v)` is the series value `0.6931471795482411`). -/
def log1p (s : Single V G Float) : Couple V Float :=
  let b : UInt64 := if G == 0 then 0 else s.bits
  let β := bladeSq V b
  let t := s.pair
  Couple.ofPair b (BPair.qlog β (BPair.mul β t (BPair.inv β ⟨t.re + f2, t.im⟩)))

/-- Julia `sqrt(t)` of a term (`src/composite.jl:436-451`): `Single(√c)` for a scalar,
`0` for a zero term (`isscalar`), else `exp(log(t)/2)`. -/
def sqrt (s : Single V G Float) : Couple V Float :=
  if G == 0 then ⟨0, Float.sqrt s.val, f0⟩
  else if s.val == f0 then ⟨0, f0, f0⟩
  else
    let l := s.log
    Couple.exp ⟨l.bits, l.re / f2, l.im / f2⟩

/-- Julia `cbrt(t)` of a term (`src/composite.jl:436-451`): `Single(∛c)` for a scalar, `0`
for a zero term, else `exp(log(t)/3)`. -/
def cbrt (s : Single V G Float) : Couple V Float :=
  if G == 0 then ⟨0, F64.cbrt s.val, f0⟩
  else if s.val == f0 then ⟨0, f0, f0⟩
  else
    let l := s.log
    Couple.exp ⟨l.bits, l.re / f3, l.im / f3⟩

/-- `cosh` of the scaled blade `c·e_b` as a scalar: `cosh(c)` (Julia's `TensorGraded{V,0}`
method) for the scalar blade, otherwise Grassmann's generic series, whose partial sums
never leave the scalars. -/
def coshBlade (V : TensorBundle) (b : UInt64) (c : Float) : Float :=
  if b == 0 then Float.cosh c
  else (BPair.cosh (bladeSq V b) ⟨f0, c⟩).re

/-- `sinh` of the scaled blade `c·e_b` as its coefficient on `e_b` (see `coshBlade`). -/
def sinhBlade (V : TensorBundle) (b : UInt64) (c : Float) : Float :=
  if b == 0 then Float.sinh c
  else (BPair.sinh (bladeSq V b) ⟨f0, c⟩).im

/-- Julia `cosh(t)` of a term (`C:456`, `C:458-481`): a scalar. -/
@[inline] def cosh (s : Single V G Float) : Single V 0 Float :=
  ⟨0, coshBlade V (if G == 0 then 0 else s.bits) s.val⟩

/-- Julia `sinh(t)` of a term (`C:515`, `C:517-539`): a term on the same blade. -/
@[inline] def sinh (s : Single V G Float) : Single V G Float :=
  ⟨s.bits, sinhBlade V (if G == 0 then 0 else s.bits) s.val⟩

/-- `tanh t = sinh t / cosh t` (AbstractTensors `AT:419`; right division by a scalar
term is multiplication by its inverse `1/x`). -/
@[inline] def tanh (s : Single V G Float) : Single V G Float :=
  let c := s.cosh.val
  ⟨s.bits, s.sinh.val * (f1 / c)⟩

/-- Julia `cos(t) = cosh(I ⟑ t)` of a term (AbstractTensors `AT:407`), a scalar. `I ⟑ t` is
again a term (the pseudoscalar contracts a blade to one blade in every metric); a scalar
`t` becomes a pseudoscalar term, so in spaces with `I² = +1` this is `cosh` (quirk B2,
replicated as DESIGN.md prescribes: oracle defect `scalar-trig-hyperbolic`). -/
def cos (s : Single V G Float) : Single V 0 Float :=
  let (σ, b') := bladeMul V (pseudoMask V) s.bits
  if σ == f0 then ⟨0, f1⟩ else ⟨0, coshBlade V b' (σ * s.val)⟩

/-- Julia `sin(t) = sinh(I ⟑ t) / I` of a term (AbstractTensors `AT:408`): a term on the
blade of `t` (right division by `I` is multiplication by `inv(I)`). -/
def sin (s : Single V G Float) : Single V G Float :=
  let i := pseudoMask V
  let (σ, b') := bladeMul V i s.bits
  if σ == f0 then ⟨s.bits, f0⟩
  else
    let y := sinhBlade V b' (σ * s.val)
    let (σ₂, b'') := bladeMul V b' i
    ⟨b'', y * invPseudoCoef V * σ₂⟩

/-- `tan t = sin t / cos t` (AbstractTensors `AT:409`). -/
@[inline] def tan (s : Single V G Float) : Single V G Float :=
  let c := s.cos.val
  let t := s.sin
  ⟨t.bits, t.val * (f1 / c)⟩

/-- `c·B` to the power `k` as a couple (Julia `^(v::TensorTerm, i)`,
`src/algebra.jl:424-438`): `cᵏ·B^k` with `B^k = β^⌊k/2⌋·B^(k mod 2)`, `β = B ⟑ B`, and
`cᵏ` Julia's `Float64^Int`. Julia's period-4 cycle agrees for `β = ±1`; for null blades,
non-unit metric entries and negative `k` it is wrong (defect `term-power-period4`); here
`k < 0` is `inv(t)^|k|`. -/
def pow (s : Single V G Float) (k : Int) : Couple V Float :=
  if k == 0 then ⟨0, f1, f0⟩
  else
    let b : UInt64 := if G == 0 then 0 else s.bits
    let (c, n) : Float × Nat :=
      if k > 0 then (s.val, k.toNat)
      else
        -- `inv(c·B) = (±1/(abs2(B)·c))·B` (`src/algebra.jl:536-546`)
        let r := if Leibniz.parityreverse (popcount b) then -f1 else f1
        (r / (bladeAbs2 V b * s.val), k.natAbs)
    let β := bladeSq V b
    let βm := if β == f1 then f1 else if β == -f1 then (if (n / 2) % 2 == 0 then f1 else -f1)
      else F64.powInt β (n / 2 : Nat)
    let v := βm * F64.powInt c n
    if b == 0 then ⟨0, v, f0⟩
    else if n % 2 == 0 then ⟨b, v, f0⟩ else ⟨b, f0, v⟩

/-- Julia `b ^ t = exp(t ⟑ log(b))` for a real base (AbstractTensors `AT:326`). -/
@[inline] def rpow (b : Float) (s : Single V G Float) : Couple V Float :=
  Couple.expBlade V (if G == 0 then 0 else s.bits) (s.val * F64.log b)

end Single

/-! ## Phasors -/

namespace Phasor

/-- Julia `complexify(z::Phasor) = amplitude(z) * exp(angle(z))` (`src/multivectors.jl:1031-1044`,
the "simple" case of a real amplitude). -/
def complexify (z : Phasor V Float) : Couple V Float :=
  let e := z.angle.exp
  ⟨e.bits, z.amp * e.re, z.amp * e.im⟩

/-- `exp(z)` of a phasor: with `complexify(z) = X + Y·B`, `exp(z) = eˣ ∠ Y·B`. Julia's
`exp(::Phasor)` (`src/composite.jl:131-134`) computes `Phasor(exp(amp + re(exp θ)), im(exp θ))`,
which is not the exponential (port-notes §8.3 item 11, fixed). -/
def exp (z : Phasor V Float) : Phasor V Float :=
  let c := z.complexify
  ⟨F64.exp c.re, ⟨c.bits, f0, c.im⟩⟩

/-- `expm1(z) = exp(z) - 1` as a couple (Julia `expm1(t::Phasor) = exp(t) - One(V)`,
`C:130`, with the fixed `exp`). -/
def expm1 (z : Phasor V Float) : Couple V Float :=
  let e := z.exp.complexify
  ⟨e.bits, e.re - f1, e.im⟩

/-- Julia `log(z::Phasor) = log(amplitude(z)) + angle(z)` (`src/composite.jl:363`). -/
def log (z : Phasor V Float) : Couple V Float :=
  ⟨z.angle.bits, F64.log z.amp + z.angle.re, z.angle.im⟩

/-- Julia `log1p(z::Phasor) = log(One(V) + z)` (`src/composite.jl:364`), where the sum
complexifies the phasor. -/
def log1p (z : Phasor V Float) : Couple V Float :=
  let c := z.complexify
  Couple.log ⟨c.bits, f1 + c.re, c.im⟩

/-- Julia `sqrt(z::Phasor) = Phasor(√amplitude, angle/2)` (`src/composite.jl:446`). -/
def sqrt (z : Phasor V Float) : Phasor V Float :=
  ⟨Float.sqrt z.amp, ⟨z.angle.bits, z.angle.re / f2, z.angle.im / f2⟩⟩

/-- Julia `cbrt(z::Phasor) = Phasor(∛amplitude, angle/3)` (`src/composite.jl:446`). -/
def cbrt (z : Phasor V Float) : Phasor V Float :=
  ⟨F64.cbrt z.amp, ⟨z.angle.bits, z.angle.re / f3, z.angle.im / f3⟩⟩

/-- Julia `inv(z::Phasor) = Phasor(inv(amplitude), -angle)` (`src/algebra.jl:547-549`). -/
def inv (z : Phasor V Float) : Phasor V Float :=
  ⟨f1 / z.amp, ⟨z.angle.bits, -z.angle.re, -z.angle.im⟩⟩

/-- Julia `z ^ n = Phasor(amplitude^n, n·angle)` (`src/algebra.jl:422-423`). -/
def pow (z : Phasor V Float) (n : Int) : Phasor V Float :=
  let k := Float.ofInt n
  ⟨F64.powInt z.amp n, ⟨z.angle.bits, k * z.angle.re, k * z.angle.im⟩⟩

/-- Julia `z ^ x = Phasor(amplitude^x, x·angle)` for a real exponent (`src/algebra.jl:422`). -/
def powf (z : Phasor V Float) (x : Float) : Phasor V Float :=
  ⟨F64.pow z.amp x, ⟨z.angle.bits, x * z.angle.re, x * z.angle.im⟩⟩

/-- Julia `radius(z::Phasor) = radius(amplitude(z)) = |amplitude|` (`src/multivectors.jl:912`). -/
@[inline] def radius (z : Phasor V Float) : Float := z.amp.abs

/-- Julia `(z::Phasor)(t) = Phasor(amplitude, angle·t)` (`src/multivectors.jl:1016`). -/
@[inline] def eval (z : Phasor V Float) (t : Float) : Phasor V Float :=
  ⟨z.amp, ⟨z.angle.bits, z.angle.re * t, z.angle.im * t⟩⟩

/-- Julia `∠(a, θ)`: the phasor `a ∠ θ·B` of a real amplitude and an angle on blade `b`. -/
@[inline] def angleOn (a : Float) (b : UInt64) (θ : Float) : Phasor V Float := ⟨a, ⟨b, f0, θ⟩⟩

end Phasor

end Grassmann
