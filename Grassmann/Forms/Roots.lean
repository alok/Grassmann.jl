/-
Closed-form roots of monic polynomials of degree ≤ 4, as Julia computes them
(Grassmann.jl `src/composite.jl:1086-1226`; port-notes/grassmann-composite.md
§4.13). They give the eigenvalues of operators of dimension `n < 5` from the
characteristic polynomial (`forms.jl:1374-1427`).

The coefficient convention is Julia's: `monicroots(a₀, a₁, …, a_{n-1})` are the
roots of `zⁿ + a_{n-1} zⁿ⁻¹ + … + a₀`. Julia's result type depends on the
values (a `Values{n,Float64}` when its formula's branch is real, a
`Values{n,ComplexF64}` otherwise); here that is the `Spectrum` sum type.

Every operation is the one Julia performs, in Julia's order, with Julia's
`cbrt` and complex `sqrt`/division (`JuliaBase`), so the results agree bit for
bit wherever the C library's `acos`/`cos` agree with openlibm's (the Viète
branch of the cubic uses them). Julia's `DomainError`s (`monicrootsreal` of a
polynomial with complex roots) are `Except.error` here.

Degree ≥ 5 (Julia: LAPACK eigenvalues of the companion matrix) is
`Grassmann.Forms.Eigen`.
-/
import Grassmann.Forms.Operator
import JuliaBase.FloatLit

namespace Grassmann.Forms

open StaticVectors JuliaBase

/-- Julia's type-unstable root/eigenvalue vector: `real` when Julia returns a
`Values{n,Float64}`, `complex` when it returns `Values{n,ComplexF64}`. -/
inductive Spectrum (n : Nat) where
  /-- A real vector (Julia `Values{n,Float64}`). -/
  | real (v : Values Float n)
  /-- A complex vector (Julia `Values{n,ComplexF64}`). -/
  | complex (v : Values (Complex Float) n)

namespace Spectrum

variable {n : Nat}

/-- The entries as complex numbers. -/
def toComplex : Spectrum n → Values (Complex Float) n
  | .real v => v.map fun x => ⟨x, 0⟩
  | .complex v => v

/-- Whether Julia's result is real-typed. -/
def isReal : Spectrum n → Bool
  | .real _ => true
  | .complex _ => false

/-- The entries as a list of complex numbers. -/
def toList (s : Spectrum n) : List (Complex Float) := s.toComplex.toList

instance : Inhabited (Spectrum n) := ⟨.real (Values.replicate 0)⟩

end Spectrum

namespace Roots

/-- `√3 / 2` as Julia evaluates `sqrt(3)/2`. -/
def sqrt3half : Float := Float.sqrt 3 / 2

/-- `2π/3` as Julia evaluates it (`2π` rounds to `6.283185307179586`). -/
def twoPiThird : Float := f64! 6.283185307179586 / 3

/-- Julia `zero!(x) = x ≈ 0 ? zero(x) : x` (`composite.jl:1086`): turns `-0.0`
into `0.0` (with the default tolerances `x ≈ 0` holds only for `x == 0`). -/
@[inline] def zero! (x : Float) : Float := if x == 0 then 0 else x

/-- Julia `zero!(z::Complex)`, componentwise. -/
@[inline] def zeroC! (z : Complex Float) : Complex Float := ⟨zero! z.re, zero! z.im⟩

/-- Julia `subzero(a, b) = (ab = a/b; ab ≈ 1 ? zero(ab) : a - b)` (`composite.jl:1088`):
a cancellation guard. -/
@[inline] def subzero (a b : Float) : Float := if F64.isapprox (a / b) 1 then 0 else a - b

/-- Julia `real * complex`. -/
@[inline] def rmul (a : Float) (z : Complex Float) : Complex Float := ⟨a * z.re, a * z.im⟩

/-- Julia `real / complex = real * inv(complex)` (complex.jl:381). -/
@[inline] def rdiv (a : Float) (z : Complex Float) : Complex Float := rmul a (ComplexF64.inv z)

/-- Julia `complex / real`, componentwise. -/
@[inline] def cdivr (z : Complex Float) (a : Float) : Complex Float := ⟨z.re / a, z.im / a⟩

/-- Julia `real + complex`. -/
@[inline] def raddc (a : Float) (z : Complex Float) : Complex Float := ⟨a + z.re, z.im⟩

/-- Julia `quadratic(a₀, a₁, rt)` with a real root discriminant `rt`
(`composite.jl:1105-1111`), the cancellation-free quadratic formula. -/
def quadraticR (a0 a1 rt : Float) : Values Float 2 :=
  if a1 < 0 then Values.ofFn fun i => if i.1 = 0 then 2 * a0 / (-a1 + rt) else (-a1 + rt) / 2
  else Values.ofFn fun i => if i.1 = 0 then (-a1 - rt) / 2 else 2 * a0 / (-a1 - rt)

/-- Julia `quadratic(a₀, a₁, rt)` with a complex `rt`. -/
def quadraticC (a0 a1 : Float) (rt : Complex Float) : Values (Complex Float) 2 :=
  if a1 < 0 then
    let s := raddc (-a1) rt
    Values.ofFn fun i => if i.1 = 0 then rdiv (2 * a0) s else cdivr s 2
  else
    let s : Complex Float := ⟨-a1 - rt.re, -rt.im⟩
    Values.ofFn fun i => if i.1 = 0 then cdivr s 2 else rdiv (2 * a0) s

/-- Julia `monicroots(a₀, a₁)` of `z² + a₁z + a₀` (`composite.jl:1101-1104`). -/
def quadratic (a0 a1 : Float) : Spectrum 2 :=
  let sq := a1 * a1 - 4 * a0
  if sq < 0 then .complex (quadraticC a0 a1 (ComplexF64.sqrt ⟨sq, 0⟩))
  else .real (quadraticR a0 a1 (Float.sqrt sq))

/-- The cubic's `(q, r)` of `z³ + a₂z² + a₁z + a₀` and `a₂/3` (`composite.jl:1113-1114`). -/
@[inline] def cubicQR (a0 a1 a2 : Float) : Float × Float × Float :=
  let a22 := a2 * a2
  let a23 := a2 / 3
  (subzero (a1 / 3) (a22 / 9), a1 * a2 / 6 - a0 / 2 - a22 * a2 / 27, a23)

/-- Viète's angle `ϕ₁` and `2√(-q)` of the three-real-roots branch (`composite.jl:1129-1135`). -/
@[inline] def viete (q r : Float) : Float × Float :=
  let sq := Float.sqrt (-q)
  if q < 0 then
    let c := r / (if q > -1 then Float.sqrt (-(q * q * q)) else sq * sq * sq)
    (Float.acos (if F64.isapprox c.abs 1 then F64.sign c else c) / 3, 2 * sq)
  else (sq / 3, 2 * sq)

/-- The three Viète roots, ascending (`composite.jl:1136-1137`). -/
@[inline] def vieteRoots (q r a23 : Float) : Values Float 3 :=
  let (ϕ1, sq2) := viete q r
  let ϕ2 := ϕ1 - twoPiThird
  let ϕ3 := ϕ1 + twoPiThird
  Values.ofFn fun i => match i.1 with
    | 0 => sq2 * Float.cos ϕ3 - a23
    | 1 => sq2 * Float.cos ϕ2 - a23
    | _ => sq2 * Float.cos ϕ1 - a23

/-- Julia `monicroots(a₀, a₁, a₂)` of `z³ + a₂z² + a₁z + a₀` (`composite.jl:1112-1140`):
Cardano with one real root (sorted real-first by Julia's rule), Viète with three.
`forceComplex` is Julia's `Val(true)` (`monicrootscomplex`). -/
def cubic (a0 a1 a2 : Float) (forceComplex : Bool := false) : Spectrum 3 :=
  let (q, r, a23) := cubicQR a0 a1 a2
  let r2 := r * r
  let q3 := q * q * q
  if r2 + q3 > 0 then
    let A := F64.cbrt (r.abs + Float.sqrt (r2 + q3))
    let qA := q / A
    let t := if r < 0 then qA - A else A - qA
    let x := zero! (-(t / 2 + a23))
    let y := zero! (sqrt3half * (A + qA))
    let z := t - a23
    .complex <| Values.ofFn fun i =>
      if z < x then (match i.1 with | 0 => ⟨z, 0⟩ | 1 => ⟨x, -y⟩ | _ => ⟨x, y⟩)
      else (match i.1 with | 0 => ⟨x, -y⟩ | 1 => ⟨x, y⟩ | _ => ⟨z, 0⟩)
  else
    let out := vieteRoots q r a23
    if forceComplex then .complex (out.map fun x => ⟨x, 0⟩) else .real out

/-- Julia `cubicmax(a₀, a₁, a₂)` (`composite.jl:1142-1160`): the largest real root. -/
def cubicmax (a0 a1 a2 : Float) : Float :=
  let (q, r, a23) := cubicQR a0 a1 a2
  let r2 := r * r
  let q3 := q * q * q
  if r2 + q3 > 0 then
    let A := F64.cbrt (r.abs + Float.sqrt (r2 + q3))
    (if r < 0 then q / A - A else A - q / A) - a23
  else
    let sq := Float.sqrt (-q)
    let θ := if q < 0 then
        let c := r / (if q > -1 then Float.sqrt (-q3) else sq * sq * sq)
        Float.acos (if F64.isapprox c.abs 1 then F64.sign c else c)
      else sq
    2 * sq * Float.cos (θ / 3) - a23

/-- Julia `quartic(a₀, a₁, a₂, a₃)` (`composite.jl:1161-1170`): Ferrari's
factorisation `(z² + p₁z + q₁)(z² + p₂z + q₂)`, returned as `(q₁, q₂, -p₁/2, -p₂/2)`. -/
def quartic (a0 a1 a2 a3 : Float) : Float × Float × Float × Float :=
  let a04 := 4 * a0
  let u := cubicmax (a04 * a2 - a1 * a1 - a0 * a3 * a3) (a1 * a3 - a04) (-a2)
  let a32 := a3 / 2
  let u2 := u / 2
  let z1 := zero! (a32 * a32 + u - a2)
  let psq := if z1 ≤ 0 then 0 else Float.sqrt z1
  let qsq := if F64.isapprox (u2 * u2 / a0) 1 then 0 else Float.sqrt (u2 * u2 - a0)
  let p1 := a32 - psq
  let p2 := a32 + psq
  let qsqpm := if a1 - a3 * u / 2 > 0 then qsq else -qsq
  (u2 + qsqpm, u2 - qsqpm, p1 / -2, p2 / -2)

/-- Julia `monicroots(a₀, a₁, a₂, a₃)` of `z⁴ + a₃z³ + a₂z² + a₁z + a₀`
(`composite.jl:1171-1180`). -/
def quarticRoots (a0 a1 a2 a3 : Float) : Spectrum 4 :=
  let (q1, q2, p12, p22) := quartic a0 a1 a2 a3
  let sq1 := p12 * p12 - q1
  let sq2 := p22 * p22 - q2
  if sq1 < 0 || sq2 < 0 then
    -- Julia's `p ± rt` is a real (then promoted, imaginary part `+0.0`) when `rt` is real
    let pm := fun (p sq : Float) (neg : Bool) =>
      if sq < 0 then
        let rt := ComplexF64.sqrt ⟨sq, 0⟩
        if neg then (⟨p - rt.re, -rt.im⟩ : Complex Float) else ⟨p + rt.re, rt.im⟩
      else ⟨if neg then p - Float.sqrt sq else p + Float.sqrt sq, 0⟩
    .complex <| Values.ofFn fun i => match i.1 with
      | 0 => pm p22 sq2 true | 1 => pm p22 sq2 false
      | 2 => pm p12 sq1 true | _ => pm p12 sq1 false
  else
    let rt1 := Float.sqrt sq1
    let rt2 := Float.sqrt sq2
    .real <| Values.ofFn fun i => match i.1 with
      | 0 => p22 - rt2 | 1 => p22 + rt2 | 2 => p12 - rt1 | _ => p12 + rt1

/-- Julia `monicroots(a...)` for degree `n ≤ 4` (`composite.jl:1096-1180`):
`a = (a₀, …, a_{n-1})`; `none` for `n ≥ 5` (Julia: eigenvalues of the companion
matrix, `Grassmann.Forms.Eigen`). -/
def monicroots? {n : Nat} (a : Values Float n) : Option (Spectrum n) :=
  let c := fun (i : Nat) => getD (α := Float) a i
  match n with
  | 0 => some (.real (Values.replicate 0))
  | 1 => some (.real (Values.replicate (-c 0)))
  | 2 => some (quadratic (c 0) (c 1))
  | 3 => some (cubic (c 0) (c 1) (c 2))
  | 4 => some (quarticRoots (c 0) (c 1) (c 2) (c 3))
  | _ => none

/-- Julia `monicrootsreal(a...)` (`composite.jl:1182-1206`): real roots, or
Julia's `DomainError` when a square root of a negative number is taken. -/
def monicrootsreal? {n : Nat} (a : Values Float n) : Option (Except String (Values Float n)) :=
  let c := fun (i : Nat) => getD (α := Float) a i
  let dom := fun (x : Float) => s!"DomainError with {F64.showString x}"
  match n with
  | 0 => some (.ok (Values.replicate 0))
  | 1 => some (.ok (Values.replicate (-c 0)))
  | 2 =>
    let sq := c 1 * c 1 - 4 * c 0
    some (if sq < 0 then .error (dom sq) else .ok (quadraticR (c 0) (c 1) (Float.sqrt sq)))
  | 3 =>
    let (q, r, a23) := cubicQR (c 0) (c 1) (c 2)
    some (if -q < 0 then .error (dom (-q)) else
      -- Julia evaluates `sqrt(-q*q*q)` (not `sqrt(-(q^3))`) in `monicrootsreal`
      let sq := Float.sqrt (-q)
      let c' := if q < 0 then r / (if q > -1 then Float.sqrt (-q * q * q) else sq * sq * sq) else 0
      let c' := if F64.isapprox c'.abs 1 then F64.sign c' else c'
      if c'.abs > 1 then .error s!"DomainError with {F64.showString c'}" else
      let (ϕ1, sq2) := if q < 0 then (Float.acos c' / 3, 2 * sq) else (sq / 3, 2 * sq)
      let ϕ2 := ϕ1 - twoPiThird
      let ϕ3 := ϕ1 + twoPiThird
      .ok (Values.ofFn fun i => match i.1 with
        | 0 => sq2 * Float.cos ϕ3 - a23 | 1 => sq2 * Float.cos ϕ2 - a23 | _ => sq2 * Float.cos ϕ1 - a23))
  | 4 =>
    let (q1, q2, p12, p22) := quartic (c 0) (c 1) (c 2) (c 3)
    let s1 := zero! (p12 * p12 - q1)
    let s2 := zero! (p22 * p22 - q2)
    some (if s2 < 0 then .error (dom s2) else if s1 < 0 then .error (dom s1) else
      let rt1 := Float.sqrt s1
      let rt2 := Float.sqrt s2
      .ok (Values.ofFn fun i => match i.1 with
        | 0 => p22 - rt2 | 1 => p22 + rt2 | 2 => p12 - rt1 | _ => p12 + rt1))
  | _ => none

/-- Julia `monicrootscomplex(a...)` (`composite.jl:1208-1226`): complex roots. -/
def monicrootscomplex? {n : Nat} (a : Values Float n) : Option (Values (Complex Float) n) :=
  let c := fun (i : Nat) => getD (α := Float) a i
  match n with
  | 0 => some (Values.replicate ⟨0, 0⟩)
  | 1 => some (Values.replicate ⟨-c 0, 0⟩)
  | 2 => some (quadraticC (c 0) (c 1) (ComplexF64.sqrt ⟨c 1 * c 1 - 4 * c 0, 0⟩))
  | 3 => some (cubic (c 0) (c 1) (c 2) (forceComplex := true)).toComplex
  | 4 =>
    let (q1, q2, p12, p22) := quartic (c 0) (c 1) (c 2) (c 3)
    let rt1 := ComplexF64.sqrt ⟨subzero (p12 * p12) q1, 0⟩
    let rt2 := ComplexF64.sqrt ⟨subzero (p22 * p22) q2, 0⟩
    some (Values.ofFn fun i => match i.1 with
      | 0 => ⟨p22 - rt2.re, -rt2.im⟩ | 1 => ⟨p22 + rt2.re, rt2.im⟩
      | 2 => ⟨p12 - rt1.re, -rt1.im⟩ | _ => ⟨p12 + rt1.re, rt1.im⟩)
  | _ => none

end Roots

end Grassmann.Forms
