/-
Transcendental functions of dynamic elements with Julia's result kinds (Grassmann.jl
`src/composite.jl:24-560`, AbstractTensors `src/AbstractTensors.jl:317-480, 530-549`;
port-notes/grassmann-composite.md).

Julia decides the kind of `exp(t)`, `log(t)`, … by the arithmetic of its algorithm: the
closed form `cos θ + t·(sin θ/θ)` of a bivector term is `Number + Single`, a `Couple` in a
plain space and a `Spinor` in a conformal one; `exp` of a `Chain{2}` in `ℝ3` is a `Spinor`,
of a `Chain{1}` a `Multivector`; `log` of a term goes through `Couple(t)`. This module runs
Julia's algorithms *on the dynamic layer*, with its `+`, `⟑` and scalar actions, so every
result has Julia's kind and, in the closed forms, Julia's values bit for bit (the typed
functions of `Grassmann.Composite` compute the same values in fixed containers). Scalars
use Julia's own kernels (`JuliaBase.F64`), complex paths `JuliaBase.ComplexF64`.

| function | kinds (Julia's dispatch) |
|---|---|
| `exp` | `𝟎 ↦ One`; scalar terms `Single(exp x)`; a zero term `Couple(1, 0)`; terms and chains whose square is a scalar: `One + t` (null) or `cos θ + t·sin θ/θ`, `cosh θ + t·sinh θ/θ`; couples, spinors, multivectors: `eˢ·(…)` of the non-scalar part; otherwise `One + expm1(t)`; a `CoSpinor` as a `Multivector`, a `PseudoCouple` on the scalar blade as a couple on `I`, other pseudo-couples through `multispin` |
| `expm1` | Julia's series (`t + t²/2 + …`, stopping when the norms stop decreasing), the complex `expm1` for couples with `B² = -1`, the dense series of spinors and multivectors |
| `log`, `log1p` | terms through `Couple(t)`; couples `log(radius) + angle` or complex; Euclidean quaternions in polar form; everything else `qlog((t-1)/(t+1))` (`none` where the inverse is undefined: Julia throws) |
| `sqrt`, `cbrt` | a scalar element's root; couples and Euclidean quaternions `radius^(1/n)·exp(angle/n)` (complex for `B² = -1`); otherwise `exp(log(t)/n)` |
| `cosh`, `sinh` | scalar terms `Single`; couples with `B² = -1` complex; otherwise Julia's series |
| `cos`, `sin`, `tan`, `tanh` | AbstractTensors: `cos t = cosh(I⟑t)`, `sin t = sinh(I⟑t)/I`, `tan = sin/cos`, `tanh = sinh/cosh` (quirk B2 kept: hyperbolic for scalars when `I² = +1`) |
| `abs`, `unit`, `coabs`, `unitize`, `geomabs`, `unitnorm` | `sqrt(abs2(t))` (a `Single` for graded elements and couples: `abs(a) = 3.74v`), `t/abs(t)`, the complemented `abs`, … |
| `b ^ t` (`rpow`) | `exp(t⟑log(b))` (`2^v12` is a `Couple`) |

Julia defects fixed as in the typed layer (port-notes/grassmann-composite.md §8.3): the
parabolic `exp` (`eˢ(1 + t)` for `eˢ(1 + m)`), the zero-angle `sin 0/0`, `cbrt` of an
elliptic couple (the principal complex cube root), `exp(::Phasor)`. Kept: Julia's series and
their stopping rule, the approximate `isscalar` test, quirk B2.

Coefficients are `Float` (Julia `Float64`).
-/
import Grassmann.Dynamic.Division
import Grassmann.Composite.Scalar

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase

namespace TA

variable {V : TensorBundle} [Kernels V]

/-! ## Helpers -/

/-- `0.0`. -/
def c0 : Float := f64! 0.0
/-- `1.0`. -/
def c1 : Float := f64! 1.0
/-- `2.0`. -/
def c2 : Float := f64! 2.0
/-- `3.0`. -/
def c3 : Float := f64! 3.0
/-- `6.0`. -/
def c6 : Float := f64! 6.0
/-- `24.0`. -/
def c24 : Float := f64! 24.0
/-- `-0.5`. -/
def cmhalf : Float := f64! -0.5
/-- `1.0e-5` (Julia's PGA exponential cut-off). -/
def cPgaCut : Float := f64! 1.0e-5

/-- A natural number as a `Float` (through `UInt64`, docs/PERF.md). -/
@[inline] def natF (k : Nat) : Float := k.toUInt64.toFloat

/-- `value(scalar(t))`. -/
@[inline] def scalarValue (t : TA V Float) : Float := (scalar t).coeff 0

/-- `sin θ / θ` with the removable singularity filled in (Julia returns `NaN` at `θ = 0`). -/
@[inline] def sinOver (θ : Float) : Float := if θ == c0 then c1 else F64.sin θ / θ

/-- `sinh θ / θ`, filled in at `0`. -/
@[inline] def sinhOver (θ : Float) : Float := if θ == c0 then c1 else F64.sinh θ / θ

/-- Julia's closed form `cos θ + m·(sin θ/θ)` (`hint < 0`) or `cosh θ + m·(sinh θ/θ)`
(`hint > 0`); a unit blade `m` (`Submanifold`) takes `sin θ` itself
(`src/composite.jl:136-159`). -/
def closedForm (hint θ : Float) (m : TA V Float) (unitBlade : Bool) : TA V Float :=
  if hint < c0 then numAdd (F64.cos θ) (mulScalar m (if unitBlade then F64.sin θ else sinOver θ))
  else numAdd (F64.cosh θ) (mulScalar m (if unitBlade then F64.sinh θ else sinhOver θ))

/-- `sqrt(|value(scalar(abs2(t)))|)`, the angle of the closed forms. -/
@[inline] def angleOf (t : TA V Float) : Float := Float.sqrt (Float.abs (scalarValue (abs2 t)))

/-- Julia `isR301(V)`: the diagonal form `⟨1,1,1,0⟩` (projective geometric algebra with the
null generator last), which has its own bivector exponential (`src/composite.jl:143-148`). -/
def isR301 (V : TensorBundle) : Bool :=
  match V.metric with
  | .diagonal d => !V.isdual && d == #[1, 1, 1, 0]
  | _ => false

/-- Julia `iszero(metric(V))`: a Euclidean signature (no negative generator). -/
def euclideanSignature (V : TensorBundle) : Bool :=
  match V.metric with
  | .euclid => true
  | .signature s => s == 0 && !V.hasconformal && !V.istangent
  | _ => false

/-- Julia `isnull(t)` of a term: a zero value. -/
@[inline] def termNull : TA V Float → Bool
  | single _ x => x == c0
  | _ => false

/-- A couple as a complex number. -/
@[inline] def toC (re im : Float) : Complex Float := ⟨re, im⟩

/-- A complex number as a couple on blade `b`. -/
@[inline] def ofC (b : UInt64) (w : Complex Float) : TA V Float := couple b w.re w.im

/-- Whether a spinor or multivector is (numerically) its scalar part (Julia's generated
methods: `scalar(b) ≈ norm(b)`). -/
@[inline] def denseScalar (t : TA V Float) : Bool := F64.isapprox (scalarValue t) (norm t)

/-! ## Series (`src/composite.jl:31-83, 303-321, 458-539`) -/

/-- Julia's `expm1` series `t + t²/2 + t³/3! + …` (`src/composite.jl:31-51`): terms are
added while their norms decrease (or stay above `1`) and the partial sums move. `gen`
selects the generated `Spinor`/`Multivector` version (`src/composite.jl:53-83`), which
starts its last-norm slot at `0` instead of `norm(t)`. -/
def expm1Series (t : TA V Float) (gen : Bool := false) : TA V Float :=
  let f := norm t
  let term := divScalar (mul t t) c2
  go t term f (norm term) (if gen then c0 else f) 3 10000
where
  /-- The loop: `S` the partial sum, `n₁ n₂ n₃` Julia's `norms`, `k` the next index. -/
  go (S term : TA V Float) (n₁ n₂ n₃ : Float) (k : Nat) : Nat → TA V Float
    | 0 => S
    | fuel + 1 =>
      if !(n₂ < n₁ || n₂ > c1) then S
      else
        let S := S + term
        let ns := norm S
        if F64.isapprox ns n₃ then S
        else
          let term := mul term (divScalar t (natF k))
          go S term n₂ (norm term) ns (k + 1) fuel

/-- Julia's `cosh` series `1 + τ/2 + τ²/4! + …`, `τ = t⟑t` (`src/composite.jl:458-510`). -/
def coshSeries (t : TA V Float) : TA V Float :=
  let τ := mul t t
  let S := divScalar τ c2
  let term := divScalar (mul τ τ) c24
  let f := norm S
  add one (go τ S term f (norm term) f 6 10000)
where
  /-- The loop (`k` steps by two). -/
  go (τ S term : TA V Float) (n₁ n₂ n₃ : Float) (k : Nat) : Nat → TA V Float
    | 0 => S
    | fuel + 1 =>
      if !(n₂ < n₁ || n₂ > c1) then S
      else
        let S := S + term
        let ns := norm S
        if F64.isapprox ns n₃ then S
        else
          let term := mul term (divScalar τ (natF (k * (k - 1))))
          go τ S term n₂ (norm term) ns (k + 2) fuel

/-- Julia's `sinh` series `t + t⟑τ/3! + …` (`src/composite.jl:517-560`). -/
def sinhSeries (t : TA V Float) : TA V Float :=
  let τ := mul t t
  let f := norm t
  let term := divScalar (mul t τ) c6
  go τ t term f (norm term) f 5 10000
where
  /-- The loop (`k` steps by two). -/
  go (τ S term : TA V Float) (n₁ n₂ n₃ : Float) (k : Nat) : Nat → TA V Float
    | 0 => S
    | fuel + 1 =>
      if !(n₂ < n₁ || n₂ > c1) then S
      else
        let S := S + term
        let ns := norm S
        if F64.isapprox ns n₃ then S
        else
          let term := mul term (divScalar τ (natF (k * (k - 1))))
          go τ S term n₂ (norm term) ns (k + 2) fuel

/-- Julia `qlog(w) = 2(w + w³/3 + w⁵/5 + …) = 2 atanh w` (`src/composite.jl:303-321`); a
`PseudoCouple` goes through `multispin`, a `CoSpinor` through `Multivector`. -/
def qlog (w : TA V Float) : TA V Float :=
  let w := match w with
    | pseudo .. => multispin w
    | cospinor _ => toMultiTA w
    | _ => w
  let w2 := mul w w
  let f := norm w
  let prod := mul w w2
  let term := divScalar prod c3
  smul c2 (go w w2 w prod term f (norm term) f 5 10000)
where
  /-- The loop (`k` steps by two, at most `10000`). -/
  go (w w2 S prod term : TA V Float) (n₁ n₂ n₃ : Float) (k : Nat) : Nat → TA V Float
    | 0 => S
    | fuel + 1 =>
      if !(n₂ < n₁ || n₂ > c1) || k > 10000 then S
      else
        let S := S + term
        let ns := norm S
        if F64.isapprox ns n₃ then S
        else
          let prod := mul prod w2
          let term := divScalar prod (natF k)
          go w w2 S prod term n₂ (norm term) ns (k + 2) fuel

/-! ## The exponential -/

/-- Julia `expm1` of a spinor or multivector (the generated method,
`src/composite.jl:53-83`): the scalar's `expm1` when the element is scalar, else the
series. -/
def expm1Dense (t : TA V Float) : TA V Float :=
  if denseScalar t then single 0 (F64.expm1 (scalarValue t)) else expm1Series t true

/-- Julia `expm1(t)` of everything but pseudo-couples and phasors
(`src/composite.jl:26-83`). -/
def expm1Core (t : TA V Float) : TA V Float :=
  match t with
  | zero => zero
  | infinity => infinity
  | one => single 0 (F64.expm1 c1)
  | single 0 x => single 0 (F64.expm1 x)
  | chain 0 c => single 0 (F64.expm1 (getD c.v 0))
  | chain .. => match multispin t with
    | cospinor _ => expm1Dense (toMultiTA t)
    | s => expm1Dense s
  | couple b re im =>
    if bladeSq V b == -1 then ofC b (ComplexF64.expm1 (toC re im)) else expm1Series t
  | pseudo .. => match multispin t with
    | cospinor _ => expm1Dense (toMultiTA t)
    | pseudo .. => expm1Series t
    | s => expm1Dense s
  | spinor _ | multi _ => expm1Dense t
  | cospinor _ => expm1Dense (toMultiTA t)
  | _ => expm1Series t

/-- Julia `exp` of a term or chain (`src/composite.jl:136-160`). -/
def expGraded (t : TA V Float) : TA V Float :=
  let isTermT := isterm t
  let unit := match t with | one | blade _ => true | _ => false
  if isTermT && termNull t then
    couple ((bits? t).getD 0) c1 c0
  else if (match t with | chain 2 _ => true | _ => false) && isR301 V then
    -- Julia's `⟨1,1,1,0⟩` bivector exponential
    let u := Float.sqrt (Float.abs (getD (contraction t t).toDense.v 0))
    if u < cPgaCut then add one t
    else
      let v := mulScalar (wedge t t) (cmhalf / u)
      let cu := F64.cos u
      let su := F64.sin u
      add (numSub cu (mulScalar v su))
        (mul (mul (numAdd su (mulScalar v cu)) t) (numSub (c1 / u) (divScalar v (u * u))))
  else
    let i := if isTermT then ofBlade ((bits? t).getD 0) else t
    let sq := mul i i
    if isscalar sq then
      let hint := scalarValue sq
      if hint == c0 then add one t
      else if t.grade? == some 0 then single 0 (F64.exp (scalarValue t))
      else closedForm hint (angleOf t) t unit
    else add one (expm1Core t)

/-- Julia `exp` of a couple (`src/composite.jl:99-110`): `eʳᵉ` times the closed form of its
blade part; for a null blade the couple `eʳᵉ(1 + im·B)` (Julia: `eʳᵉ(1 + t)`, a `Couple` with
the wrong scalar, defect `exp-nilpotent-couple`: the kind is kept, the value fixed). -/
def expCouple (b : UInt64) (re im : Float) : TA V Float :=
  let mt : TA V Float := single b im
  let hint := F64.ofRat (bladeSq V b)
  let er := F64.exp re
  -- null blade: Julia's kind (`eʳᵉ·(One + t)`, a `Couple`), the value `eʳᵉ(1 + im·B)`
  if hint == c0 then couple b er (er * im)
  else smul er (closedForm hint (angleOf mt) mt false)

/-- Julia `exp` of a spinor or multivector (`src/composite.jl:85-97`): `eˢ` times the closed
form of the non-scalar part `m` when `m⟑m` is a scalar (`eˢ(1 + m)` when it is null;
Julia: `eˢ(1 + t)`, fixed), otherwise `One + expm1(t)`. -/
def expDense (t : TA V Float) : TA V Float :=
  let s := scalarValue t
  let mt := t - single 0 s
  let sq := mul mt mt
  if isscalar sq then
    let hint := scalarValue sq
    let es := F64.exp s
    if hint == c0 then smul es (add one mt)
    else smul es (closedForm hint (angleOf mt) mt false)
  else add one (expm1Dense t)

/-- Julia `exp(t)` of everything but phasors. -/
def expCore (t : TA V Float) : TA V Float :=
  match t with
  | zero => one
  | infinity => infinity
  | couple b re im => expCouple b re im
  | pseudo b re im =>
    if b == 0 then
      match expCouple (V := V) (pseudoBits V) re im with
      | couple _ r i => pseudo b r i
      | out => out
    else match multispin t with
      | cospinor _ => expDense (toMultiTA t)
      | s => expDense s
  | spinor _ | multi _ => expDense t
  | cospinor _ => expDense (toMultiTA t)
  | phasor .. => t
  | _ => expGraded t

/-- Julia `complexify(z::Phasor) = amplitude(z)·exp(angle(z))` (`src/multivectors.jl:1031`);
other elements are themselves. -/
def complexify (t : TA V Float) : TA V Float :=
  match t with
  | phasor amp θ => smul amp (expCore θ)
  | _ => t

/-- Julia `exp(t)` (module docstring). A phasor `z` with `complexify(z) = X + Y·B` gives
`eˣ ∠ Y·B` (Julia's `Phasor(exp(amp + re(exp θ)), im(exp θ))` is not the exponential:
port-notes/grassmann-composite.md §8.3 item 11, fixed). -/
def exp (t : TA V Float) : TA V Float :=
  match t with
  | phasor .. =>
    match complexify t with
    | couple b re im => phasor (F64.exp re) (single b im)
    | c => expCore c
  | _ => expCore t

/-- Julia `expm1(t)` (`src/composite.jl:26-130`). -/
def expm1 (t : TA V Float) : TA V Float :=
  match t with
  | pseudo b .. => if b == 0 then add (expCore t) (neg one) else expm1Core t
  | phasor .. => add (complexify (exp t)) (neg one)
  | _ => expm1Core t

/-! ## Logarithms -/

/-- Julia `radius(z) = √(re² - im²·B²)` of a couple (`src/multivectors.jl:912`). -/
@[inline] def coupleRadius (b : UInt64) (re im : Float) : Float :=
  Float.sqrt (re * re - im * im * F64.ofRat (bladeSq V b))

/-- Julia `angle(z)` coefficient of a couple (`src/composite.jl:619-627`): `atan(im, re)`
for `B² = -1`, Grassmann's `atanh(im, re)` for `B² = +1`, `NaN` otherwise (Julia throws). -/
def coupleAngle (b : UInt64) (re im : Float) : Float :=
  let β := bladeSq V b
  if β == -1 then F64.atan2 im re
  else if β == 1 then Composite.atanh2 im re
  else F64.nan

/-- Julia `log` of a couple (`src/composite.jl:365`): the complex `log` when `B² = -1`,
otherwise `log(radius) + angle`. -/
def logCouple (b : UInt64) (re im : Float) : TA V Float :=
  if bladeSq V b == -1 then ofC b (ComplexF64.log (toC re im))
  else numAdd (F64.log (coupleRadius (V := V) b re im)) (single b (coupleAngle (V := V) b re im))

/-- Julia `Couple(t)` of a term (`src/multivectors.jl:699-704`): a scalar `x` becomes
`x + 0·I` on the pseudoscalar, any other term `0 + x·B`. -/
def coupleOfTerm (b : UInt64) (x : Float) : UInt64 × Float × Float :=
  if b == 0 then (pseudoBits V, x, c0) else (b, c0, x)

/-- Julia `radius(q)` and `angle(q, r)` of a quaternion (`src/composite.jl:629-633`):
`r = value(scalar(abs(q)))`, `angle = (acos(s/r)/|b|)·b` with `b = bivector(q)`. -/
def quatPolar (q : TA V Float) : Float × TA V Float :=
  let r := Float.sqrt (scalarValue (abs2 q))
  let b := bivector q
  let nb := Float.sqrt (scalarValue (abs2 b))
  (r, mulScalar b (F64.acos (scalarValue q / r) / nb))

/-- Whether an element is a Julia `Quaternion` (a `Spinor` with four entries). -/
def isQuaternion : TA V Float → Bool
  | spinor _ => halfDim V.n false == 4
  | _ => false

/-- Julia `log(t)` (`src/composite.jl:360-400`); `none` where Julia throws
(`inv(m) is undefined` in `qlog((t-1)/(t+1))`). -/
def log? (t : TA V Float) : Option (TA V Float) :=
  match t with
  | one => some zero
  | infinity => some infinity
  | zero => some (single 0 (F64.log c0))
  | blade b => let (B, r, i) := coupleOfTerm (V := V) b c1; some (logCouple B r i)
  | single b x => let (B, r, i) := coupleOfTerm (V := V) b x; some (logCouple B r i)
  | chain 0 c => some (single 0 (F64.log (getD c.v 0)))
  | couple b re im => some (logCouple b re im)
  | pseudo b re im =>
    if b == 0 then
      match logCouple (V := V) (pseudoBits V) re im with
      | couple _ r i => some (pseudo b r i)
      | out => some out
    else generic (multispin t)
  | phasor amp θ => some (numAdd (F64.log amp) θ)
  | spinor _ =>
    if isQuaternion t && euclideanSignature V then
      let (r, a) := quatPolar t
      some (numAdd (F64.log r) a)
    else generic t
  | cospinor _ => generic (toMultiTA t)
  | _ => generic t
where
  /-- `qlog((t - One)/(t + One))`. -/
  generic (t : TA V Float) : Option (TA V Float) :=
    (div? (add t (neg one)) (add t one)).map qlog

/-- Julia `log(t)`; panics where Julia throws. -/
def log (t : TA V Float) : TA V Float :=
  match log? t with
  | some x => x
  | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"

/-- Julia `log1p(t)` (`src/composite.jl:366-371`): complex `log1p` for couples with
`B² = -1`, `log(1 + t)` for other couples, Euclidean quaternions and phasors, otherwise
`qlog(t/(t+2))`. -/
def log1p? (t : TA V Float) : Option (TA V Float) :=
  match t with
  | couple b re im => coupleLog1p b re im
  | phasor .. => log? (add one (complexify t))
  | pseudo b re im =>
    if b == 0 then
      match coupleLog1p (pseudoBits V) re im with
      | some (couple _ r i) => some (pseudo b r i)
      | out => out
    else qlogOf (multispin t)
  | spinor _ =>
    if isQuaternion t && euclideanSignature V then log? (add one t) else qlogOf t
  | _ => qlogOf t
where
  /-- `qlog(t/(t + 2))`. -/
  qlogOf (t : TA V Float) : Option (TA V Float) :=
    (div? t (add t (single 0 c2))).map qlog
  /-- A couple's `log1p`: the complex one for `B² = -1`, else `log(1 + z)`. -/
  coupleLog1p (b : UInt64) (re im : Float) : Option (TA V Float) :=
    if bladeSq V b == -1 then some (ofC b (ComplexF64.log1p (toC re im)))
    else log? (add one (couple b re im))

/-! ## Roots -/

/-- Julia `sqrt`/`cbrt` (`src/composite.jl:436-451`): `n = 2` or `3`. -/
def root? (n : Nat) (t : TA V Float) : Option (TA V Float) :=
  let nf := natF n
  let r1 := fun (x : Float) => if n == 2 then Float.sqrt x else F64.cbrt x
  match t with
  | zero => some zero
  | infinity => some infinity
  | one => some one
  | single 0 x => some (single 0 (r1 x))
  | chain 0 c => some (single 0 (r1 (getD c.v 0)))
  | couple b re im =>
    if bladeSq V b == -1 then
      some (ofC b (if n == 2 then ComplexF64.sqrt (toC re im) else complexCbrt (toC re im)))
    else
      -- `radius^(1/n)·exp(angle/n)`
      some (smul (r1 (coupleRadius (V := V) b re im))
        (expCore (single b (coupleAngle (V := V) b re im / nf))))
  | phasor amp θ => some (phasor (r1 amp) (divScalar θ nf))
  | _ =>
    if isQuaternion t && euclideanSignature V then
      let (r, a) := quatPolar t
      some (smul (r1 r) (expCore (divScalar a nf)))
    else if isscalar t then some (single 0 (r1 (scalarValue t)))
    else (log? t).map fun l => expCore (divScalar l nf)

/-- Julia `sqrt(t)`; panics where Julia throws. -/
def sqrt (t : TA V Float) : TA V Float :=
  match root? 2 t with
  | some x => x
  | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"

/-- Julia `cbrt(t)`; panics where Julia throws. -/
def cbrt (t : TA V Float) : TA V Float :=
  match root? 3 t with
  | some x => x
  | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"

/-! ## Hyperbolic and trigonometric functions -/

/-- Julia `cosh(t)` (`src/composite.jl:456-510`). -/
def cosh (t : TA V Float) : TA V Float :=
  match t with
  | zero => one
  | infinity => infinity
  | one => single 0 (F64.cosh c1)
  | single 0 x => single 0 (F64.cosh x)
  | chain 0 c => single 0 (F64.cosh (getD c.v 0))
  | couple b re im =>
    if bladeSq V b == -1 then ofC b (ComplexF64.cosh (toC re im)) else coshSeries t
  | pseudo .. => dense (multispin t)
  | spinor _ | multi _ => dense t
  | cospinor _ => dense (toMultiTA t)
  | _ => coshSeries t
where
  /-- The generated spinor/multivector method (the scalar's `cosh` when scalar). -/
  dense (t : TA V Float) : TA V Float :=
    match t with
    | spinor _ | multi _ =>
      if denseScalar t then single 0 (F64.cosh (scalarValue t)) else coshSeries t
    | cospinor _ => coshSeries (toMultiTA t)
    | _ => coshSeries t

/-- Julia `sinh(t)` (`src/composite.jl:515-560`). -/
def sinh (t : TA V Float) : TA V Float :=
  match t with
  | zero => zero
  | infinity => infinity
  | one => single 0 (F64.sinh c1)
  | single 0 x => single 0 (F64.sinh x)
  | chain 0 c => single 0 (F64.sinh (getD c.v 0))
  | couple b re im =>
    if bladeSq V b == -1 then ofC b (ComplexF64.sinh (toC re im)) else sinhSeries t
  | pseudo .. => dense (multispin t)
  | spinor _ | multi _ => dense t
  | cospinor _ => dense (toMultiTA t)
  | _ => sinhSeries t
where
  /-- The generated spinor/multivector method (the scalar's `sinh` when scalar). -/
  dense (t : TA V Float) : TA V Float :=
    match t with
    | spinor _ | multi _ =>
      if denseScalar t then single 0 (F64.sinh (scalarValue t)) else sinhSeries t
    | cospinor _ => sinhSeries (toMultiTA t)
    | _ => sinhSeries t

/-- The pseudoscalar `I = V(I)` as an element. -/
@[inline] def pseudoI (V : TensorBundle) : TA V Float := ofBlade (pseudoBits V)

/-- AbstractTensors `cos(t) = cosh(I ⟑ t)` (`src/AbstractTensors.jl:407`). -/
def cos (t : TA V Float) : TA V Float := cosh (mul (pseudoI V) t)

/-- AbstractTensors `sin(t) = sinh(I ⟑ t) / I` (`src/AbstractTensors.jl:408`). -/
def sin (t : TA V Float) : TA V Float := div (sinh (mul (pseudoI V) t)) (pseudoI V)

/-- AbstractTensors `tan(t) = sin(t) / cos(t)`; `none` where the division is undefined. -/
def tan? (t : TA V Float) : Option (TA V Float) := div? (sin t) (cos t)

/-- AbstractTensors `tanh(t) = sinh(t) / cosh(t)`; `none` where the division is undefined. -/
def tanh? (t : TA V Float) : Option (TA V Float) := div? (sinh t) (cosh t)

/-- Julia `tan(t)`; panics where Julia throws. -/
def tan (t : TA V Float) : TA V Float := div (sin t) (cos t)

/-- Julia `tanh(t)`; panics where Julia throws. -/
def tanh (t : TA V Float) : TA V Float := div (sinh t) (cosh t)

/-! ## Norms and normalizations (AbstractTensors `src/AbstractTensors.jl:435-480`) -/

/-- Julia `abs(t) = sqrt(abs2(t))`: a `Single` for graded elements and couples
(`abs(1v₁ + 2v₂ + 3v₃) = 3.7416573867739413v`, `abs(1 + v₁₂) = 1.4142135623730951v`). -/
def abs? (t : TA V Float) : Option (TA V Float) := root? 2 (abs2 t)

/-- Julia `abs(t)`; panics where Julia throws. -/
def abs (t : TA V Float) : TA V Float := sqrt (abs2 t)

/-- Julia `unit(t) = t / abs(t)` (AbstractTensors `src/AbstractTensors.jl:460`). -/
def unit (t : TA V Float) : TA V Float := div t (abs t)

/-- Julia `coabs(t) = antiabs(t) = complementleft(abs(complementright(t)))`
(AbstractTensors `src/AbstractTensors.jl:530-549`). -/
def coabs (t : TA V Float) : TA V Float := complementleft (abs (complementright t))

/-- Julia `coabs2(t) = complementleft(abs2(complementright(t)))`. -/
def coabs2 (t : TA V Float) : TA V Float := complementleft (abs2 (complementright t))

/-- Julia `unitize(t) = t / value(coabs(t))` (`counit`, AbstractTensors
`src/AbstractTensors.jl:468`): division by the coefficient of the complemented `abs`. -/
def unitize (t : TA V Float) : TA V Float :=
  let c := coabs t
  divScalar t (match c.term? with
    | some (_, x) => x
    | none => (c.toDense.v.toArray.find? (· != c0)).getD c0)

/-- Julia `antiabs(t)` / `pseudoabs(t)` (= `coabs`, AbstractTensors `src/AbstractTensors.jl:549`). -/
@[inline] def antiabs (t : TA V Float) : TA V Float := coabs t

/-- Julia `antiabs2(t)` / `pseudoabs2(t)` (= `coabs2`). -/
@[inline] def antiabs2 (t : TA V Float) : TA V Float := coabs2 t

/-- Julia `geomabs(t) = abs(t) + coabs(t)` (AbstractTensors `src/AbstractTensors.jl:452`). -/
def geomabs (t : TA V Float) : TA V Float := add (abs t) (coabs t)

/-- Julia `unitnorm(t) = t / norm(geomabs(t))` (AbstractTensors `src/AbstractTensors.jl:477`). -/
def unitnorm (t : TA V Float) : TA V Float := divScalar t (norm (geomabs t))

/-! ## Powers with real exponents and bases -/

/-- Julia `b ^ t = exp(t ⟑ log(b))` for a real base (AbstractTensors
`src/AbstractTensors.jl:326`; `2^v₁₂` is a `Couple`). -/
def rpow (b : Float) (t : TA V Float) : TA V Float := exp (mulScalar t (F64.log b))

/-- Julia `exp2(t) = exp(log(2)⋅t)` and `exp10(t)` (AbstractTensors
`src/AbstractTensors.jl:383-386`). -/
def exp2 (t : TA V Float) : TA V Float := exp (smul (F64.log c2) t)

/-- Julia `log2(t) = log2(ℯ)·log(t)`; `none` where `log` is undefined. -/
def log2? (t : TA V Float) : Option (TA V Float) :=
  (log? t).map (smul (F64.log2 (F64.exp c1)))

end TA

end Grassmann
