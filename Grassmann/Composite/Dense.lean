/-
Composite functions of dense elements: `Multivector` and `Spinor`
(Grassmann.jl `src/composite.jl:54-96`, `:299-399`, `:436-570`;
port-notes/grassmann-composite.md §4.1-4.5).

Both containers are closed under the geometric product, so every series runs
inside them (`Values Float n` storage, the space's `Kernels` for products):

* `exp t`: the closed form `e^s(cos θ + m·sin θ/θ)` (or `cosh`/`sinh`, or
  `e^s(1 + m)` when the square is null) whenever `m = t - s` squares to a scalar
  (Julia's approximate `isscalar`), otherwise `1 + expm1(t)`;
* `expm1`, `cosh`, `sinh`: Julia's *generated* series (`Composite.Series`);
* `log t = qlog((t-1)/(t+1))`, `log1p t = qlog(t/(t+2))` with right division
  `a ⟑ inv(b)`: Julia throws `inv(m) is undefined` when `(~m)⟑m` is neither a scalar
  nor a single grade; the results are then `NaN` vectors (`log?` returns `none`);
* `sqrt`, `cbrt`: `isscalar(t) ? qrt(scalar(t)) : exp(log(t)/n)`.

The quaternion closed forms of `log`/`sqrt`/`cbrt` (`Spinor` of `ℝ3`) need the
chain exponential and live in `Grassmann.Composite.Spinor`.

Julia defects fixed (port-notes §8.3): `exp` of an element whose non-scalar part
squares to zero returns `e^s(1 + t)` instead of `e^s(1 + m)` (item 1; so
`exp(Multivector(2.0))` is `3e²` in Julia, `e²` here); a zero angle's `0/0`
(item 2); the generated `cosh`/`sinh` throw `UndefVarError` (item 3); the
generated `expm1` of a negative pure scalar returns `0` (item 13).
-/
import Grassmann.Composite.Couple

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase Composite

variable {V : TensorBundle}

/-! ## Multivectors -/

namespace Multivector

/-- The multivector with every coefficient `NaN` (the value of an operation Julia rejects). -/
def nan : Multivector V Float := ⟨Values.replicate Composite.nan⟩

/-- Julia `k + t` for a real `k`: `k` added to the scalar coefficient only. -/
@[inline] def addScalar (k : Float) (m : Multivector V Float) : Multivector V Float :=
  ⟨m.v.modify ⟨0, Nat.two_pow_pos V.n⟩ (k + ·)⟩

/-- Julia `norm(t)`: the Euclidean norm of the coefficients. -/
@[inline] def fnorm (m : Multivector V Float) : Float := m.v.norm

/-- Julia `isscalar(m) = norm(m) ≈ norm(scalar(m))` (`src/multivectors.jl:1140`). -/
@[inline] def isScalar (m : Multivector V Float) : Bool := isScalarNorms m.fnorm m.scalarValue

/-- `m` with its scalar coefficient replaced by `0` (Julia `t - scalar(t)`). -/
@[inline] def dropScalar (m : Multivector V Float) : Multivector V Float :=
  ⟨m.v.set ⟨0, Nat.two_pow_pos V.n⟩ f0⟩

/-- `⟨(~a) ⟑ b⟩₀` (the scalar product through the space's projecting kernel). -/
@[inline] def revScalar (a b : Multivector V Float) : Float :=
  getD (Kernels.binProj .reverseMul .full .full (.chain 0) a.v b.v : Values Float _) 0

variable [Kernels V]

/-- Julia `inv(m)` as a total function: `NaN` coefficients where Julia throws
`inv(m) is undefined` (`src/algebra.jl:486-532`). -/
@[inline] def invD (m : Multivector V Float) : Multivector V Float := (Multivector.inv? m).getD nan

/-- Julia's generated `expm1(b::Multivector)` (`src/composite.jl:54-81`): the scalar
`expm1(s)` when `b` is (approximately) the scalar `s`, else the generated series. -/
def expm1 (b : Multivector V Float) : Multivector V Float :=
  let nb := b.fnorm
  let sb := b.scalarValue
  if approx sb.abs nb then Multivector.scalar (F64.expm1 sb)
  else expm1Generated (· + ·) (· * ·) (· / ·) fnorm b

/-- Julia `exp(t::Multivector)` (`src/composite.jl:83-96`, parabolic defect fixed):
the closed form when `m = t - scalar(t)` squares to a scalar, else `1 + expm1(t)`. -/
def exp (t : Multivector V Float) : Multivector V Float :=
  let s := t.scalarValue
  let m := t.dropScalar
  let sq := m * m
  if isScalarNorms sq.fnorm sq.scalarValue then
    let hint := sq.scalarValue
    let es := F64.exp s
    if hint == f0 then addScalar es (es * m)
    else
      let θ := Float.sqrt (Float.abs (revScalar m m))
      if hint < f0 then
        let x := sinOver θ
        ⟨(addScalar (Float.cos θ) (m * x)).v.map (es * ·)⟩
      else
        let x := sinhOver θ
        ⟨(addScalar (Float.cosh θ) (m * x)).v.map (es * ·)⟩
  else addScalar f1 (expm1 t)

/-- The generated `cosh` series of Grassmann (`src/composite.jl:483-513`, which throws
`UndefVarError` in Julia 0.8.46 and is completed here): `cosh(s)` for a scalar,
else `1 + τ/2 + τ²/4! + …` with `τ = b⟑b`. -/
def cosh (b : Multivector V Float) : Multivector V Float :=
  let sb := b.scalarValue
  if approx sb.abs b.fnorm then Multivector.scalar (Float.cosh sb)
  else addScalar f1 (coshGeneratedTail (· + ·) (· * ·) (· / ·) fnorm (b * b))

/-- The generated `sinh` series of Grassmann (`src/composite.jl:541-570`, completed as
`cosh`): `sinh(s)` for a scalar, else `b + b⟑τ/3! + …` with `τ = b⟑b`. -/
def sinh (b : Multivector V Float) : Multivector V Float :=
  let sb := b.scalarValue
  if approx sb.abs b.fnorm then Multivector.scalar (Float.sinh sb)
  else
    let τ := b * b
    sinhGeneratedWith (· + ·) (· / ·) fnorm (· * τ) b

/-- Grassmann's `qlog(w)` (`src/composite.jl:303-321`): `2 atanh w`. -/
@[inline] def qlog (w : Multivector V Float) : Multivector V Float :=
  qlogWith (· + ·) (· * ·) (· / ·) (· * ·) fnorm w

/-- Julia `log(t) = qlog((t - 1)/(t + 1))` (`src/composite.jl:369`), or `none` where Julia
throws (`inv(t + 1)` undefined). -/
def log? (t : Multivector V Float) : Option (Multivector V Float) :=
  (addScalar f1 t).inv?.map fun i => qlog (addScalar (-f1) t * i)

/-- Julia `log(t::Multivector)`; `NaN` coefficients where Julia throws. -/
@[inline] def log (t : Multivector V Float) : Multivector V Float := (log? t).getD nan

/-- Julia `log1p(t) = qlog(t/(t + 2))` (`src/composite.jl:370`), or `none`. -/
def log1p? (t : Multivector V Float) : Option (Multivector V Float) :=
  (addScalar f2 t).inv?.map fun i => qlog (t * i)

/-- Julia `log1p(t::Multivector)`; `NaN` coefficients where Julia throws. -/
@[inline] def log1p (t : Multivector V Float) : Multivector V Float := (log1p? t).getD nan

/-- Julia `sqrt(t) = isscalar(t) ? sqrt(scalar(t)) : exp(log(t)/2)` (`src/composite.jl:438`). -/
def sqrt (t : Multivector V Float) : Multivector V Float :=
  if t.isScalar then Multivector.scalar (Float.sqrt t.scalarValue) else exp (log t / f2)

/-- Julia `cbrt(t) = isscalar(t) ? cbrt(scalar(t)) : exp(log(t)/3)` (`src/composite.jl:438`). -/
def cbrt (t : Multivector V Float) : Multivector V Float :=
  if t.isScalar then Multivector.scalar (F64.cbrt t.scalarValue) else exp (log t / f3)

/-- Julia `t ^ k` for a multivector (`src/algebra.jl:440-470`): Julia's repeated and binary
multiplication, and `inv(t)^|k|` for `k < 0` (Julia returns `One` there). -/
def pow (t : Multivector V Float) (k : Int) : Multivector V Float :=
  if k ≥ 0 then powJulia (· * ·) one t k.toNat else powJulia (· * ·) one t.invD k.natAbs

end Multivector

/-! ## Spinors (the even subalgebra) -/

namespace Half

/-- The spinor with every coefficient `NaN`. -/
def nan : Half V false Float := ⟨Values.replicate Composite.nan⟩

/-- The scalar coefficient of a spinor (storage index `0`, `0` when `n = 0`... never empty). -/
@[inline] def scalarValue (s : Half V false Float) : Float := getD s.v 0

/-- Julia `k + t` for a real `k` on a spinor. -/
@[inline] def addScalar (k : Float) (s : Half V false Float) : Half V false Float :=
  ⟨(Values.ofFn fun i => if i.1 = 0 then k + s.v.get i else s.v.get i)⟩

/-- Julia `norm(t)`. -/
@[inline] def fnorm {p : Bool} (s : Half V p Float) : Float := s.v.norm

/-- Julia `isscalar(s)`. -/
@[inline] def isScalar (s : Half V false Float) : Bool := isScalarNorms s.fnorm s.scalarValue

/-- `s` with its scalar coefficient replaced by `0`. -/
@[inline] def dropScalar (s : Half V false Float) : Half V false Float :=
  ⟨Values.ofFn fun i => if i.1 = 0 then f0 else s.v.get i⟩

/-- The spinor `x·1`. -/
@[inline] def scalarF (x : Float) : Half V false Float := Spinor.scalar x

variable [Kernels V]

/-- The geometric product of two spinors (a spinor). -/
@[inline] def smul' (a b : Half V false Float) : Half V false Float :=
  ⟨Kernels.bin .mul (halfLayout false) (halfLayout false) (halfLayout false) a.v b.v⟩

/-- `⟨(~a) ⟑ b⟩₀` of two spinors. -/
@[inline] def revScalar (a b : Half V false Float) : Float :=
  getD (Kernels.binProj .reverseMul (halfLayout false) (halfLayout false) (.chain 0) a.v b.v :
    Values Float _) 0

/-- Julia `inv(s)` of a spinor as a total function (`NaN` where Julia throws). -/
@[inline] def invD (s : Half V false Float) : Half V false Float := (Half.inv? s).getD nan

/-- Division of every coefficient by a real number. -/
@[inline] def sdiv {p : Bool} (s : Half V p Float) (k : Float) : Half V p Float := ⟨s.v.map (· / k)⟩

/-- Julia's generated `expm1(b::Spinor)` (`src/composite.jl:54-81`). -/
def expm1 (b : Half V false Float) : Half V false Float :=
  let nb := b.fnorm
  let sb := b.scalarValue
  if approx sb.abs nb then scalarF (F64.expm1 sb)
  else expm1Generated (· + ·) smul' sdiv fnorm b

/-- Julia `exp(t::Spinor)` (`src/composite.jl:83-96`, parabolic defect fixed). -/
def exp (t : Half V false Float) : Half V false Float :=
  let s := t.scalarValue
  let m := t.dropScalar
  let sq := smul' m m
  if isScalarNorms sq.fnorm sq.scalarValue then
    let hint := sq.scalarValue
    let es := F64.exp s
    if hint == f0 then addScalar es ⟨m.v.map (es * ·)⟩
    else
      let θ := Float.sqrt (Float.abs (revScalar m m))
      let (c, x) := if hint < f0 then (Float.cos θ, sinOver θ) else (Float.cosh θ, sinhOver θ)
      ⟨(addScalar c ⟨m.v.map (· * x)⟩).v.map (es * ·)⟩
  else addScalar f1 (expm1 t)

/-- The generated `cosh` of a spinor (`src/composite.jl:483-513`, completed). -/
def cosh (b : Half V false Float) : Half V false Float :=
  let sb := b.scalarValue
  if approx sb.abs b.fnorm then scalarF (Float.cosh sb)
  else addScalar f1 (coshGeneratedTail (· + ·) smul' sdiv fnorm (smul' b b))

/-- The generated `sinh` of a spinor (`src/composite.jl:541-570`, completed). -/
def sinh (b : Half V false Float) : Half V false Float :=
  let sb := b.scalarValue
  if approx sb.abs b.fnorm then scalarF (Float.sinh sb)
  else
    let τ := smul' b b
    sinhGeneratedWith (· + ·) sdiv fnorm (smul' · τ) b

/-- Grassmann's `qlog(w)` on a spinor. -/
@[inline] def qlog (w : Half V false Float) : Half V false Float :=
  qlogWith (· + ·) smul' sdiv (fun k s => ⟨s.v.map (k * ·)⟩) fnorm w

/-- Julia's generic `log(t) = qlog((t - 1)/(t + 1))` on a spinor (`src/composite.jl:369`),
or `none` where Julia throws. -/
def logSeries? (t : Half V false Float) : Option (Half V false Float) :=
  (addScalar f1 t).inv?.map fun i => qlog (smul' (addScalar (-f1) t) i)

/-- Julia's generic `log1p(t) = qlog(t/(t + 2))` on a spinor, or `none`. -/
def log1pSeries? (t : Half V false Float) : Option (Half V false Float) :=
  (addScalar f2 t).inv?.map fun i => qlog (smul' t i)

/-- Julia `t ^ k` for a spinor (`src/algebra.jl:440-470`), `inv(t)^|k|` for `k < 0`. -/
def pow (t : Half V false Float) (k : Int) : Half V false Float :=
  if k ≥ 0 then powJulia smul' Spinor.one t k.toNat else powJulia smul' Spinor.one t.invD k.natAbs

end Half

end Grassmann
