import Grassmann

/-!
# Versors, the Riemann sphere and conformal up/down maps

What the Grassmann README figures need beyond the static layer (DESIGN.md §4.2), written
with its typed products (`Spinor * Spinor`, `R >>> x`, `x ⊘ R`, `∧`, `⋅`):

* `expEven`: Julia's `exp` of an even element (`Grassmann.jl src/composite.jl:83-96,
  136-160`): the closed form `cos θ + t·sin θ/θ` (or `cosh`/`sinh`) when `t²` is a scalar,
  otherwise `1 + expm1(t)` with Julia's Taylor loop and its termination rule
  (`src/composite.jl:55-80`), so the truncation error (≈1e-9 for the README versors) is
  the same as Julia's;
* `upRiemann`/`downRiemann`: `↑`/`↓` of a space with `∞` but no `∅` (the stereographic
  Riemann-sphere maps, `src/Grassmann.jl:164-212`);
* `upConformal`/`downConformal`: `↑`/`↓` of conformal space `⟨∞∅…⟩`;
* `points`: Julia `points(f, r) = vector.(f.(r))` (`src/Grassmann.jl:68`) as coordinate
  arrays of chosen generators (Julia's `V(2,3,4).(points(f))`).

The composite functions of Grassmann (`exp`, `log`, …) are not in the Lean library yet
(`Grassmann/Algebra/Norms.lean`); this module keeps the gallery's copy local until they are.
-/

namespace Gallery.Versor

open Grassmann DirectSum StaticVectors

variable {V : TensorBundle} [Kernels V]

/-- `√eps(Float64)`, Julia's default `rtol` of `isapprox` on `Float64`. -/
def rtol : Float := 1.4901161193847656e-8

/-- Julia `isapprox(a, b)` on floats (`rtol = √eps`, `atol = 0`). -/
@[inline] def approx (a b : Float) : Bool :=
  a == b || (a.isFinite && b.isFinite && (a - b).abs ≤ rtol * (if a.abs > b.abs then a.abs else b.abs))

/-- The scalar coefficient of a spinor. -/
@[inline] def spinorScalar (s : Spinor V Float) : Float := scalarValue s

/-- Julia `isscalar(t) = norm(t) ≈ norm(scalar(t))` (`src/multivectors.jl:1140`). -/
@[inline] def isScalar (s : Spinor V Float) : Bool := approx (norm s) (spinorScalar s).abs

/-- Julia's `expm1` Taylor loop for a spinor (`src/composite.jl:55-80`): with
`S = b`, `out = b²/2`, repeat `S += out` until `‖S‖ ≈` its previous value, the next term
being `out = (out/k)·b`. The loop runs while the term norm decreases or exceeds 1, at most up
to `k = 10000`, as in Julia. -/
def expm1Loop (b : Spinor V Float) : Nat → Spinor V Float → Spinor V Float → Float → Float → Float →
    Spinor V Float
  | 0, S, _, _, _, _ => S
  | fuel + 1, S, out, n1, n2, n3 =>
    let k := 10002 - (fuel + 1)
    if !((n2 < n1 || n2 > 1) && k ≤ 10000) then S else
    let S := S + out
    let ns := norm S
    if approx ns n3 then S else
    let out : Spinor V Float := ((out / k.toUInt64.toFloat : Spinor V Float) * b : Half V (false ^^ false) Float)
    expm1Loop b fuel S out n2 (norm out) ns

/-- Julia `expm1(b::Spinor)` (`src/composite.jl:55-80`). -/
def expm1 (b : Spinor V Float) : Spinor V Float :=
  let nb := norm b
  let sb := spinorScalar b
  if approx sb nb then Spinor.scalar (Float.exp sb - 1) else
  let out : Spinor V Float := ((b * b : Half V (false ^^ false) Float) / (2 : Float))
  -- `k` starts at 3; the fuel counts down so that `k = 10002 - fuel`
  expm1Loop b 9999 b out nb (norm out) 0

/-- Julia `exp(t)` of an even element (`src/composite.jl:83-96`; for a bivector chain or term
`src/composite.jl:136-160` reduces to the same computation since its scalar part is zero):
`e^{⟨t⟩₀}·(cos θ + m·sin θ/θ)` (`cosh`/`sinh` when `m² > 0`) if `m = t - ⟨t⟩₀` squares to a
scalar, with `θ = √|⟨~m m⟩₀|`, and `1 + expm1(t)` otherwise. -/
def expEven (t : Spinor V Float) : Spinor V Float :=
  let st := spinorScalar t
  let m := t - Spinor.scalar st
  let sq : Spinor V Float := (m * m : Half V (false ^^ false) Float)
  if isScalar sq then
    let hint := spinorScalar sq
    if hint == 0 then Float.exp st * (Spinor.one + t) else
    let θ := (spinorScalar (Half.abs2 m)).abs.sqrt
    let body : Spinor V Float :=
      if hint < 0 then Spinor.scalar (Float.cos θ) + m * (Float.sin θ / θ)
      else Spinor.scalar (Float.cosh θ) + m * (Float.sinh θ / θ)
    Float.exp st * body
  else Spinor.one + expm1 t

/-- A bivector as a spinor. -/
@[inline] def ofBivector (c : Chain V 2 Float) : Spinor V Float := (Half.ofChain c).cast rfl

/-- The unit vector `e_b` (blade bits `b`, one generator) as a chain. -/
@[inline] def basisVector (b : Submanifold V 1) : Chain V 1 Float := Chain.ofBlade b 1

/-! ## The Riemann sphere: `↑`, `↓` with one null-free point at infinity -/

/-- Julia `↑ω` in a space with `∞` (or `∅`) alone (`src/Grassmann.jl:172-177`):
`b·(ω²-1)/(ω²+1) + 2ω/(ω²+1)` with `ω² = (~ω)⋅ω` and `b` the point at infinity. -/
def upRiemann (b : Chain V 1 Float) (ω : Chain V 1 Float) : Chain V 1 Float :=
  let ω2 := getD (contraction (~ω) ω : Chain V (1 - 1) Float).v 0
  let iω2 := 1 / (ω2 + 1)
  b * ((ω2 - 1) * iω2) + (2 * iω2) * ω

/-- Julia `↓ω` in a space with `∞` (or `∅`) alone (`src/Grassmann.jl:201-204`):
`(~(ω∧b)⋅b)/(1 - b⋅ω)`. -/
def downRiemann (b : Chain V 1 Float) (ω : Chain V 1 Float) : Chain V 1 Float :=
  let wb : Chain V (1 + 1) Float := ω ∧ b
  let num : Chain V (1 + 1 - 1) Float := contraction (~wb) b
  let den := 1 - getD (contraction b ω : Chain V (1 - 1) Float).v 0
  (num.cast (by decide)) / den

/-! ## Conformal space `⟨∞∅…⟩` -/

/-- Julia `↑ω` in conformal space (`src/Grassmann.jl:169`): `(v∞/2)·((~ω)⋅ω) + v∅ + ω`. -/
def upConformal (inf orig : Chain V 1 Float) (ω : Chain V 1 Float) : Chain V 1 Float :=
  let ω2 := getD (contraction (~ω) ω : Chain V (1 - 1) Float).v 0
  (inf * (1 / 2 : Float)) * ω2 + orig + ω

/-- Julia `↓ω` in conformal space (`src/Grassmann.jl:197`):
`((v∞∅∧ω)⋅inv(~v∞∅)) / (-ω⋅v∞)` (for a vector `ω` the divisor is a scalar). -/
def downConformal (inf orig : Chain V 1 Float) (ω : Chain V 1 Float) : Chain V 1 Float :=
  let io : Chain V (1 + 1) Float := inf ∧ orig
  let ioInv : Chain V 2 Float := Chain.inv (~io)
  let t : Chain V (1 + 1 + 1) Float := io ∧ ω
  let num : Chain V (1 + 1 + 1 - 2) Float := contraction t ioInv
  let den := -getD (contraction ω inf : Chain V (1 - 1) Float).v 0
  (num.cast (by decide)) / den

/-! ## Sampling curves -/

/-- The coordinates `ω[i₁], ω[i₂], ω[i₃]` (0-based chain indices) of `f t` for every `t`
of `ts` (Julia `V(i₁+1, i₂+1, i₃+1).(points(f, ts))`), as three arrays. Tail-recursive. -/
@[specialize] def points3 (f : Float → Chain V 1 Float) (i₁ i₂ i₃ : Nat) (ts : FloatArray) :
    FloatArray × FloatArray × FloatArray :=
  go 0 (FloatArray.emptyWithCapacity ts.size) (FloatArray.emptyWithCapacity ts.size)
    (FloatArray.emptyWithCapacity ts.size)
where
  /-- the sampling loop -/
  go (i : Nat) (xs ys zs : FloatArray) : FloatArray × FloatArray × FloatArray :=
    if h : i < ts.size then
      let w := (f ts[i]).v
      go (i + 1) (xs.push (getD w i₁)) (ys.push (getD w i₂)) (zs.push (getD w i₃))
    else (xs, ys, zs)
  termination_by ts.size - i

end Gallery.Versor
