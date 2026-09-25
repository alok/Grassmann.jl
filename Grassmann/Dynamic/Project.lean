/-
The canonical up/down maps of projective and conformal geometry on dynamic elements:
Julia `project` (`↑`) and `reject` (`↓`) (Grassmann.jl `src/Grassmann.jl:164-212`).

`↑ω` lifts an element of the Euclidean part into the model space and `↓` goes back, by the
space's null generators:

| space | `↑ω` | `↓ω` |
|---|---|---|
| no `∞`, no `∅` | `ω` | `ω` |
| `∞` and `∅` (conformal) | `(v∞·½)⟑((~ω)⋅ω) + v∅ + ω` | `((v∞∅ ∧ ω)⋅inv(~v∞∅)) / (-ω⋅v∞)` |
| `∞` or `∅` alone (the Riemann sphere, `b = v∞` or `v∅`) | `b⟑((ω²-1)·inv(ω²+1)) + (2·inv(ω²+1))⟑ω`, `ω² = (~ω)⋅ω` | `(~(ω ∧ b)⋅b) / (1 - b⋅ω)` |

with the explicit forms `project(ω, b)`, `project(ω, p, m)`, `reject(ω, b)`,
`reject(ω, ∞, ∅)`. Every step is the dynamic layer's arithmetic, so results have Julia's kinds
(`↑(v₁ + v₂ + v₃)` in `S"∞+++"` is a `Chain`, in `S"∞∅+++"` a `Multivector`). The maps divide
(`inv`): coefficients must have a division (`Float`, `Rat`; Julia turns `Int64` into
`Float64`), and `none` is returned where Julia's inverse is undefined.
-/
import Grassmann.Dynamic.Division

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace TA

variable {V : TensorBundle} {α : Type} [Coeff α] [Kernels V] [Div α] [JNorm α]

/-- The null generator `v∞` (the first generator of a space with `∞`). -/
@[inline] def vinf (_ : TensorBundle) : UInt64 := 1

/-- The null generator `v∅` (after `v∞` when both are present). -/
@[inline] def vorigin (V : TensorBundle) : UInt64 := if V.hasinf then 2 else 1

/-- Julia `project(ω, b)`: `(2·inv(ω²+1))⟑ω + ((ω²-1)⟑inv(ω²+1))⟑b`, `ω² = (~ω)⋅ω`. -/
def projectWith? (ω b : TA V α) : Option (TA V α) := do
  let ω2 := contraction (reverse ω) ω
  let iω2 ← inv? (addNum ω2 Coeff.one)
  return add (mul (smul (Coeff.ofInt 2) iω2) ω) (mul (mul (subNum ω2 Coeff.one) iω2) b)

/-- Julia `project(ω, p, m)`: `(2·inv(s+1))⟑ω + ((s-1)·inv(s+1))⟑p + ((s+1)·inv(s+1))⟑m`
with `s = scalar((~ω)⋅ω)`. -/
def projectWith₂? (ω p m : TA V α) : Option (TA V α) := do
  let ω2 := scalar (contraction (reverse ω) ω)
  let iω2 ← inv? (addNum ω2 Coeff.one)
  return add (add (mul (smul (Coeff.ofInt 2) iω2) ω) (mul (mul (subNum ω2 Coeff.one) iω2) p))
    (mul (mul (addNum ω2 Coeff.one) iω2) m)

/-- Julia `project(ω)` / `↑ω` (module docstring); `none` where an inverse is undefined. -/
def project? (ω : TA V α) : Option (TA V α) :=
  if !(V.hasinf || V.hasorigin) then some ω
  else if V.hasinf && V.hasorigin then
    let half : α := Coeff.one / Coeff.ofInt 2
    some (add (add (mul (single (vinf V) half) (contraction (reverse ω) ω)) (blade (vorigin V))) ω)
  else do
    let ω2 := contraction (reverse ω) ω
    let iω2 ← inv? (addNum ω2 Coeff.one)
    let b : TA V α := blade (if V.hasinf then vinf V else vorigin V)
    return add (mul b (mul (subNum ω2 Coeff.one) iω2)) (mul (smul (Coeff.ofInt 2) iω2) ω)

/-- Julia `reject(ω, b)`: `(~(b ∧ ω)⋅b) / (1 - ω⋅b)`. -/
def rejectWith? (ω b : TA V α) : Option (TA V α) :=
  div? (contraction (reverse (wedge b ω)) b) (numSub Coeff.one (contraction ω b))

/-- Julia `reject(ω, ∞, ∅)`: `((m ∧ ω)⋅~inv(m)) / (-ω⋅∞)` with `m = ∞ ∧ ∅`. -/
def rejectWith₂? (ω i o : TA V α) : Option (TA V α) := do
  let m := wedge i o
  let im ← inv? m
  div? (contraction (wedge m ω) (reverse im)) (contraction (neg ω) i)

/-- Julia `reject(ω)` / `↓ω` (module docstring); `none` where a division is undefined. -/
def reject? (ω : TA V α) : Option (TA V α) :=
  if !(V.hasinf || V.hasorigin) then some ω
  else if V.hasinf && V.hasorigin then do
    let vio : TA V α := blade (vinf V ||| vorigin V)
    let r ← inv? (smul Coeff.one (reverse vio))
    div? (contraction (wedge vio ω) r) (contraction (neg ω) (blade (vinf V)))
  else
    let b : TA V α := blade (if V.hasinf then vinf V else vorigin V)
    div? (contraction (reverse (wedge ω b)) b) (numSub Coeff.one (contraction b ω))

end TA

end Grassmann
