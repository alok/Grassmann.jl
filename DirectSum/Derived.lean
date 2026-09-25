/-
Derived blade-level operators (port-notes/grassmann-parity.md §2.3): the Julia
operators that compose the basic products (`BladeAlgebra`) with involutions and
complements.

| Julia | definition | here |
|---|---|---|
| `a ⨼ b`, `a < b` | `contraction(b,a)` (`AbstractTensors.jl src/AbstractTensors.jl:259,262`) | `contractionLeft` |
| `a ⨽ b`, `a > b`, `a \| b`, `dot` | `contraction(a,b)` (`:264-265`) | `contraction` |
| `a << b` | `contraction(b,~a)` (`:260`) | `contractionRevLeft` |
| `a >> b` | `contraction(~a,b)` (`:261`) | `contractionRevRight` |
| `a ∗ b` | `(~a)⟑b` (`:257`) | `reverseMul` |
| `a ⊛ b` | `scalar(contraction(a,b))` (`:258`) | `scalarContraction` |
| `a ⟇ b`, `veedot` | `complementleft(!a * !b)` (Grassmann `src/algebra.jl:391`) | `veedot` |
| `antidot(a,b)` | `complementleft(contraction(!a,!b))` (`src/algebra.jl:396`) | `antidot` |

Julia evaluates these on `Submanifold`/`Single` values, so the result *kind*
follows its `Single` arithmetic: a coefficient multiplies a bare blade into a
`Single` (`-1 * v₁ = -1v₁`), coefficients of `Single`s multiply, and `𝟎`
absorbs. `mapBilinear`/`mapLinear` implement exactly that, and the oracle suite
(`Tests/DirectSum/Derived.lean`) checks kinds and strings as well as terms.
-/
import DirectSum.BladeAlgebra

namespace DirectSum

open Bits Leibniz

namespace BladeResult

/-- Julia `scalar(x)` of a blade-level result: the grade-0 part (`v` stays a
bare blade, `c·v` a `Single`), `𝟎` when there is none. -/
def scalarPart : BladeResult → BladeResult
  | zero => zero
  | blade b => if b == 0 then blade 0 else zero
  | single c b => if b == 0 then single c 0 else zero
  | sum t => match t.find? (·.1 == 0) with
    | some (_, c) => if c == 0 then zero else single c 0
    | none => zero
  | nested z r => match r.scalarPart with
    | zero => zero
    | r' => nested z r'

/-- Julia `iseven(t)` for a blade-level result (`src/parity.jl:465-478`): every
term has even grade (tangent bits counted, Julia's type-level grade); `𝟎` is
both even and odd. -/
def isEvenGrade : BladeResult → Bool
  | zero => true
  | r => r.terms.all fun (b, _) => popcount b % 2 == 0

/-- Julia `isodd(t)` for a blade-level result. -/
def isOddGrade : BladeResult → Bool
  | zero => true
  | r => r.terms.all fun (b, _) => popcount b % 2 == 1

end BladeResult

namespace TensorBundle

variable (V : TensorBundle)

/-- Bilinear extension of a blade-pair operation to blade-level results,
following Julia's `Single` arithmetic: `𝟎` absorbs, the coefficients of the two
factors multiply the blade result (`BladeResult.scale`, so a bare blade times a
coefficient becomes a `Single`), and a bare blade contributes no coefficient.
Multi-term inputs are expanded term by term and merged. -/
def mapBilinear (f : UInt64 → UInt64 → Except String BladeResult) :
    BladeResult → BladeResult → Except String BladeResult
  | .zero, _ | _, .zero => .ok .zero
  | .blade a, .blade b => f a b
  | .blade a, .single d b => return (← f a b).scale d
  | .single c a, .blade b => return (← f a b).scale c
  | .single c a, .single d b => return (← f a b).scale (c * d)
  | x, y => do
    let mut acc : Terms := #[]
    for (a, c) in x.terms do
      for (b, d) in y.terms do
        for (k, v) in (← f a b).terms do
          acc := acc.add k (c * d * v)
    return .ofTerms V.n acc

/-- Julia `a << b = contraction(b, ~a)` (`AbstractTensors.jl:260`). -/
def contractionRevLeft (a b : UInt64) : Except String BladeResult :=
  V.mapBilinear (fun x y => .ok (V.contraction x y)) (.blade b) (V.reverse a)

/-- Julia `a >> b = contraction(~a, b)` (`AbstractTensors.jl:261`). -/
def contractionRevRight (a b : UInt64) : Except String BladeResult :=
  V.mapBilinear (fun x y => .ok (V.contraction x y)) (V.reverse a) (.blade b)

/-- Julia `a ∗ b = (~a) ⟑ b` (`AbstractTensors.jl:257`). -/
def reverseMul (a b : UInt64) : Except String BladeResult :=
  V.mapBilinear (fun x y => .ok (V.mul x y)) (V.reverse a) (.blade b)

/-- Julia `a ⊛ b = scalar(contraction(a, b))` (`AbstractTensors.jl:258`). -/
def scalarContraction (a b : UInt64) : BladeResult := (V.contraction a b).scalarPart

/-- Julia `veedot(a,b) = a ⟇ b = complementleft(!a * !b)` (Grassmann
`src/algebra.jl:391`): the geometric antiproduct. Throws (like every
complement) in a dyadic space. -/
def veedot (a b : UInt64) : Except String BladeResult := do
  let p ← V.mapBilinear (fun x y => .ok (V.mul x y)) (← V.complementright a) (← V.complementright b)
  V.mapLinear V.complementleft p

/-- Julia `antidot(a,b) = complementleft(contraction(!a, !b))` (Grassmann
`src/algebra.jl:396`). -/
def antidot (a b : UInt64) : Except String BladeResult := do
  let p ← V.mapBilinear (fun x y => .ok (V.contraction x y))
    (← V.complementright a) (← V.complementright b)
  V.mapLinear V.complementleft p

/-- Grassmann `paritycomplementinverse(N,G)` (`src/parity.jl:37-39`):
`parityreverse(N-G) ⊻ parityreverse(G) ⊻ isodd(binomial(N,2))`, the sign of
undoing a complement (unused in Julia; kept for completeness of the parity
API). It equals the parity of `G(N-G)`, see `paritycomplementinverse_eq`. -/
@[inline] def _root_.DirectSum.paritycomplementinverse (n g : Nat) : Bool :=
  (parityreverse (n - g) != parityreverse g) != (binomial n 2 % 2 == 1)

/-- `paritycomplementinverse N G` is the parity of `G(N-G)` (since
`C(N,2) = C(G,2) + C(N-G,2) + G(N-G)`), checked for `N ≤ 24`. -/
theorem _root_.DirectSum.paritycomplementinverse_eq :
    ∀ n < 25, ∀ g ≤ n, paritycomplementinverse n g = ((g * (n - g)) % 2 == 1) := by
  decide +kernel

/-- Grassmann `parityregressivenum(V,A,B)` (`src/parity.jl:57-60`): the
regressive product as `(±1, C, t, Z)`. -/
def parityregressivenum (a b : UInt64) : Int × UInt64 × Bool × UInt64 :=
  let (neg, c, t, z) := V.parityregressive a b
  (if neg then -1 else 1, c, t, z)

end TensorBundle

end DirectSum
