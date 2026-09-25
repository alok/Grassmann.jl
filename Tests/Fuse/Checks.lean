/-
Fused ≡ unfused (`Grassmann.Fuse`): for every standard space, `basis!` spaces with non-unit
metric coefficients, and both `Float` (bit for bit up to the sign of zero) and `Int` (exact)
coefficients, a battery of expressions evaluated through `fused%` and through the typed
operations agree on random operands. The expressions cover every primitive reflection knows
(kernels of every field, fused sandwiches, `+ - neg`, scalar multiples, conversions, grade
projections, `getD`, division) and results of every kind (chains, halves, multivectors,
coefficients).
-/
import Tests.Fuse.Common

open Grassmann DirectSum StaticVectors

namespace FuseTests

/-- `4` (a constant in scalar expressions). -/
def c4 : Float := 4

/-- `fuse_checks% "label" V α`: the fusion checks of space `V` at coefficient type `α` with chain and half operands, as a function `(seed : Nat) → Tally → Tally`. -/
syntax (name := fuse_checksStx) "fuse_checks% " str term:max term:max : term

macro_rules
  | `(fuse_checks% $label $V $α) => `(show Nat → Tally → Tally from fun seed t0 => Id.run do
      let s (k : Nat) := seed * 97 + k
      let nm (x : String) := $label ++ " " ++ x
      let mut t := t0
      t := (fcheck (nm "R*v*~R") (R : Spinor $V $α) (v : Chain $V 1 $α) => (R * v * ~R : CoSpinor $V $α)) (s 1) t
      t := (fcheck (nm "R*(u∧w)*~R") (R : Spinor $V $α) (u : Chain $V 1 $α) (w : Chain $V 1 $α) =>
        (R * (u ∧ w) * ~R : Spinor $V $α)) (s 2) t
      t := (fcheck (nm "v ⊘ R") (R : Spinor $V $α) (v : Chain $V 1 $α) => (v ⊘ R : Chain $V 1 $α)) (s 3) t
      t := (fcheck (nm "R >>> v") (R : Spinor $V $α) (v : Chain $V 1 $α) => (R >>> v : Chain $V 1 $α)) (s 4) t
      t := (fcheck (nm "v ⊘ u") (u : Chain $V 1 $α) (v : Chain $V 1 $α) => (v ⊘ u : Chain $V 1 $α)) (s 5) t
      t := (fcheck (nm "S >>> T") (S : Spinor $V $α) (T : Spinor $V $α) => (S >>> T : Spinor $V $α)) (s 6) t
      t := (fcheck (nm "(s*t)*~s") (x : Spinor $V $α) (y : Spinor $V $α) => (x * y * ~x : Spinor $V $α)) (s 8) t
      t := (fcheck (nm "u*w*u") (u : Chain $V 1 $α) (w : Chain $V 1 $α) => (u * w * u : CoSpinor $V $α)) (s 11) t
      t := (fcheck (nm "C*u*C") (c : Chain $V 2 $α) (u : Chain $V 1 $α) => (c * u * c : CoSpinor $V $α)) (s 12) t
      t := (fcheck (nm "(u∧w)⋅u") (u : Chain $V 1 $α) (w : Chain $V 1 $α) => ((u ∧ w) ⋅ u)) (s 13) t
      t := (fcheck (nm "u⨼c") (u : Chain $V 1 $α) (c : Chain $V 2 $α) => (u ⨼ c)) (s 14) t
      t := (fcheck (nm "⋆(u∧w)") (u : Chain $V 1 $α) (w : Chain $V 1 $α) => (⋆(u ∧ w) : Chain $V (($V).n - 2) $α)) (s 15) t
      t := (fcheck (nm "u×w") (u : Chain $V 1 $α) (w : Chain $V 1 $α) => (u × w : Chain $V (($V).n - (1 + 1)) $α)) (s 16) t
      t := (fcheck (nm "x*u+w*x") (x : $α) (u : Chain $V 1 $α) (w : Chain $V 1 $α) => (x * u + w * x)) (s 24) t
      t := (fcheck (nm "-(s-t)") (x : Spinor $V $α) (y : Spinor $V $α) => (-(x - y) : Spinor $V $α)) (s 25) t
      t := (fcheck (nm "(R*v*~R).grade 1") (R : Spinor $V $α) (v : Chain $V 1 $α) =>
        ((R * v * ~R : CoSpinor $V $α).grade 1)) (s 29) t
      t := (fcheck (nm "abs2 s") (x : Spinor $V $α) => x.abs2) (s 30) t
      t := (fcheck (nm "abs2 u") (u : Chain $V 1 $α) => u.abs2) (s 32) t
      t := (fcheck (nm "Chain(n-1)∨Chain(n-1)") (a : Chain $V (($V).n - 1) $α) (b : Chain $V (($V).n - 1) $α) =>
        (a ∨ b)) (s 33) t
      t := (fcheck (nm "scalar(u*w*u*w)") (u : Chain $V 1 $α) (w : Chain $V 1 $α) =>
        (scalarValue (u * w * u * w : Spinor $V $α))) (s 35) t
      t := (fcheck (nm "(u⋅w).get 0 + x") (u : Chain $V 1 $α) (w : Chain $V 1 $α) (x : $α) =>
        (getD (u ⋅ w).v 0 + x)) (s 36) t
      -- literal blades (`x·e₁` as a `Single`, folded to a one-hot chain at elaboration time)
      t := (fcheck (nm "x e₁ + u") (x : $α) (u : Chain $V 1 $α) =>
        ((x * (⟨1⟩ : Submanifold $V 1) : Single $V 1 $α) + u : Chain $V 1 $α)) (s 37) t
      t := (fcheck (nm "R (x e₂) ~R") (R : Spinor $V $α) (x : $α) =>
        (R * (x * (⟨2⟩ : Submanifold $V 1) : Single $V 1 $α) * ~R : CoSpinor $V $α)) (s 38) t
      return t)

/-- `fuse_checks_dense% "label" V α`: the checks with `Multivector` operands (their straight-line code grows as `4ⁿ`: the suite runs them in the smaller spaces). -/
syntax (name := fuse_checks_denseStx) "fuse_checks_dense% " str term:max term:max : term

macro_rules
  | `(fuse_checks_dense% $label $V $α) => `(show Nat → Tally → Tally from fun seed t0 => Id.run do
      let s (k : Nat) := seed * 97 + k
      let nm (x : String) := $label ++ " " ++ x
      let mut t := t0
      t := (fcheck (nm "a*b+c") (a : Multivector $V $α) (b : Multivector $V $α) (c : Multivector $V $α) =>
        a * b + c) (s 7) t
      t := (fcheck (nm "a-(b*c+~a)") (a : Multivector $V $α) (b : Multivector $V $α) (c : Multivector $V $α) =>
        a - (b * c + ~a)) (s 9) t
      t := (fcheck (nm "(a∨b)∧c") (a : Multivector $V $α) (b : Multivector $V $α) (c : Multivector $V $α) =>
        ((a ∨ b : Multivector $V $α) ∧ c : Multivector $V $α)) (s 10) t
      t := (fcheck (nm "a⊛b") (a : Multivector $V $α) (b : Multivector $V $α) => (a ⊛ b : Chain $V 0 $α)) (s 17) t
      t := (fcheck (nm "a∗b") (a : Multivector $V $α) (b : Multivector $V $α) => (a ∗ b : Multivector $V $α)) (s 18) t
      t := (fcheck (nm "!a⋅b") (a : Multivector $V $α) (b : Multivector $V $α) =>
        (contraction (complementRight a : Multivector $V $α) b : Multivector $V $α)) (s 19) t
      t := (fcheck (nm "⋆a*~b") (a : Multivector $V $α) (b : Multivector $V $α) =>
        ((⋆a : Multivector $V $α) * ~b)) (s 20) t
      t := (fcheck (nm "u+c") (u : Chain $V 1 $α) (c : Chain $V 2 $α) => (u + c : Multivector $V $α)) (s 21) t
      t := (fcheck (nm "u+a") (u : Chain $V 1 $α) (a : Multivector $V $α) => (u + a : Multivector $V $α)) (s 22) t
      t := (fcheck (nm "2*a-b") (a : Multivector $V $α) (b : Multivector $V $α) => ((2 : $α) * a - b)) (s 23) t
      t := (fcheck (nm "grade2(a*b)") (a : Multivector $V $α) (b : Multivector $V $α) => (gradePart (a * b) 2)) (s 26) t
      t := (fcheck (nm "even(a)*odd(b)") (a : Multivector $V $α) (b : Multivector $V $α) =>
        ((even a : Spinor $V $α) * (odd b : CoSpinor $V $α))) (s 27) t
      t := (fcheck (nm "involute(clifford(a))") (a : Multivector $V $α) => (involute (clifford a))) (s 28) t
      t := (fcheck (nm "abs2 a") (a : Multivector $V $α) => a.abs2) (s 31) t
      t := (fcheck (nm "scalar(a*b)") (a : Multivector $V $α) (b : Multivector $V $α) => (scalarValue (a * b))) (s 34) t
      return t)

/-- `fuse_checks_float% "label" V Float`: the checks that need `Float` coefficients (division, inverses, float scalars). -/
syntax (name := fuse_checks_floatStx) "fuse_checks_float% " str term:max term:max : term

macro_rules
  | `(fuse_checks_float% $label $V $_α) => `(show Nat → Tally → Tally from fun seed t0 => Id.run do
      let s (k : Nat) := seed * 97 + k
      let nm (x : String) := $label ++ " " ++ x
      let mut t := t0
      t := (fcheck (nm "u⁻¹") (u : Chain $V 1 Float) => u⁻¹) (s 40) t
      t := (fcheck (nm "u/w") (u : Chain $V 1 Float) (w : Chain $V 1 Float) => (u / w : Spinor $V Float)) (s 41) t
      t := (fcheck (nm "a/2.5") (a : Multivector $V Float) => (a / (2.5 : Float))) (s 42) t
      t := (fcheck (nm "4*a-b") (a : Multivector $V Float) (b : Multivector $V Float) => (c4 * a - b)) (s 43) t
      t := (fcheck (nm "sqrt-scaled") (a : Multivector $V Float) (b : Multivector $V Float) =>
        (Float.sqrt (scalarValue (a * a)).abs * b)) (s 44) t
      return t)

end FuseTests
