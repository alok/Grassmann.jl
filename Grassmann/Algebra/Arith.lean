/-
Module arithmetic: `+`, `-`, negation, scalar `*`/`/` on both sides
(port-notes/grassmann-types.md §4.5, grassmann-algebra.md §4.4-4.5,
grassmann-products.md §4.10-4.11; DESIGN.md §4.2 `+ -` row).

Result types are static (DESIGN.md §4.2): the sum of two elements lives in the
smallest container that is always correct given the *types* of the operands.

| operands | result |
|---|---|
| `Chain V G`, `Half V p`, `Multivector V` with itself | the same type |
| two grade-`G` terms/chains (`Chain`, `Single`, `Submanifold`) | `Chain V G` |
| scalar `α` and `Multivector` / `Spinor` / `Chain V 0` | that type |
| anything else (different grades, halves of different parity, `Couple`s, ...) | `Multivector V` |

Julia narrows further by *value-dependent* rules (`1 + v₁₂` is a `Couple`,
`Chain{0} + Chain{2}` a `Spinor`): those depend on runtime blades or on grade
parities the instance cannot inspect, and are the job of the dynamic layer
(DESIGN.md §4.3). The coefficients agree with Julia's in every case, including
its defective `PseudoCouple ± PseudoCouple` (defect `pseudocouple-addsub`, fixed:
componentwise) and `Chain{0} - term` (defect `chain-minus-term-swap`, fixed).

Scalars act on the left and on the right (`s * x = map (s * ·)`,
`x * s = map (· * s)`, `x / s = map (· / s)`, Julia `src/products.jl:830-851`),
so non-commutative coefficients keep their order. A scalar times a unit blade is a
`Single` (`2 * v₁ = 2v₁`).
-/
import Grassmann.Types.Convert

namespace Grassmann

open DirectSum StaticVectors AbstractTensors

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α]

/-! ## Same-type module operations -/

instance : Add (Chain V G α) := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Sub (Chain V G α) := ⟨fun a b => ⟨a.v - b.v⟩⟩
instance : Neg (Chain V G α) := ⟨fun a => ⟨-a.v⟩⟩
instance : Zero (Chain V G α) := ⟨Chain.zero⟩

instance : Add (Half V p α) := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Sub (Half V p α) := ⟨fun a b => ⟨a.v - b.v⟩⟩
instance : Neg (Half V p α) := ⟨fun a => ⟨-a.v⟩⟩
instance : Zero (Half V p α) := ⟨Half.zero⟩

instance : Add (Multivector V α) := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Sub (Multivector V α) := ⟨fun a b => ⟨a.v - b.v⟩⟩
instance : Neg (Multivector V α) := ⟨fun a => ⟨-a.v⟩⟩
instance : Zero (Multivector V α) := ⟨Multivector.zero⟩

instance : One (Multivector V α) := ⟨Multivector.one⟩
instance : One (Half V false α) := ⟨Spinor.one⟩

instance : Neg (Single V G α) := ⟨fun s => ⟨s.bits, -s.val⟩⟩
instance : Neg (Couple V α) := ⟨fun z => ⟨z.bits, -z.re, -z.im⟩⟩
instance : Neg (PseudoCouple V α) := ⟨fun z => ⟨z.bits, -z.re, -z.im⟩⟩

/-! ## Sums of mixed types -/

/-- Two grade-`G` terms or chains add to a `Chain V G` (Julia `adder`, rule 6,
and `term ± Chain{G}`; `src/algebra.jl:747-855`). Below the default priority so
that `Chain + Chain` uses the `Add` instance directly. -/
instance (priority := 900) {X Y : Type} [AsChain X V G α] [AsChain Y V G α] :
    HAdd X Y (Chain V G α) := ⟨fun a b => AsChain.toChain a + AsChain.toChain b⟩

instance (priority := 900) {X Y : Type} [AsChain X V G α] [AsChain Y V G α] :
    HSub X Y (Chain V G α) := ⟨fun a b => AsChain.toChain a - AsChain.toChain b⟩

/-- Any other sum is a `Multivector` (DESIGN.md §4.2). -/
instance (priority := low) {X Y : Type} [DenseLayout X V α] [DenseLayout Y V α] :
    HAdd X Y (Multivector V α) := ⟨fun a b => toMultivector a + toMultivector b⟩

instance (priority := low) {X Y : Type} [DenseLayout X V α] [DenseLayout Y V α] :
    HSub X Y (Multivector V α) := ⟨fun a b => toMultivector a - toMultivector b⟩

/-! ## Scalars in sums (Julia `t ± n = t ± n·One(V)`, `src/products.jl:852-859`) -/

instance : HAdd α (Multivector V α) (Multivector V α) := ⟨fun s m => Multivector.scalar s + m⟩
instance : HAdd (Multivector V α) α (Multivector V α) := ⟨fun m s => m + Multivector.scalar s⟩
instance : HSub α (Multivector V α) (Multivector V α) := ⟨fun s m => Multivector.scalar s - m⟩
instance : HSub (Multivector V α) α (Multivector V α) := ⟨fun m s => m - Multivector.scalar s⟩

instance : HAdd α (Half V false α) (Half V false α) := ⟨fun s h => Spinor.scalar s + h⟩
instance : HAdd (Half V false α) α (Half V false α) := ⟨fun h s => h + Spinor.scalar s⟩
instance : HSub α (Half V false α) (Half V false α) := ⟨fun s h => Spinor.scalar s - h⟩
instance : HSub (Half V false α) α (Half V false α) := ⟨fun h s => h - Spinor.scalar s⟩

instance : HAdd α (Chain V 0 α) (Chain V 0 α) := ⟨fun s c => Chain.scalar s + c⟩
instance : HAdd (Chain V 0 α) α (Chain V 0 α) := ⟨fun c s => c + Chain.scalar s⟩
instance : HSub α (Chain V 0 α) (Chain V 0 α) := ⟨fun s c => Chain.scalar s - c⟩
instance : HSub (Chain V 0 α) α (Chain V 0 α) := ⟨fun c s => c - Chain.scalar s⟩

instance (priority := low) {X : Type} [DenseLayout X V α] : HAdd α X (Multivector V α) :=
  ⟨fun s x => Multivector.scalar s + toMultivector x⟩
instance (priority := low) {X : Type} [DenseLayout X V α] : HAdd X α (Multivector V α) :=
  ⟨fun x s => toMultivector x + Multivector.scalar s⟩
instance (priority := low) {X : Type} [DenseLayout X V α] : HSub α X (Multivector V α) :=
  ⟨fun s x => Multivector.scalar s - toMultivector x⟩
instance (priority := low) {X : Type} [DenseLayout X V α] : HSub X α (Multivector V α) :=
  ⟨fun x s => toMultivector x - Multivector.scalar s⟩

/-! ## Scalar multiplication and division -/

instance : HMul α (Chain V G α) (Chain V G α) := ⟨fun s c => ⟨c.v.map (s * ·)⟩⟩
instance : HMul (Chain V G α) α (Chain V G α) := ⟨fun c s => ⟨c.v.map (· * s)⟩⟩
instance : SMul α (Chain V G α) := ⟨fun s c => ⟨c.v.map (s * ·)⟩⟩
instance [Div α] : HDiv (Chain V G α) α (Chain V G α) := ⟨fun c s => ⟨c.v.map (· / s)⟩⟩

instance : HMul α (Half V p α) (Half V p α) := ⟨fun s h => ⟨h.v.map (s * ·)⟩⟩
instance : HMul (Half V p α) α (Half V p α) := ⟨fun h s => ⟨h.v.map (· * s)⟩⟩
instance : SMul α (Half V p α) := ⟨fun s h => ⟨h.v.map (s * ·)⟩⟩
instance [Div α] : HDiv (Half V p α) α (Half V p α) := ⟨fun h s => ⟨h.v.map (· / s)⟩⟩

instance : HMul α (Multivector V α) (Multivector V α) := ⟨fun s m => ⟨m.v.map (s * ·)⟩⟩
instance : HMul (Multivector V α) α (Multivector V α) := ⟨fun m s => ⟨m.v.map (· * s)⟩⟩
instance : SMul α (Multivector V α) := ⟨fun s m => ⟨m.v.map (s * ·)⟩⟩
instance [Div α] : HDiv (Multivector V α) α (Multivector V α) := ⟨fun m s => ⟨m.v.map (· / s)⟩⟩

instance : HMul α (Single V G α) (Single V G α) := ⟨fun s x => ⟨x.bits, s * x.val⟩⟩
instance : HMul (Single V G α) α (Single V G α) := ⟨fun x s => ⟨x.bits, x.val * s⟩⟩
instance : SMul α (Single V G α) := ⟨fun s x => ⟨x.bits, s * x.val⟩⟩
instance [Div α] : HDiv (Single V G α) α (Single V G α) := ⟨fun x s => ⟨x.bits, x.val / s⟩⟩

instance : HMul α (Couple V α) (Couple V α) := ⟨fun s z => ⟨z.bits, s * z.re, s * z.im⟩⟩
instance : HMul (Couple V α) α (Couple V α) := ⟨fun z s => ⟨z.bits, z.re * s, z.im * s⟩⟩
instance : SMul α (Couple V α) := ⟨fun s z => ⟨z.bits, s * z.re, s * z.im⟩⟩
instance [Div α] : HDiv (Couple V α) α (Couple V α) := ⟨fun z s => ⟨z.bits, z.re / s, z.im / s⟩⟩

instance : HMul α (PseudoCouple V α) (PseudoCouple V α) := ⟨fun s z => ⟨z.bits, s * z.re, s * z.im⟩⟩
instance : HMul (PseudoCouple V α) α (PseudoCouple V α) := ⟨fun z s => ⟨z.bits, z.re * s, z.im * s⟩⟩
instance : SMul α (PseudoCouple V α) := ⟨fun s z => ⟨z.bits, s * z.re, s * z.im⟩⟩
instance [Div α] : HDiv (PseudoCouple V α) α (PseudoCouple V α) :=
  ⟨fun z s => ⟨z.bits, z.re / s, z.im / s⟩⟩

/-- Julia `x * b` for a scalar and a unit blade: a `Single` (`DirectSum.jl src/DirectSum.jl:519-529`). -/
instance : HMul α (Submanifold V G) (Single V G α) := ⟨fun s b => ⟨b.bits, s⟩⟩
instance : HMul (Submanifold V G) α (Single V G α) := ⟨fun b s => ⟨b.bits, s⟩⟩
instance : HSMul α (Submanifold V G) (Single V G α) := ⟨fun s b => ⟨b.bits, s⟩⟩

end Grassmann
