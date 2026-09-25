/-
AbstractLattices: the shared meet/join vocabulary of the chakravala stack.

Julia source: `AbstractLattices.jl src/AbstractLattices.jl` (19 lines). In Julia,
`∧ === wedge` and `∨ === vee` are single generic functions that every downstream
package extends with methods (Bool here; `TruthValues` in DeMorgan; tree grafting in
Dendriform; the exterior and regressive products in AbstractTensors → Leibniz →
Grassmann). The Lean counterpart of "one generic function extended everywhere" is a
typeclass: `HWedge`/`HVee` below. They are heterogeneous (`α → β → γ` with `γ` an
`outParam`) because Grassmann's `∧` maps `Chain V G × Chain V H → Chain V (G+H)`.

Notation policy (docs/DESIGN.md §4.4): this library defines **no** notation. Lean's
core `∧`/`∨` are `And`/`Or`; Grassmann owns the scoped overloads of those tokens and
maps them onto `HWedge.wedge`/`HVee.vee`. Every instance declared against these classes
(Bool, DeMorgan truth tables, Dendriform trees) is therefore picked up automatically.
-/

namespace AbstractLattices

universe u v w

/-- Heterogeneous meet, Julia `wedge`/`∧` (`AbstractLattices.jl:5,8`).

`γ` is an `outParam` so that result types can be computed from the argument types,
e.g. `Chain V G → Chain V H → Chain V (G + H)` in Grassmann. -/
class HWedge (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The meet / exterior product `a ∧ b` (Julia `wedge(a, b)`). -/
  wedge : α → β → γ

/-- Heterogeneous join, Julia `vee`/`∨` (`AbstractLattices.jl:6,9`). -/
class HVee (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The join / regressive product `a ∨ b` (Julia `vee(a, b)`). -/
  vee : α → β → γ

/-- Distance, Julia `dist` (`AbstractLattices.jl:17`): a generic function stub with no
methods in the Julia package. Metric packages supply instances. -/
class Dist (α : Type u) (β : outParam (Type v)) where
  /-- The distance between two points. -/
  dist : α → α → β

export HWedge (wedge)
export HVee (vee)
export Dist (dist)

/-- Unary meet is the identity, Julia `wedge(x) = x` (`AbstractLattices.jl:11`). It is
the base case of Julia's variadic folds. -/
@[inline] def wedge₁ {α : Type u} (x : α) : α := x

/-- Unary join is the identity, Julia `vee(x) = x` (`AbstractLattices.jl:12`). -/
@[inline] def vee₁ {α : Type u} (x : α) : α := x

/-- Left fold of a homogeneous meet over `x :: xs`, i.e. Julia's `∧(x, xs...)` for
packages that define the variadic method (AbstractTensors does). -/
@[inline] def wedgeAll {α : Type u} [HWedge α α α] (x : α) (xs : List α) : α :=
  xs.foldl wedge x

/-- Left fold of a homogeneous join over `x :: xs` (Julia `∨(x, xs...)`). -/
@[inline] def veeAll {α : Type u} [HVee α α α] (x : α) (xs : List α) : α :=
  xs.foldl vee x

/-! ## Bool (`AbstractLattices.jl:14-15`, present in 0.2.2 / 0.3.x) -/

/-- `wedge(p::Bool, q::Bool) = p && q` (`AbstractLattices.jl:14`). -/
instance : HWedge Bool Bool Bool := ⟨(· && ·)⟩

/-- `vee(p::Bool, q::Bool) = p || q` (`AbstractLattices.jl:15`). -/
instance : HVee Bool Bool Bool := ⟨(· || ·)⟩

@[simp] theorem wedge_bool (p q : Bool) : wedge p q = (p && q) := rfl
@[simp] theorem vee_bool (p q : Bool) : vee p q = (p || q) := rfl

/-! ## Lattice laws

A homogeneous `HWedge α α α` / `HVee α α α` pair is a lattice when it satisfies the
four commutative/associative laws and the two absorption laws. Instances of these
classes are how downstream packages *prove* that their `∧`/`∨` is a lattice (DeMorgan's
truth values are a Boolean algebra; Grassmann's `∧` is *not* a lattice, which is why the
classes above carry no laws). -/

/-- Lattice axioms for a homogeneous meet/join pair. -/
class LawfulLattice (α : Type u) [HWedge α α α] [HVee α α α] : Prop where
  /-- `a ∧ b = b ∧ a` -/
  wedge_comm : ∀ a b : α, wedge a b = wedge b a
  /-- `a ∨ b = b ∨ a` -/
  vee_comm : ∀ a b : α, vee a b = vee b a
  /-- `(a ∧ b) ∧ c = a ∧ (b ∧ c)` -/
  wedge_assoc : ∀ a b c : α, wedge (wedge a b) c = wedge a (wedge b c)
  /-- `(a ∨ b) ∨ c = a ∨ (b ∨ c)` -/
  vee_assoc : ∀ a b c : α, vee (vee a b) c = vee a (vee b c)
  /-- absorption `a ∧ (a ∨ b) = a` -/
  wedge_vee_self : ∀ a b : α, wedge a (vee a b) = a
  /-- absorption `a ∨ (a ∧ b) = a` -/
  vee_wedge_self : ∀ a b : α, vee a (wedge a b) = a

/-- A lattice whose meet distributes over its join. -/
class LawfulDistribLattice (α : Type u) [HWedge α α α] [HVee α α α] : Prop
    extends LawfulLattice α where
  /-- `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)` -/
  wedge_vee_distrib : ∀ a b c : α, wedge a (vee b c) = vee (wedge a b) (wedge a c)

section Laws
variable {α : Type u} [HWedge α α α] [HVee α α α] [LawfulLattice α]

/-- Idempotence of meet follows from the two absorption laws. -/
theorem wedge_self (a : α) : wedge a a = a := by
  have h := LawfulLattice.wedge_vee_self a (wedge a a)
  rwa [LawfulLattice.vee_wedge_self] at h

/-- Idempotence of join follows from the two absorption laws. -/
theorem vee_self (a : α) : vee a a = a := by
  have h := LawfulLattice.vee_wedge_self a (vee a a)
  rwa [LawfulLattice.wedge_vee_self] at h

/-- The two descriptions of the lattice order agree: `a ∧ b = a ↔ a ∨ b = b`. -/
theorem wedge_eq_left_iff_vee_eq_right (a b : α) : wedge a b = a ↔ vee a b = b := by
  constructor
  · intro h
    rw [← h, LawfulLattice.vee_comm, LawfulLattice.wedge_comm, LawfulLattice.vee_wedge_self]
  · intro h
    rw [← h, LawfulLattice.wedge_vee_self]

end Laws

instance : LawfulDistribLattice Bool where
  wedge_comm := by decide
  vee_comm := by decide
  wedge_assoc := by decide
  vee_assoc := by decide
  wedge_vee_self := by decide
  vee_wedge_self := by decide
  wedge_vee_distrib := by decide

/-! ## Min/max lattices

`AbstractLattices.jl test/runtests.jl:4-15` extends `∧`/`∨` to numbers as `min`/`max`.
Those methods live only in the test file (in Grassmann `∧` on scalars is the product), so
the Lean port keeps them behind a wrapper type instead of a global instance. -/

/-- A value viewed in the min/max lattice (`∧ = min`, `∨ = max`), as in
`AbstractLattices.jl test/runtests.jl:4-11`. -/
structure MinMax (α : Type u) where
  /-- The wrapped value. -/
  val : α
  deriving DecidableEq, Repr

instance {α : Type u} [Min α] : HWedge (MinMax α) (MinMax α) (MinMax α) :=
  ⟨fun a b => ⟨min a.val b.val⟩⟩

instance {α : Type u} [Max α] : HVee (MinMax α) (MinMax α) (MinMax α) :=
  ⟨fun a b => ⟨max a.val b.val⟩⟩

instance : LawfulDistribLattice (MinMax Nat) where
  wedge_comm a b := by simp only [wedge, MinMax.mk.injEq]; omega
  vee_comm a b := by simp only [vee, MinMax.mk.injEq]; omega
  wedge_assoc a b c := by simp only [wedge, MinMax.mk.injEq]; omega
  vee_assoc a b c := by simp only [vee, MinMax.mk.injEq]; omega
  wedge_vee_self a b := by cases a; simp only [wedge, vee, MinMax.mk.injEq]; omega
  vee_wedge_self a b := by cases a; simp only [wedge, vee, MinMax.mk.injEq]; omega
  wedge_vee_distrib a b c := by simp only [wedge, vee, MinMax.mk.injEq]; omega

instance : LawfulDistribLattice (MinMax Int) where
  wedge_comm a b := by simp only [wedge, MinMax.mk.injEq]; omega
  vee_comm a b := by simp only [vee, MinMax.mk.injEq]; omega
  wedge_assoc a b c := by simp only [wedge, MinMax.mk.injEq]; omega
  vee_assoc a b c := by simp only [vee, MinMax.mk.injEq]; omega
  wedge_vee_self a b := by cases a; simp only [wedge, vee, MinMax.mk.injEq]; omega
  vee_wedge_self a b := by cases a; simp only [wedge, vee, MinMax.mk.injEq]; omega
  wedge_vee_distrib a b c := by simp only [wedge, vee, MinMax.mk.injEq]; omega

end AbstractLattices
