/-
Notation coexistence (DESIGN §4.4): with `open AbstractTensors`, the scoped
`∧ ∨ × !` overload core's `And`, `Or`, `Prod` and `not` through choice nodes.
Everything below is checked at compile time: Prop, type and Bool uses keep
their core meaning, and the tensor operators resolve on tensor types.
-/
import AbstractTensors

open AbstractTensors

namespace Tests.AbstractTensors.Notation

/-- A toy two-component "tensor" `s + v·e` with a nilpotent `e` (the dual numbers). -/
structure T2 where
  /-- scalar part -/
  s : Int
  /-- `e` part -/
  v : Int
  deriving DecidableEq, Repr

instance : Wedge T2 T2 T2 := ⟨fun x y => ⟨x.s * y.s, x.s * y.v + x.v * y.s⟩⟩
instance : Vee T2 T2 T2 := ⟨fun x y => ⟨x.s * y.v + x.v * y.s, x.v * y.v⟩⟩
instance : WedgeDot T2 T2 T2 := ⟨fun x y => ⟨x.s * y.s, x.s * y.v + x.v * y.s⟩⟩
instance : VeeDot T2 T2 T2 := ⟨fun x y => ⟨x.s * y.v + x.v * y.s, x.v * y.v⟩⟩
instance : Contraction T2 T2 Int := ⟨fun x y => x.s * y.s⟩
instance : Sandwich T2 T2 T2 := ⟨fun x r => ⟨x.s * r.s * r.s, x.v * r.s * r.s⟩⟩
instance : TensorProd T2 T2 (T2 × T2) := ⟨fun x y => (x, y)⟩
instance : Hodge T2 T2 := ⟨fun x => ⟨x.v, x.s⟩⟩
instance : ComplementRight T2 T2 := ⟨fun x => ⟨x.v, -x.s⟩⟩
instance : ComplementLeft T2 T2 := ⟨fun x => ⟨-x.v, x.s⟩⟩
instance : Reverse T2 := ⟨fun x => ⟨x.s, -x.v⟩⟩
instance : Involute T2 := ⟨fun x => ⟨x.s, -x.v⟩⟩
instance : Even T2 Int := ⟨T2.s⟩
instance : Odd T2 Int := ⟨T2.v⟩
instance : StaticVectors.Conj T2 := ⟨fun x => ⟨x.s, -x.v⟩⟩

/-- First sample element. -/
def a : T2 := ⟨1, 2⟩
/-- Second sample element. -/
def b : T2 := ⟨3, 4⟩

/-! ### Tensor readings

`∧`, `∨` and `×` sit at the precedence of `And`/`Or`/`Prod` (35/30/35), below
`=` (50), so equations about them need parentheses. -/

example : (a ∧ b) = ⟨3, 10⟩ := by decide
example : (a ∨ b) = ⟨10, 8⟩ := by decide
example : (a × b) = ⟨10, 3⟩ := by decide     -- default `×` is `⋆(a ∧ b)` (AT:349)
example : a ⟑ b = ⟨3, 10⟩ := by decide
example : a ⊖ b = ⟨3, 10⟩ := by decide
example : a ⟇ b = ⟨10, 8⟩ := by decide
example : a ⋅ b = 3 := by decide
example : a ⨽ b = 3 := by decide
example : a ⨼ b = 3 := by decide
example : a ⊘ b = ⟨9, 18⟩ := by decide
example : a ⊗ b = (a, b) := by decide
example : ⋆a = ⟨2, 1⟩ := by decide
example : !a = ⟨2, -1⟩ := by decide
example : ~a = ⟨1, -2⟩ := by decide
example : a₊ = 1 := by decide
example : a₋ = 2 := by decide
example : aǂ = ⟨1, -2⟩ := by decide
example : aˣ = ⟨1, -2⟩ := by decide
example : a ∗ b = ⟨3, -2⟩ := by decide           -- `(~a) ⟑ b` (AT:257)
example : a ⊛ b = 3 := by decide                 -- `scalar(a ⋅ b)` (AT:258)
-- right associativity at the `And`/`Or` level; prefix `⋆` binds tighter
example : (a ∧ b ∧ a) = (a ∧ (b ∧ a)) := rfl
example : (a ∨ b ∨ a) = (a ∨ (b ∨ a)) := rfl
example : ((⋆a) ∧ b) = (⋆a ∧ b) := rfl
-- `⟑` binds like `*`, `⟇` like `+`
example : (a ⟑ b ⟇ a) = ((a ⟑ b) ⟇ a) := rfl
-- `co`: complement-conjugated functions (Julia `@co`)
example : co (fun x : T2 => x ∧ x) a = ⟨4, 4⟩ := by decide
-- Unparenthesized, `a ∧ b = c` reads `a ∧ (b = c)`, which is rejected for
-- tensors (neither `And a _` nor `Wedge T2 Prop _` typechecks).

/-! ### Core readings still work in the same file -/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example : ∀ p q : Prop, p ∧ q → q ∧ p := fun _ _ ⟨hp, hq⟩ => ⟨hq, hp⟩
example (p q : Prop) : p ∨ q → q ∨ p := fun h => h.elim Or.inr Or.inl
example : (1 = 1) ∨ False := Or.inl rfl
example : ∃ n : Nat, n = 1 ∧ n + 1 = 2 := ⟨1, rfl, rfl⟩
example : (1 + 1 = 2) ∧ (2 * 2 = 4) := by decide
theorem and_swap_iff {p q : Prop} : p ∧ q ↔ q ∧ p :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩
/-- A Prop-valued definition using `∧`. -/
def andProp (p q : Prop) : Prop := p ∧ q
example : Prop → Prop → Prop := fun p q => p ∧ q ∨ q
-- `×` on types
/-- A value of a product type. -/
def pair : Nat × Bool := (1, true)
example : (Nat × Nat × Nat) = (Nat × (Nat × Nat)) := rfl
example : (Nat × Bool) = Prod Nat Bool := rfl
/-- Swap, written with `×` in its type. -/
def swap' {α β : Type} (p : α × β) : β × α := (p.2, p.1)
-- `!` on Bool
example : (!true) = false := rfl
example (x : Bool) : (!!x) = x := by cases x <;> rfl
example : (!(true && false)) = true := rfl
-- mixing: tensor equations inside Prop connectives
example : ((a ∧ b) = ⟨3, 10⟩) ∧ ((a ∨ b) = ⟨10, 8⟩) := by decide
example : (a ∧ b) = ⟨3, 10⟩ ∨ False := Or.inl (by decide)

end Tests.AbstractTensors.Notation
