/-
`Multivector V α`: a general element, all `2ⁿ` coefficients (Julia
`Multivector{V,T,X}`, `Grassmann.jl src/multivectors.jl:229-412`;
port-notes/grassmann-types.md §3.3, §4.1, §4.3).

Storage order is Julia's `basisindex` order: grade-major, lexicographic within a
grade (`Leibniz.indexBasisAll`). The coefficient accessor uses the correct
`basisindex` (Julia's `m.v13` wrongly uses `bladeindex`, and `m[b]` indexes a
grade block: defect `multivector-getproperty`, fixed here).
-/
import Grassmann.Types.Half

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

/-- A general element of the algebra of `V` (Julia `Multivector{V,α}`). -/
structure Multivector (V : TensorBundle) (α : Type) [Coeff α] where
  /-- The `2ⁿ` coefficients in Julia's `basisindex` order. -/
  v : Values α (2 ^ V.n)

namespace Multivector

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Build from the components. -/
@[inline] def ofFn (f : Fin (2 ^ V.n) → α) : Multivector V α := ⟨Values.ofFn f⟩

/-- Build from a list of length `2ⁿ` (Julia `Multivector{V}(v::AbstractVector)`). -/
def ofList? (l : List α) : Option (Multivector V α) := (Values.ofList? l).map (⟨·⟩)

/-- Build from an array of length `2ⁿ`. -/
def ofArray? (a : Array α) : Option (Multivector V α) := (Values.ofArray? a).map (⟨·⟩)

/-- Build from a list whose length `2ⁿ` is checked at elaboration time (Julia
`Multivector{V}(1,2,…,8)`; the literal `mv![…]`). -/
def ofList (l : List α) (h : l.length = 2 ^ V.n := by decide) : Multivector V α :=
  ⟨Values.ofFn fun i => l[i.1]'(by have := i.2; omega)⟩

/-- The zero multivector (Julia `zero(Multivector{V,T})`, printed `0v⃖`). -/
@[inline] def zero : Multivector V α := ⟨zeroValues _⟩

/-- A scalar as a multivector. -/
def scalar (x : α) : Multivector V α := ⟨Values.ofFn fun i => if i.1 = 0 then x else Coeff.zero⟩

/-- Julia `one(::Multivector)` (printed `1v⃖`). -/
@[inline] def one : Multivector V α := scalar Coeff.one

/-- The `i`-th component (0-based). -/
@[inline] def get (m : Multivector V α) (i : Fin (2 ^ V.n)) : α := m.v.get i

instance : GetElem (Multivector V α) Nat α (fun _ i => i < 2 ^ V.n) where
  getElem m i h := m.v.get ⟨i, h⟩

/-- The coefficient of blade `b` (at Julia's `basisindex`). -/
def coeff (m : Multivector V α) (b : UInt64) : α :=
  if Layout.full.contains V.n b then getD m.v (Leibniz.basisRank V.n b) else Coeff.zero

/-- The scalar coefficient (Julia `value(scalar(m))`). -/
@[inline] def scalarValue (m : Multivector V α) : α := getD m.v 0

/-- The grade-`g` block as a chain (Julia `m(g)`, `grade(m, g)`;
`src/multivectors.jl:300-316`). A zero chain for `g > n`. -/
@[inline] def grade (m : Multivector V α) (g : Nat) : Chain V g α :=
  ⟨convertLayout V.n .full (.chain g) m.v⟩

/-- The grade-`g` block as a `Values` (Julia `m[g]`, `src/multivectors.jl:305-309`). -/
@[inline] def gradeValues (m : Multivector V α) (g : Nat) : Values α (Leibniz.binomial V.n g) :=
  (m.grade g).v

/-- The even or odd part as a half (Julia `even(m)`, `odd(m)`,
`src/products.jl:1488-1522`). -/
@[inline] def half (m : Multivector V α) (p : Bool) : Half V p α :=
  ⟨convertLayout V.n .full (halfLayout p) m.v⟩

/-- `x · e_b` (Julia `Multivector(x, b)`, `src/multivectors.jl:384-393`). -/
def ofBlade {G : Nat} (b : Submanifold V G) (x : α) : Multivector V α :=
  let r := Leibniz.basisRank V.n b.bits
  ofFn fun i => if i.1 = r then x else Coeff.zero

/-- The terms `(blade, coefficient)` in storage order. -/
def terms (m : Multivector V α) : Array (UInt64 × α) :=
  let bs := Leibniz.indexBasisAll V.n
  m.v.toArray.zipIdx.map fun (x, i) => (bs[i]!, x)

/-- Map the coefficients. -/
@[inline] def map {β : Type} [Coeff β] (f : α → β) (m : Multivector V α) : Multivector V β :=
  ⟨m.v.map f⟩

/-- Whether every coefficient is exactly zero. -/
@[inline] def isZero (m : Multivector V α) : Bool := m.v.all Coeff.isZero

instance : Inhabited (Multivector V α) := ⟨zero⟩

instance [BEq α] : BEq (Multivector V α) := ⟨fun a b => a.v == b.v⟩

instance [DecidableEq α] : DecidableEq (Multivector V α) := fun a b =>
  if h : a.v = b.v then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse fun e => h (by cases e; rfl)

instance : AbstractTensors.TensorMixed (Multivector V α) TensorBundle V α where

instance : AbstractTensors.Value (Multivector V α) (Values α (2 ^ V.n)) := ⟨Multivector.v⟩

end Multivector

/-! ## Literals (Julia `Chain{V,1}(4,5,6)`, `Multivector{V}(1,…,8)`, `Spinor{V}(…)`)

The space, grade and coefficient type come from the expected type; the length is checked
at elaboration time (`decide`), so a wrong count is a type error instead of Julia's run-time
`DimensionMismatch`:

```lean
open Grassmann
def a : Chain ℝ3 1 Int := chain![1, 2, 3]
def q : Spinor ℝ3 Int := spinor![1, 2, 3, 4]
def m : Multivector ℝ3 Int := mv![1, 2, 3, 4, 5, 6, 7, 8]
```
-/

/-- A chain literal `chain![x₁, …, xₖ]` (Julia `Chain{V,G}(x₁, …, xₖ)`), `k = binomial(n, G)`. -/
scoped macro "chain![" xs:term,* "]" : term => `(Grassmann.Chain.ofList [$xs,*])

/-- A multivector literal `mv![x₁, …, x₂ₙ]` (Julia `Multivector{V}(…)`), in Julia's storage
order (grade-major, lexicographic within a grade). -/
scoped macro "mv![" xs:term,* "]" : term => `(Grassmann.Multivector.ofList [$xs,*])

/-- A spinor literal `spinor![…]` (Julia `Spinor{V}(…)`, the even grades in storage order). -/
scoped macro "spinor![" xs:term,* "]" : term =>
  `((Grassmann.Half.ofList [$xs,*] : Grassmann.Half _ false _))

/-- A co-spinor literal `cospinor![…]` (Julia `CoSpinor{V}(…)`, the odd grades). -/
scoped macro "cospinor![" xs:term,* "]" : term =>
  `((Grassmann.Half.ofList [$xs,*] : Grassmann.Half _ true _))

end Grassmann
