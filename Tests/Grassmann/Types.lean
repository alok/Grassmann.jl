/-
The typed element API:

* compile-time checks of the static result types (DESIGN.md §4.2), for
  concrete and for variable spaces and grades;
* storage orders (Julia `bladeindex`/`basisindex`/`spinindex`/`antiindex`),
  constructors, accessors and the container conversions of
  port-notes/grassmann-types.md §4.2-4.3;
* Julia display goldens (grassmann-types.md §5.4);
* inverses (`Multivector`, `Couple` with either sign of `B²`), `isapprox`;
* the `Kernels` extension point: a default-priority instance for a concrete
  space replaces the reference kernels.
-/
import Tests.Grassmann.Common

open Grassmann DirectSum StaticVectors

namespace GrassmannTests.Types

/-! ## Static result types -/

section StaticTypes

variable (a b : Chain ℝ3 1 Int) (B : Chain ℝ3 2 Int) (T : Chain ℝ3 3 Int)
  (s : Spinor ℝ3 Int) (o : CoSpinor ℝ3 Int) (m : Multivector ℝ3 Int)
  (x y : Single ℝ3 1 Int) (e₁ e₂ : Submanifold ℝ3 1) (z : Couple ℝ3 Int)

example : Spinor ℝ3 Int := a * b
example : CoSpinor ℝ3 Int := a * B
example : Spinor ℝ3 Int := a ⟑ T
example : CoSpinor ℝ3 Int := s * o
example : Spinor ℝ3 Int := o * o
example : CoSpinor ℝ3 Int := a * s
example : Multivector ℝ3 Int := m * a
example : Chain ℝ3 2 Int := a ∧ b
example : Chain ℝ3 3 Int := a ∧ B
example : Chain ℝ3 4 Int := B ∧ B
example : Chain ℝ3 1 Int := B ∨ B
example : Chain ℝ3 0 Int := a ∨ B
example : Chain ℝ3 1 Int := B ⋅ a
example : Chain ℝ3 0 Int := a ⋅ b
example : Chain ℝ3 1 Int := a ⨼ B
example : Chain ℝ3 1 Int := a × b
example : Chain ℝ3 2 Int := ⋆a
example : Chain ℝ3 2 Int := !a
example : CoSpinor ℝ3 Int := ⋆s
example : Chain ℝ3 1 Int := ~a
example : Spinor ℝ3 Int := ~s
example : Chain ℝ3 1 Int := a ⊘ s
example : Chain ℝ3 1 Int := s >>> a
example : Chain ℝ3 1 Int := a ⊘ B
example : Spinor ℝ3 Int := s ⊘ o
example : Chain ℝ3 1 Int := a + b
example : Multivector ℝ3 Int := a + B
example : Chain ℝ3 1 Int := x + y
example : Chain ℝ3 1 Int := x + a
example : Chain ℝ3 1 Int := e₁ + e₂
example : Couple ℝ3 Int := e₁ * e₂
example : Single ℝ3 1 Int := (3 : Int) * e₁
example : Multivector ℝ3 Int := z + a
example : Multivector ℝ3 Int := z * s
example : Spinor ℝ3 Int := m₊
example : CoSpinor ℝ3 Int := m₋
example : Chain ℝ3 2 Int := bivector m
example : Chain ℝ3 3 Int := volume s
example : Spinor ℝ3 Int := (2 : Int) + s
example : Multivector ℝ3 Int := (2 : Int) + a

-- variable space and grades: the indices stay symbolic
example {V : TensorBundle} {G H : Nat} (c : Chain V G Rat) (d : Chain V H Rat) :
    Half V ((G + H) % 2 == 1) Rat := c * d
example {V : TensorBundle} {G H : Nat} (c : Chain V G Rat) (d : Chain V H Rat) :
    Chain V (G + H) Rat := c ∧ d
example {V : TensorBundle} {G H : Nat} (c : Chain V G Rat) (d : Chain V H Rat) :
    Chain V (G + H - V.n) Rat := c ∨ d
example {V : TensorBundle} {G : Nat} (c : Chain V G Rat) : Chain V (V.n - G) Rat := ⋆c
example {V : TensorBundle} {p q : Bool} (h : Half V p Rat) (k : Half V q Rat) : Half V (p ^^ q) Rat := h * k
example {V : TensorBundle} {p : Bool} (h : Half V p Rat) : Half V (p ^^ (V.n % 2 == 1)) Rat := !h

-- sizes are kernel-reducible
example : halfDim 4 true = 8 ∧ halfDim 1 false = 1 ∧ Leibniz.binomial 5 2 = 10 := by decide

end StaticTypes

/-! ## Values -/

/-- Build from a list (the test inputs have the right length). -/
def chain (V : TensorBundle) (G : Nat) (l : List Int) : Chain V G Int := (Chain.ofList? l).getD Chain.zero
/-- Build a half from a list. -/
def half (V : TensorBundle) (p : Bool) (l : List Int) : Half V p Int := (Half.ofList? l).getD Half.zero
/-- Build a multivector from a list. -/
def multi (V : TensorBundle) (l : List Int) : Multivector V Int :=
  (Multivector.ofList? l).getD Multivector.zero

/-- Run the type/API suite. -/
def run : IO Tally := do
  let mut t : Tally := {}
  let E3 := S!"+++"
  let E4 := S!"++++"
  -- constructors reject wrong lengths
  t := t.check ((Chain.ofList? [1, 2] : Option (Chain E3 1 Int)).isNone) "Chain.ofList? wrong length"
  t := t.check ((Multivector.ofList? [1, 2, 3] : Option (Multivector E3 Int)).isNone) "Multivector.ofList? wrong length"
  -- storage orders: lexicographic within a grade, grade-major across grades
  let c2 := chain E4 2 [1, 2, 3, 4, 5, 6]
  t := t.check (c2.coeff 0b1001 == 3 && c2.coeff 0b0110 == 4 && c2.coeff 0b0001 == 0) "bladeindex order"
  let m := multi E3 [1, 2, 3, 4, 5, 6, 7, 8]
  t := t.check (m.coeff 0b101 == 6 && m.coeff 0b111 == 8 && m.scalarValue == 1) "basisindex order"
  t := t.check ((m.grade 2).v.toList == [5, 6, 7] && (m.grade 4).v.toList == []) "grade blocks"
  let s := half E3 false [1, 2, 3, 4]
  t := t.check ((s.grade 2).v.toList == [2, 3, 4] && (s.grade 1).v.toList == [0, 0, 0]) "spinor grades"
  t := t.check ((c2.term ⟨2, by decide⟩).bits == 0b1001) "term blade"
  t := t.check ((Leibniz.indexEven 4).toList == [0, 3, 5, 9, 6, 10, 12, 15]) "spinindex order"
  -- conversions (grassmann-types.md §4.2)
  let c1 := chain E3 1 [4, 5, 6]
  t := t.check (toString (toMultivector c1) == "0 + 4v₁ + 5v₂ + 6v₃") "Multivector(Chain)"
  t := t.check (toString (Half.ofChain (chain E3 2 [1, 2, 3])) == "0 + 1v₁₂ + 2v₁₃ + 3v₂₃") "Spinor(Chain)"
  t := t.check (toString (Half.ofChain c1) == "4v₁ + 5v₂ + 6v₃ + 0v₁₂₃") "CoSpinor(Chain)"
  t := t.check (toString (toMultivector (half E3 true [5, 6, 7, 8])) == "0 + 5v₁ + 6v₂ + 7v₃ + 8v₁₂₃")
    "Multivector(CoSpinor)"
  t := t.check (toString (toMultivector (⟨0b011, 1, 2⟩ : Couple E3 Int)) == "1 + 2v₁₂") "Multivector(Couple)"
  t := t.check (toString (toMultivector (⟨0b001, 3, 4⟩ : PseudoCouple E3 Int)) == "0 + 3v₁ + 4v₁₂₃")
    "Multivector(PseudoCouple)"
  t := t.check (toString (m.half true) == "2v₁ + 3v₂ + 4v₃ + 8v₁₂₃") "odd part"
  -- display (grassmann-types.md §5.4)
  t := t.check (toString (chain E3 1 [1, 1, 0]) == "1v₁ + 1v₂ + 0v₃") "Chain show"
  t := t.check (toString (chain E3 0 [7]) == "7v") "grade-0 Chain show"
  t := t.check (toString m == "1 + 2v₁ + 3v₂ + 4v₃ + 5v₁₂ + 6v₁₃ + 7v₂₃ + 8v₁₂₃") "Multivector show"
  t := t.check (toString (multi E3 [0, 0, 0, 0, 0, 0, 0, 0]) == "0v⃖" &&
    toString (multi E3 [3, 0, 0, 0, 0, 0, 0, 0]) == "3v⃖") "Multivector scalar show"
  t := t.check (toString (multi E3 [0, 1, 0, 0, 0, 0, 0, -1]) == "0 + 1v₁ - 1v₁₂₃") "Multivector zeros skipped"
  t := t.check (toString s == "1 + 2v₁₂ + 3v₁₃ + 4v₂₃") "Spinor show"
  t := t.check (toString (half E3 true [1, 2, 3, 4]) == "1v₁ + 2v₂ + 3v₃ + 4v₁₂₃") "CoSpinor show"
  t := t.check (toString (⟨0b011, 1, -2⟩ : Couple E3 Int) == "1 - 2v₁₂") "Couple show"
  t := t.check (toString (⟨0b001, 1, 2⟩ : PseudoCouple E3 Int) == "1v₁ + 2v₁₂₃") "PseudoCouple show"
  t := t.check (toString (⟨0b001, 2⟩ : Single E3 1 Int) == "2v₁") "Single show"
  t := t.check (toString (⟨0b001, 1/2⟩ : Single E3 1 Rat) == "(1//2)v₁") "Rational Single show"
  let cf : Chain E3 1 Float := Chain.ofFn fun i => #[1.0 / 3.0, 2.0 / 3.0, 1.0e-20][i.1]!
  t := t.check (toString cf == "0.333333v₁ + 0.666667v₂ + 1.0e-20v₃") "compact Float Chain show"
  t := t.check (toString (⟨0b001, 1.0 / 3.0⟩ : Single E3 1 Float) == "0.3333333333333333v₁")
    "non-compact Float Single show"
  let cga : Chain CGA3 1 Int := chain CGA3 1 [1, 2, 3, 4, 5]
  t := t.check (toString cga == "1v∞ + 2v∅ + 3v₁ + 4v₂ + 5v₃") "conformal labels"
  -- Julia goldens of the products (grassmann-products.md §5)
  let a := chain E3 1 [1, 2, 3]
  let b := chain E3 1 [4, 5, 6]
  t := t.check (toString (a * b) == "32 - 3v₁₂ - 6v₁₃ - 3v₂₃") "a*b"
  t := t.check (toString (a ∧ b) == "-3v₁₂ - 6v₁₃ - 3v₂₃") "a∧b"
  t := t.check (toString (a ⋅ b) == "32v") "a⋅b"
  t := t.check (toString (!m) == "8 + 7v₁ - 6v₂ + 5v₃ + 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃") "!m (docs)"
  let V3 := S!"++-"
  t := t.check (toString (⋆(multi V3 [1, 2, 3, 4, 5, 6, 7, 8])) ==
    "-8 - 7v₁ + 6v₂ + 5v₃ - 4v₁₂ - 3v₁₃ + 2v₂₃ + 1v₁₂₃") "hodge in S\"++-\" (docs)"
  -- inverses over Rat
  let mr : Multivector E3 Rat := (Multivector.ofList? [1, 0, 0, 0, 0, 0, 0, 2]).getD Multivector.zero
  t := t.check ((mr.inv?).map (·.v.toList) == some [1/5, 0, 0, 0, 0, 0, 0, -2/5]) "inv(1 + 2I)"
  let generic : Multivector E3 Rat := (Multivector.ofList? [1, 2, 3, 4, 5, 6, 7, 8]).getD Multivector.zero
  t := t.check (generic.inv?).isNone "inv of a generic multivector is undefined (Julia throws)"
  for (bits, nm) in [((0b011 : UInt64), "v₁₂"), (0b001, "v₁"), (0b111, "v₁₂₃")] do
    let z : Couple E3 Rat := ⟨bits, 1, 2⟩
    t := t.check (toMultivector z * toMultivector z⁻¹ == Multivector.one) s!"Couple inverse on {nm}"
  -- isapprox: componentwise for chains (Julia `0 ≈ 1e-20` is false)
  let c0 : Chain E3 1 Float := Chain.ofFn fun _ => 0
  let ce : Chain E3 1 Float := Chain.ofFn fun i => if i.1 = 0 then 1.0e-20 else 0
  t := t.check (!c0.isapprox ce && c0.isapprox c0) "Chain isapprox"
  -- isapprox: norm-based for multivectors (and across element types)
  let mf : Multivector E3 Float := Multivector.ofFn fun i => Float.ofNat i.1
  let mf' : Multivector E3 Float := Multivector.ofFn fun i => Float.ofNat i.1 + 1.0e-12
  t := t.check (Grassmann.isapprox mf mf' && !Grassmann.isapprox mf (mf + mf)
    && Grassmann.isapprox (toMultivector ce) c0 (atol := 1.0e-15)) "norm-based isapprox"
  -- equality
  t := t.check (decide (a = a) && !decide (a = b) && a == a) "DecidableEq/BEq"
  return t

end GrassmannTests.Types

/-! ## `basis!` -/

namespace GrassmannTests.BasisE3
basis! S!"+++"
end GrassmannTests.BasisE3

namespace GrassmannTests.BasisCGA
basis! S!"∞∅+++"
end GrassmannTests.BasisCGA

namespace GrassmannTests.Basis

open BasisE3 in
example : Couple V Int := v₁ * v₂
open BasisE3 in
example : Chain V 1 Int := v1 + v₂
open BasisE3 in
example : Submanifold V 3 := v₁₂₃

/-- `basis!` declares the space, the scalar, every blade and the ASCII aliases. -/
def run : IO Tally := do
  let mut t : Tally := {}
  t := t.check (BasisE3.V == S!"+++" && BasisE3.v.bits == 0 && BasisE3.v₁₂.bits == 3
    && BasisE3.v123.bits == 7) "basis! S!\"+++\" names"
  let e : Couple BasisCGA.V Int := BasisCGA.«v∞» * BasisCGA.«v∅»
  t := t.check (e.re == -1 && e.im == 1 && e.bits == 3) "v∞ v∅ = -1 + v∞∅"
  t := t.check (BasisCGA.vinf.bits == 1 && BasisCGA.vo.bits == 2 && BasisCGA.vinfo1.bits == 7)
    "conformal ASCII aliases"
  t := t.check (toString (BasisCGA.«v∞∅₁₂₃» : Submanifold BasisCGA.V 5) == "v∞∅₁₂₃") "conformal blade name"
  return t

end GrassmannTests.Basis

/-! ## The kernel extension point

A default-priority `Kernels` instance for one concrete space replaces the
low-priority reference instance. This one negates every binary product, so the
dispatch is observable. -/

namespace GrassmannTests.Extension

/-- A space with its own (deliberately wrong) kernels. -/
abbrev Negated : TensorBundle := S!"+-+"

instance : Kernels Negated where
  bin op la lb lc x y := -(Grassmann.Kernel.refBin Negated op la lb lc x y)

/-- The custom instance is used for products; unary maps keep the reference. -/
def run : IO Tally := do
  let a : Chain Negated 1 Int := (Chain.ofList? [1, 2, 3]).getD Chain.zero
  let b : Chain Negated 1 Int := (Chain.ofList? [4, 5, 6]).getD Chain.zero
  let viaRef : Values Int 4 := Grassmann.Kernel.refBin Negated .mul (.chain 1) (.chain 1) .even a.v b.v
  let t : Tally := {}
  let t := t.check ((a * b).v.toList == (-viaRef).toList) "generated-instance dispatch"
  let t := t.check ((~a).v.toList == a.v.toList) "fields left out keep their reference defaults"
  return t

end GrassmannTests.Extension
