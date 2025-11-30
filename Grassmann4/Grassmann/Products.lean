/-
  Grassmann/Products.lean - Clifford algebra products

  This file implements the three fundamental products of Clifford algebra:
  1. **Geometric Product**: The full Clifford product a·b
  2. **Wedge Product (Exterior)**: a∧b, antisymmetric, grade-increasing
  3. **Dot Product (Inner)**: a⋅b, symmetric, grade-decreasing

  The geometric product is the fundamental operation, with:
    a·b = a∧b + a⋅b (for vectors)
    a·b = a⌋b + a∧b + a⌊b (general decomposition)

  Key insight: All products between basis blades reduce to:
  - A sign (computed by parity functions)
  - A result blade (computed by XOR for wedge, AND for contraction)
-/
import Grassmann.Parity

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-! ## Blade Products

Products between basis blades are the building blocks.
Each product returns a sign and a result blade (or zero).
-/

/-- Result of a blade product: either zero or a signed blade -/
inductive BladeProduct (sig : Signature n) where
  | zero : BladeProduct sig
  | nonzero : Int → Blade sig → BladeProduct sig
  deriving Repr

namespace BladeProduct

/-- Check if result is zero -/
def isZero : BladeProduct sig → Bool
  | zero => true
  | nonzero _ _ => false

/-- Get the sign (1 if zero) -/
def sign : BladeProduct sig → Int
  | zero => 0
  | nonzero s _ => s

/-- Get the blade (scalar if zero) -/
def blade : BladeProduct sig → Blade sig
  | zero => Blade.scalar
  | nonzero _ b => b

end BladeProduct

/-! ## Geometric Product of Blades

The geometric product is the fundamental Clifford product.
For basis blades, it's computed as:
- Result blade: a XOR b (symmetric difference of basis vectors)
- Sign: parityjoin(a, b) with metric contribution
-/

/-- Geometric product of two basis blades -/
def geometricProductBlades (a b : Blade sig) : BladeProduct sig :=
  let resultBits := a.bits ^^^ b.bits
  let sign := geometricSign sig a b
  .nonzero sign ⟨resultBits⟩

/-! ## Wedge (Exterior) Product

The wedge product is antisymmetric and grade-additive:
- grade(a ∧ b) = grade(a) + grade(b)
- a ∧ b = -b ∧ a (for vectors)
- a ∧ a = 0

For basis blades, zero if they share any basis vectors.
-/

/-- Wedge product of two basis blades -/
def wedgeProductBlades (a b : Blade sig) : BladeProduct sig :=
  if (a.bits &&& b.bits) != 0 then
    .zero  -- Shared basis vectors → zero
  else
    let resultBits := a.bits ||| b.bits  -- Union of basis vectors
    let sign := wedgeSign sig a b
    .nonzero sign ⟨resultBits⟩

/-! ## Left Contraction (Interior Product)

Left contraction a⌋b contracts a into b:
- Non-zero only if grade(a) ≤ grade(b) and a ⊆ b (as sets of basis vectors)
- grade(a⌋b) = grade(b) - grade(a)

This is often called the "dot product" in GA literature.
-/

/-- Left contraction of two basis blades -/
def leftContractionBlades (a b : Blade sig) : BladeProduct sig :=
  if (a.bits &&& b.bits) != a.bits then
    .zero  -- a not contained in b
  else if a.grade > b.grade then
    .zero  -- Grade condition
  else
    let resultBits := a.bits ^^^ b.bits  -- Remove a's vectors from b
    let sign := geometricSign sig a b
    .nonzero sign ⟨resultBits⟩

/-- Right contraction of two basis blades -/
def rightContractionBlades (a b : Blade sig) : BladeProduct sig :=
  if (a.bits &&& b.bits) != b.bits then
    .zero  -- b not contained in a
  else if b.grade > a.grade then
    .zero
  else
    let resultBits := a.bits ^^^ b.bits
    let sign := geometricSign sig a b
    .nonzero sign ⟨resultBits⟩

/-! ## Scalar Product

The scalar product extracts the grade-0 part of the geometric product.
For basis blades, non-zero only when a = b.
-/

/-- Scalar product of two basis blades (returns Int) -/
def scalarProductBlades (a b : Blade sig) : Int :=
  if a.bits != b.bits then 0
  else geometricSign sig a b

/-! ## Regressive Product

The regressive product is dual to the wedge product:
- a ∨ b = ⋆(⋆a ∧ ⋆b)
where ⋆ is the Hodge dual.

For basis blades, it's the "meet" operation.
-/

/-- Regressive product of two basis blades -/
def regressiveProductBlades (a b : Blade sig) : BladeProduct sig :=
  -- Take complement, wedge, take complement
  let aComp := a.bits ^^^ pseudoscalar
  let bComp := b.bits ^^^ pseudoscalar
  -- Check if complements share basis vectors
  if (aComp &&& bComp) != 0 then
    .zero
  else
    let wedgeComp := aComp ||| bComp
    let resultBits := wedgeComp ^^^ pseudoscalar
    -- Sign computation is more complex, simplified here
    let sign := wedgeSign sig ⟨aComp⟩ ⟨bComp⟩ * leftComplementSign sig ⟨wedgeComp⟩
    .nonzero sign ⟨resultBits⟩

/-! ## Single Products

Extend blade products to scaled blades (Singles).
-/

/-- Geometric product of two singles -/
def geometricProductSingles [Mul F] [Neg F] (a b : Single sig F) : Single sig F :=
  match geometricProductBlades a.blade b.blade with
  | .zero => ⟨a.coeff * b.coeff, Blade.scalar⟩  -- Should use zero, but keeping simple
  | .nonzero sign blade =>
    let coeff := if sign < 0 then -(a.coeff * b.coeff) else a.coeff * b.coeff
    ⟨coeff, blade⟩

/-- Wedge product of two singles -/
def wedgeProductSingles [Mul F] [Neg F] [Zero F] (a b : Single sig F) : Single sig F :=
  match wedgeProductBlades a.blade b.blade with
  | .zero => ⟨0, Blade.scalar⟩
  | .nonzero sign blade =>
    let coeff := if sign < 0 then -(a.coeff * b.coeff) else a.coeff * b.coeff
    ⟨coeff, blade⟩

/-! ## Tests -/

-- Geometric product tests
#eval geometricProductBlades (e1 : Blade R3) (e1 : Blade R3)  -- e1·e1 = 1·scalar
#eval geometricProductBlades (e1 : Blade R3) (e2 : Blade R3)  -- e1·e2 = e12
#eval geometricProductBlades (e2 : Blade R3) (e1 : Blade R3)  -- e2·e1 = -e12
#eval geometricProductBlades (e12 : Blade R3) (e12 : Blade R3)  -- e12·e12 = -1·scalar

-- Wedge product tests
#eval wedgeProductBlades (e1 : Blade R3) (e2 : Blade R3)  -- e1∧e2 = e12
#eval wedgeProductBlades (e2 : Blade R3) (e1 : Blade R3)  -- e2∧e1 = -e12
#eval wedgeProductBlades (e1 : Blade R3) (e1 : Blade R3)  -- e1∧e1 = 0
#eval wedgeProductBlades (e12 : Blade R3) (e3 : Blade R3)  -- e12∧e3 = e123

-- Left contraction tests
#eval leftContractionBlades (e1 : Blade R3) (e12 : Blade R3)  -- e1⌋e12 = e2
#eval leftContractionBlades (e1 : Blade R3) (e23 : Blade R3)  -- e1⌋e23 = 0
#eval leftContractionBlades (e12 : Blade R3) (e1 : Blade R3)  -- e12⌋e1 = 0 (grade too high)

-- Scalar product tests
#eval scalarProductBlades (e1 : Blade R3) (e1 : Blade R3)  -- 1
#eval scalarProductBlades (e1 : Blade R3) (e2 : Blade R3)  -- 0
#eval scalarProductBlades (e12 : Blade R3) (e12 : Blade R3)  -- -1

end Grassmann
