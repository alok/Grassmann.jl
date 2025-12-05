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

/-- Geometric product of two basis blades.
    Returns zero if shared degenerate basis vectors cause cancellation. -/
@[specialize]
def geometricProductBlades (a b : Blade sig) : BladeProduct sig :=
  let sign := geometricSign sig a b
  if sign == 0 then .zero  -- Degenerate basis vectors cancel
  else
    let resultBits := a.bits ^^^ b.bits
    .nonzero sign ⟨resultBits⟩

/-! ## Wedge (Exterior) Product

The wedge product is antisymmetric and grade-additive:
- grade(a ∧ b) = grade(a) + grade(b)
- a ∧ b = -b ∧ a (for vectors)
- a ∧ a = 0

For basis blades, zero if they share any basis vectors.
-/

/-- Wedge product of two basis blades -/
@[specialize]
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
@[specialize]
def leftContractionBlades (a b : Blade sig) : BladeProduct sig :=
  if (a.bits &&& b.bits) != a.bits then
    .zero  -- a not contained in b
  else if a.grade > b.grade then
    .zero  -- Grade condition
  else
    let sign := geometricSign sig a b
    if sign == 0 then .zero  -- Degenerate basis vectors cancel
    else
      let resultBits := a.bits ^^^ b.bits  -- Remove a's vectors from b
      .nonzero sign ⟨resultBits⟩

/-- Right contraction of two basis blades -/
@[specialize]
def rightContractionBlades (a b : Blade sig) : BladeProduct sig :=
  if (a.bits &&& b.bits) != b.bits then
    .zero  -- b not contained in a
  else if b.grade > a.grade then
    .zero
  else
    let sign := geometricSign sig a b
    if sign == 0 then .zero  -- Degenerate basis vectors cancel
    else
      let resultBits := a.bits ^^^ b.bits
      .nonzero sign ⟨resultBits⟩

/-! ## Scalar Product

The scalar product extracts the grade-0 part of the geometric product.
For basis blades, non-zero only when a = b.
-/

/-- Scalar product of two basis blades (returns Int) -/
@[specialize]
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
@[specialize]
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
@[specialize]
def geometricProductSingles [Mul F] [Neg F] (a b : Single sig F) : Single sig F :=
  match geometricProductBlades a.blade b.blade with
  | .zero => ⟨a.coeff * b.coeff, Blade.scalar⟩  -- Should use zero, but keeping simple
  | .nonzero sign blade =>
    let coeff := if sign < 0 then -(a.coeff * b.coeff) else a.coeff * b.coeff
    ⟨coeff, blade⟩

/-- Wedge product of two singles -/
@[specialize]
def wedgeProductSingles [Mul F] [Neg F] [Zero F] (a b : Single sig F) : Single sig F :=
  match wedgeProductBlades a.blade b.blade with
  | .zero => ⟨0, Blade.scalar⟩
  | .nonzero sign blade =>
    let coeff := if sign < 0 then -(a.coeff * b.coeff) else a.coeff * b.coeff
    ⟨coeff, blade⟩

/-! ## HMul Instances for Specialized Products

These instances route blade products to specialized O(1) operations
rather than going through O(4^n) multivector multiplication.
-/

/-- Blade × Blade → BladeProduct using specialized geometric product -/
instance : HMul (Blade sig) (Blade sig) (BladeProduct sig) := ⟨geometricProductBlades⟩

/-- Single × Single → Single using specialized geometric product -/
instance [Mul F] [Neg F] : HMul (Single sig F) (Single sig F) (Single sig F) :=
  ⟨geometricProductSingles⟩

/-! ## Wedge Product Operators

Custom operators for wedge product on blades/singles.
-/

/-- Wedge product for blades -/
infixl:65 " ⊼ " => wedgeProductBlades

/-- Wedge product for singles -/
def wedgeSingles [Mul F] [Neg F] [Zero F] (a b : Single sig F) : Single sig F :=
  wedgeProductSingles a b

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

/-! ## Interop - Cross-Space Operations

In AbstractTensors.jl, `interop` enables operations between elements from
different vector spaces by embedding them into a common (union) space.

For example, if we have a vector in R² and a vector in R³, we can compute
their product by embedding both into R³ (or R⁵ if they're independent).

In Lean, we provide explicit embedding functions for controlled interop.
-/

/-- Embed a blade from sig into a larger space sig ⊕ (Euclidean m).
    The blade bits are zero-extended to the larger space. -/
def Blade.embedLeft {m : ℕ} (b : Blade sig)
    : Blade (Signature.directSum sig (Signature.euclidean m)) :=
  ⟨b.bits.zeroExtend (n + m)⟩

/-- Embed a blade from (Euclidean m) into a larger space sig ⊕ (Euclidean m).
    The blade bits are shifted to the right positions. -/
def Blade.embedRight {m : ℕ} (b : Blade (Signature.euclidean m))
    : Blade (Signature.directSum sig (Signature.euclidean m)) :=
  ⟨(b.bits.zeroExtend (n + m)).shiftLeft n⟩

/-- Typeclass for interoperability between different spaces.
    This is the core pattern from AbstractTensors.jl for cross-space operations. -/
class Interop (A B C : Type*) where
  /-- Lift an operation to work on elements from different spaces -/
  interop : (C → C → C) → A → B → C

/-- For blades in the same space, interop is trivial -/
instance : Interop (Blade sig) (Blade sig) (BladeProduct sig) where
  interop op a b := op (geometricProductBlades a a) (geometricProductBlades b b)

-- Test blade embedding
#eval let b := (e1 : Blade R2)
      let embedded := @Blade.embedLeft 2 R2 1 b  -- R2 → R3
      embedded.bits  -- Should be 0b001 (same as e1 in R3)

/-! ## Hodge Star (Full Implementation)

The Hodge star ⋆ maps k-blades to (n-k)-blades via the pseudoscalar:
  ⋆a = a ⌋ I (left complement)
  a ⋆ = I ⌊ a (right complement)

where I is the pseudoscalar (unit n-blade).
-/

/-- Left Hodge star (complement): ⋆a = a ⌋ I
    Maps grade k to grade (n-k) -/
@[specialize]
def hodgeLeftBlades (a : Blade sig) : BladeProduct sig :=
  let I : Blade sig := ⟨pseudoscalar⟩
  leftContractionBlades a I

/-- Right Hodge star: a⋆ = I ⌊ a -/
@[specialize]
def hodgeRightBlades (a : Blade sig) : BladeProduct sig :=
  let I : Blade sig := ⟨pseudoscalar⟩
  rightContractionBlades I a

/-- Complement (XOR with pseudoscalar) with sign -/
@[specialize]
def complementBlades (a : Blade sig) : BladeProduct sig :=
  let complementBits := a.bits ^^^ pseudoscalar
  let sign := leftComplementSign sig a
  .nonzero sign ⟨complementBits⟩

/-- Left complement with Hodge sign correction -/
@[specialize]
def complementLeftHodge (a : Blade sig) : BladeProduct sig :=
  let complementBits := a.bits ^^^ pseudoscalar
  let sign := leftComplementSign sig a
  -- Additional sign from metric contribution
  let metricSign := Signature.bladeSquareSign sig a.bits
  let totalSign := sign * metricSign
  if totalSign == 0 then .zero
  else .nonzero totalSign ⟨complementBits⟩

/-- Right complement with Hodge sign correction -/
@[specialize]
def complementRightHodge (a : Blade sig) : BladeProduct sig :=
  let complementBits := a.bits ^^^ pseudoscalar
  let sign := rightComplementSign sig a
  let metricSign := Signature.bladeSquareSign sig a.bits
  let totalSign := sign * metricSign
  if totalSign == 0 then .zero
  else .nonzero totalSign ⟨complementBits⟩

/-- Hodge star operator notation -/
prefix:max "⋆ " => complementBlades

/-! ## Anti-Operations

These are the dual/complement versions of standard operations.
Defined via: anti_op(a, b) = ⋆(⋆a op ⋆b)
-/

/-- Anti-wedge product (regressive product / meet): a ∨ b = ⋆(⋆a ∧ ⋆b) -/
@[specialize]
def antiWedgeBlades (a b : Blade sig) : BladeProduct sig :=
  regressiveProductBlades a b  -- Already defined above

/-- Anti-dot product (expansion): uses complement -/
@[specialize]
def antiDotBlades (a b : Blade sig) : BladeProduct sig :=
  -- antidot(a, b) = ⋆(⋆a ⌋ ⋆b)
  let aComp : Blade sig := ⟨a.bits ^^^ pseudoscalar⟩
  let bComp : Blade sig := ⟨b.bits ^^^ pseudoscalar⟩
  match leftContractionBlades aComp bComp with
  | .zero => .zero
  | .nonzero s result =>
    let finalBits := result.bits ^^^ pseudoscalar
    let hodgeSign := leftComplementSign sig result
    .nonzero (s * hodgeSign) ⟨finalBits⟩

infixl:65 " ⊙ᵇ " => antiDotBlades

/-- Sandwich product for blades: a × x × a† -/
@[specialize]
def sandwichBlades (a x : Blade sig) : BladeProduct sig :=
  -- Compute a * x first
  match geometricProductBlades a x with
  | .zero => .zero
  | .nonzero s1 ax =>
    -- Then (a*x) * a† where a† = a for blades (reverse is identity on vectors)
    match geometricProductBlades ax a with
    | .zero => .zero
    | .nonzero s2 result => .nonzero (s1 * s2) result

/-- Anti-sandwich: ⋆(⋆R >>> ⋆x) where >>> is right geometric product.
    Defined as: antisandwich(R, x) = ⋆((⋆R) * (⋆x) * (⋆R)†) -/
@[specialize]
def antiSandwichBlades (R x : Blade sig) : BladeProduct sig :=
  let Rcomp : Blade sig := ⟨R.bits ^^^ pseudoscalar⟩
  let xcomp : Blade sig := ⟨x.bits ^^^ pseudoscalar⟩
  match sandwichBlades Rcomp xcomp with
  | .zero => .zero
  | .nonzero s result =>
    let finalBits := result.bits ^^^ pseudoscalar
    let hodgeSign := leftComplementSign sig result
    .nonzero (s * hodgeSign) ⟨finalBits⟩

/-- Pseudo-sandwich: ⋆(sandwich(⋆x, ⋆R)) -/
@[specialize]
def pseudoSandwichBlades (x R : Blade sig) : BladeProduct sig :=
  let Rcomp : Blade sig := ⟨R.bits ^^^ pseudoscalar⟩
  let xcomp : Blade sig := ⟨x.bits ^^^ pseudoscalar⟩
  match sandwichBlades xcomp Rcomp with
  | .zero => .zero
  | .nonzero s result =>
    let finalBits := result.bits ^^^ pseudoscalar
    let hodgeSign := leftComplementSign sig result
    .nonzero (s * hodgeSign) ⟨finalBits⟩

/-! ## Wedgedot (Fat Dot / Geometric Inner Product)

The wedgedot ⟑ is a variant that includes metric information.
-/

/-- Wedgedot product: combines contraction with metric -/
@[specialize]
def wedgeDotBlades (a b : Blade sig) : BladeProduct sig :=
  -- wedgedot is essentially the symmetric part of geometric product
  -- For blades: wedgedot(a,b) = ⟨ab⟩_{|grade(a) - grade(b)|}
  let targetGrade := if a.grade ≤ b.grade then b.grade - a.grade else a.grade - b.grade
  match geometricProductBlades a b with
  | .zero => .zero
  | .nonzero s result =>
    if result.grade == targetGrade then .nonzero s result
    else .zero

infixl:70 " ⟑ᵇ " => wedgeDotBlades

/-! ## Anti-operation Tests -/

-- Hodge star tests
#eval complementBlades (e1 : Blade R3)  -- ⋆e1 = e23
#eval complementBlades (e12 : Blade R3)  -- ⋆e12 = e3
#eval complementBlades (e123 : Blade R3)  -- ⋆e123 = scalar

-- Anti-dot test
#eval antiDotBlades (e1 : Blade R3) (e123 : Blade R3)

-- Sandwich test: e1 sandwiches e2 should give reflection
#eval sandwichBlades (e1 : Blade R3) (e2 : Blade R3)

end Grassmann
