/-
  Grassmann/Notation.lean - Unicode notation for Grassmann algebra

  This file provides nice Unicode notation for Clifford algebra operations.

  **Important**: We avoid `∧` for wedge product since it conflicts with
  Prop.And in Lean. Instead we use `⋀` (n-ary logical and, U+22C0) or
  `∧ᵍ` with a subscript to disambiguate.

  Operators:
  - `⋀` or `∧ᵍ` : Wedge (exterior) product
  - `⌋` : Left contraction (interior product)
  - `⌊` : Right contraction
  - `⊛` : Geometric product
  - `⊙` : Scalar product
  - `⋁` : Regressive product (meet)
  - `†` : Reverse (dagger)
  - `⋆` : Hodge star / complement
-/
import Grassmann.Products

namespace Grassmann

/-! ## Blade Notation -/

section BladeNotation

variable {n : ℕ} {sig : Signature n}

-- Wedge product of blades (use ⋀ to avoid conflict with ∧)
infixl:65 " ⋀ " => wedgeProductBlades

-- Geometric product of blades
infixl:70 " ⊛ " => geometricProductBlades

-- Left contraction
infixl:65 " ⌋ " => leftContractionBlades

-- Right contraction
infixl:65 " ⌊ " => rightContractionBlades

-- Regressive product (meet)
infixl:65 " ⋁ " => regressiveProductBlades

end BladeNotation

/-! ## Single Notation -/

section SingleNotation

variable {n : ℕ} {sig : Signature n} {F : Type*}

-- Note: These require typeclass constraints, so we provide them
-- through explicit instances

end SingleNotation

/-! ## Grade Selection Notation

Common notation uses subscript to select grade:
  ⟨M⟩₀ = scalar part
  ⟨M⟩₁ = vector part
  ⟨M⟩₂ = bivector part
-/

-- Grade projection will be implemented with Multivector type

/-! ## Reverse and Involute

The reverse operation (†) reverses the order of basis vectors:
  (e₁∧e₂)† = e₂∧e₁ = -e₁∧e₂

The grade involute (ˆ) applies (-1)^grade:
  ê = -e for vectors
  (e₁∧e₂)ˆ = e₁∧e₂ for bivectors

Note: These operations on blades just return the blade itself.
The sign is tracked separately via reverseSign/involuteSign.
-/

/-! ## Hodge Star / Complement

The Hodge star ⋆ maps k-blades to (n-k)-blades via the complement.
Note: ⋆ conflicts with HMul, use explicit complement function
-/

/-! ## Tests -/

-- Wedge product notation
#eval (e1 : Blade R3) ⋀ (e2 : Blade R3)  -- e12
#eval (e2 : Blade R3) ⋀ (e1 : Blade R3)  -- -e12
#eval (e1 : Blade R3) ⋀ (e1 : Blade R3)  -- zero

-- Geometric product notation
#eval (e1 : Blade R3) ⊛ (e2 : Blade R3)  -- e12
#eval (e1 : Blade R3) ⊛ (e1 : Blade R3)  -- scalar

-- Left contraction notation
#eval (e1 : Blade R3) ⌋ (e12 : Blade R3)  -- e2
#eval (e1 : Blade R3) ⌋ (e23 : Blade R3)  -- zero

-- Regressive product notation
#eval (e12 : Blade R3) ⋁ (e23 : Blade R3)  -- e2 (the meet)

-- Chained operations (note: products return BladeProduct, not Blade, so can't chain directly)
#eval ((e1 : Blade R3) ⋀ (e2 : Blade R3))  -- e12

-- To chain, we'd need to extract the blade from BladeProduct
-- This will be handled by the Multivector type which tracks linear combinations

end Grassmann
