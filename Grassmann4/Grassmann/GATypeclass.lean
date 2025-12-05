/-
  Grassmann/GATypeclass.lean - Polymorphic GAlgebra Typeclass Hierarchy

  This module provides a unified interface for Grassmann/Clifford algebra
  operations that works across all representations (Dense, Sparse, Truncated).

  Design:
  - GABasis: Basic basis vector access
  - GABlade: Blade construction from bitmasks
  - GAlgebra: Full Clifford algebra operations

  Usage:
    variable [GAlgebra sig M Float]
    def rotate (v : M) (angle : Float) : M := ...
-/
import Grassmann.Manifold
import Grassmann.Blade
import Grassmann.Proof

open Grassmann.Proof

namespace Grassmann

variable {n : ℕ} {sig : Signature n}

/-! ## Core Typeclasses -/

/-- Basis vector access for a Grassmann algebra representation.
    Provides access to individual basis vectors and scalar construction. -/
class GABasis (sig : Signature n) (M : Type*) (F : Type*) where
  /-- Single basis vector by 0-indexed position -/
  basisVector : Fin n → M
  /-- Scalar multivector from field element -/
  scalar : F → M
  /-- Zero multivector -/
  zero : M
  /-- One (scalar 1) -/
  one : M

/-- Blade construction from bitmasks.
    Extends GABasis with the ability to construct arbitrary blades. -/
class GABlade (sig : Signature n) (M : Type*) (F : Type*)
    extends GABasis sig M F where
  /-- Blade from BitVec mask (bit i set = includes basis vector i) -/
  blade : BitVec n → M

/-- Full Clifford algebra operations.
    The main typeclass for polymorphic GA algorithms. -/
class GAlgebra (sig : Signature n) (M : Type*) (F : Type*)
    extends GABlade sig M F where
  /-- Geometric (Clifford) product -/
  mul : M → M → M
  /-- Wedge (exterior) product -/
  wedge : M → M → M
  /-- Left contraction -/
  leftContract : M → M → M
  /-- Right contraction -/
  rightContract : M → M → M
  /-- Reverse involution (dagger) -/
  reverse : M → M
  /-- Grade involution -/
  involute : M → M
  /-- Clifford conjugate -/
  conjugate : M → M
  /-- Scalar part extraction -/
  scalarPart : M → F
  /-- Addition -/
  add : M → M → M
  /-- Negation -/
  neg : M → M
  /-- Scalar multiplication -/
  smul : F → M → M
  /-- Grade projection (extract grade k component) -/
  gradeProject : M → ℕ → M

/-! ## Operator Instances

Note: These instances use outParam to help type inference.
The signature determines both the multivector type M and scalar field F.
-/

-- No generic instances here - each representation (Multivector, MultivectorS, TruncatedMV)
-- defines its own Mul, Add, etc. instances. The GAlgebra typeclass provides the operations
-- via mul, add, etc. fields, and the notation operators (⊛, ⋀, etc.) use these directly.

/-! ## Unified Notation -/

/-- Geometric product (⊛) -/
scoped infixl:70 " ⊛ " => GAlgebra.mul

/-- Wedge product (⋀) -/
scoped infixl:65 " ⋀ " => GAlgebra.wedge

/-- Left contraction (⌋) -/
scoped infixl:65 " ⌋ " => GAlgebra.leftContract

/-- Right contraction (⌊) -/
scoped infixl:65 " ⌊ " => GAlgebra.rightContract

/-- Reverse/dagger (†) -/
scoped postfix:max "†" => GAlgebra.reverse

/-- Grade involution (ˆ) -/
scoped postfix:max "ˆ" => GAlgebra.involute

/-- Clifford conjugate (‡) -/
scoped postfix:max "‡" => GAlgebra.conjugate

/-! ## Scalar Multiplication Notation -/

/-- Scalar multiplication via GAlgebra -/
scoped infixr:73 " • " => GAlgebra.smul

/-! ## Convenience Functions

These functions are marked @[specialize] to ensure the compiler generates
specialized code for each concrete representation (Multivector, MultivectorS, etc.)
rather than using dictionary-passing at runtime.
-/

/-- Sandwich product: R ▷ x = R * x * R† -/
@[specialize]
def sandwich [inst : GAlgebra sig M F] (R x : M) : M :=
  inst.mul (inst.mul R x) (inst.reverse R)

scoped notation R " ▷ " x => sandwich R x

/-- Norm squared: x * x† (scalar part) -/
@[specialize]
def normSq [inst : GAlgebra sig M F] (x : M) : F :=
  inst.scalarPart (inst.mul x (inst.reverse x))

/-- Unit normalize: x / |x| (specialized for Float) -/
@[specialize]
def unitNormalizeFloat [inst : GAlgebra sig M Float] (x : M) : M :=
  let n := inst.scalarPart (inst.mul x (inst.reverse x))
  inst.smul (1.0 / Float.sqrt n) x

/-- Inverse: x† / (x * x†) for unit versors (specialized for Float) -/
@[specialize]
def versorInverseFloat [inst : GAlgebra sig M Float] (x : M) : M :=
  let n := inst.scalarPart (inst.mul x (inst.reverse x))
  inst.smul (1.0 / n) (inst.reverse x)

/-- Grade extraction notation -/
scoped notation "⟨" m "⟩₀" => GAlgebra.gradeProject m 0
scoped notation "⟨" m "⟩₁" => GAlgebra.gradeProject m 1
scoped notation "⟨" m "⟩₂" => GAlgebra.gradeProject m 2
scoped notation "⟨" m "⟩₃" => GAlgebra.gradeProject m 3

/-! ## Signature Utilities -/

-- Signature.clr is defined in Manifold.lean with proper degenerate support

/-- Common signature shortcuts -/
abbrev Cl (p q : ℕ) := Signature.clr p q 0

/-! ## Named Algebra Signatures -/

/-- 3D Euclidean: Cl(3,0,0) -/
abbrev sigR3 : Signature 3 := Signature.euclidean 3

/-- 3D Projective GA: Cl(3,0,1) -/
abbrev sigPGA3 : Signature 4 := Signature.clr 3 0 1

/-- 3D Conformal GA: Cl(4,1,0) -/
abbrev sigCGA3 : Signature 5 := Signature.clr 4 1 0

/-- Spacetime Algebra: Cl(1,3,0) -/
abbrev sigSTA : Signature 4 := Signature.clr 1 3 0

/-! ## Tests -/

#check @GAlgebra.mul
#check @sandwich
#check @normSq

end Grassmann
