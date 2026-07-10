/-
  Grassmann/CoeffOps.lean - Lawless coefficient operations

  Computational geometric-algebra kernels only need concrete arithmetic
  operations.  They do not need, and for IEEE `Float` cannot honestly have,
  the algebraic laws carried by `Ring`.
-/
import Mathlib.Algebra.Ring.Defs

namespace Grassmann

/-- Arithmetic operations required by computational multivector kernels.

`CoeffOps` deliberately contains no laws.  In particular, its `Float`
instance does not claim associativity, distributivity, or any other ring
property for IEEE floating-point arithmetic. -/
class CoeffOps (F : Type*)
    extends Zero F, One F, OfNat F 2, Add F, Sub F, Neg F, Mul F where

/-- Every genuine ring supplies the lawless computational interface. -/
instance {F : Type*} [Ring F] : CoeffOps F where

/-- IEEE `Float` supplies arithmetic operations, but no ring laws. -/
instance : CoeffOps Float where

end Grassmann
