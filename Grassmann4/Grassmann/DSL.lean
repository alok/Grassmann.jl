/-
  Grassmann/DSL.lean - Elegant Domain-Specific Language for Grassmann Algebra

  This module provides clean, mathematical syntax for working with
  geometric/Clifford algebras in Lean 4.

  ## Features

  ### Subscript Notation for Blades
  ```
  e₁, e₂, e₃     -- Basis vectors
  e₁₂, e₁₃, e₂₃  -- Bivectors
  e₁₂₃           -- Trivector
  e[10], e[1,15] -- Fallback for indices > 9
  ```

  ### Algebra Context Blocks
  ```
  Cl(3,0,0) {
    let v := e₁ + e₂
    v ⊛ v
  }

  R3 { e₁ ⋀ e₂ }      -- Shortcut for Cl(3,0,0)
  PGA3 { ... }         -- Cl(3,0,1)
  CGA3 { ... }         -- Cl(4,1,0)
  ```

  ### Polymorphic Operations
  All operations work across Dense, Sparse, and Truncated representations
  via the GAlgebra typeclass.

  ## Usage

  ```
  import Grassmann.DSL

  open Grassmann Grassmann.DSL

  #eval R3 {
    let v := 2 • e₁ + 3 • e₂
    let biv := e₁₂
    (v ⊛ biv).scalarPart
  }
  ```
-/
import Grassmann.GATypeclass
import Grassmann.DSL.Subscript
import Grassmann.DSL.Context

namespace Grassmann.DSL

-- Re-export key components
export Grassmann (
  Signature
  GAlgebra GABasis GABlade
  sandwich normSq
  sigR3 sigPGA3 sigCGA3 sigSTA
)

end Grassmann.DSL
