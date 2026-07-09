/-
  Grassmann/Reference.lean - opt-in dense and extended API

  This module preserves the broad Lean 4 port surface without making its
  proof placeholders, dense allocations, or development-oriented utilities a
  transitive dependency of `import Grassmann`.

  The generic `Multivector` model remains valuable as the readable behavioral
  reference for packed kernels.  It currently imports `Grassmann.Proof`, whose
  Float algebra instances are axiom-backed; do not mistake this aggregation
  module for the supported proof-free runtime.
-/
import Grassmann

-- Dense/reference interoperability and alternative representations.
import Grassmann.MVDense
import Grassmann.MultivectorArray
import Grassmann.SparseMultivector
import Grassmann.TruncatedMV
import Grassmann.Storage
import Grassmann.Repr
import Grassmann.PrettyPrint

-- Versors and extended geometric-algebra models.
import Grassmann.Versor
import Grassmann.Spinor
import Grassmann.RotorExp
import Grassmann.PGA
import Grassmann.PGATransforms
import Grassmann.CGA
import Grassmann.CGAGen
import Grassmann.SignatureGen

-- Dense utilities and optimization/reference infrastructure.
import Grassmann.LinearAlgebra
import Grassmann.Calculus
import Grassmann.SpecialFunctions
import Grassmann.VectorUtils
import Grassmann.R3Utils
import Grassmann.Visualization
import Grassmann.SignTables
import Grassmann.GradeSet
import Grassmann.BladeIndex
import Grassmann.GANotation
import Grassmann.DSL
