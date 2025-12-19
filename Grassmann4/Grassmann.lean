-- Root import file for Grassmann Algebra library

-- Core infrastructure
import Grassmann.Proof         -- SciLean-style sorry_proof, Float Ring/Field
import Grassmann.Linearity     -- Debug helpers for exclusivity / in-place updates
import Grassmann.BitMask
import Grassmann.Manifold
import Grassmann.Blade
import Grassmann.SimplexChain  -- Chain type from Grassmann.jl
import Grassmann.Parity
import Grassmann.Products
import Grassmann.Notation

-- Multivector representations
import Grassmann.DataArray        -- Float "plain data" buffers for hot paths
import Grassmann.Multivector      -- Dense 2^n array (proof-friendly)
import Grassmann.MV               -- Unified DataArray-backed multivector (recommended)
import Grassmann.MultivectorArray
import Grassmann.SparseMultivector -- Sparse TreeMap
import Grassmann.TruncatedMV       -- Truncated grades for high-dim
import Grassmann.EvenMV            -- Kernel tables for even-grade operations
import Grassmann.Storage           -- Storage backend abstraction
import Grassmann.Repr              -- MultivectorRepr typeclass
import Grassmann.PrettyPrint       -- Unicode pretty-printing

-- Algebraic structures
import Grassmann.Versor
import Grassmann.Spinor            -- Spinors (MV-backed)
import Grassmann.RotorExp

-- Geometric algebras
import Grassmann.CGA              -- Conformal GA (hardcoded 5D)
import Grassmann.PGA              -- Projective GA (MV-backed)
import Grassmann.CGAGen           -- Generic n-dimensional CGA
import Grassmann.SignatureGen     -- Signature generation

-- Applications
import Grassmann.LinearAlgebra
import Grassmann.Calculus
import Grassmann.SpecialFunctions
import Grassmann.VectorUtils        -- Generic n-dimensional utilities
import Grassmann.R3Utils            -- 3D-specific conveniences
import Grassmann.Visualization

-- Theorems and proofs
import Grassmann.Theorems
import Grassmann.AnchorTheorems

-- Performance optimization
import Grassmann.SignTables        -- Precomputed sign tables
import Grassmann.GradeSet          -- Compile-time grade tracking
import Grassmann.StaticOpt         -- Static optimization patterns
import Grassmann.BladeIndex        -- Sparse index iteration

-- Code generation
import Grassmann.MetalCodegen
import Grassmann.GANotation

-- Domain-Specific Language
import Grassmann.DSL
import Grassmann.DSLDemo
import Grassmann.GATypeclass

-- NOTE: Development-time checks and `#eval`-heavy demo files live under
-- `Grassmann.All` so that `import Grassmann` stays lightweight for downstream
-- users and for compilation performance.

-- DEPRECATED: The following files are no longer imported and will be removed:
-- - Grassmann.MultivectorDA   (use Grassmann.MV instead)
-- - Grassmann.GradedMVDA      (use Grassmann.MV with Parity instead)
-- - Grassmann.EvenMVDA        (use Grassmann.MV sig .even instead)
