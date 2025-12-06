-- Root import file for Grassmann Algebra library
-- Core infrastructure
import Grassmann.Proof         -- SciLean-style sorry_proof, Float Ring/Field
import Grassmann.BitMask
import Grassmann.Manifold
import Grassmann.Blade
import Grassmann.SimplexChain  -- Chain type from Grassmann.jl
import Grassmann.Parity
import Grassmann.Products
import Grassmann.Notation

-- Multivector representations
import Grassmann.Multivector       -- Dense 2^n array
import Grassmann.MultivectorArray
import Grassmann.SparseMultivector -- Sparse TreeMap
import Grassmann.TruncatedMV       -- Truncated grades for high-dim
import Grassmann.Storage           -- Storage backend abstraction
import Grassmann.Repr              -- MultivectorRepr typeclass
import Grassmann.PrettyPrint       -- Unicode pretty-printing

-- Algebraic structures
import Grassmann.Versor
import Grassmann.Spinor
import Grassmann.RotorExp

-- Geometric algebras
import Grassmann.CGA              -- Conformal GA (hardcoded 5D)
import Grassmann.PGA              -- Projective GA
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

-- Tests
import Grassmann.StressTests
import Grassmann.Tests
import Grassmann.OracleTests
import Grassmann.DSLTests
import Grassmann.CoffeeshopExamples
