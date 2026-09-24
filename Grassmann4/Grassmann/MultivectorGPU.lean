/-
  Grassmann/MultivectorGPU.lean - DataArrayN-backed multivector for GPU operations

  This module provides Float-specialized multivectors backed by SciLean's DataArrayN
  for efficient GPU computation via Metal. Use this for:
  - Batch physics simulations
  - Collision detection
  - Constraint solving
  - Any high-performance numeric work

  The generic `Multivector sig F` is still used for proofs and flexibility.
-/
import Grassmann.DataArray
import Grassmann.Multivector
import Grassmann.PGA
import Grassmann.Physics
import SciLean.Data.DataArray

namespace Grassmann.GPU

open SciLean
open Grassmann

/-! ## GPU-Optimized Multivector Type -/

/-- GPU-optimized multivector backed by DataArrayN.
    Fixed to Float coefficients for Metal/GPU compatibility.
    Signature info is at type level only (not stored). -/
structure MultivectorGPU (n : ℕ) where
  /-- DataArrayN backing with 2^n Float coefficients -/
  data : GrassmannArray n
  deriving Inhabited

namespace MultivectorGPU

variable {n : ℕ}

/-! ### Constructors -/

/-- Zero multivector -/
@[inline]
def zero : MultivectorGPU n :=
  ⟨GrassmannArray.zeros n⟩

/-- Scalar multivector -/
@[inline]
def scalar (x : Float) : MultivectorGPU n :=
  ⟨GrassmannArray.scalar n x⟩

/-- Unit scalar -/
@[inline]
def one : MultivectorGPU n := scalar 1.0

/-- Basis blade at index i (i = bitmask) -/
@[inline]
def basis (i : Nat) : MultivectorGPU n :=
  let arr := GrassmannArray.zeros n
  ⟨arr.set! i 1.0⟩

/-! ### Coefficient Access -/

/-- Get coefficient at blade index -/
@[inline]
def get (m : MultivectorGPU n) (i : Nat) : Float :=
  m.data.get! i

/-- Set coefficient at blade index -/
@[inline]
def set (m : MultivectorGPU n) (i : Nat) (x : Float) : MultivectorGPU n :=
  ⟨m.data.set! i x⟩

/-- Scalar part (index 0) -/
@[inline]
def scalarPart (m : MultivectorGPU n) : Float :=
  m.get 0

/-! ### Arithmetic Operations -/

/-- Addition -/
@[inline]
def add (a b : MultivectorGPU n) : MultivectorGPU n :=
  ⟨a.data + b.data⟩

/-- Subtraction -/
@[inline]
def sub (a b : MultivectorGPU n) : MultivectorGPU n :=
  ⟨a.data - b.data⟩

/-- Scalar multiplication -/
@[inline]
def smul (c : Float) (m : MultivectorGPU n) : MultivectorGPU n :=
  ⟨c • m.data⟩

/-- Negation -/
@[inline]
def neg (m : MultivectorGPU n) : MultivectorGPU n :=
  ⟨-m.data⟩

instance : Add (MultivectorGPU n) := ⟨add⟩
instance : Sub (MultivectorGPU n) := ⟨sub⟩
instance : Neg (MultivectorGPU n) := ⟨neg⟩
instance : HMul Float (MultivectorGPU n) (MultivectorGPU n) := ⟨smul⟩

/-! ### Conversion from generic Multivector -/

/-- Convert generic Multivector to GPU version -/
def ofMultivector {sig : Signature n} (m : Multivector sig Float) : MultivectorGPU n :=
  ⟨GrassmannArray.ofFn m.coeffs⟩

/-- Convert GPU multivector to generic -/
def toMultivector (sig : Signature n) (m : MultivectorGPU n) : Multivector sig Float :=
  ⟨fun i => m.get i.val⟩

end MultivectorGPU

/-! ## Batch Operations for GPU

These prepare data for Metal kernel dispatch.
-/

/-- Batch of multivectors for GPU operations -/
abbrev MultivectorBatch (n : ℕ) := Array (MultivectorGPU n)

/-- Convert Array of generic multivectors to GPU batch -/
def toBatch {n : ℕ} {sig : Signature n}
    (arr : Array (Multivector sig Float)) : MultivectorBatch n :=
  arr.map MultivectorGPU.ofMultivector

/-- Convert GPU batch back to generic multivectors -/
def fromBatch {n : ℕ} (sig : Signature n)
    (batch : MultivectorBatch n) : Array (Multivector sig Float) :=
  batch.map (MultivectorGPU.toMultivector sig)

/-! ## PGA3-Specific GPU Types -/

/-- PGA3 motor for GPU (16 coefficients) -/
abbrev MotorGPU := MultivectorGPU 4

/-- PGA3 point for GPU -/
abbrev PointGPU := MultivectorGPU 4

namespace MotorGPU

/-- Identity motor (scalar = 1) -/
def identity : MotorGPU := MultivectorGPU.scalar 1.0

/-- Create motor from position (translation only) -/
def fromPosition (x y z : Float) : MotorGPU :=
  let m := MultivectorGPU.scalar 1.0
  -- Translation bivectors: e01, e02, e03 at indices 3, 5, 9
  let m := m.set 3 (0.5 * x)
  let m := m.set 5 (0.5 * y)
  let m := m.set 9 (0.5 * z)
  m

/-- Extract position from motor -/
def toPosition (m : MotorGPU) : Float × Float × Float :=
  (2.0 * m.get 3, 2.0 * m.get 5, 2.0 * m.get 9)

end MotorGPU

/-! ## Rigid Body GPU Batch -/

/-- GPU-optimized rigid body state -/
structure RigidBodyGPU where
  /-- Motor (pose) -/
  motor : MotorGPU
  /-- Linear velocity (x, y, z) -/
  linVel : Float × Float × Float
  /-- Angular velocity (xy, xz, yz) -/
  angVel : Float × Float × Float
  /-- Inverse mass -/
  invMass : Float
  deriving Inhabited

namespace RigidBodyGPU

/-- Convert from CPU rigid body -/
def ofRigidBody (body : Physics.RigidBody) : RigidBodyGPU :=
  { motor := MultivectorGPU.ofMultivector body.motor
    linVel := (body.velocity.v01, body.velocity.v02, body.velocity.v03)
    angVel := (body.velocity.omega12, body.velocity.omega13, body.velocity.omega23)
    invMass := 1.0 / body.mass }

/-- Convert to CPU rigid body -/
def toRigidBody (body : RigidBodyGPU) : Physics.RigidBody :=
  { motor := MultivectorGPU.toMultivector PGA3 body.motor
    velocity := {
      omega12 := body.angVel.1
      omega13 := body.angVel.2.1
      omega23 := body.angVel.2.2
      v01 := body.linVel.1
      v02 := body.linVel.2.1
      v03 := body.linVel.2.2
    }
    mass := 1.0 / body.invMass
    invInertia := 1.0 }

end RigidBodyGPU

/-- Batch of rigid bodies for GPU physics -/
abbrev RigidBodyBatch := Array RigidBodyGPU

/-! ## Sphere for GPU Collision -/

/-- Sphere representation for GPU collision detection -/
structure SphereGPU where
  x : Float
  y : Float
  z : Float
  radius : Float
  deriving Inhabited, Repr

/-- Collision result from GPU -/
structure CollisionResultGPU where
  i : Nat
  j : Nat
  penetration : Float
  normalX : Float
  normalY : Float
  normalZ : Float
  contactX : Float
  contactY : Float
  contactZ : Float
  deriving Inhabited, Repr

/-! ## Tests

Note: #eval! tests are commented out due to ByteArray.replicate extern issue.
The types and functions are still verified via type checking.
-/

-- Type checks pass - functions are well-typed
#check MultivectorGPU.scalar (n := 3)
#check MultivectorGPU.basis (n := 3)
#check MotorGPU.fromPosition
#check RigidBodyGPU.ofRigidBody
#check RigidBodyGPU.toRigidBody

end Grassmann.GPU
