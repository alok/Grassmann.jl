/-
  Grassmann/Couple.lean - Scalar + Single Blade type

  Port of Grassmann.jl's Couple{V,B,T} type.

  A Couple is like a generalized complex number: a scalar plus a single blade.
  This is useful for:
  - Complex numbers: scalar + e₁₂ where e₁₂² = -1
  - Split-complex (hyperbolic): scalar + e₁₂ where e₁₂² = +1
  - Dual numbers: scalar + e₀ where e₀² = 0

  The key insight is that the algebraic structure depends on B²:
  - If B² = -1: behaves like ℂ (complex)
  - If B² = +1: behaves like split-complex (has zero divisors)
  - If B² = 0: behaves like dual numbers (nilpotent)
-/
import Grassmann.Multivector

namespace Grassmann

variable {n : ℕ} {sig : Signature n} {F : Type*}

/-! ## Couple Type

Like Complex{T} but the imaginary unit is any blade B.
Stores: a + b·B where a, b : F and B is a fixed basis blade.
-/

/-- A Couple is a scalar plus a scaled blade: a + b·B.
    The blade B is fixed at the type level via its bitmask.
    This is more efficient than full Multivector when only one blade is needed. -/
structure Couple (sig : Signature n) (bladeBits : BitVec n) (F : Type*) where
  /-- The scalar (real) part -/
  re : F
  /-- The blade (imaginary) coefficient -/
  im : F
  deriving Repr

namespace Couple

variable {bladeBits : BitVec n} [Ring F]

/-- The blade this Couple uses -/
def blade : Blade sig := ⟨bladeBits⟩

/-- Zero couple -/
def zero : Couple sig bladeBits F := ⟨0, 0⟩

/-- Unit scalar (real 1) -/
def one : Couple sig bladeBits F := ⟨1, 0⟩

/-- Pure scalar -/
def scalar (x : F) : Couple sig bladeBits F := ⟨x, 0⟩

/-- Pure blade (imaginary unit) -/
def pureIm (x : F) : Couple sig bladeBits F := ⟨0, x⟩

/-- The "imaginary unit" B with coefficient 1 -/
def imUnit : Couple sig bladeBits F := ⟨0, 1⟩

/-- Create from scalar and blade coefficient -/
def mk' (a b : F) : Couple sig bladeBits F := ⟨a, b⟩

/-- Addition -/
def add (x y : Couple sig bladeBits F) : Couple sig bladeBits F :=
  ⟨x.re + y.re, x.im + y.im⟩

/-- Subtraction -/
def sub (x y : Couple sig bladeBits F) : Couple sig bladeBits F :=
  ⟨x.re - y.re, x.im - y.im⟩

/-- Negation -/
def neg (x : Couple sig bladeBits F) : Couple sig bladeBits F :=
  ⟨-x.re, -x.im⟩

/-- Scalar multiplication -/
def smul (s : F) (x : Couple sig bladeBits F) : Couple sig bladeBits F :=
  ⟨s * x.re, s * x.im⟩

/-- Compute B² using the signature.
    Returns the sign: +1, -1, or 0 -/
def bladeSquareSign : Int :=
  let b : Blade sig := ⟨bladeBits⟩
  geometricSign sig b b

/-- Multiplication: (a + bB)(c + dB) = (ac + bd·B²) + (ad + bc)B
    The key is B² which depends on the signature. -/
def mul (x y : Couple sig bladeBits F) : Couple sig bladeBits F :=
  let bsq := bladeSquareSign (sig := sig) (bladeBits := bladeBits)
  -- B² can be +1, -1, or 0
  -- (a + bB)(c + dB) = ac + adB + bcB + bd·B²
  --                  = (ac + bd·B²) + (ad + bc)B
  let realPart := x.re * y.re + (if bsq == 1 then x.im * y.im
                                 else if bsq == -1 then -(x.im * y.im)
                                 else 0)  -- bsq == 0, nilpotent
  let imPart := x.re * y.im + x.im * y.re
  ⟨realPart, imPart⟩

/-- Conjugate: a + bB → a - bB (negate the blade part) -/
def conj (x : Couple sig bladeBits F) : Couple sig bladeBits F :=
  ⟨x.re, -x.im⟩

/-- Squared norm: x * conj(x) = a² - b²·B²
    For complex (B² = -1): a² + b²
    For split-complex (B² = +1): a² - b² (can be negative!)
    For dual (B² = 0): a² -/
def normSq (x : Couple sig bladeBits F) : F :=
  let bsq := bladeSquareSign (sig := sig) (bladeBits := bladeBits)
  if bsq == 1 then x.re * x.re - x.im * x.im        -- Split-complex
  else if bsq == -1 then x.re * x.re + x.im * x.im  -- Complex
  else x.re * x.re                                   -- Dual

/-- Inverse (when it exists): x⁻¹ = conj(x) / normSq(x) -/
def inv [Div F] (x : Couple sig bladeBits F) : Couple sig bladeBits F :=
  let nsq := x.normSq
  ⟨x.re / nsq, -x.im / nsq⟩

/-- Division -/
def div [Div F] (x y : Couple sig bladeBits F) : Couple sig bladeBits F :=
  x.mul y.inv

/-- Convert to full Multivector -/
def toMultivector (x : Couple sig bladeBits F) : Multivector sig F :=
  (Multivector.scalar x.re).add ((Multivector.ofBlade ⟨bladeBits⟩).smul x.im)

/-- Check if this is a complex-like algebra (B² = -1) -/
def isComplex : Bool := bladeSquareSign (sig := sig) (bladeBits := bladeBits) == -1

/-- Check if this is a split-complex algebra (B² = +1) -/
def isSplitComplex : Bool := bladeSquareSign (sig := sig) (bladeBits := bladeBits) == 1

/-- Check if this is a dual number algebra (B² = 0) -/
def isDual : Bool := bladeSquareSign (sig := sig) (bladeBits := bladeBits) == 0

instance : Zero (Couple sig bladeBits F) := ⟨zero⟩
instance : One (Couple sig bladeBits F) := ⟨one⟩
instance : Add (Couple sig bladeBits F) := ⟨add⟩
instance : Sub (Couple sig bladeBits F) := ⟨sub⟩
instance : Neg (Couple sig bladeBits F) := ⟨neg⟩
instance : Mul (Couple sig bladeBits F) := ⟨mul⟩
instance : SMul F (Couple sig bladeBits F) := ⟨smul⟩

end Couple

/-! ## Common Couple Types -/

/-- Complex numbers as Couple over Cl(0,1) with blade e₁ where e₁² = -1 -/
abbrev Complex' (F : Type*) := Couple ℂ_sig (0b1 : BitVec 1) F

/-- Split-complex (hyperbolic) numbers: scalar + j where j² = +1 -/
abbrev SplitComplex (F : Type*) := Couple R1 (0b1 : BitVec 1) F

/-- Dual numbers: scalar + ε where ε² = 0 -/
abbrev DualNumber (F : Type*) := Couple (Signature.clr 0 0 1) (0b1 : BitVec 1) F

/-- Quaternion-like: use e₁₂ bivector in Cl(0,2) -/
abbrev QuaternionI (F : Type*) := Couple ℍ_sig (0b11 : BitVec 2) F

/-! ## Gaussian Integers -/

/-- Gaussian integers: Complex' Int -/
abbrev GaussianInteger := Complex' Int

namespace GaussianInteger

/-- Create a Gaussian integer a + bi -/
def mk (a b : Int) : GaussianInteger := ⟨a, b⟩

/-- The Gaussian integer i -/
def i : GaussianInteger := ⟨0, 1⟩

/-- Gaussian integer norm (always non-negative) -/
def norm (z : GaussianInteger) : Int := z.re * z.re + z.im * z.im

end GaussianInteger

/-! ## Tests -/

section Tests

-- Complex-like multiplication: (1 + i)(1 + i) = 2i where i² = -1
#eval let z : Complex' Int := ⟨1, 1⟩
      let zz := z * z
      (zz.re, zz.im)  -- (0, 2) since (1+i)² = 1 + 2i + i² = 1 + 2i - 1 = 2i

-- Split-complex: (1 + j)(1 + j) = 2 + 2j where j² = +1
#eval let z : SplitComplex Int := ⟨1, 1⟩
      let zz := z * z
      (zz.re, zz.im)  -- (2, 2) since (1+j)² = 1 + 2j + j² = 1 + 2j + 1 = 2 + 2j

-- Dual: (1 + ε)(1 + ε) = 1 + 2ε where ε² = 0
#eval let z : DualNumber Int := ⟨1, 1⟩
      let zz := z * z
      (zz.re, zz.im)  -- (1, 2) since (1+ε)² = 1 + 2ε + ε² = 1 + 2ε

-- Complex conjugate and norm
#eval let z : Complex' Int := ⟨3, 4⟩
      z.normSq  -- 25 = 3² + 4²

-- Split-complex "norm" (not always positive!)
#eval let z : SplitComplex Int := ⟨3, 4⟩
      z.normSq  -- -7 = 3² - 4² (can be negative!)

-- Gaussian integer arithmetic
#eval let z := GaussianInteger.mk 3 4
      let w := GaussianInteger.mk 1 2
      let sum := z + w
      (sum.re, sum.im)  -- (4, 6)

#eval GaussianInteger.norm (GaussianInteger.mk 3 4)  -- 25

-- Type checks
#eval @Couple.isComplex 1 ℂ_sig (0b1 : BitVec 1)  -- true
#eval @Couple.isSplitComplex 1 R1 (0b1 : BitVec 1)  -- true

end Tests

/-! ## Phasor Type

A Phasor represents r·exp(iθ·B) = r·(cos(θ) + sin(θ)·B) for a blade B.
In polar form: magnitude r and angle θ (stored as imaginary part).

This is more efficient than Couple for rotations since we store
log coordinates (r, θ) instead of Cartesian (re, im).
-/

/-- A Phasor stores a complex-like value in polar form: r·exp(iθ·B).
    - `radius` is the magnitude r
    - `angle` is the phase θ (in radians)
    - B is the blade (from the type parameter bladeBits) -/
structure Phasor (sig : Signature n) (bladeBits : BitVec n) (F : Type*) where
  /-- The magnitude r -/
  radius : F
  /-- The angle θ in radians -/
  angle : F
  deriving Repr

namespace Phasor

variable {n : ℕ} {sig : Signature n} {bladeBits : BitVec n} {F : Type*}

/-- The blade this Phasor uses -/
def blade : Blade sig := ⟨bladeBits⟩

/-- Zero phasor -/
def zero [Zero F] : Phasor sig bladeBits F := ⟨0, 0⟩

/-- Unit phasor (r=1, θ=0) -/
def one [One F] [Zero F] : Phasor sig bladeBits F := ⟨1, 0⟩

/-- Create from polar coordinates -/
def polar (r θ : F) : Phasor sig bladeBits F := ⟨r, θ⟩

/-- Convert to Couple (Cartesian form) -/
def toCouple (p : Phasor sig bladeBits Float) : Couple sig bladeBits Float :=
  let c := Float.cos p.angle
  let s := Float.sin p.angle
  ⟨p.radius * c, p.radius * s⟩

/-- Create from Couple (requires computing atan2 and sqrt) -/
def ofCouple (c : Couple sig bladeBits Float) : Phasor sig bladeBits Float :=
  let r := Float.sqrt (c.re * c.re + c.im * c.im)
  let θ := Float.atan2 c.im c.re
  ⟨r, θ⟩

/-- Multiplication in polar form: (r₁, θ₁) × (r₂, θ₂) = (r₁r₂, θ₁+θ₂) -/
def mul [Mul F] [Add F] (p q : Phasor sig bladeBits F) : Phasor sig bladeBits F :=
  ⟨p.radius * q.radius, p.angle + q.angle⟩

/-- Division in polar form: (r₁, θ₁) / (r₂, θ₂) = (r₁/r₂, θ₁-θ₂) -/
def div [Div F] [Sub F] (p q : Phasor sig bladeBits F) : Phasor sig bladeBits F :=
  ⟨p.radius / q.radius, p.angle - q.angle⟩

/-- Conjugate: (r, θ) → (r, -θ) -/
def conj [Neg F] (p : Phasor sig bladeBits F) : Phasor sig bladeBits F :=
  ⟨p.radius, -p.angle⟩

/-- Power: (r, θ)^n = (r^n, n·θ) -/
def pow (p : Phasor sig bladeBits Float) (n : Float) : Phasor sig bladeBits Float :=
  ⟨Float.pow p.radius n, n * p.angle⟩

/-- Square root -/
def sqrt (p : Phasor sig bladeBits Float) : Phasor sig bladeBits Float :=
  ⟨Float.sqrt p.radius, p.angle / 2⟩

instance [Mul F] [Add F] : Mul (Phasor sig bladeBits F) := ⟨mul⟩
instance [Div F] [Sub F] : Div (Phasor sig bladeBits F) := ⟨div⟩

end Phasor

/-- Angle notation: ∠(r, θ) creates a Phasor with given signature and blade bits -/
def angle {n : Nat} (sig : Signature n) (bladeBits : BitVec n) (r θ : F) : Phasor sig bladeBits F := ⟨r, θ⟩

-- Note: The ∠ notation is context-dependent - use Phasor.mk directly for clarity

/-! ## Quaternion Extras

The quaternion basis elements i, j, k can be represented as bivectors
in Cl(0,2) or specific blades in Cl(0,3).

In Cl(0,2): e₁² = e₂² = -1, so e₁e₂ is the "k" direction
In standard quaternion convention:
  i² = j² = k² = ijk = -1
-/

/-- Quaternion type: uses Cl(0,2) with blade e₁₂ as the "complex structure" -/
abbrev Quaternion (F : Type*) := Couple ℍ_sig (0b11 : BitVec 2) F

namespace Quaternion

variable {F : Type*} [Ring F]

/-- Quaternion from scalar and vector parts -/
def mk (w x y z : F) : Quaternion F × Quaternion F :=
  -- w + xi + yj + zk represented as pair of couples
  -- Real part uses scalar, imaginary uses e12
  (⟨w, x⟩, ⟨y, z⟩)

/-- Pure imaginary quaternion i (corresponds to e₁ in GA) -/
def qi : Quaternion Int := ⟨0, 1⟩

/-- Hamilton's i, j, k as basis elements.
    Note: Full quaternion arithmetic requires 4 components.
    For a complete implementation, use Multivector over ℍ_sig. -/
def basis : Unit := ()

end Quaternion

-- Standard quaternion basis elements as multivector blades
section QuaternionBasis

/-- Quaternion i: e₁ in Cl(0,2), squares to -1 -/
def 𝕚 : Blade ℍ_sig := ⟨0b01⟩

/-- Quaternion j: e₂ in Cl(0,2), squares to -1 -/
def 𝕛 : Blade ℍ_sig := ⟨0b10⟩

/-- Quaternion k: e₁e₂ in Cl(0,2), squares to -1 -/
def 𝕜 : Blade ℍ_sig := ⟨0b11⟩

-- Verify: 𝕚² = 𝕛² = 𝕜² = -1
#eval geometricSign ℍ_sig 𝕚 𝕚  -- -1
#eval geometricSign ℍ_sig 𝕛 𝕛  -- -1
#eval geometricSign ℍ_sig 𝕜 𝕜  -- -1

-- Verify: 𝕚𝕛 = 𝕜
#eval let prod := geometricProductBlades 𝕚 𝕛
      match prod with
      | .nonzero s b => (s, b.bits.toNat)
      | .zero => (0, 0)  -- (1, 3) means +𝕜

end QuaternionBasis

/-! ## Phasor Tests -/

section PhasorTests

-- Create a phasor with r=2, θ=π/4
#eval let p : Phasor ℂ_sig (0b1 : BitVec 1) Float := ⟨2.0, 0.785398⟩  -- π/4 ≈ 0.785
      p.toCouple  -- Should be approximately (√2, √2) ≈ (1.414, 1.414)

-- Phasor multiplication: (2, π/4) × (3, π/6) = (6, 5π/12)
#eval let p1 : Phasor ℂ_sig (0b1 : BitVec 1) Float := ⟨2.0, 0.785398⟩
      let p2 : Phasor ℂ_sig (0b1 : BitVec 1) Float := ⟨3.0, 0.523599⟩
      let prod := p1 * p2
      (prod.radius, prod.angle)  -- (6.0, 1.309)

end PhasorTests

end Grassmann
