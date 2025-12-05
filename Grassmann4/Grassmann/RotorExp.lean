/-
  Grassmann/RotorExp.lean - Exponential and logarithm for rotors

  Key formulas for Clifford algebra:
  - For bivector B with B² = -|B|²: exp(B) = cos(|B|) + sin(|B|)·B/|B|
  - For bivector B with B² = +|B|²: exp(B) = cosh(|B|) + sinh(|B|)·B/|B|
  - For bivector B with B² = 0:    exp(B) = 1 + B

  Rotors are elements of the even subalgebra: R = exp(B/2) for half-angle rotation.
  The sandwich product R·v·R† rotates vector v.
-/
import Grassmann.SparseMultivector

namespace Grassmann

/-! ## Scalar Functions for exp/log computation -/

/-- Factorial function for Taylor series -/
def factorial : Nat → Float
  | 0 => 1.0
  | n + 1 => (n + 1).toFloat * factorial n

/-- Taylor series for exp: Σ xⁿ/n! -/
def expTaylor (x : Float) (terms : Nat := 15) : Float :=
  let rec go (n : Nat) (xn : Float) (acc : Float) : Float :=
    match n with
    | 0 => acc
    | n + 1 =>
      let term := xn / factorial (terms - n)
      go n (xn * x) (acc + term)
  go terms 1.0 0.0

/-- Taylor series for sin: Σ (-1)ⁿx^(2n+1)/(2n+1)! -/
def sinTaylor (x : Float) (terms : Nat := 12) : Float :=
  let x2 := x * x
  let rec go (k : Nat) (xn : Float) (sign : Float) (acc : Float) : Float :=
    if k >= terms then acc
    else
      let term := sign * xn / factorial (2 * k + 1)
      go (k + 1) (xn * x2) (-sign) (acc + term)
  go 0 x 1.0 0.0

/-- Taylor series for cos: Σ (-1)ⁿx^(2n)/(2n)! -/
def cosTaylor (x : Float) (terms : Nat := 12) : Float :=
  let x2 := x * x
  let rec go (k : Nat) (xn : Float) (sign : Float) (acc : Float) : Float :=
    if k >= terms then acc
    else
      let term := sign * xn / factorial (2 * k)
      go (k + 1) (xn * x2) (-sign) (acc + term)
  go 0 1.0 1.0 0.0

/-- sinh(x) = (exp(x) - exp(-x))/2 via Taylor -/
def sinhTaylor (x : Float) (terms : Nat := 10) : Float :=
  let x2 := x * x
  let rec go (n : Nat) (xn : Float) (acc : Float) : Float :=
    match n with
    | 0 => acc
    | n + 1 =>
      let k := terms - n
      let term := xn * x / factorial (2 * k + 1)
      go n (xn * x2) (acc + term)
  go terms 1.0 0.0

/-- cosh(x) = (exp(x) + exp(-x))/2 via Taylor -/
def coshTaylor (x : Float) (terms : Nat := 10) : Float :=
  let x2 := x * x
  let rec go (n : Nat) (xn : Float) (acc : Float) : Float :=
    match n with
    | 0 => acc
    | n + 1 =>
      let k := terms - n
      let term := xn / factorial (2 * k)
      go n (xn * x2) (acc + term)
  go terms 1.0 0.0

/-! ## Exponential of Bivector -/

variable {n : ℕ} {sig : Signature n}

/-- Compute B² for a bivector (returns scalar part) -/
def bivectorSquare (B : MultivectorS sig Float) : Float :=
  (B * B).scalarPart

/-- Exponential of a pure bivector.
    Uses the appropriate formula based on B²:
    - B² < 0 (Euclidean): exp(B) = cos(|B|) + sin(|B|)·B/|B|
    - B² > 0 (hyperbolic): exp(B) = cosh(|B|) + sinh(|B|)·B/|B|
    - B² = 0 (degenerate): exp(B) = 1 + B -/
def expBivector (B : MultivectorS sig Float) : MultivectorS sig Float :=
  let B2 := bivectorSquare B
  let epsilon := 1e-10
  if B2.abs < epsilon then
    -- B² ≈ 0: exp(B) = 1 + B (nilpotent case)
    MultivectorS.scalar 1.0 + B
  else if B2 < 0 then
    -- B² = -|B|² (Euclidean/elliptic): exp(B) = cos + sin·B/|B|
    let norm := Float.sqrt (-B2)
    let c := cosTaylor norm
    let s := sinTaylor norm
    let Bnorm := B.smul (s / norm)
    MultivectorS.scalar c + Bnorm
  else
    -- B² = +|B|² (hyperbolic): exp(B) = cosh + sinh·B/|B|
    let norm := Float.sqrt B2
    let ch := coshTaylor norm
    let sh := sinhTaylor norm
    let Bnorm := B.smul (sh / norm)
    MultivectorS.scalar ch + Bnorm

/-- Exponential of a general multivector via Taylor series.
    exp(M) = Σ Mⁿ/n!
    Use for non-bivector elements or when the bivector formula isn't applicable. -/
def expTaylorMV (M : MultivectorS sig Float) (terms : Nat := 12) : MultivectorS sig Float :=
  let rec go (n : Nat) (Mn : MultivectorS sig Float) (acc : MultivectorS sig Float) : MultivectorS sig Float :=
    match n with
    | 0 => acc
    | n + 1 =>
      let k := terms - n
      let fact := factorial k
      let term := Mn.smul (1.0 / fact)
      go n (Mn * M) (acc + term)
  go terms (MultivectorS.scalar 1.0) MultivectorS.zero

/-! ## Logarithm of Rotor -/

/-- Extract bivector part of a multivector (grade 2 components).
    A blade has grade 2 if popcount(bits) = 2. -/
def bivectorPart (M : MultivectorS sig Float) : MultivectorS sig Float :=
  ⟨M.coeffs.foldl (init := Std.TreeMap.empty) fun acc idx coeff =>
    if popcount idx = 2 then acc.insert idx coeff else acc⟩

/-- Logarithm of a unit rotor R = cos(θ) + sin(θ)·B where B is a unit bivector.
    log(R) = θ·B = arccos(scalar part)·(bivector part normalized)
    Assumes R is a unit rotor (|R| = 1). -/
def logRotor (R : MultivectorS sig Float) : MultivectorS sig Float :=
  let s := R.scalarPart  -- cos(θ)
  let B := bivectorPart R  -- sin(θ)·B̂
  let B2 := bivectorSquare B
  let epsilon := 1e-10
  if B2.abs < epsilon then
    -- Pure scalar (identity rotor), log = 0
    MultivectorS.zero
  else if B2 < 0 then
    -- Euclidean case: sin²(θ) = -B²
    let sinTheta := Float.sqrt (-B2)
    let theta := Float.atan2 sinTheta s  -- arctan(sin/cos) = θ
    if sinTheta.abs < epsilon then
      MultivectorS.zero
    else
      B.smul (theta / sinTheta)  -- θ·B̂ = θ·B/sin(θ)
  else
    -- Hyperbolic case: sinh²(θ) = B²
    let sinhTheta := Float.sqrt B2
    -- For hyperbolic: cosh²(θ) - sinh²(θ) = 1
    -- So cosh(θ) = s, sinh(θ) = |B_norm|
    let theta := Float.log (s + sinhTheta)  -- arcsinh formula
    B.smul (theta / sinhTheta)

/-! ## Rotor Creation -/

/-- Create a rotor that rotates by angle θ in the plane defined by bivector B.
    The resulting rotor R satisfies: R·v·R† rotates v by 2θ in the B plane.
    So for a rotation by angle α, use makeRotor(B, α/2). -/
def makeRotor (B : MultivectorS sig Float) (halfAngle : Float) : MultivectorS sig Float :=
  expBivector (B.smul halfAngle)

/-- Spherical linear interpolation between two unit rotors.
    slerp(R1, R2, t) smoothly interpolates from R1 (t=0) to R2 (t=1). -/
def slerp (R1 R2 : MultivectorS sig Float) (t : Float) : MultivectorS sig Float :=
  -- R = R1 · exp(t · log(R1† · R2))
  let R1_rev := R1†ₛ
  let delta := R1_rev * R2
  let logDelta := logRotor delta
  let interpolated := expBivector (logDelta.smul t)
  R1 * interpolated

/-! ## Tests -/

-- Pi constant
def piConst : Float := 3.141592653589793

-- Test with R3 Euclidean signature
def R3test : Signature 3 := Signature.euclidean 3

-- Bivector e12
def e12_test : MultivectorS R3test Float :=
  let e1 := MultivectorS.basis (⟨0, by omega⟩ : Fin 3)
  let e2 := MultivectorS.basis (⟨1, by omega⟩ : Fin 3)
  e1 * e2

-- exp(π/4 · e12) should be cos(π/4) + sin(π/4)·e12 ≈ 0.707 + 0.707·e12
#eval! let θ := piConst / 4
       let R := expBivector (e12_test.smul θ)
       (R.scalarPart, R.coeffBlade ⟨BitVec.ofNat 3 3⟩)
-- Expected: approximately (0.707, 0.707)

-- Verify e12² = -1
#eval! bivectorSquare e12_test  -- Expected: -1.0

-- Test log(exp(B)) ≈ B
#eval! let B := e12_test.smul 0.5
       let R := expBivector B
       let B_back := logRotor R
       (B.coeffBlade ⟨BitVec.ofNat 3 3⟩,
        B_back.coeffBlade ⟨BitVec.ofNat 3 3⟩)
-- Expected: approximately (0.5, 0.5)

-- Test slerp
#eval! let R1 := MultivectorS.scalar 1.0  -- Identity rotor
       let R2 := expBivector (e12_test.smul (piConst / 4))  -- 45° rotation
       let Rmid := slerp R1 R2 0.5  -- Should be 22.5° rotation
       (Rmid.scalarPart, Rmid.coeffBlade ⟨BitVec.ofNat 3 3⟩)
-- Expected: cos(π/8) ≈ 0.924, sin(π/8) ≈ 0.383

/-! ## Closed-Form Exponential for Dense Multivectors

Port of Grassmann.jl's exp function for Multivector type (not just sparse).
-/

/-- Exponential of a bivector in dense Multivector representation.
    Uses the closed-form formula based on B². -/
def expBivectorDense [Ring F] [Div F]
    (B : Multivector sig F) : Multivector sig Float :=
  -- Get bivector part (grade 2)
  let B2 := B.gradeProject 2
  -- Compute B²
  let B2sq := (B2 * B2).scalarPart
  -- Convert to float for transcendentals
  sorry  -- Need Float instance for F

/-- Full exponential for dense Multivector (Float only).
    Handles mixed even/odd parts via series. -/
def expMultivector (M : Multivector sig Float) : Multivector sig Float :=
  let scalar := M.scalarPart
  let rest := M.sub (Multivector.scalar scalar)
  let restSq := (rest * rest).scalarPart
  let epsilon := 1e-10
  if Float.abs restSq < epsilon then
    -- Nilpotent: exp(M) = exp(s)(1 + rest)
    let es := Float.exp scalar
    (Multivector.scalar es).add (rest.smul es)
  else if restSq < 0 then
    -- Elliptic case: exp(M) = exp(s)(cos|r| + sin|r|·r/|r|)
    let norm := Float.sqrt (-restSq)
    let es := Float.exp scalar
    let c := Float.cos norm
    let s := Float.sin norm
    (Multivector.scalar (es * c)).add (rest.smul (es * s / norm))
  else
    -- Hyperbolic case: exp(M) = exp(s)(cosh|r| + sinh|r|·r/|r|)
    let norm := Float.sqrt restSq
    let es := Float.exp scalar
    let ch := Float.cosh norm
    let sh := Float.sinh norm
    (Multivector.scalar (es * ch)).add (rest.smul (es * sh / norm))

/-- Exponential series for general multivector (when closed form doesn't apply).
    exp(M) = Σ Mⁿ/n! -/
def expSeries (M : Multivector sig Float) (terms : Nat := 15) : Multivector sig Float :=
  let rec go (n : Nat) (Mn : Multivector sig Float) (acc : Multivector sig Float) : Multivector sig Float :=
    match n with
    | 0 => acc
    | n + 1 =>
      let k := terms - n
      let fact := factorial k
      let term := Mn.smul (1.0 / fact)
      go n (Mn * M) (acc.add term)
  go terms Multivector.one Multivector.zero

/-- Logarithm of a unit rotor (dense representation).
    log(R) = θ·B where R = cos(θ) + sin(θ)·B -/
def logRotorDense (R : Multivector sig Float) : Multivector sig Float :=
  let s := R.scalarPart
  let B := R.gradeProject 2  -- bivector part
  let Bsq := (B * B).scalarPart
  let epsilon := 1e-10
  if Float.abs Bsq < epsilon then
    Multivector.zero  -- Identity rotor
  else if Bsq < 0 then
    -- Euclidean: sin²(θ) = -B²
    let sinTheta := Float.sqrt (-Bsq)
    let theta := Float.atan2 sinTheta s
    if Float.abs sinTheta < epsilon then Multivector.zero
    else B.smul (theta / sinTheta)
  else
    -- Hyperbolic
    let sinhTheta := Float.sqrt Bsq
    let theta := Float.log (s + sinhTheta)
    B.smul (theta / sinhTheta)

/-- Create rotor for rotation by angle in the plane of bivector B (dense).
    The sandwich R·v·R† rotates v by 2×halfAngle. -/
def makeRotorDense (B : Multivector sig Float) (halfAngle : Float) : Multivector sig Float :=
  expMultivector (B.gradeProject 2 |>.smul halfAngle)

/-- Rotation in the e_i ∧ e_j plane -/
def rotorFromPlane (i j : Fin n) (halfAngle : Float) : Multivector sig Float :=
  let ei : Multivector sig Float := Multivector.basis i
  let ej : Multivector sig Float := Multivector.basis j
  let B := ei ⋀ᵐ ej
  expMultivector (B.smul halfAngle)

/-- Spherical linear interpolation (SLERP) for dense rotors -/
def slerpDense (R1 R2 : Multivector sig Float) (t : Float) : Multivector sig Float :=
  let R1rev := R1†
  let delta := R1rev * R2
  let logDelta := logRotorDense delta
  let interpolated := expMultivector (logDelta.smul t)
  R1 * interpolated

/-! ## Power and Sqrt for Rotors -/

/-- Power of a rotor: R^t = exp(t·log(R)) -/
def rotorPow (R : Multivector sig Float) (t : Float) : Multivector sig Float :=
  expMultivector ((logRotorDense R).smul t)

/-- Square root of a rotor: R^(1/2) -/
def rotorSqrt (R : Multivector sig Float) : Multivector sig Float :=
  rotorPow R 0.5

/-! ## Additional Dense Tests -/

-- Test dense exponential
#eval! let e12m : Multivector R3test Float := Multivector.ofBlade ⟨0b011⟩
       let θ := piConst / 4
       let R := expMultivector (e12m.smul θ)
       (R.scalarPart, R.coeff ⟨0b011⟩)
-- Expected: (cos(π/4), sin(π/4)) ≈ (0.707, 0.707)

-- Test rotor from plane
#eval! let R := rotorFromPlane (sig := R3test) ⟨0, by omega⟩ ⟨1, by omega⟩ (piConst / 4)
       (R.scalarPart, R.coeff ⟨0b011⟩)

#eval IO.println "✓ RotorExp module loaded"

end Grassmann
