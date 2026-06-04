/-
  Grassmann/NativeVector.lean - Native Lean Vector-backed multivectors

  This is the intentionally simple starter representation for the Lean 4 port:
  coefficients live in Lean's built-in `Vector` type, indexed by blade bitmask.
  It is not the fastest backend; it is the small, inspectable baseline that is
  easy to plot, test, and compare against the Julia-era implementation.
-/
import Grassmann.Products
import Grassmann.GATypeclass

namespace Grassmann

/-- Full multivector with coefficients stored in Lean's native `Vector`.

The coefficient at index `k` is the coefficient of the basis blade whose bitmask
is `k`. For example, in R3: `0` is scalar, `1` is e1, `2` is e2, `3` is e12,
and `7` is e123.
-/
structure NativeMV (sig : Signature n) where
  coeffs : Vector Float (2 ^ n)
  deriving Repr

namespace NativeMV

variable {n : Nat} {sig : Signature n}

/-- Zero multivector. -/
@[inline]
def zero (sig : Signature n) : NativeMV sig :=
  ⟨Vector.replicate (2 ^ n) 0.0⟩

/-- Scalar multivector. -/
@[inline]
def scalar (sig : Signature n) (x : Float) : NativeMV sig :=
  ⟨Vector.ofFn fun i => if i.val = 0 then x else 0.0⟩

/-- Unit scalar. -/
@[inline]
def one (sig : Signature n) : NativeMV sig := scalar sig 1.0

/-- Get a coefficient by blade bitmask. Out-of-range masks read as zero. -/
@[inline]
def coeff (m : NativeMV sig) (bladeMask : Nat) : Float :=
  if h : bladeMask < 2 ^ n then
    m.coeffs.get ⟨bladeMask, h⟩
  else
    0.0

/-- Set a coefficient by blade bitmask. Out-of-range masks are ignored. -/
@[inline]
def setCoeff (m : NativeMV sig) (bladeMask : Nat) (x : Float) : NativeMV sig :=
  if h : bladeMask < 2 ^ n then
    ⟨m.coeffs.set bladeMask x h⟩
  else
    m

/-- Basis blade with coefficient 1. -/
@[inline]
def blade (sig : Signature n) (bladeMask : Nat) : NativeMV sig :=
  (zero sig).setCoeff bladeMask 1.0

/-- Basis vector e_i. -/
@[inline]
def basisVector (sig : Signature n) (i : Fin n) : NativeMV sig :=
  blade sig (1 <<< i.val)

/-- Build from `(bladeMask, coefficient)` pairs. -/
@[inline]
def ofPairs (sig : Signature n) (pairs : List (Nat × Float)) : NativeMV sig :=
  pairs.foldl (init := zero sig) fun acc (mask, x) => acc.setCoeff mask x

/-- Convert to an ordinary array for debugging and export. -/
@[inline]
def toArray (m : NativeMV sig) : Array Float := m.coeffs.toArray

/-- Add two multivectors. -/
@[inline]
def add (a b : NativeMV sig) : NativeMV sig :=
  ⟨Vector.zipWith (fun x y => x + y) a.coeffs b.coeffs⟩

/-- Negate a multivector. -/
@[inline]
def neg (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.map (fun x => -x) m.coeffs⟩

/-- Subtract two multivectors. -/
@[inline]
def sub (a b : NativeMV sig) : NativeMV sig := add a (neg b)

/-- Scalar multiplication. -/
@[inline]
def smul (x : Float) (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.map (fun c => x * c) m.coeffs⟩

/-- Scalar part, the coefficient of the grade-0 basis blade. -/
@[inline]
def scalarPart (m : NativeMV sig) : Float :=
  m.coeff 0

/-- Reverse operation. Grade `k` gets sign `(-1)^(k*(k-1)/2)`. -/
@[inline]
def reverse (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun i =>
    let k := popcount i.val
    let sign := if (k * (k - 1) / 2) % 2 = 0 then 1.0 else -1.0
    sign * m.coeffs.get i⟩

/-- Grade involution. Grade `k` gets sign `(-1)^k`. -/
@[inline]
def involute (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun i =>
    let k := popcount i.val
    let sign := if k % 2 = 0 then 1.0 else -1.0
    sign * m.coeffs.get i⟩

/-- Clifford conjugate. Grade `k` gets sign `(-1)^(k*(k+1)/2)`. -/
@[inline]
def conjugate (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun i =>
    let k := popcount i.val
    let sign := if (k * (k + 1) / 2) % 2 = 0 then 1.0 else -1.0
    sign * m.coeffs.get i⟩

/-- Grade projection. -/
@[inline]
def gradeProject (m : NativeMV sig) (gradeTarget : Nat) : NativeMV sig :=
  ⟨Vector.ofFn fun i =>
    if popcount i.val = gradeTarget then m.coeffs.get i else 0.0⟩

/-- Even-grade projection. -/
@[inline]
def evenPart (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun i =>
    if popcount i.val % 2 = 0 then m.coeffs.get i else 0.0⟩

/-- Odd-grade projection. -/
@[inline]
def oddPart (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun i =>
    if popcount i.val % 2 = 1 then m.coeffs.get i else 0.0⟩

private def allBladeIndices (n : Nat) : List (Fin (2 ^ n)) :=
  List.finRange (2 ^ n)

/-- Coefficient of `a * b` at output blade mask `outMask`. -/
@[inline]
def geometricCoeffAt (sig : Signature n) (a b : NativeMV sig) (outMask : Nat) : Float :=
  (allBladeIndices n).foldl (init := 0.0) fun acc i =>
    (allBladeIndices n).foldl (init := acc) fun acc j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      let sign := geometricSign sig bi bj
      let resultMask := i.val ^^^ j.val
      if sign = 0 || resultMask != outMask then
        acc
      else
        acc + Float.ofInt sign * a.coeffs.get i * b.coeffs.get j

/-- Geometric product using the straightforward O(4^n) native-vector baseline. -/
@[inline]
def geometricProduct (a b : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun out => geometricCoeffAt sig a b out.val⟩

/-- Coefficient of `a wedge b` at output blade mask `outMask`. -/
@[inline]
def wedgeCoeffAt (sig : Signature n) (a b : NativeMV sig) (outMask : Nat) : Float :=
  (allBladeIndices n).foldl (init := 0.0) fun acc i =>
    (allBladeIndices n).foldl (init := acc) fun acc j =>
      if (i.val &&& j.val) != 0 then
        acc
      else
        let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
        let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
        let resultMask := i.val ||| j.val
        if resultMask != outMask then
          acc
        else
          acc + Float.ofInt (wedgeSign sig bi bj) * a.coeffs.get i * b.coeffs.get j

/-- Exterior product using the same native-vector baseline style. -/
@[inline]
def wedge (a b : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun out => wedgeCoeffAt sig a b out.val⟩

/-- Coefficient of the left contraction `a ⌋ b` at output blade mask `outMask`. -/
@[inline]
def leftContractCoeffAt (sig : Signature n) (a b : NativeMV sig) (outMask : Nat) : Float :=
  (allBladeIndices n).foldl (init := 0.0) fun acc i =>
    (allBladeIndices n).foldl (init := acc) fun acc j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      let resultMask := i.val ^^^ j.val
      if (bi.bits &&& bj.bits) != bi.bits || bi.grade > bj.grade || resultMask != outMask then
        acc
      else
        let sign := leftContractionSign sig bi bj
        if sign = 0 then
          acc
        else
          acc + Float.ofInt sign * a.coeffs.get i * b.coeffs.get j

/-- Left contraction using the straightforward O(4^n) native-vector baseline. -/
@[inline]
def leftContract (a b : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun out => leftContractCoeffAt sig a b out.val⟩

/-- Coefficient of the right contraction `a ⌊ b` at output blade mask `outMask`. -/
@[inline]
def rightContractCoeffAt (sig : Signature n) (a b : NativeMV sig) (outMask : Nat) : Float :=
  (allBladeIndices n).foldl (init := 0.0) fun acc i =>
    (allBladeIndices n).foldl (init := acc) fun acc j =>
      let bi : Blade sig := ⟨BitVec.ofNat n i.val⟩
      let bj : Blade sig := ⟨BitVec.ofNat n j.val⟩
      let resultMask := i.val ^^^ j.val
      if (bj.bits &&& bi.bits) != bj.bits || bj.grade > bi.grade || resultMask != outMask then
        acc
      else
        let sign := geometricSign sig bi bj
        if sign = 0 then
          acc
        else
          acc + Float.ofInt sign * a.coeffs.get i * b.coeffs.get j

/-- Right contraction using the straightforward O(4^n) native-vector baseline. -/
@[inline]
def rightContract (a b : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun out => rightContractCoeffAt sig a b out.val⟩

/-- Hodge dual, matching the proof-friendly dense multivector convention. -/
@[inline]
def hodgeDual (m : NativeMV sig) : NativeMV sig :=
  ⟨Vector.ofFn fun out =>
    let outBlade : Blade sig := ⟨BitVec.ofNat n out.val⟩
    let dualBits := outBlade.bits ^^^ pseudoscalar
    let dualIdx := dualBits.toNat
    let sign := leftComplementSign sig ⟨dualBits⟩
    let coeff := m.coeff dualIdx
    if sign < 0 then -coeff else coeff⟩

/-- Regressive product / meet, defined by dualizing the exterior product. -/
@[inline]
def regressiveProduct (a b : NativeMV sig) : NativeMV sig :=
  hodgeDual (wedge (hodgeDual a) (hodgeDual b))

/-- Sandwich action `r * x * reverse r`, useful for rotor demos. -/
@[inline]
def sandwich (r x : NativeMV sig) : NativeMV sig :=
  geometricProduct (geometricProduct r x) r.reverse

/-- Convert a coordinate vector into a grade-1 multivector. -/
@[inline]
def fromVector (sig : Signature n) (coords : Vector Float n) : NativeMV sig :=
  (List.finRange n).foldl (init := zero sig) fun acc i =>
    acc.setCoeff (1 <<< i.val) (coords.get i)

/-- Extract grade-1 coordinates into a native Lean `Vector`. -/
@[inline]
def toVector (m : NativeMV sig) : Vector Float n :=
  Vector.ofFn fun i => m.coeff (1 <<< i.val)

/-- Native coordinate vector `(x, y)`. -/
@[inline]
def coords2 (x y : Float) : Vector Float 2 :=
  Vector.ofFn fun i => if i.val = 0 then x else y

/-- R2 vector from coordinates. -/
@[inline]
def vec2 (sig : Signature 2) (x y : Float) : NativeMV sig :=
  fromVector sig (coords2 x y)

/-- Native coordinate vector `(x, y, z)`. -/
@[inline]
def coords3 (x y z : Float) : Vector Float 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => x
    | 1 => y
    | _ => z

/-- R3 vector from coordinates. -/
@[inline]
def vec3 (sig : Signature 3) (x y z : Float) : NativeMV sig :=
  fromVector sig (coords3 x y z)

instance : Zero (NativeMV sig) := ⟨zero sig⟩
instance : One (NativeMV sig) := ⟨one sig⟩
instance : Add (NativeMV sig) := ⟨add⟩
instance : Sub (NativeMV sig) := ⟨sub⟩
instance : Neg (NativeMV sig) := ⟨neg⟩
instance : Mul (NativeMV sig) := ⟨geometricProduct⟩
instance : SMul Float (NativeMV sig) := ⟨smul⟩

postfix:max "†ᵥ" => NativeMV.reverse
postfix:max "ˆᵥ" => NativeMV.involute
postfix:max "‡ᵥ" => NativeMV.conjugate
infixl:65 " ⋀ᵥ " => NativeMV.wedge
infixl:65 " ⌋ᵥ " => NativeMV.leftContract
infixl:65 " ⌊ᵥ " => NativeMV.rightContract
prefix:max "⋆ᵥ" => NativeMV.hodgeDual
infixl:65 " ⋁ᵥ " => NativeMV.regressiveProduct

instance : GAlgebra sig (NativeMV sig) Float where
  basisVector := basisVector sig
  scalar := scalar sig
  zero := zero sig
  one := one sig
  blade bits := blade sig bits.toNat
  mul := geometricProduct
  wedge := wedge
  leftContract := leftContract
  rightContract := rightContract
  reverse := reverse
  involute := involute
  conjugate := conjugate
  scalarPart := scalarPart
  add := add
  neg := neg
  smul := smul
  gradeProject := gradeProject

/-! ## Basic Theorems -/

@[ext]
theorem ext {a b : NativeMV sig} (h : ∀ mask, a.coeff mask = b.coeff mask) : a = b := by
  cases a with
  | mk ac =>
  cases b with
  | mk bc =>
    congr
    apply Vector.ext
    intro i hi
    have hcoeff := h i
    simpa [coeff, hi] using hcoeff

@[simp]
theorem coeff_zero (mask : Nat) :
    (zero sig).coeff mask = 0.0 := by
  unfold coeff zero
  split
  · simp only [Vector.get, Vector.replicate, Array.getElem_replicate]
  · rfl

@[simp]
theorem coeff_scalar_zero (x : Float) :
    (scalar sig x).coeff 0 = x := by
  unfold coeff scalar
  split
  · simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
    rfl
  · have hpow : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
    contradiction

@[simp]
theorem coeff_scalar_of_ne_zero (x : Float) {mask : Nat} (hmask : mask ≠ 0) :
    (scalar sig x).coeff mask = 0.0 := by
  unfold coeff scalar
  split
  · simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
    simp [hmask]
  · rfl

/-- Coefficient formula for native-vector scalars. -/
theorem coeff_scalar (x : Float) (mask : Nat) :
    (scalar sig x).coeff mask = if mask = 0 then x else 0.0 := by
  by_cases hmask : mask = 0
  · subst mask
    simp [coeff_scalar_zero]
  · simp [hmask, coeff_scalar_of_ne_zero]

@[simp]
theorem coeff_one (mask : Nat) :
    (one sig).coeff mask = if mask = 0 then 1.0 else 0.0 := by
  unfold one
  exact coeff_scalar 1.0 mask

theorem coeff_gradeProject (m : NativeMV sig) (k mask : Nat) :
    (m.gradeProject k).coeff mask = if popcount mask = k then m.coeff mask else 0.0 := by
  unfold coeff gradeProject
  split
  · simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
    rfl
  · simp

theorem coeff_evenPart (m : NativeMV sig) (mask : Nat) :
    m.evenPart.coeff mask = if popcount mask % 2 = 0 then m.coeff mask else 0.0 := by
  unfold coeff evenPart
  split
  · simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
    rfl
  · simp

theorem coeff_oddPart (m : NativeMV sig) (mask : Nat) :
    m.oddPart.coeff mask = if popcount mask % 2 = 1 then m.coeff mask else 0.0 := by
  unfold coeff oddPart
  split
  · simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
    rfl
  · simp

/-- Setting an in-range native-vector coefficient updates that blade mask. -/
theorem coeff_setCoeff_same (m : NativeMV sig) {mask : Nat} (x : Float)
    (hmask : mask < 2 ^ n) :
    (m.setCoeff mask x).coeff mask = x := by
  unfold setCoeff coeff
  simp only [hmask, ↓reduceDIte]
  simp only [Vector.get, Vector.set]
  simp

/-- Setting one in-range native-vector coefficient leaves other in-range masks unchanged. -/
theorem coeff_setCoeff_ne (m : NativeMV sig) {setMask queryMask : Nat} (x : Float)
    (hset : setMask < 2 ^ n) (hquery : queryMask < 2 ^ n) (hne : setMask ≠ queryMask) :
    (m.setCoeff setMask x).coeff queryMask = m.coeff queryMask := by
  unfold setCoeff coeff
  simp only [hset, hquery, ↓reduceDIte]
  simp only [Vector.get, Vector.set]
  simp [Array.getElem_set, hne]

/-- Coefficient law for native-vector writes, including ignored out-of-range writes. -/
theorem coeff_setCoeff (m : NativeMV sig) (setMask queryMask : Nat) (x : Float) :
    (m.setCoeff setMask x).coeff queryMask =
      if _ : setMask < 2 ^ n then
        if queryMask = setMask then x else m.coeff queryMask
      else
        m.coeff queryMask := by
  by_cases hset : setMask < 2 ^ n
  · by_cases hq : queryMask = setMask
    · subst queryMask
      simp [hset, coeff_setCoeff_same]
    · by_cases hquery : queryMask < 2 ^ n
      · have hne : setMask ≠ queryMask := fun h => hq h.symm
        simp [hset, hq, coeff_setCoeff_ne (hset := hset) (hquery := hquery) (hne := hne)]
      · unfold coeff setCoeff
        simp [hset, hquery, hq]
  · unfold setCoeff
    simp [hset]

/-- The blade mask used by a native basis vector is in coefficient range. -/
theorem basisVector_mask_lt (i : Fin n) : 1 <<< i.val < 2 ^ n := by
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) i.isLt

/-- Distinct native basis vectors have distinct blade masks. -/
theorem basisVector_mask_ne {i j : Fin n} (hij : i ≠ j) :
    1 <<< i.val ≠ 1 <<< j.val := by
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)).ne hval

/-- A native basis blade has coefficient 1 at its own in-range mask. -/
theorem coeff_blade_same (mask : Nat) (hmask : mask < 2 ^ n) :
    (blade sig mask).coeff mask = 1.0 := by
  unfold blade
  exact coeff_setCoeff_same (zero sig) 1.0 hmask

/-- A native basis blade has coefficient 0 at every other in-range mask. -/
theorem coeff_blade_ne {setMask queryMask : Nat} (hset : setMask < 2 ^ n)
    (hquery : queryMask < 2 ^ n) (hne : setMask ≠ queryMask) :
    (blade sig setMask).coeff queryMask = 0.0 := by
  unfold blade
  rw [coeff_setCoeff_ne (hset := hset) (hquery := hquery) (hne := hne)]
  exact coeff_zero queryMask

/-- Coefficient formula for native basis blades. -/
theorem coeff_blade (setMask queryMask : Nat) :
    (blade sig setMask).coeff queryMask =
      if _ : setMask < 2 ^ n then
        if queryMask = setMask then 1.0 else 0.0
      else
        0.0 := by
  unfold blade
  rw [coeff_setCoeff]
  by_cases hset : setMask < 2 ^ n
  · by_cases hq : queryMask = setMask
    · subst queryMask
      simp [hset]
    · simp [hset, hq, coeff_zero]
  · simp [hset, coeff_zero]

/-- A native basis vector has coefficient 1 at its own blade mask. -/
theorem coeff_basisVector_same (i : Fin n) :
    (basisVector sig i).coeff (1 <<< i.val) = 1.0 := by
  unfold basisVector
  exact coeff_blade_same (1 <<< i.val) (basisVector_mask_lt i)

/-- A native basis vector has coefficient 0 at every other in-range mask. -/
theorem coeff_basisVector_ne {i : Fin n} {queryMask : Nat}
    (hquery : queryMask < 2 ^ n) (hne : 1 <<< i.val ≠ queryMask) :
    (basisVector sig i).coeff queryMask = 0.0 := by
  unfold basisVector
  exact coeff_blade_ne (basisVector_mask_lt i) hquery hne

/-- Coefficient formula for native basis vectors. -/
theorem coeff_basisVector (i : Fin n) (queryMask : Nat) :
    (basisVector sig i).coeff queryMask =
      if queryMask = 1 <<< i.val then 1.0 else 0.0 := by
  unfold basisVector
  rw [coeff_blade]
  simp [basisVector_mask_lt i]

/-- Coefficients extracted by `toVector` are exactly the grade-1 blade coefficients. -/
theorem coeff_toVector (m : NativeMV sig) (i : Fin n) :
    m.toVector.get i = m.coeff (1 <<< i.val) := by
  unfold toVector
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- The native coordinate vector of a basis vector has coefficient 1 in its own slot. -/
theorem toVector_basisVector_same (i : Fin n) :
    ((basisVector sig i).toVector).get i = 1.0 := by
  rw [coeff_toVector]
  exact coeff_basisVector_same i

/-- The native coordinate vector of a basis vector has coefficient 0 in other slots. -/
theorem toVector_basisVector_ne {i j : Fin n} (hij : i ≠ j) :
    ((basisVector sig i).toVector).get j = 0.0 := by
  rw [coeff_toVector]
  exact coeff_basisVector_ne (basisVector_mask_lt j) (basisVector_mask_ne hij)

/-- `vec2` round-trips through native coordinate extraction. -/
@[simp]
theorem toVector_vec2 (sig : Signature 2) (x y : Float) :
    (vec2 sig x y).toVector = coords2 x y := by
  apply Vector.ext
  intro i hi
  cases i with
  | zero =>
      simp [vec2, fromVector, toVector, coords2, coeff, setCoeff, List.finRange_succ,
        Vector.get, Vector.set, Array.getElem_set]
  | succ i =>
      cases i with
      | zero =>
          simp [vec2, fromVector, toVector, coords2, coeff, setCoeff, List.finRange_succ,
            Vector.get, Vector.set, Array.getElem_set]
      | succ i =>
          omega

/-- `vec3` round-trips through native coordinate extraction. -/
@[simp]
theorem toVector_vec3 (sig : Signature 3) (x y z : Float) :
    (vec3 sig x y z).toVector = coords3 x y z := by
  apply Vector.ext
  intro i hi
  cases i with
  | zero =>
      simp [vec3, fromVector, toVector, coords3, coeff, setCoeff, List.finRange_succ,
        Vector.get, Vector.set, Array.getElem_set]
  | succ i =>
      cases i with
      | zero =>
          simp [vec3, fromVector, toVector, coords3, coeff, setCoeff, List.finRange_succ,
            Vector.get, Vector.set, Array.getElem_set]
      | succ i =>
          cases i with
          | zero =>
              simp [vec3, fromVector, toVector, coords3, coeff, setCoeff, List.finRange_succ,
                Vector.get, Vector.set, Array.getElem_set]
          | succ i =>
              omega

/-- Coefficient of a native-vector sum at an in-range blade mask. -/
theorem coeff_add (a b : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (a + b).coeff mask = a.coeff mask + b.coeff mask := by
  change (NativeMV.add a b).coeff mask = a.coeff mask + b.coeff mask
  unfold coeff NativeMV.add
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.zipWith, Array.getElem_zipWith]
  rfl

/-- Total coefficient formula for native-vector addition, including out-of-range masks. -/
theorem coeff_add_total (a b : NativeMV sig) (mask : Nat) :
    (a + b).coeff mask =
      if _ : mask < 2 ^ n then a.coeff mask + b.coeff mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_add]
  · unfold coeff
    simp [hmask]

/-- Coefficient of native-vector negation at an in-range blade mask. -/
theorem coeff_neg (m : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (-m).coeff mask = -m.coeff mask := by
  change (NativeMV.neg m).coeff mask = -m.coeff mask
  unfold coeff NativeMV.neg
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.map, Array.getElem_map]
  rfl

/-- Total coefficient formula for native-vector negation, including out-of-range masks. -/
theorem coeff_neg_total (m : NativeMV sig) (mask : Nat) :
    (-m).coeff mask = if _ : mask < 2 ^ n then -m.coeff mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_neg]
  · unfold coeff
    simp [hmask]

/-- Coefficient of native-vector subtraction at an in-range blade mask.
    This is stated in executable `add`/`neg` form to avoid assuming exact Float ring laws. -/
theorem coeff_sub_add_neg (a b : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (a - b).coeff mask = a.coeff mask + -b.coeff mask := by
  change (NativeMV.sub a b).coeff mask = a.coeff mask + -b.coeff mask
  unfold NativeMV.sub NativeMV.add NativeMV.neg coeff
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.zipWith, Array.getElem_zipWith,
    Vector.map, Array.getElem_map]
  rfl

/-- Total coefficient formula for native-vector subtraction, in executable `add`/`neg` form. -/
theorem coeff_sub_add_neg_total (a b : NativeMV sig) (mask : Nat) :
    (a - b).coeff mask =
      if _ : mask < 2 ^ n then a.coeff mask + -b.coeff mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_sub_add_neg]
  · unfold coeff
    simp [hmask]

/-- Coefficient of native-vector scalar multiplication at an in-range blade mask. -/
theorem coeff_smul (x : Float) (m : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (x • m).coeff mask = x * m.coeff mask := by
  change (NativeMV.smul x m).coeff mask = x * m.coeff mask
  unfold coeff NativeMV.smul
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.map, Array.getElem_map]
  rfl

/-- Total coefficient formula for native-vector scalar multiplication. -/
theorem coeff_smul_total (x : Float) (m : NativeMV sig) (mask : Nat) :
    (x • m).coeff mask = if _ : mask < 2 ^ n then x * m.coeff mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_smul]
  · unfold coeff
    simp [hmask]

/-- Native scalar part is the coefficient of the scalar blade. -/
@[simp]
theorem scalarPart_eq_coeff_zero (m : NativeMV sig) :
    m.scalarPart = m.coeff 0 := rfl

/-- Coefficient of native-vector reverse at an in-range blade mask. -/
theorem coeff_reverse (m : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    m.reverse.coeff mask =
      (let k := popcount mask
       let sign := if (k * (k - 1) / 2) % 2 = 0 then 1.0 else -1.0
       sign * m.coeff mask) := by
  unfold coeff reverse
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector reverse, including out-of-range masks. -/
theorem coeff_reverse_total (m : NativeMV sig) (mask : Nat) :
    m.reverse.coeff mask =
      if _ : mask < 2 ^ n then
        (let k := popcount mask
         let sign := if (k * (k - 1) / 2) % 2 = 0 then 1.0 else -1.0
         sign * m.coeff mask)
      else
        0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_reverse]
  · unfold coeff reverse
    simp [hmask]

/-- Coefficient of native-vector grade involution at an in-range blade mask. -/
theorem coeff_involute (m : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    m.involute.coeff mask =
      (let k := popcount mask
       let sign := if k % 2 = 0 then 1.0 else -1.0
       sign * m.coeff mask) := by
  unfold coeff involute
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector grade involution. -/
theorem coeff_involute_total (m : NativeMV sig) (mask : Nat) :
    m.involute.coeff mask =
      if _ : mask < 2 ^ n then
        (let k := popcount mask
         let sign := if k % 2 = 0 then 1.0 else -1.0
         sign * m.coeff mask)
      else
        0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_involute]
  · unfold coeff involute
    simp [hmask]

/-- Coefficient of native-vector Clifford conjugate at an in-range blade mask. -/
theorem coeff_conjugate (m : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    m.conjugate.coeff mask =
      (let k := popcount mask
       let sign := if (k * (k + 1) / 2) % 2 = 0 then 1.0 else -1.0
       sign * m.coeff mask) := by
  unfold coeff conjugate
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector Clifford conjugate. -/
theorem coeff_conjugate_total (m : NativeMV sig) (mask : Nat) :
    m.conjugate.coeff mask =
      if _ : mask < 2 ^ n then
        (let k := popcount mask
         let sign := if (k * (k + 1) / 2) % 2 = 0 then 1.0 else -1.0
         sign * m.coeff mask)
      else
        0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_conjugate]
  · unfold coeff conjugate
    simp [hmask]

/-- Coefficient formula for native-vector geometric product at an in-range blade mask. -/
theorem coeff_geometricProduct (a b : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (a * b).coeff mask = geometricCoeffAt sig a b mask := by
  change (NativeMV.geometricProduct a b).coeff mask = geometricCoeffAt sig a b mask
  unfold coeff geometricProduct
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector geometric product. -/
theorem coeff_geometricProduct_total (a b : NativeMV sig) (mask : Nat) :
    (a * b).coeff mask =
      if _ : mask < 2 ^ n then geometricCoeffAt sig a b mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_geometricProduct]
  · unfold coeff
    simp [hmask]

/-- Coefficient formula for native-vector wedge product at an in-range blade mask. -/
theorem coeff_wedge (a b : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (a ⋀ᵥ b).coeff mask = wedgeCoeffAt sig a b mask := by
  unfold coeff wedge
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector wedge product. -/
theorem coeff_wedge_total (a b : NativeMV sig) (mask : Nat) :
    (a ⋀ᵥ b).coeff mask =
      if _ : mask < 2 ^ n then wedgeCoeffAt sig a b mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_wedge]
  · unfold coeff
    simp [hmask]

/-- Coefficient formula for native-vector left contraction at an in-range blade mask. -/
theorem coeff_leftContract (a b : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (a ⌋ᵥ b).coeff mask = leftContractCoeffAt sig a b mask := by
  unfold coeff leftContract
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector left contraction. -/
theorem coeff_leftContract_total (a b : NativeMV sig) (mask : Nat) :
    (a ⌋ᵥ b).coeff mask =
      if _ : mask < 2 ^ n then leftContractCoeffAt sig a b mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_leftContract]
  · unfold coeff
    simp [hmask]

/-- Coefficient formula for native-vector right contraction at an in-range blade mask. -/
theorem coeff_rightContract (a b : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (a ⌊ᵥ b).coeff mask = rightContractCoeffAt sig a b mask := by
  unfold coeff rightContract
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector right contraction. -/
theorem coeff_rightContract_total (a b : NativeMV sig) (mask : Nat) :
    (a ⌊ᵥ b).coeff mask =
      if _ : mask < 2 ^ n then rightContractCoeffAt sig a b mask else 0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_rightContract]
  · unfold coeff
    simp [hmask]

/-- Coefficient formula for native-vector Hodge dual at an in-range blade mask. -/
theorem coeff_hodgeDual (m : NativeMV sig) {mask : Nat} (hmask : mask < 2 ^ n) :
    (⋆ᵥm).coeff mask =
      (let outBlade : Blade sig := ⟨BitVec.ofNat n mask⟩
       let dualBits := outBlade.bits ^^^ pseudoscalar
       let dualIdx := dualBits.toNat
       let sign := leftComplementSign sig ⟨dualBits⟩
       let coeff := m.coeff dualIdx
       if sign < 0 then -coeff else coeff) := by
  unfold coeff hodgeDual
  simp only [hmask, ↓reduceDIte, Vector.get, Vector.ofFn, Array.getElem_ofFn]
  rfl

/-- Total coefficient formula for native-vector Hodge dual. -/
theorem coeff_hodgeDual_total (m : NativeMV sig) (mask : Nat) :
    (⋆ᵥm).coeff mask =
      if _ : mask < 2 ^ n then
        (let outBlade : Blade sig := ⟨BitVec.ofNat n mask⟩
         let dualBits := outBlade.bits ^^^ pseudoscalar
         let dualIdx := dualBits.toNat
         let sign := leftComplementSign sig ⟨dualBits⟩
         let coeff := m.coeff dualIdx
         if sign < 0 then -coeff else coeff)
      else
        0.0 := by
  by_cases hmask : mask < 2 ^ n
  · simp [hmask, coeff_hodgeDual]
  · unfold coeff
    simp [hmask]

@[simp]
theorem gradeProject_idem (m : NativeMV sig) (k : Nat) :
    (m.gradeProject k).gradeProject k = m.gradeProject k := by
  ext mask
  rw [coeff_gradeProject, coeff_gradeProject]
  by_cases h : popcount mask = k
  · simp [h]
  · simp [h]

theorem gradeProject_orthogonal (m : NativeMV sig) {j k : Nat} (hjk : j ≠ k) :
    (m.gradeProject j).gradeProject k = zero sig := by
  ext mask
  rw [coeff_gradeProject, coeff_zero, coeff_gradeProject]
  by_cases hk : popcount mask = k
  · simp only [hk, ↓reduceIte]
    by_cases hkj : k = j
    · exact False.elim (hjk hkj.symm)
    · simp only [hkj, ↓reduceIte]
  · simp only [hk, ↓reduceIte]

@[simp]
theorem gradeProject_zero (k : Nat) :
    (zero sig).gradeProject k = zero sig := by
  ext mask
  rw [coeff_gradeProject, coeff_zero]
  by_cases h : popcount mask = k
  · simp [h]
  · simp [h]

@[simp]
theorem evenPart_zero : (zero sig).evenPart = zero sig := by
  ext mask
  rw [coeff_evenPart, coeff_zero]
  by_cases h : popcount mask % 2 = 0
  · simp [h]
  · simp [h]

@[simp]
theorem oddPart_zero : (zero sig).oddPart = zero sig := by
  ext mask
  rw [coeff_oddPart, coeff_zero]
  by_cases h : popcount mask % 2 = 1
  · simp [h]
  · simp [h]

theorem gradeProject_evenPart (m : NativeMV sig) (k : Nat) :
    m.evenPart.gradeProject k = if k % 2 = 0 then m.gradeProject k else zero sig := by
  ext mask
  rw [coeff_gradeProject, coeff_evenPart]
  by_cases hmask : mask < 2 ^ n
  · by_cases hk : popcount mask = k
    · subst k
      by_cases he : popcount mask % 2 = 0
      · simp [he, coeff_gradeProject]
      · simp [he]
    · by_cases he : k % 2 = 0
      · simp [hk, he, coeff_gradeProject]
      · simp [hk, he, coeff_zero]
  · unfold coeff
    simp [hmask]

theorem gradeProject_oddPart (m : NativeMV sig) (k : Nat) :
    m.oddPart.gradeProject k = if k % 2 = 1 then m.gradeProject k else zero sig := by
  ext mask
  rw [coeff_gradeProject, coeff_oddPart]
  by_cases hmask : mask < 2 ^ n
  · by_cases hk : popcount mask = k
    · subst k
      by_cases ho : popcount mask % 2 = 1
      · simp [ho, coeff_gradeProject]
      · simp [ho]
    · by_cases ho : k % 2 = 1
      · simp [hk, ho, coeff_gradeProject]
      · simp [hk, ho, coeff_zero]
  · unfold coeff
    simp [hmask]

@[simp]
theorem evenPart_idem (m : NativeMV sig) :
    m.evenPart.evenPart = m.evenPart := by
  ext mask
  rw [coeff_evenPart, coeff_evenPart]
  by_cases h : popcount mask % 2 = 0
  · simp [h]
  · simp [h]

@[simp]
theorem oddPart_idem (m : NativeMV sig) :
    m.oddPart.oddPart = m.oddPart := by
  ext mask
  rw [coeff_oddPart, coeff_oddPart]
  by_cases h : popcount mask % 2 = 1
  · simp [h]
  · simp [h]

@[simp]
theorem oddPart_evenPart (m : NativeMV sig) :
    m.evenPart.oddPart = zero sig := by
  ext mask
  rw [coeff_oddPart, coeff_zero, coeff_evenPart]
  by_cases hOdd : popcount mask % 2 = 1
  · simp [hOdd]
  · simp [hOdd]

@[simp]
theorem evenPart_oddPart (m : NativeMV sig) :
    m.oddPart.evenPart = zero sig := by
  ext mask
  rw [coeff_evenPart, coeff_zero, coeff_oddPart]
  by_cases hEven : popcount mask % 2 = 0
  · simp [hEven]
  · simp [hEven]

/-! ## Small executable checks -/

section Checks

#eval! (NativeMV.basisVector R3 ⟨0, by omega⟩ * NativeMV.basisVector R3 ⟨0, by omega⟩).coeff 0
#eval! (NativeMV.basisVector R3 ⟨0, by omega⟩ * NativeMV.basisVector R3 ⟨1, by omega⟩).coeff 3
#eval! (NativeMV.basisVector R3 ⟨1, by omega⟩ * NativeMV.basisVector R3 ⟨0, by omega⟩).coeff 3
#eval (NativeMV.vec3 R3 1.0 2.0 3.0).toVector.toArray

end Checks

end NativeMV

end Grassmann
