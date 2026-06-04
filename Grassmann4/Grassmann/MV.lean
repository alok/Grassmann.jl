/-
  Grassmann/MV.lean - Unified Multivector Type

  A single parameterized type `MV sig p` that handles all grade-parity combinations:
  - `sig : Signature n` carries dimension and metric
  - `p : Parity` carries grade parity at the type level (even/odd/full)

  Performance comes from compiler specialization via `@[inline]`, not hand-written
  kernels. The same generic code works for ALL dimensions.
-/
import Grassmann.DataArray
import Grassmann.Parity
import Grassmann.SignTables
import Grassmann.Proof  -- for sorry_proof
import Grassmann.EvenMV  -- for Kernel tables (fast even×even path)

namespace Grassmann

/-! ## Grade Parity

Grade parity tracks whether a multivector contains only even grades, only odd grades,
or potentially both. This is a type-level tag that guides sparse iteration. -/

/-- Grade parity: even, odd, or full -/
inductive Parity where
  | even  -- grades 0, 2, 4, ...
  | odd   -- grades 1, 3, 5, ...
  | full  -- all grades
  deriving DecidableEq, Repr, Inhabited

namespace Parity

/-- Product of parities follows the Z/2Z group law -/
@[inline]
def mul : Parity → Parity → Parity
  | .even, .even => .even
  | .odd,  .odd  => .even
  | .even, .odd  => .odd
  | .odd,  .even => .odd
  | _,     _     => .full

instance : Mul Parity := ⟨mul⟩

/-- Check if a grade belongs to this parity -/
@[inline]
def contains (p : Parity) (g : Nat) : Bool :=
  match p with
  | .even => g % 2 == 0
  | .odd  => g % 2 == 1
  | .full => true

/-- Check if a blade mask belongs to this parity (based on popcount) -/
@[inline]
def containsMask (p : Parity) (mask : Nat) : Bool :=
  match p with
  | .even => popcount mask % 2 == 0
  | .odd  => popcount mask % 2 == 1
  | .full => true

end Parity

/-! ## Storage Size and Index Mappings

For packed storage, parity determines layout:
- `.even` or `.odd` → 2^(n-1) coefficients
- `.full` → 2^n coefficients

Index mappings convert between packed indices and blade masks. -/

/-- Storage size depends on parity -/
@[inline]
def storageSize (n : Nat) (p : Parity) : Nat :=
  match p with
  | .even | .odd => 2^(n-1)
  | .full => 2^n

/-! ## Unified Multivector Type -/

/-- The unified multivector type.

`MV sig p` is a multivector over signature `sig` with grade parity `p`.
Coefficients are stored in a contiguous `DataArray` of size 2^n.

The parity `p` is a type-level tag that:
1. Guides sparse iteration (only visit indices with matching parity)
2. Computes output parity automatically via `Parity.mul`
3. Enables type-safe grade algebra: even × even = even, etc. -/
structure MV {n : ℕ} (sig : Signature n) (p : Parity) where
  coeffs : DataArray

namespace MV

variable {n : ℕ} {sig : Signature n} {p p1 p2 : Parity}

/-! ### Index Computation

These functions compute which blade indices belong to a parity.
We cache index arrays for common dimensions to avoid recomputation. -/

/-- Compute blade indices for a parity. Generic for all dimensions. -/
@[inline]
def computeIndices (n : Nat) (p : Parity) : Array Nat :=
  match p with
  | .even => (Array.range (2^n)).filter fun i => popcount i % 2 == 0
  | .odd  => (Array.range (2^n)).filter fun i => popcount i % 2 == 1
  | .full => Array.range (2^n)

/-! ### Cached Index Arrays for Common Dimensions -/

private def evenIdx2 : Array Nat := #[0, 3]
private def oddIdx2 : Array Nat := #[1, 2]
private def fullIdx2 : Array Nat := #[0, 1, 2, 3]

private def evenIdx3 : Array Nat := #[0, 3, 5, 6]
private def oddIdx3 : Array Nat := #[1, 2, 4, 7]
private def fullIdx3 : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7]

private def evenIdx4 : Array Nat := #[0, 3, 5, 6, 9, 10, 12, 15]
private def oddIdx4 : Array Nat := #[1, 2, 4, 7, 8, 11, 13, 14]
private def fullIdx4 : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

private def evenIdx5 : Array Nat := #[0, 3, 5, 6, 9, 10, 12, 15, 17, 18, 20, 23, 24, 27, 29, 30]
private def oddIdx5 : Array Nat := #[1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31]

/-! ### Cached Pack Maps (blade mask → packed index) -/

-- n=2: even masks [0,3] → packed [0,1], odd masks [1,2] → packed [0,1]
private def evenPackMap2 : Array Nat := #[0, 0, 0, 1]
private def oddPackMap2 : Array Nat := #[0, 0, 1, 0]

-- n=3: even masks [0,3,5,6] → packed [0,1,2,3], odd masks [1,2,4,7] → packed [0,1,2,3]
private def evenPackMap3 : Array Nat := #[0, 0, 0, 1, 0, 2, 3, 0]
private def oddPackMap3 : Array Nat := #[0, 0, 1, 0, 2, 0, 0, 3]

-- n=4: even masks [0,3,5,6,9,10,12,15] → packed [0..7]
private def evenPackMap4 : Array Nat := #[0, 0, 0, 1, 0, 2, 3, 0, 0, 4, 5, 0, 6, 0, 0, 7]
-- n=4: odd masks [1,2,4,7,8,11,13,14] → packed [0..7]
private def oddPackMap4 : Array Nat := #[0, 0, 1, 0, 2, 0, 0, 3, 4, 0, 0, 5, 0, 6, 7, 0]

-- n=5: 32 entries each, 16 packed indices
private def evenPackMap5 : Array Nat := #[
  0, 0, 0, 1, 0, 2, 3, 0, 0, 4, 5, 0, 6, 0, 0, 7,
  0, 8, 9, 0, 10, 0, 0, 11, 12, 0, 0, 13, 0, 14, 15, 0]
private def oddPackMap5 : Array Nat := #[
  0, 0, 1, 0, 2, 0, 0, 3, 4, 0, 0, 5, 0, 6, 7, 0,
  8, 0, 0, 9, 0, 10, 11, 0, 0, 12, 13, 0, 14, 0, 0, 15]

/-- Get cached indices or compute on-the-fly. Inlined for specialization. -/
@[inline]
def indices (n : Nat) (p : Parity) : Array Nat :=
  match n, p with
  | 2, .even => evenIdx2
  | 2, .odd  => oddIdx2
  | 2, .full => fullIdx2
  | 3, .even => evenIdx3
  | 3, .odd  => oddIdx3
  | 3, .full => fullIdx3
  | 4, .even => evenIdx4
  | 4, .odd  => oddIdx4
  | 4, .full => fullIdx4
  | 5, .even => evenIdx5
  | 5, .odd  => oddIdx5
  | _, _     => computeIndices n p

/-- Unpack: packed index → blade mask. Uses the indices array (which IS the unpack map). -/
@[inline]
def unpackIdx (n : Nat) (p : Parity) (pi : Nat) : Nat :=
  (indices n p).getD pi 0

/-- Compute pack index on the fly (for dimensions without cached tables). -/
@[inline]
def computePackIdx (n : Nat) (p : Parity) (mask : Nat) : Nat :=
  let idx := indices n p
  match idx.findIdx? (· == mask) with
  | some i => i
  | none => 0  -- Should not happen for valid masks

/-- Pack: blade mask → packed index. Uses cached tables for common dimensions. -/
@[inline]
def packIdx (n : Nat) (p : Parity) (mask : Nat) : Nat :=
  match n, p with
  | 2, .even => evenPackMap2.getD mask 0
  | 2, .odd  => oddPackMap2.getD mask 0
  | 3, .even => evenPackMap3.getD mask 0
  | 3, .odd  => oddPackMap3.getD mask 0
  | 4, .even => evenPackMap4.getD mask 0
  | 4, .odd  => oddPackMap4.getD mask 0
  | 5, .even => evenPackMap5.getD mask 0
  | 5, .odd  => oddPackMap5.getD mask 0
  | _, .full => mask  -- Identity for full
  | _, _     => computePackIdx n p mask

/-! ### Constructors -/

/-- Zero multivector -/
@[inline]
def zero (sig : Signature n) (p : Parity) : MV sig p :=
  ⟨DataArray.zeros (storageSize n p)⟩

/-- Scalar multivector (only valid for even or full parity) -/
@[inline]
def scalar (sig : Signature n) (x : Float) : MV sig .even :=
  -- Scalar is at blade mask 0, which is packed index 0 for .even
  ⟨(DataArray.zeros (storageSize n .even)).set! 0 x⟩

/-- Unit scalar -/
@[inline]
def one (sig : Signature n) : MV sig .even := scalar sig 1.0

/-! ### Accessors -/

/-- Get coefficient at blade mask (user-friendly interface). -/
@[inline]
def coeff (m : MV sig p) (bladeMask : Nat) : Float :=
  if bladeMask < 2 ^ n then
    if Parity.containsMask p bladeMask then
      let pi := packIdx n p bladeMask
      m.coeffs.get! pi
    else 0.0
  else 0.0

/-- Get coefficient at packed index (fast internal interface). -/
@[inline]
def coeffPacked (m : MV sig p) (pi : Nat) : Float :=
  m.coeffs.get! pi

/-- Get scalar part (grade 0 coefficient).
    For even/full: scalar is at packed index 0.
    For odd: there is no scalar component. -/
@[inline]
def scalarPart (m : MV sig p) : Float :=
  match p with
  | .even | .full => m.coeffs.get! 0
  | .odd => 0.0

/-- Set coefficient at blade mask. Returns a new MV with the updated coefficient. -/
@[inline]
def setCoeff (m : MV sig p) (bladeMask : Nat) (x : Float) : MV sig p :=
  if bladeMask < 2 ^ n then
    if Parity.containsMask p bladeMask then
      let pi := packIdx n p bladeMask
      ⟨m.coeffs.set! pi x⟩
    else m
  else m

/-! ### Basic Theorems -/

@[simp]
theorem coeff_of_not_lt (m : MV sig p) {bladeMask : Nat}
    (hmask : ¬ bladeMask < 2 ^ n) :
    m.coeff bladeMask = 0.0 := by
  unfold coeff
  simp [hmask]

@[simp]
theorem coeff_of_wrong_parity (m : MV sig p) {bladeMask : Nat}
    (hparity : Parity.containsMask p bladeMask = false) :
    m.coeff bladeMask = 0.0 := by
  unfold coeff
  by_cases hmask : bladeMask < 2 ^ n
  · simp [hmask, hparity]
  · simp [hmask]

@[simp]
theorem setCoeff_of_not_lt (m : MV sig p) {bladeMask : Nat} (x : Float)
    (hmask : ¬ bladeMask < 2 ^ n) :
    m.setCoeff bladeMask x = m := by
  unfold setCoeff
  simp [hmask]

@[simp]
theorem setCoeff_of_wrong_parity (m : MV sig p) {bladeMask : Nat} (x : Float)
    (hparity : Parity.containsMask p bladeMask = false) :
    m.setCoeff bladeMask x = m := by
  unfold setCoeff
  by_cases hmask : bladeMask < 2 ^ n
  · simp [hmask, hparity]
  · simp [hmask]

/-- Build an MV from a list of (bladeMask, coefficient) pairs. -/
@[inline]
def ofPairs (sig : Signature n) (p : Parity) (pairs : List (Nat × Float)) : MV sig p :=
  pairs.foldl (init := zero sig p) fun acc (mask, x) => acc.setCoeff mask x

/-! ### The Multiplication Kernel

The generic kernel uses pack/unpack for all parity combinations.
For even×even with cached signature tables, we have a fast path that
reuses EvenMV.Kernel's precomputed tables directly. -/

/-- Generic packed geometric product kernel (uses pack/unpack) -/
@[inline]
def mulKernelGeneric (sig : Signature n) (p1 p2 : Parity) (a b : DataArray) : DataArray := Id.run do
  let pOut := p1 * p2
  let size1 := storageSize n p1
  let size2 := storageSize n p2
  let mut out := DataArray.zeros (storageSize n pOut)
  -- Use cached sign table if available, otherwise fall back to direct computation
  match cachedSignTable (n := n) sig with
  | some table =>
    for pi in [:size1] do
      let mi := unpackIdx n p1 pi  -- packed → blade mask
      let ai := a.get! pi
      if ai != 0.0 then  -- Skip zero coefficients
        for pj in [:size2] do
          let mj := unpackIdx n p2 pj  -- packed → blade mask
          let sign := table.lookup mi mj
          if sign != 0 then
            let mk := mi ^^^ mj  -- result blade mask
            let pk := packIdx n pOut mk  -- blade mask → packed
            let bj := b.get! pj
            let contrib := if sign < 0 then -ai * bj else ai * bj
            out := out.set! pk (out.get! pk + contrib)
    out
  | none =>
    -- Fallback: compute signs on the fly
    for pi in [:size1] do
      let mi := unpackIdx n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
        for pj in [:size2] do
          let mj := unpackIdx n p2 pj
          let bj_blade : Blade sig := ⟨BitVec.ofNat n mj⟩
          let sign := geometricSign sig bi bj_blade
          if sign != 0 then
            let mk := mi ^^^ mj
            let pk := packIdx n pOut mk
            let bj := b.get! pj
            let contrib := (Float.ofInt sign) * ai * bj
            out := out.set! pk (out.get! pk + contrib)
    out

/-- Fast path even×even kernel using EvenMV.Kernel's precomputed tables.
    Matches EvenMVDA.geometricProduct exactly. -/
@[inline, always_inline, specialize]
def mulKernelEvenEven (n : Nat) (signs : Array Int8) (a b : DataArray) : DataArray := Id.run do
  let idxEven := EvenMV.Kernel.evenPackedIdxCached n
  let mulIdx := EvenMV.Kernel.evenMulIdxCached n
  let sizeEven := storageSize n .even
  let mut out := DataArray.zeros sizeEven
  for i in idxEven do
    let ai := a.get! i
    let base := i * sizeEven
    for j in idxEven do
      let sign := signs.getD (base + j) 0
      if sign != 0 then
        let k := mulIdx.getD (base + j) 0
        let bj := b.get! j
        let coeff := ai * bj
        let contrib := if sign < 0 then -coeff else coeff
        let old := out.get! k
        out := out.set! k (old + contrib)
  return out

/-! ### Typeclass-Based Compile-Time Dispatch

The `MVMulKernel` typeclass enables compile-time specialization of the multiplication
kernel. For known (n, sig, p1, p2) combinations, the compiler selects a specialized
kernel with zero runtime dispatch. -/

/-- Compile-time kernel selection for MV multiplication.
    Instance resolution happens at compile time, eliminating runtime dispatch. -/
class MVMulKernel (n : ℕ) (sig : Signature n) (p1 p2 : Parity) where
  /-- The multiplication kernel for this combination -/
  kernel : DataArray → DataArray → DataArray

/-! #### Specialized Kernels for Canonical Signatures

These call the optimized `mulKernelEvenEven` with the correct precomputed sign table. -/

@[inline, always_inline] def mulKernelR2EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 2 EvenMV.Kernel.evenMulSignR2 a b

@[inline, always_inline] def mulKernelR3EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 3 EvenMV.Kernel.evenMulSignR3 a b

@[inline, always_inline] def mulKernelR4EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 4 EvenMV.Kernel.evenMulSignR4 a b

@[inline, always_inline] def mulKernelSTAEvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 4 EvenMV.Kernel.evenMulSignSTA a b

@[inline, always_inline] def mulKernelPGA3EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 4 EvenMV.Kernel.evenMulSignPGA3 a b

@[inline, always_inline] def mulKernelCGA3EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 5 EvenMV.Kernel.evenMulSignCGA3 a b

/-! #### Specialized Instances (High Priority)

These instances are selected at compile time for known signatures.
Using @[default_instance] ensures these are preferred. -/

@[default_instance 2000]
instance instMVMulKernelR2EvenEven : MVMulKernel 2 R2 .even .even where
  kernel := mulKernelR2EvenEven

@[default_instance 2000]
instance instMVMulKernelR3EvenEven : MVMulKernel 3 R3 .even .even where
  kernel := mulKernelR3EvenEven

@[default_instance 2000]
instance instMVMulKernelR4EvenEven : MVMulKernel 4 R4 .even .even where
  kernel := mulKernelR4EvenEven

@[default_instance 2000]
instance instMVMulKernelSTAEvenEven : MVMulKernel 4 STA .even .even where
  kernel := mulKernelSTAEvenEven

@[default_instance 2000]
instance instMVMulKernelPGA3EvenEven : MVMulKernel 4 PGA3 .even .even where
  kernel := mulKernelPGA3EvenEven

@[default_instance 2000]
instance instMVMulKernelCGA3EvenEven : MVMulKernel 5 CGA3 .even .even where
  kernel := mulKernelCGA3EvenEven

/-! #### Generic Fallback (Low Priority) -/

/-- Generic fallback for any (n, sig, p1, p2) without specialized instance. -/
@[default_instance 100]
instance instMVMulKernelFallback : MVMulKernel n sig p1 p2 where
  kernel a b := mulKernelGeneric sig p1 p2 a b

/-! #### Multiplication via Typeclass with Aggressive Inlining -/

/-- Typeclass-based multiplication kernel accessor with forced inlining. -/
@[inline, always_inline, specialize]
def mulKernelTC (sig : Signature n) (p1 p2 : Parity) [inst : MVMulKernel n sig p1 p2]
    (a b : DataArray) : DataArray :=
  inst.kernel a b

/-- Geometric product using typeclass dispatch with @[specialize]. -/
@[inline, always_inline, specialize]
def mulTC [inst : MVMulKernel n sig p1 p2] (a : MV sig p1) (b : MV sig p2) : MV sig (p1 * p2) :=
  ⟨inst.kernel a.coeffs b.coeffs⟩

/-! #### Multiplication via Direct Dispatch (Fallback) -/

/-- Direct multiplication kernel with fast path for even×even. -/
@[inline, always_inline]
def mulKernelDirect (sig : Signature n) (p1 p2 : Parity) (a b : DataArray) : DataArray :=
  match p1, p2 with
  | .even, .even =>
    match @EvenMV.Kernel.evenMulSignCached n sig sig with
    | some signs => mulKernelEvenEven n signs a b
    | none => mulKernelGeneric sig p1 p2 a b
  | _, _ => mulKernelGeneric sig p1 p2 a b

/-- Geometric product - uses typeclass dispatch with specialization. -/
@[inline, always_inline, specialize]
def mul [inst : MVMulKernel n sig p1 p2] (a : MV sig p1) (b : MV sig p2) : MV sig (p1 * p2) :=
  ⟨inst.kernel a.coeffs b.coeffs⟩

/-- Geometric product using direct dispatch (no typeclass overhead). -/
@[inline, always_inline]
def mulDirect (a : MV sig p1) (b : MV sig p2) : MV sig (p1 * p2) :=
  ⟨mulKernelDirect sig p1 p2 a.coeffs b.coeffs⟩

/-- Backward-compatible mulKernel wrapper. -/
@[inline, always_inline]
def mulKernel (sig : Signature n) (p1 p2 : Parity) [inst : MVMulKernel n sig p1 p2]
    (a b : DataArray) : DataArray :=
  inst.kernel a b

/-! ### Scalar Multiplication -/

@[inline]
def smul (s : Float) (m : MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi => s * m.coeffs.get! pi)⟩

/-! ### Addition -/

@[inline]
def add (a b : MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi => a.coeffs.get! pi + b.coeffs.get! pi)⟩

/-! ### Negation -/

@[inline]
def neg (m : MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi => -m.coeffs.get! pi)⟩

/-! ### Reverse (Dagger) -/

/-- Reverse operation: reverses the order of basis vectors in each blade.
    For grade k, this multiplies by (-1)^(k(k-1)/2). -/
@[inline]
def rev (m : MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := unpackIdx n p pi  -- get blade mask from packed index
    let g := popcount mask
    let sign := if (g * (g - 1) / 2) % 2 == 0 then 1.0 else -1.0
    sign * m.coeffs.get! pi)⟩

/-- Grade involution: multiplies each grade-k blade by `(-1)^k`. -/
@[inline]
def involute (m : MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := unpackIdx n p pi
    let g := popcount mask
    let sign := if g % 2 == 0 then 1.0 else -1.0
    sign * m.coeffs.get! pi)⟩

/-- Clifford conjugate: multiplies each grade-k blade by `(-1)^(k(k+1)/2)`. -/
@[inline]
def conjugate (m : MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := unpackIdx n p pi
    let g := popcount mask
    let sign := if (g * (g + 1) / 2) % 2 == 0 then 1.0 else -1.0
    sign * m.coeffs.get! pi)⟩

/-! ### Grade Projection -/

/-- Project to even part (from full MV, extracting even-grade components) -/
@[inline]
def evenPart (m : MV sig .full) : MV sig .even :=
  -- Full storage uses identity mapping, so we can read directly by blade mask
  -- Even output is packed, so we iterate over even packed indices
  let szEven := storageSize n .even
  ⟨DataArray.ofArray ((Array.range szEven).map fun pi =>
    let mask := unpackIdx n .even pi  -- Get blade mask for this even index
    m.coeffs.get! mask)⟩  -- Full uses identity: coeffs[mask] is the value

/-- Project to odd part (from full MV, extracting odd-grade components) -/
@[inline]
def oddPart (m : MV sig .full) : MV sig .odd :=
  let szOdd := storageSize n .odd
  ⟨DataArray.ofArray ((Array.range szOdd).map fun pi =>
    let mask := unpackIdx n .odd pi
    m.coeffs.get! mask)⟩

/-- Project to a single grade while preserving the packed parity storage.

For `.even` or `.odd`, projecting to a grade outside the parity simply produces
zero because every packed index already has the opposite parity filtered out. -/
@[inline]
def gradeProject (m : MV sig p) (k : Nat) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := unpackIdx n p pi
    if popcount mask == k then m.coeffs.get! pi else 0.0)⟩

/-! ### Conversions -/

/-- Widen even to full (unpacks even storage into full storage) -/
@[inline]
def evenToFull (m : MV sig .even) : MV sig .full :=
  let szFull := storageSize n .full
  ⟨DataArray.ofArray ((Array.range szFull).map fun mask =>
    if Parity.containsMask .even mask then
      let pi := packIdx n .even mask
      m.coeffs.get! pi
    else 0.0)⟩

/-- Widen odd to full (unpacks odd storage into full storage) -/
@[inline]
def oddToFull (m : MV sig .odd) : MV sig .full :=
  let szFull := storageSize n .full
  ⟨DataArray.ofArray ((Array.range szFull).map fun mask =>
    if Parity.containsMask .odd mask then
      let pi := packIdx n .odd mask
      m.coeffs.get! pi
    else 0.0)⟩

/-- Convert to proof-friendly Multivector -/
@[inline]
def toMultivector (m : MV sig p) : Multivector sig Float :=
  ⟨fun i =>
    let mask := i.val
    if Parity.containsMask p mask then
      let pi := packIdx n p mask
      m.coeffs.get! pi
    else 0.0⟩

/-- Convert from proof-friendly Multivector -/
@[inline]
def ofMultivector (m : Multivector sig Float) (p : Parity) : MV sig p :=
  let sz := storageSize n p
  ⟨DataArray.ofArray ((Array.range sz).map fun pi =>
    let mask := unpackIdx n p pi
    m.coeffs ⟨mask, Proof.sorryProofAxiom⟩)⟩

/-! ### Typeclass Instances -/

-- NOTE: Using mulDirect instead of mul (typeclass) for better runtime performance.
-- Typeclass dispatch adds ~1.5x overhead vs direct dispatch.
instance instHMulMV : HMul (MV sig p1) (MV sig p2) (MV sig (p1 * p2)) where
  hMul := mulDirect

instance instMulEven : Mul (MV sig .even) where
  mul a b := mulDirect a b

instance instMulFull : Mul (MV sig .full) where
  mul a b := mulDirect a b

instance instHMulFloat : HMul Float (MV sig p) (MV sig p) where
  hMul := smul

instance instAdd : Add (MV sig p) where
  add := add

instance instNeg : Neg (MV sig p) where
  neg := neg

instance instCoeEvenFull : Coe (MV sig .even) (MV sig .full) := ⟨evenToFull⟩
instance instCoeOddFull : Coe (MV sig .odd) (MV sig .full) := ⟨oddToFull⟩
instance instCoeEvenToMV : Coe (MV sig .even) (Multivector sig Float) := ⟨toMultivector⟩
instance instCoeOddToMV : Coe (MV sig .odd) (Multivector sig Float) := ⟨toMultivector⟩
instance instCoeFullToMV : Coe (MV sig .full) (Multivector sig Float) := ⟨toMultivector⟩

end MV

/-! ## Convenient Aliases -/

/-- Rotor (even multivector, typically normalized) -/
abbrev Rotor' {n : ℕ} (sig : Signature n) := MV sig .even

/-- Spinor (even multivector) -/
abbrev Spinor'' {n : ℕ} (sig : Signature n) := MV sig .even

/-- Full multivector with all grades -/
abbrev FullMV {n : ℕ} (sig : Signature n) := MV sig .full

/-- Vector (odd multivector, grade 1) -/
abbrev Vec' {n : ℕ} (sig : Signature n) := MV sig .odd

/-! ## Sandwich Product for MV -/

/-- Sandwich product: R * x * R† (rotation/reflection) -/
@[inline]
def mvSandwich {n : ℕ} {sig : Signature n} {p : Parity}
    (R : MV sig .even) (x : MV sig p) : MV sig p :=
  -- R * x gives parity (even * p) = p
  -- (R * x) * R† gives parity (p * even) = p
  let Rx : MV sig p := ⟨MV.mulKernelDirect sig .even p R.coeffs x.coeffs⟩
  ⟨MV.mulKernelDirect sig p .even Rx.coeffs (MV.rev R).coeffs⟩

/-! ## PGA Subtypes

These are subtypes of MV for common PGA entities. Using subtypes with `sorry`
proofs lets computation work immediately while proofs can be added later.
The key benefit: multiplication is inherited from the base MV type. -/

namespace PGA

/-- Motor in PGA: even multivector representing rigid transforms.
    Contains only grades 0, 2, and n (pseudoscalar). -/
def Motor {n : ℕ} (sig : Signature n) := MV sig .even

namespace Motor
variable {n : ℕ} {sig : Signature n}

/-- Create a motor from an even MV. -/
@[inline] def mk (m : MV sig .even) : Motor sig := m

/-- Get the underlying MV. -/
@[inline] def toMV (m : Motor sig) : MV sig .even := m

/-- Compose two motors. -/
@[inline] def compose (m1 m2 : Motor sig) : Motor sig :=
  MV.mulDirect m1 m2

instance : Mul (Motor sig) where mul := compose

/-- Identity motor (scalar 1). -/
@[inline] def identity (sig : Signature n) : Motor sig := MV.one sig

/-- Reverse of a motor. -/
@[inline] def rev (m : Motor sig) : Motor sig := MV.rev m

/-- Apply motor to transform an MV via sandwich product. -/
@[inline] def apply (m : Motor sig) (x : MV sig p) : MV sig p :=
  mvSandwich m x

end Motor

/-- Point in PGA: grade-3 trivector (for 3D PGA). -/
def Point {n : ℕ} (sig : Signature n) := MV sig .odd

namespace Point
variable {n : ℕ} {sig : Signature n}

/-- Create point from an odd MV. -/
@[inline] def mk (m : MV sig .odd) : Point sig := m

/-- Get the underlying MV. -/
@[inline] def toMV (p : Point sig) : MV sig .odd := p

end Point

/-- Plane in PGA: grade-1 vector. -/
def Plane {n : ℕ} (sig : Signature n) := MV sig .odd

namespace Plane
variable {n : ℕ} {sig : Signature n}

/-- Create plane from an odd MV. -/
@[inline] def mk (m : MV sig .odd) : Plane sig := m

/-- Get the underlying MV. -/
@[inline] def toMV (p : Plane sig) : MV sig .odd := p

end Plane

/-- Line in PGA: grade-2 bivector. -/
def Line {n : ℕ} (sig : Signature n) := MV sig .even

namespace Line
variable {n : ℕ} {sig : Signature n}

/-- Create line from an even MV. -/
@[inline] def mk (m : MV sig .even) : Line sig := m

/-- Get the underlying MV. -/
@[inline] def toMV (l : Line sig) : MV sig .even := l

end Line

/-- Transform a point by a motor. -/
@[inline] def Motor.transformPoint {n : ℕ} {sig : Signature n}
    (m : Motor sig) (p : Point sig) : Point sig :=
  mvSandwich m p

/-- Transform a plane by a motor. -/
@[inline] def Motor.transformPlane {n : ℕ} {sig : Signature n}
    (m : Motor sig) (p : Plane sig) : Plane sig :=
  mvSandwich m p

/-- Transform a line by a motor. -/
@[inline] def Motor.transformLine {n : ℕ} {sig : Signature n}
    (m : Motor sig) (l : Line sig) : Line sig :=
  mvSandwich m l

end PGA

end Grassmann
