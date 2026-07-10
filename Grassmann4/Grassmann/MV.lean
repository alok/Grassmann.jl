/-
  Grassmann/MV.lean - Unified Multivector Type

  A single parameterized type `MV sig p` that handles all grade-parity combinations:
  - `sig : Signature n` carries dimension and metric
  - `p : Parity` carries grade parity at the type level (even/odd/full)

  Performance comes from compiler specialization via `@[inline]`, not hand-written
  kernels. The same generic code works for ALL dimensions.
-/
import Grassmann.DataArray
import Grassmann.PGA3Kernel
import Grassmann.Parity
import Grassmann.Products
import Grassmann.GATypeclass
import Grassmann.SignTablesCore
import Grassmann.EvenKernelTables

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
  private mk ::
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

/-- Reconstruct the discarded low mask bit from a packed rank's popcount. -/
@[inline, always_inline]
private def packedLowBit (n : Nat) (p : Parity) (rankPopcount : Nat) : Nat :=
  if n == 0 then 0 else
    match p with
    | .even => rankPopcount % 2
    | .odd => (rankPopcount % 2) ^^^ 1
    | .full => 0

/-- Allocation-free packed-index decoding for a caller-validated index.

For `n >= 1`, each adjacent mask pair contains exactly one even and one odd
popcount. The high bits are the packed index and the reconstructed low bit is
therefore determined by the packed index's own popcount parity. Dimension zero
keeps the historical one-slot parity layout and decodes that compatibility slot
as mask zero. -/
@[inline, always_inline]
def unpackIdxValid (n : Nat) (p : Parity) (pi : Nat) : Nat :=
  match p with
  | .full => pi
  | .even | .odd =>
      (pi <<< 1) ||| packedLowBit n p (popcount pi)

/-- Allocation-free packed rank for a caller-validated blade mask. -/
@[inline, always_inline]
def packIdxValid (_n : Nat) (p : Parity) (mask : Nat) : Nat :=
  match p with
  | .full => mask
  | .even | .odd => mask >>> 1

/-- Unpack a packed index into its blade mask.

Full storage is identity-indexed for every input. Parity storage returns zero
for an out-of-range index and preserves the historical dimension-zero
compatibility behavior. -/
@[inline]
def unpackIdx (n : Nat) (p : Parity) (pi : Nat) : Nat :=
  match p with
  | .full => pi
  | .even =>
      if n == 0 then 0
      else if pi < storageSize n .even then unpackIdxValid n .even pi else 0
  | .odd =>
      if n == 0 then 0
      else if pi < storageSize n .odd then unpackIdxValid n .odd pi else 0

/-- Checked arithmetic pack index, returning zero for an invalid blade mask. -/
@[inline]
def computePackIdx (n : Nat) (p : Parity) (mask : Nat) : Nat :=
  if mask < 2 ^ n && Parity.containsMask p mask then
    packIdxValid n p mask
  else
    0

/-- Pack a blade mask, preserving full storage's public identity behavior. -/
@[inline]
def packIdx (n : Nat) (p : Parity) (mask : Nat) : Nat :=
  match p with
  | .full => mask
  | .even =>
      if mask < 2 ^ n && Parity.containsMask .even mask then
        packIdxValid n .even mask
      else
        0
  | .odd =>
      if mask < 2 ^ n && Parity.containsMask .odd mask then
        packIdxValid n .odd mask
      else
        0

/-! ### Constructors -/

/-- Zero multivector -/
@[inline]
def zero (sig : Signature n) (p : Parity) : MV sig p :=
  ⟨DataArray.zeros (storageSize n p)⟩

/-- Import a native coefficient buffer after validating the packed layout.

This is the boundary constructor for bindings and other low-level consumers.
The raw `MV` constructor is private so downstream code cannot accidentally
create a value whose buffer is shorter than every kernel expects.
-/
@[inline]
def ofDataArray? (sig : Signature n) (p : Parity) (coeffs : DataArray) : Option (MV sig p) :=
  if coeffs.size == storageSize n p then
    some ⟨coeffs⟩
  else
    none

/-!
These fixed PGA3 constructors keep the raw `MV` constructor private while
letting the supported high-level API share the same straight-line buffers as
the native binding layer.
-/

/-- Construct a well-formed packed PGA3 point without generic index updates. -/
@[inline, always_inline]
def pga3Point (x y z : Float) : MV PGA3 .odd :=
  ⟨PGA3Kernel.point x y z⟩

/-- Construct a well-formed packed PGA3 plane without generic index updates. -/
@[inline, always_inline]
def pga3Plane (nx ny nz d : Float) : MV PGA3 .odd :=
  ⟨PGA3Kernel.plane nx ny nz d⟩

/-- Construct a well-formed packed PGA3 line without generic index updates. -/
@[inline, always_inline]
def pga3Line (dx dy dz mx my mz : Float) : MV PGA3 .even :=
  ⟨PGA3Kernel.line dx dy dz mx my mz⟩

/-- Construct a well-formed packed PGA3 rotor without generic index updates. -/
@[inline, always_inline]
def pga3Rotor (axisX axisY axisZ angle : Float) : MV PGA3 .even :=
  ⟨PGA3Kernel.rotor axisX axisY axisZ angle⟩

/-- Construct a well-formed packed PGA3 translator without generic index updates. -/
@[inline, always_inline]
def pga3Translator (x y z : Float) : MV PGA3 .even :=
  ⟨PGA3Kernel.translator x y z⟩

/-- Number of packed coefficients required by this multivector's layout. -/
@[inline, always_inline]
def coefficientCount (_m : MV sig p) : Nat := storageSize n p

/-- Check the internal packed-buffer invariant at an API or FFI boundary. -/
@[inline, always_inline]
def isWellFormed (m : MV sig p) : Bool :=
  m.coeffs.size == storageSize n p

/-- Scalar multivector (only valid for even or full parity) -/
@[inline]
def scalar (sig : Signature n) (x : Float) : MV sig .even :=
  -- Scalar is at blade mask 0, which is packed index 0 for .even
  ⟨(DataArray.zeros (storageSize n .even)).set! 0 x⟩

/-- Unit scalar -/
@[inline]
def one (sig : Signature n) : MV sig .even := scalar sig 1.0

/-- Unit scalar in full storage. -/
@[inline]
def oneFull (sig : Signature n) : MV sig .full :=
  ⟨(DataArray.zeros (storageSize n .full)).set! 0 1.0⟩

/-! ### Accessors -/

/-- Get coefficient at blade mask (user-friendly interface). -/
@[inline]
def coeff (m : MV sig p) (bladeMask : Nat) : Float :=
  if bladeMask < 2 ^ n then
    if Parity.containsMask p bladeMask then
      let pi := packIdxValid n p bladeMask
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
      let pi := packIdxValid n p bladeMask
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
reuses the production even-kernel tables directly. -/

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
      let mi := unpackIdxValid n p1 pi  -- packed → blade mask
      let ai := a.get! pi
      if ai != 0.0 then  -- Skip zero coefficients
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj  -- packed → blade mask
          let sign := table.lookup mi mj
          if sign != 0 then
            let mk := mi ^^^ mj  -- result blade mask
            let pk := packIdxValid n pOut mk  -- blade mask → packed
            let bj := b.get! pj
            let contrib := if sign < 0 then -ai * bj else ai * bj
            out := out.set! pk (out.get! pk + contrib)
    out
  | none =>
    -- Fallback: compute signs on the fly
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj_blade : Blade sig := ⟨BitVec.ofNat n mj⟩
          let sign := geometricSign sig bi bj_blade
          if sign != 0 then
            let mk := mi ^^^ mj
            let pk := packIdxValid n pOut mk
            let bj := b.get! pj
            let contrib := (Float.ofInt sign) * ai * bj
            out := out.set! pk (out.get! pk + contrib)
    out

/-- Generic packed wedge-product kernel.
    Only disjoint blades contribute, and the output parity is the grade-sum parity. -/
@[inline]
def wedgeKernelGeneric (sig : Signature n) (p1 p2 : Parity)
    (a b : DataArray) : DataArray := Id.run do
  let pOut := p1 * p2
  let size1 := storageSize n p1
  let size2 := storageSize n p2
  let mut out := DataArray.zeros (storageSize n pOut)
  match cachedSignTable (n := n) sig with
  | some table =>
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj := b.get! pj
          if bj != 0.0 && (mi &&& mj) == 0 then
            let sign := table.lookup mi mj
            if sign != 0 then
              let mk := mi ||| mj
              let pk := packIdxValid n pOut mk
              let contrib := if sign < 0 then -ai * bj else ai * bj
              out := out.set! pk (out.get! pk + contrib)
    out
  | none =>
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj := b.get! pj
          if bj != 0.0 && (mi &&& mj) == 0 then
            let bjBlade : Blade sig := ⟨BitVec.ofNat n mj⟩
            let sign := wedgeSign sig bi bjBlade
            if sign != 0 then
              let mk := mi ||| mj
              let pk := packIdxValid n pOut mk
              let contrib := if sign < 0 then -ai * bj else ai * bj
              out := out.set! pk (out.get! pk + contrib)
    out

/-- Generic packed left-contraction kernel. -/
@[inline]
def leftContractKernelGeneric (sig : Signature n) (p1 p2 : Parity)
    (a b : DataArray) : DataArray := Id.run do
  let pOut := p1 * p2
  let size1 := storageSize n p1
  let size2 := storageSize n p2
  let mut out := DataArray.zeros (storageSize n pOut)
  match cachedSignTable (n := n) sig with
  | some table =>
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj := b.get! pj
          if bj != 0.0 && (mi &&& mj) == mi && popcount mi <= popcount mj then
            let sign := table.lookup mi mj
            if sign != 0 then
              let mk := mi ^^^ mj
              let pk := packIdxValid n pOut mk
              let reverseNeg := reverseSign (popcount mi) < 0
              let geometricNeg := sign < 0
              let contrib := if reverseNeg != geometricNeg then -ai * bj else ai * bj
              out := out.set! pk (out.get! pk + contrib)
    out
  | none =>
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj := b.get! pj
          if bj != 0.0 && (mi &&& mj) == mi && popcount mi <= popcount mj then
            let bjBlade : Blade sig := ⟨BitVec.ofNat n mj⟩
            let sign := leftContractionSign sig bi bjBlade
            if sign != 0 then
              let mk := mi ^^^ mj
              let pk := packIdxValid n pOut mk
              let contrib := if sign < 0 then -ai * bj else ai * bj
              out := out.set! pk (out.get! pk + contrib)
    out

/-- Generic packed right-contraction kernel. -/
@[inline]
def rightContractKernelGeneric (sig : Signature n) (p1 p2 : Parity)
    (a b : DataArray) : DataArray := Id.run do
  let pOut := p1 * p2
  let size1 := storageSize n p1
  let size2 := storageSize n p2
  let mut out := DataArray.zeros (storageSize n pOut)
  match cachedSignTable (n := n) sig with
  | some table =>
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj := b.get! pj
          if bj != 0.0 && (mj &&& mi) == mj && popcount mj <= popcount mi then
            let sign := table.lookup mj mi
            if sign != 0 then
              let mk := mi ^^^ mj
              let pk := packIdxValid n pOut mk
              let reverseNeg := reverseSign (popcount mj) < 0
              let geometricNeg := sign < 0
              let contrib := if reverseNeg != geometricNeg then -ai * bj else ai * bj
              out := out.set! pk (out.get! pk + contrib)
    out
  | none =>
    for pi in [:size1] do
      let mi := unpackIdxValid n p1 pi
      let ai := a.get! pi
      if ai != 0.0 then
        let bi : Blade sig := ⟨BitVec.ofNat n mi⟩
        for pj in [:size2] do
          let mj := unpackIdxValid n p2 pj
          let bj := b.get! pj
          if bj != 0.0 && (mj &&& mi) == mj && popcount mj <= popcount mi then
            let bjBlade : Blade sig := ⟨BitVec.ofNat n mj⟩
            let sign := rightContractionSign sig bi bjBlade
            if sign != 0 then
              let mk := mi ^^^ mj
              let pk := packIdxValid n pOut mk
              let contrib := if sign < 0 then -ai * bj else ai * bj
              out := out.set! pk (out.get! pk + contrib)
    out

/-- Fast path even×even kernel using the shared precomputed tables.
    Matches EvenMVDA.geometricProduct exactly. -/
@[inline, always_inline, specialize]
def mulKernelEvenEven (n : Nat) (signs : Array Int8) (a b : DataArray) : DataArray := Id.run do
  let idxEven := EvenKernelTables.evenPackedIdxCached n
  let mulIdx := EvenKernelTables.evenMulIdxCached n
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
  mulKernelEvenEven 2 EvenKernelTables.evenMulSignR2 a b

/-- Straight-line quaternion kernel for the R3 even subalgebra.

Packed coefficient order is `[1, e12, e13, e23]`. Keeping this fixed-size
kernel branch-free avoids the allocation, table lookups, and nested loops of
the generic even kernel in the rotor composition hot path.
-/
@[inline, always_inline]
def mulKernelR3EvenEven (a : @& DataArray) (b : @& DataArray) : DataArray :=
  let a0 := a.get! 0
  let a1 := a.get! 1
  let a2 := a.get! 2
  let a3 := a.get! 3
  let b0 := b.get! 0
  let b1 := b.get! 1
  let b2 := b.get! 2
  let b3 := b.get! 3
  let c0 := a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3
  let c1 := a0 * b1 + a1 * b0 - a2 * b3 + a3 * b2
  let c2 := a0 * b2 + a1 * b3 + a2 * b0 - a3 * b1
  let c3 := a0 * b3 - a1 * b2 + a2 * b1 + a3 * b0
  FloatArray.emptyWithCapacity 4
    |>.push c0
    |>.push c1
    |>.push c2
    |>.push c3

@[inline, always_inline] def mulKernelR4EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 4 EvenKernelTables.evenMulSignR4 a b

@[inline, always_inline] def mulKernelSTAEvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 4 EvenKernelTables.evenMulSignSTA a b

/-- Shared straight-line dual-quaternion kernel for the PGA3 even subalgebra.

Packed mask order is `[0, 3, 5, 6, 9, 10, 12, 15]`. The implementation lives
in the Init-only `PGA3Kernel` module so native bindings and `MV` use exactly the
same arithmetic.
-/
@[inline, always_inline]
def mulKernelPGA3EvenEven (a : @& DataArray) (b : @& DataArray) : DataArray :=
  PGA3Kernel.motorMul a b

@[inline, always_inline] def mulKernelCGA3EvenEven (a b : DataArray) : DataArray :=
  mulKernelEvenEven 5 EvenKernelTables.evenMulSignCGA3 a b

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

/-- Cached-table fallback for even products without a straight-line kernel. -/
@[inline, always_inline]
def mulKernelEvenEvenDirect (sig : Signature n) (a : @& DataArray) (b : @& DataArray) : DataArray :=
  match EvenKernelTables.evenMulSignCached sig with
  | some signs => mulKernelEvenEven n signs a b
  | none => mulKernelGeneric sig .even .even a b

/-- Direct multiplication kernel with fast path for even×even. -/
@[inline, always_inline]
def mulKernelDirect (sig : Signature n) (p1 p2 : Parity)
    (a : @& DataArray) (b : @& DataArray) : DataArray :=
  match p1, p2 with
  | .even, .even =>
    if n == 3 && sig.metric.toNat == 0 && sig.degenerate.toNat == 0 then
      mulKernelR3EvenEven a b
    else if n == 4 && sig.metric.toNat == 0 && sig.degenerate.toNat == 8 then
      mulKernelPGA3EvenEven a b
    else
      mulKernelEvenEvenDirect sig a b
  | .even, .odd =>
    if n == 4 && sig.metric.toNat == 0 && sig.degenerate.toNat == 8 then
      PGA3Kernel.evenOddMul a b
    else
      mulKernelGeneric sig .even .odd a b
  | .odd, .even =>
    if n == 4 && sig.metric.toNat == 0 && sig.degenerate.toNat == 8 then
      PGA3Kernel.oddEvenMul a b
    else
      mulKernelGeneric sig .odd .even a b
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

/-! ### Exterior and Interior Products -/

@[inline]
def wedge (a : MV sig p1) (b : MV sig p2) : MV sig (p1 * p2) :=
  ⟨wedgeKernelGeneric sig p1 p2 a.coeffs b.coeffs⟩

@[inline]
def leftContract (a : MV sig p1) (b : MV sig p2) : MV sig (p1 * p2) :=
  ⟨leftContractKernelGeneric sig p1 p2 a.coeffs b.coeffs⟩

@[inline]
def rightContract (a : MV sig p1) (b : MV sig p2) : MV sig (p1 * p2) :=
  ⟨rightContractKernelGeneric sig p1 p2 a.coeffs b.coeffs⟩

/-! ### Dual and Derived Products -/

/-- Hodge-negation bits indexed by output blade mask for dimensions up to six.

For output `o`, Hodge reads the complementary input `(2^n - 1) - o`. The two
masks are disjoint, so the left-complement sign is signature-independent and is
exactly their permutation sign. Packing those signs in one native word avoids
recomputing transpositions or consulting the much larger geometric sign table. -/
@[noinline]
private def hodgeDualNegBits : Nat → UInt64
  | 0 => 0x0
  | 1 => 0x0
  | 2 => 0x2
  | 3 => 0x24
  | 4 => 0x24b2
  | 5 => 0x24b24d24
  | 6 => 0x24b24d24b2db24b2
  | _ => 0x0

/-- Tail-recursive Hodge loop using one native negation bit per output slot. -/
private def hodgeDualSmallAux (m : @& DataArray) (negBits : UInt64) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! remaining
      let result := if negBits &&& 1 != 0 then -value else value
      hodgeDualSmallAux m (negBits >>> 1) remaining (out.push result)

/-- Allocation-tight Hodge fallback for dimensions whose sign sequence does
not fit in a `UInt64`. Complementary masks make `parityJoinBasic` exactly the
left-complement sign used by the dense reference implementation. -/
private def hodgeDualLargeAux (n : Nat) (m : @& DataArray) (outMask : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! remaining
      let result := if parityJoinBasic remaining outMask n then -value else value
      hodgeDualLargeAux n m (outMask + 1) remaining (out.push result)

/-- Hodge dual for full packed storage.

The dual may flip even/odd parity when the dimension is odd, so this operation
is exposed on `.full` storage where every grade can be represented directly. -/
@[inline]
def hodgeDual (m : @& MV sig .full) : MV sig .full :=
  let szFull := storageSize n .full
  let out := FloatArray.emptyWithCapacity szFull
  if n ≤ 6 then
    ⟨hodgeDualSmallAux m.coeffs (hodgeDualNegBits n) szFull out⟩
  else
    ⟨hodgeDualLargeAux n m.coeffs 0 szFull out⟩

/-- Regressive product / meet for full packed storage, defined by dualizing the
exterior product. -/
@[inline]
def regressiveProduct (a b : MV sig .full) : MV sig .full :=
  hodgeDual (wedge (hodgeDual a) (hodgeDual b))

/-! ### Scalar Multiplication -/

/-- Tail-recursive coefficient loop for packed scalar multiplication. -/
private def smulAux (s : Float) (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      smulAux s m (i + 1) remaining (out.push (s * m.get! i))

@[inline]
def smul (s : Float) (m : @& MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨smulAux s m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-! ### Addition -/

/-- Tail-recursive coefficient loop for packed addition. -/
private def addAux (a b : @& DataArray) (i : Nat) : Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      addAux a b (i + 1) remaining (out.push (a.get! i + b.get! i))

@[inline]
def add (a : @& MV sig p) (b : @& MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨addAux a.coeffs b.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-! ### Subtraction -/

/-- Tail-recursive coefficient loop for packed subtraction.

Keeping the loop explicit avoids the closure and per-iteration control objects
introduced by generic `ForIn` lowering while the unique `FloatArray` is grown
in place. -/
private def subAux (a b : @& DataArray) (i : Nat) : Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      subAux a b (i + 1) remaining (out.push (a.get! i - b.get! i))

/-- Subtract packed multivectors without allocating an intermediate negation. -/
@[inline]
def sub (a : @& MV sig p) (b : @& MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨subAux a.coeffs b.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-! ### Negation -/

/-- Tail-recursive coefficient loop for packed negation. -/
private def negAux (m : @& DataArray) (i : Nat) : Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      negAux m (i + 1) remaining (out.push (-m.get! i))

@[inline]
def neg (m : @& MV sig p) : MV sig p :=
  let sz := storageSize n p
  ⟨negAux m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-! ### More Full-Storage Derived Products -/

/-- Grassmann ("fat dot") contraction for full packed storage.

The left and right contractions both contain the equal-grade scalar term.  We
subtract that shared term once, reusing the left contraction's scalar slot so
the operation does not need another geometric-product traversal. -/
@[inline]
def fatDot (a b : MV sig .full) : MV sig .full :=
  let left := leftContract a b
  let both := add left (rightContract a b)
  both.setCoeff 0 (both.scalarPart - left.scalarPart)

/-- Commutator product `(ab - ba) / 2` for full packed storage. -/
@[inline]
def commutator (a b : MV sig .full) : MV sig .full :=
  smul 0.5 (sub (mulDirect a b) (mulDirect b a))

/-- Anticommutator product `(ab + ba) / 2` for full packed storage. -/
@[inline]
def antiCommutator (a b : MV sig .full) : MV sig .full :=
  smul 0.5 (add (mulDirect a b) (mulDirect b a))

/-! ### Reverse (Dagger) -/

/-- Whether reverse negates the coefficient at a blade mask. -/
@[inline]
private def reverseNegates (mask : Nat) : Bool :=
  let g := popcount mask
  (g * (g - 1) / 2) % 2 != 0

/-- Tail-recursive reverse loop for identity-indexed full storage. -/
private def revFullAux (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! i
      let result := if reverseNegates i then -value else value
      revFullAux m (i + 1) remaining (out.push result)

/-- Tail-recursive reverse loop with arithmetic parity-index decoding. -/
private def revPackedAux (n : Nat) (p : Parity) (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! i
      let result := if reverseNegates (unpackIdxValid n p i) then -value else value
      revPackedAux n p m (i + 1) remaining (out.push result)

/-- Reverse operation: reverses the order of basis vectors in each blade.
    For grade k, this multiplies by (-1)^(k(k-1)/2). -/
@[inline]
def rev (m : @& MV sig p) : MV sig p :=
  let sz := storageSize n p
  match p with
  | .full =>
      ⟨revFullAux m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩
  | .even =>
      ⟨revPackedAux n .even m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩
  | .odd =>
      ⟨revPackedAux n .odd m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-- Tail-recursive grade-involution loop for full storage. -/
private def involuteFullAux (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! i
      let result := if popcount i % 2 == 0 then value else -value
      involuteFullAux m (i + 1) remaining (out.push result)

/-- Grade involution: multiplies each grade-k blade by `(-1)^k`. -/
@[inline]
def involute (m : @& MV sig p) : MV sig p :=
  match p with
  | .even => m
  | .odd => neg m
  | .full =>
      let sz := storageSize n .full
      ⟨involuteFullAux m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-- Whether Clifford conjugation negates the coefficient at a blade mask. -/
@[inline]
private def conjugateNegates (mask : Nat) : Bool :=
  let g := popcount mask
  (g * (g + 1) / 2) % 2 != 0

/-- Tail-recursive Clifford-conjugation loop for full storage. -/
private def conjugateFullAux (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! i
      let result := if conjugateNegates i then -value else value
      conjugateFullAux m (i + 1) remaining (out.push result)

/-- Tail-recursive Clifford-conjugation loop with arithmetic parity decoding. -/
private def conjugatePackedAux (n : Nat) (p : Parity) (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! i
      let result := if conjugateNegates (unpackIdxValid n p i) then -value else value
      conjugatePackedAux n p m (i + 1) remaining (out.push result)

/-- Clifford conjugate: multiplies each grade-k blade by `(-1)^(k(k+1)/2)`. -/
@[inline]
def conjugate (m : @& MV sig p) : MV sig p :=
  let sz := storageSize n p
  match p with
  | .full =>
      ⟨conjugateFullAux m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩
  | .even =>
      ⟨conjugatePackedAux n .even m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩
  | .odd =>
      ⟨conjugatePackedAux n .odd m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-! ### Grade Projection -/

/-- Tail-recursive full-to-parity projection with arithmetic rank decoding. -/
private def parityPartAux (n : Nat) (p : Parity) (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let mask := unpackIdxValid n p i
      parityPartAux n p m (i + 1) remaining (out.push (m.get! mask))

/-- Project to even part (from full MV, extracting even-grade components) -/
@[inline]
def evenPart (m : @& MV sig .full) : MV sig .even :=
  if n == 0 then
    ⟨m.coeffs⟩
  else
    let sz := storageSize n .even
    ⟨parityPartAux n .even m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-- Project to odd part (from full MV, extracting odd-grade components) -/
@[inline]
def oddPart (m : @& MV sig .full) : MV sig .odd :=
  if n == 0 then
    ⟨m.coeffs⟩
  else
    let sz := storageSize n .odd
    ⟨parityPartAux n .odd m.coeffs 0 sz (FloatArray.emptyWithCapacity sz)⟩

/-- Tail-recursive grade projection for identity-indexed full storage. -/
private def gradeProjectFullAux (m : @& DataArray) (k i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := if popcount i == k then m.get! i else 0.0
      gradeProjectFullAux m k (i + 1) remaining (out.push value)

/-- Tail-recursive grade projection for even or odd packed storage. -/
private def gradeProjectPackedAux (n : Nat) (p : Parity) (m : @& DataArray)
    (k i : Nat) : Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let rankPopcount := popcount i
      let bladeGrade := rankPopcount + packedLowBit n p rankPopcount
      let value := if bladeGrade == k then m.get! i else 0.0
      gradeProjectPackedAux n p m k (i + 1) remaining (out.push value)

/-- Project to a single grade while preserving the packed parity storage.

For `.even` or `.odd`, projecting to a grade outside the parity simply produces
zero because every packed index already has the opposite parity filtered out. -/
@[inline]
def gradeProject (m : @& MV sig p) (k : Nat) : MV sig p :=
  if n == 0 then
    if k == 0 then ⟨m.coeffs⟩ else zero sig p
  else if k > n || !Parity.contains p k then
    zero sig p
  else
    let sz := storageSize n p
    match p with
    | .full =>
        ⟨gradeProjectFullAux m.coeffs k 0 sz (FloatArray.emptyWithCapacity sz)⟩
    | .even =>
        ⟨gradeProjectPackedAux n .even m.coeffs k 0 sz
          (FloatArray.emptyWithCapacity sz)⟩
    | .odd =>
        ⟨gradeProjectPackedAux n .odd m.coeffs k 0 sz
          (FloatArray.emptyWithCapacity sz)⟩

instance instGAGradeProject : GAGradeProject (MV sig p) where
  gradeProject := gradeProject

/-! ### Parity Widening -/

/-- Tail-recursive parity widening. Each packed rank owns one adjacent pair of
full-storage masks, so one input read emits two output coefficients. -/
private def parityToFullAux (n : Nat) (p : Parity) (m : @& DataArray) (i : Nat) :
    Nat → FloatArray → FloatArray
  | 0, out => out
  | remaining + 1, out =>
      let value := m.get! i
      let low := packedLowBit n p (popcount i)
      let out' :=
        if low == 0 then
          (out.push value).push 0.0
        else
          (out.push 0.0).push value
      parityToFullAux n p m (i + 1) remaining out'

/-- Widen even to full (unpacks even storage into full storage) -/
@[inline]
def evenToFull (m : @& MV sig .even) : MV sig .full :=
  if n == 0 then
    ⟨m.coeffs⟩
  else
    let sz := storageSize n .even
    ⟨parityToFullAux n .even m.coeffs 0 sz
      (FloatArray.emptyWithCapacity (storageSize n .full))⟩

/-- Widen odd to full (unpacks odd storage into full storage) -/
@[inline]
def oddToFull (m : @& MV sig .odd) : MV sig .full :=
  if n == 0 then
    zero sig .full
  else
    let sz := storageSize n .odd
    ⟨parityToFullAux n .odd m.coeffs 0 sz
      (FloatArray.emptyWithCapacity (storageSize n .full))⟩

/-! ### Typeclass Instances -/

instance instZero : Zero (MV sig p) where
  zero := zero sig p

instance instOneEven : One (MV sig .even) where
  one := one sig

instance instOneFull : One (MV sig .full) where
  one := oneFull sig

instance instInhabited : Inhabited (MV sig p) where
  default := zero sig p

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

instance instSMulFloat : SMul Float (MV sig p) where
  smul := smul

instance instAdd : Add (MV sig p) where
  add := add

instance instSub : Sub (MV sig p) where
  sub := sub

instance instNeg : Neg (MV sig p) where
  neg := neg

instance instCoeEvenFull : Coe (MV sig .even) (MV sig .full) := ⟨evenToFull⟩
instance instCoeOddFull : Coe (MV sig .odd) (MV sig .full) := ⟨oddToFull⟩

/-- Full packed `MV` supports the generic `GAlgebra` API.

Parity-indexed `.even` and `.odd` values cannot implement this single-carrier
typeclass because products may change parity. Full storage can represent every
grade, so it is the right packed target for polymorphic algorithms. -/
instance instGAlgebraFull : GAlgebra sig (MV sig .full) Float where
  basisVector i := ofPairs sig .full [(1 <<< i.val, 1.0)]
  scalar x := ofPairs sig .full [(0, x)]
  zero := zero sig .full
  one := oneFull sig
  blade bits := ofPairs sig .full [(bits.toNat, 1.0)]
  mul := fun a b => mulDirect a b
  wedge := fun a b => wedge a b
  leftContract := fun a b => leftContract a b
  rightContract := fun a b => rightContract a b
  reverse := rev
  involute := involute
  conjugate := conjugate
  scalarPart := scalarPart
  add := add
  neg := neg
  smul := smul
  gradeProject := gradeProject

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

@[inline, always_inline]
private def mvSandwichGeneric {n : ℕ} {sig : Signature n} {p : Parity}
    (R : MV sig .even) (x : MV sig p) : MV sig p :=
  -- R * x gives parity (even * p) = p
  -- (R * x) * R† gives parity (p * even) = p
  let Rx : MV sig p := ⟨MV.mulKernelDirect sig .even p R.coeffs x.coeffs⟩
  ⟨MV.mulKernelDirect sig p .even Rx.coeffs (MV.rev R).coeffs⟩

/-- Sandwich product: `R * x * R†` (rotation/reflection).

PGA3 odd multivectors use the shared scalarized kernel, which covers both
points and planes without materializing the intermediate product or reverse.
-/
@[inline, always_inline]
def mvSandwich {n : ℕ} {sig : Signature n} {p : Parity}
    (R : MV sig .even) (x : MV sig p) : MV sig p :=
  match p with
  | .odd =>
    if n == 4 && sig.metric.toNat == 0 && sig.degenerate.toNat == 8 then
      ⟨PGA3Kernel.motorSandwichOdd R.coeffs x.coeffs⟩
    else
      mvSandwichGeneric R x
  | .even => mvSandwichGeneric R x
  | .full => mvSandwichGeneric R x

/-! ## PGA Subtypes

These are lightweight aliases of `MV` for common PGA entities.  They preserve
the packed representation and inherit multiplication from the base `MV` type. -/

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
