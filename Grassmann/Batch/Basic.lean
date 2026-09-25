/-
The batch containers (`Grassmann.Batch`): `Batch X`, element access, and the loop the batch
kernels run.
-/
import Grassmann.Types.Convert

namespace Grassmann

open DirectSum StaticVectors AbstractTensors

/-- `len` elements of the container `X`, stored flat and element-major: element `i` is
`data[i·k, …, i·k + k - 1]`, `k` the storage size of `X` (`BatchElem.width`). -/
structure Batch (X : Type) where
  /-- Number of elements. -/
  len : Nat
  /-- The coefficients, `len · k` of them. -/
  data : FloatArray
  deriving Inhabited

/-- A batch of grade-`G` chains (Julia `Vector{Chain{V,G,Float64}}`). -/
abbrev ChainArray (V : TensorBundle) (G : Nat) := Batch (Chain V G Float)
/-- A batch of halves (`odd = false`: spinors). -/
abbrev HalfArray (V : TensorBundle) (odd : Bool) := Batch (Half V odd Float)
/-- A batch of spinors (Julia `Vector{Spinor{V,Float64}}`). -/
abbrev SpinorArray (V : TensorBundle) := Batch (Half V false Float)
/-- A batch of multivectors (Julia `Vector{Multivector{V,Float64}}`). -/
abbrev MultivectorArray (V : TensorBundle) := Batch (Multivector V Float)

/-- The element types of batches: containers with `Float` coefficients. -/
class BatchElem (X : Type) where
  /-- Coefficients per element (the storage size). -/
  width : Nat
  /-- The coefficients of an element (`width` of them). -/
  coeffs : X → FloatArray
  /-- The element whose coefficients are `data[o, …, o + width - 1]` (zero past the end). -/
  read : FloatArray → Nat → X

namespace BatchElem

/-- The `k` coefficients at offset `o`, as a fresh vector (zero past the end). -/
@[inline] def slice (k : Nat) (a : FloatArray) (o : Nat) : Values Float k :=
  Values.ofFn fun j => a.get! (o + j.1)

end BatchElem

section Instances

variable {V : TensorBundle} {G : Nat} {p : Bool}

instance : BatchElem (Chain V G Float) where
  width := Leibniz.binomial V.n G
  coeffs x := x.v.data
  read a o := ⟨BatchElem.slice _ a o⟩

instance : BatchElem (Half V p Float) where
  width := halfDim V.n p
  coeffs x := x.v.data
  read a o := ⟨BatchElem.slice _ a o⟩

instance : BatchElem (Multivector V Float) where
  width := 2 ^ V.n
  coeffs x := x.v.data
  read a o := ⟨BatchElem.slice _ a o⟩

end Instances

namespace Batch

/-- `m` zeros, as a fresh array. -/
def zerosArray (m : Nat) : FloatArray := go m (FloatArray.emptyWithCapacity m)
where
  /-- Push `k` zeros. -/
  go : Nat → FloatArray → FloatArray
    | 0, a => a
    | k + 1, a => go k (a.push 0)

variable {X : Type} [BatchElem X]

/-- `n` zero elements. -/
def zeros (n : Nat) : Batch X := ⟨n, zerosArray (n * BatchElem.width X)⟩

/-- Pack elements into a batch (Julia `collect`). -/
def ofArray (xs : Array X) : Batch X :=
  ⟨xs.size, xs.foldl (init := FloatArray.emptyWithCapacity (xs.size * BatchElem.width X))
    fun acc x => (BatchElem.coeffs x).foldl (·.push ·) acc⟩

/-- Element `i` (a fresh element; zero past the end). -/
@[inline] def get (b : Batch X) (i : Nat) : X := BatchElem.read b.data (i * BatchElem.width X)

/-- Unpack into an array of elements. -/
def toArray (b : Batch X) : Array X := (Array.range b.len).map b.get

/-- The sum of the coefficients of the first and the last element (a cheap benchmark checksum;
the Julia twin computes the same). -/
def check (b : Batch X) : Float :=
  let k := BatchElem.width X
  let sumAt (o : Nat) : Float := (List.range k).foldl (fun acc j => acc + b.data.get! (o + j)) 0
  if b.len == 0 then 0 else sumAt 0 + sumAt ((b.len - 1) * k)

/-! ## The loop the batch kernels run

A batch kernel (`batch%`) pads its operands to the length its loop reads (`pad`: the operand
itself for every well-formed batch), takes an output array of exactly the length it writes
(`outputArray`), and then reads and writes with `rdU`/`wrU`: logically the checked `rd`/`wr`,
compiled as unchecked `uget`/`uset`, since every offset is in range by construction (a checked
read is a compare and a branch per coefficient, and the branches keep the loads from being
scheduled early: measured 1.5× on the `CGA3` multivector product). -/

/-- `i < a.usize` bounds the array. -/
theorem usize_lt_size (a : FloatArray) (i : USize) (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := USize.lt_iff_toNat_lt.mp h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [FloatArray.usize, Nat.toUSize_eq]
    exact Nat.mod_le _ _
  omega

/-- Read coefficient `i` (zero past the end). -/
@[inline] def rd (a : FloatArray) (i : USize) : Float :=
  if h : i < a.usize then a.uget i (usize_lt_size a i h) else 0

/-- Write coefficient `i` (in place when `a` is exclusive; nothing past the end). -/
@[inline] def wr (a : FloatArray) (i : USize) (x : Float) : FloatArray :=
  if h : i < a.usize then a.uset i x (usize_lt_size a i h) else a

/-- The unchecked read behind `rdU`. -/
@[inline] unsafe def rdUImpl (a : FloatArray) (i : USize) : Float := a.uget i lcProof

/-- The unchecked write behind `wrU`. -/
@[inline] unsafe def wrUImpl (a : FloatArray) (i : USize) (x : Float) : FloatArray := a.uset i x lcProof

/-- `rd` for an offset in range: logically `rd`, compiled without the bounds check. **Only for
the batch kernels**, whose offsets are in range by construction (`pad`, `outputArray`); an
offset out of range reads arbitrary memory. -/
@[implemented_by rdUImpl] def rdU (a : FloatArray) (i : USize) : Float := rd a i

/-- `wr` for an offset in range: logically `wr`, compiled without the bounds check (the
exclusivity check of `uset` stays). **Only for the batch kernels** (see `rdU`). -/
@[implemented_by wrUImpl] def wrU (a : FloatArray) (i : USize) (x : Float) : FloatArray := wr a i x

/-- `a` extended with zeros to `m` coefficients, the slow path of `pad`. -/
def padSlow (a : FloatArray) (m : Nat) : FloatArray := go (m - a.size) a
where
  /-- Push `k` zeros. -/
  go : Nat → FloatArray → FloatArray
    | 0, a => a
    | k + 1, a => go k (a.push 0)

/-- `a` extended with zeros to at least `m` coefficients: `a` itself when it is long enough
(every well-formed batch); reading it with `rd` below `m` gives the same values either way. -/
@[inline] def pad (a : FloatArray) (m : Nat) : FloatArray := if m ≤ a.size then a else padSlow a m

private unsafe def zerosCacheImpl : IO.Ref (Array FloatArray) := unsafeBaseIO (IO.mkRef #[])

/-- A few zero arrays of recently used lengths (run time only). -/
@[implemented_by zerosCacheImpl]
private opaque zerosCache : IO.Ref (Array FloatArray)

private unsafe def zerosSharedImpl (m : Nat) : FloatArray := unsafeBaseIO do
  let c ← zerosCache.get
  match c.find? (·.size == m) with
  | some z => return z
  | none =>
    let z := zerosArray m
    zerosCache.set ((if c.size ≥ 8 then c.extract 1 c.size else c).push z)
    return z

/-- `m` zeros: logically `zerosArray m`; at run time a shared zero array of each recently used
length, so that a kernel's output costs one copy (a `memcpy`, at its first write) instead of
`m` pushes (measured 8 ns per element of a `Spinor ℝ3` batch). -/
@[implemented_by zerosSharedImpl] def zerosShared (m : Nat) : FloatArray := zerosArray m

/-- The batch loop: `body i out` for `i = start, …, start + fuel - 1`, threading the output
array (tail-recursive, `USize` index; specialized at each `batch%` site on its body). -/
@[specialize] def loop (body : USize → FloatArray → FloatArray) : Nat → USize → FloatArray → FloatArray
  | 0, _, out => out
  | fuel + 1, i, out => loop body fuel (i + 1) (body i out)

/-- The output array of a batch kernel: `out` when it has exactly `m` coefficients (its storage
is reused, in place when exclusive), else a copy of shared zeros. -/
@[inline] def outputArray (out : FloatArray) (m : Nat) : FloatArray :=
  if out.size == m then out else zerosShared m

end Batch

end Grassmann
