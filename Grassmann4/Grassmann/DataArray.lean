/-
  Grassmann/DataArray.lean - SciLean-backed arrays for numeric kernels

  This module provides the numeric array backing for Grassmann algebra operations.
  We now use SciLean's DataArrayN as the "one true" backing type, which gives us:
  - Type-safe shape tracking via index types
  - GPU support via Metal (automatic on Apple Silicon)
  - BLAS integration for matrix operations
  - Unified API across CPU/GPU

  The main types:
  - `GrassmannArray n` = `Float^[Idx (2^n)]` for full multivectors
  - `EvenArray n` = `Float^[Idx (2^(n-1))]` for packed even elements
-/
import SciLean.Data.DataArray

namespace Grassmann

open SciLean

/-! ### Type aliases for Grassmann-specific shaped arrays -/

/-- Array for storing 2^n coefficients of a full multivector. -/
abbrev GrassmannArray (n : ℕ) := Float^[Idx (2^n)]

/-- Array for storing 2^(n-1) coefficients of an even multivector. -/
abbrev EvenArray (n : ℕ) := Float^[Idx (2^(n-1))]

/-! ### Constructors -/

/-- Zero-filled array of size 2^n. -/
@[inline]
def GrassmannArray.zeros (n : ℕ) : GrassmannArray n :=
  ⟨DataArray.mkZero (2^n), sorry_proof⟩

/-- Scalar multivector (1 in position 0, rest zeros). -/
@[inline]
def GrassmannArray.scalar (n : ℕ) (x : Float) : GrassmannArray n :=
  let arr := GrassmannArray.zeros n
  arr.set ⟨0, sorry_proof⟩ x

/-- Zero-filled even array of size 2^(n-1). -/
@[inline]
def EvenArray.zeros (n : ℕ) : EvenArray n :=
  ⟨DataArray.mkZero (2^(n-1)), sorry_proof⟩

/-- Scalar even multivector. -/
@[inline]
def EvenArray.scalar (n : ℕ) (x : Float) : EvenArray n :=
  let arr := EvenArray.zeros n
  arr.set ⟨0, sorry_proof⟩ x

/-! ### Accessors (compatibility layer) -/

/-- Get coefficient at index (unsafe, panics on OOB). -/
@[inline]
def GrassmannArray.get! {n : ℕ} (arr : GrassmannArray n) (i : Nat) : Float :=
  if _ : i < 2 ^ n then
    arr.get ⟨i.toUSize, sorry_proof⟩
  else
    panic! s!"GrassmannArray.get!: index {i} out of bounds for size {2 ^ n}"

/-- Set coefficient at index (unsafe). -/
@[inline]
def GrassmannArray.set! {n : ℕ} (arr : GrassmannArray n) (i : Nat) (x : Float) : GrassmannArray n :=
  if _ : i < 2 ^ n then
    arr.set ⟨i.toUSize, sorry_proof⟩ x
  else
    arr

/-- Get coefficient at index (unsafe). -/
@[inline]
def EvenArray.get! {n : ℕ} (arr : EvenArray n) (i : Nat) : Float :=
  if _ : i < 2 ^ (n - 1) then
    arr.get ⟨i.toUSize, sorry_proof⟩
  else
    panic! s!"EvenArray.get!: index {i} out of bounds for size {2 ^ (n - 1)}"

/-- Set coefficient at index (unsafe). -/
@[inline]
def EvenArray.set! {n : ℕ} (arr : EvenArray n) (i : Nat) (x : Float) : EvenArray n :=
  if _ : i < 2 ^ (n - 1) then
    arr.set ⟨i.toUSize, sorry_proof⟩ x
  else
    arr

/-! ### Conversions -/

/-- Create from function. -/
@[inline]
def GrassmannArray.ofFn {n : ℕ} (f : Fin (2 ^ n) → Float) : GrassmannArray n :=
  SciLean.ofFn fun (i : Idx (2 ^ n)) => f ⟨i.1.toNat, sorry_proof⟩

/-- Create even array from function. -/
@[inline]
def EvenArray.ofFn {n : ℕ} (f : Fin (2 ^ (n - 1)) → Float) : EvenArray n :=
  SciLean.ofFn fun (i : Idx (2 ^ (n - 1))) => f ⟨i.1.toNat, sorry_proof⟩

/-! ### Legacy DataArray compatibility

These definitions maintain backward compatibility with code using the old API.
The legacy DataArray is now backed by SciLean's DataArray Float.
-/

/-- Legacy DataArray type - now backed by SciLean's DataArray. -/
abbrev DataArray := SciLean.DataArray Float

namespace DataArray

/-- Number of elements. -/
@[inline] def len (a : DataArray) : Nat := SciLean.DataArray.size a

/-- Empty data array. -/
@[inline] def empty : DataArray := ⟨ByteArray.empty, by decide⟩

/-- Allocate a zero-filled DataArray of length n. -/
@[inline] def zeros (n : Nat) : DataArray := SciLean.DataArray.mkZero n

/-- Allocate a DataArray filled with x. -/
@[inline] def replicate (n : Nat) (x : Float) : DataArray := SciLean.DataArray.replicate n x

/-- Unsafe read (panics on OOB). -/
@[inline] def get! (a : DataArray) (i : Nat) : Float :=
  let sz := SciLean.DataArray.size a
  if _ : i < sz then
    a.get ⟨i.toUSize, sorry_proof⟩
  else
    panic! s!"DataArray.get!: index {i} out of bounds"

/-- Unsafe write. -/
@[inline] def set! (a : DataArray) (i : Nat) (x : Float) : DataArray :=
  let sz := SciLean.DataArray.size a
  if _ : i < sz then
    a.set ⟨i.toUSize, sorry_proof⟩ x
  else
    a

/-- Construct from Array Float using recursive helper. -/
private def ofArrayAux (arr : Array Float) (da : DataArray) (i : Nat) : DataArray :=
  if h : i < arr.size then
    let da' := da.set ⟨i.toUSize, sorry_proof⟩ arr[i]
    ofArrayAux arr da' (i + 1)
  else
    da
termination_by arr.size - i

@[inline] def ofArray (arr : Array Float) : DataArray :=
  ofArrayAux arr (SciLean.DataArray.mkZero arr.size) 0

/-- Convert to Array Float using recursive helper. -/
private def toArrayAux (a : DataArray) (arr : Array Float) (i : Nat) (sz : Nat) : Array Float :=
  if h : i < sz then
    let v := a.get ⟨i.toUSize, sorry_proof⟩
    toArrayAux a (arr.push v) (i + 1) sz
  else
    arr
termination_by sz - i

@[inline] def toArray (a : DataArray) : Array Float :=
  let sz := SciLean.DataArray.size a
  toArrayAux a (Array.mkEmpty sz) 0 sz

/-- Left fold using recursive helper. -/
private def foldlAux {β : Type} (f : β → Float → β) (a : DataArray)
    (acc : β) (i : Nat) (stop : Nat) : β :=
  if _ : i < stop then
    let v := a.get ⟨i.toUSize, sorry_proof⟩
    foldlAux f a (f acc v) (i + 1) stop
  else
    acc
termination_by stop - i

@[inline] def foldl {β : Type} (f : β → Float → β) (init : β) (a : DataArray)
    (start : Nat := 0) (stop : Nat := SciLean.DataArray.size a) : β :=
  let sz := SciLean.DataArray.size a
  foldlAux f a init start (min stop sz)

end DataArray

end Grassmann
