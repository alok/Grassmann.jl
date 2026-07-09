/-
  Grassmann/DataArray.lean - unboxed Float storage for numeric kernels

  The core Grassmann runtime deliberately uses Lean's built-in `FloatArray`.
  `FloatArray` is represented by a contiguous native array of doubles, has a
  stable Lean runtime C API, and does not pull the optional SciLean/Verso stack
  into every consumer of the algebra library.

  The public aliases below retain the old names while the hot `MV` path uses
  `DataArray` directly.  The dimension parameters on `GrassmannArray` and
  `EvenArray` document the intended layout; `MV` owns the runtime size checks.
-/
import Init.Data.FloatArray

namespace Grassmann

/-! ### Unboxed runtime storage -/

/-- Contiguous, unboxed Float storage used by `MV` kernels. -/
abbrev DataArray := FloatArray

namespace DataArray

/-- Number of elements. -/
@[inline, always_inline]
def len (a : DataArray) : Nat := a.size

/-- Empty data array. -/
@[inline]
def empty : DataArray := FloatArray.empty

private def replicateAux (x : Float) : Nat → FloatArray → FloatArray
  | 0, out => out
  | n + 1, out => replicateAux x n (out.push x)

/-- Allocate a DataArray filled with `x`. -/
@[inline]
def replicate (n : Nat) (x : Float) : DataArray :=
  replicateAux x n (FloatArray.emptyWithCapacity n)

/-- Allocate a zero-filled DataArray of length `n`. -/
@[inline]
def zeros (n : Nat) : DataArray := replicate n 0.0

/-- Read a coefficient through Lean's native FloatArray runtime primitive.

All `MV` constructors maintain the packed-storage length invariant, so hot
kernels stay in bounds.  The runtime primitive still handles an accidental
out-of-bounds read without introducing a second Lean-level bounds branch.
-/
@[inline, always_inline]
def get! (a : @& DataArray) (i : Nat) : Float :=
  FloatArray.get! a i

/-- Write a coefficient. Out-of-bounds writes preserve the input array. -/
@[inline, always_inline]
def set! (a : DataArray) (i : Nat) (x : Float) : DataArray :=
  FloatArray.set! a i x

/-- Copy a boxed Lean array into contiguous Float storage. -/
@[inline]
def ofArray (arr : Array Float) : DataArray :=
  arr.foldl (fun out x => out.push x) (FloatArray.emptyWithCapacity arr.size)

/-- Copy contiguous Float storage into a boxed Lean array. -/
@[inline]
def toArray (a : DataArray) : Array Float :=
  a.foldl (fun out x => out.push x) (Array.mkEmpty a.size)

/-- Left fold over a subrange of the contiguous storage. -/
@[inline]
def foldl {β : Type} (f : β → Float → β) (init : β) (a : DataArray)
    (start : Nat := 0) (stop : Nat := a.size) : β :=
  FloatArray.foldl f init a start (min stop a.size)

end DataArray

/-! ### Grassmann layout aliases -/

/-- Full multivector coefficient storage. Expected length: `2^n`. -/
abbrev GrassmannArray (_n : Nat) := DataArray

/-- Packed even multivector coefficient storage. Expected length: `2^(n-1)`. -/
abbrev EvenArray (_n : Nat) := DataArray

/-- Zero-filled full multivector storage. -/
@[inline]
def GrassmannArray.zeros (n : Nat) : GrassmannArray n :=
  DataArray.zeros (Nat.pow 2 n)

/-- Scalar full multivector storage. -/
@[inline]
def GrassmannArray.scalar (n : Nat) (x : Float) : GrassmannArray n :=
  (GrassmannArray.zeros n).set! 0 x

/-- Zero-filled packed-even multivector storage. -/
@[inline]
def EvenArray.zeros (n : Nat) : EvenArray n :=
  DataArray.zeros (Nat.pow 2 (Nat.sub n 1))

/-- Scalar packed-even multivector storage. -/
@[inline]
def EvenArray.scalar (n : Nat) (x : Float) : EvenArray n :=
  (EvenArray.zeros n).set! 0 x

/-- Read a coefficient from full multivector storage. -/
@[inline, always_inline]
def GrassmannArray.get! {n : Nat} (arr : @& GrassmannArray n) (i : Nat) : Float :=
  DataArray.get! arr i

/-- Write a coefficient in full multivector storage. -/
@[inline, always_inline]
def GrassmannArray.set! {n : Nat} (arr : GrassmannArray n) (i : Nat) (x : Float) :
    GrassmannArray n :=
  DataArray.set! arr i x

/-- Read a coefficient from packed-even multivector storage. -/
@[inline, always_inline]
def EvenArray.get! {n : Nat} (arr : @& EvenArray n) (i : Nat) : Float :=
  DataArray.get! arr i

/-- Write a coefficient in packed-even multivector storage. -/
@[inline, always_inline]
def EvenArray.set! {n : Nat} (arr : EvenArray n) (i : Nat) (x : Float) : EvenArray n :=
  DataArray.set! arr i x

/-- Construct full multivector storage from a coefficient function. -/
@[inline]
def GrassmannArray.ofFn {n : Nat} (f : Fin (Nat.pow 2 n) → Float) : GrassmannArray n :=
  DataArray.ofArray (Array.ofFn f)

/-- Construct packed-even storage from a coefficient function. -/
@[inline]
def EvenArray.ofFn {n : Nat} (f : Fin (Nat.pow 2 (Nat.sub n 1)) → Float) : EvenArray n :=
  DataArray.ofArray (Array.ofFn f)

end Grassmann
