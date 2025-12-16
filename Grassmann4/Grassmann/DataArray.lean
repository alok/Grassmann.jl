/-
  Grassmann/DataArray.lean - "Plain data" arrays for numeric kernels

  Motivation:
  - A lot of GA performance comes down to *moving floats* efficiently.
  - Lean's `Array` is convenient, but numeric kernels benefit from a single,
    explicit representation that can later be swapped for SciLean's DataArray,
    GPU buffers, etc.
  - In the short term, we focus on `Float` and expose a tiny, inlinable API.

  Design:
  - `DataArray` is currently an alias for `FloatArray`.
  - We provide a small set of operations we rely on in hot loops.
  - Debug helpers route through `Grassmann.Linearity` to catch non-exclusive
    updates that would force copies.
-/
import Grassmann.Linearity

namespace Grassmann

/-- A contiguous numeric array for performance‑critical Float paths.

Today this is `FloatArray`. Long‑term this is meant to converge with SciLean's
`DataArray` concept (plain, unstructured data buffers). -/
abbrev DataArray := FloatArray

namespace DataArray

/-- Number of elements. -/
@[inline] def size (a : DataArray) : Nat := FloatArray.size a

/-- Empty data array. -/
@[inline] def empty : DataArray := FloatArray.empty

/-- Construct from an `Array Float`. -/
@[inline] def ofArray (a : Array Float) : DataArray := FloatArray.mk a

/-- View as an `Array Float`. -/
@[inline] def toArray (a : DataArray) : Array Float := FloatArray.data a

/-- Allocate a `DataArray` of length `n`, filled with `x`. -/
@[inline] def replicate (n : Nat) (x : Float) : DataArray :=
  FloatArray.mk (Array.replicate n x)

/-- Allocate a zero-filled `DataArray` of length `n`. -/
@[inline] def zeros (n : Nat) : DataArray := replicate n 0.0

/-- Bounds-checked read (with proof, erased at runtime). -/
@[inline] def get (a : DataArray) (i : Nat)
    (h : i < FloatArray.size a := by get_elem_tactic) : Float :=
  FloatArray.get a i h

/-- Unsafe read (panics on OOB). -/
@[inline] def get! (a : DataArray) (i : Nat) : Float := FloatArray.get! a i

/-- Unsafe write (may be destructive if `a` is exclusive). -/
@[inline] def set! (a : DataArray) (i : Nat) (x : Float) : DataArray := FloatArray.set! a i x

/-- Append one element. -/
@[inline] def push (a : DataArray) (x : Float) : DataArray := FloatArray.push a x

/-- Left fold over elements. -/
@[inline] def foldl {β : Type} (f : β -> Float -> β) (init : β) (a : DataArray)
    (start : Nat := 0) (stop : Nat := FloatArray.size a) : β :=
  FloatArray.foldl f init a start stop

/-! ### Debugging exclusivity / linearity

These helpers are intended for perf debugging. When a buffer is unexpectedly
non-exclusive, `set!` will copy, killing performance.
-/

/-- Print a warning if `a` is not exclusive (i.e. updates would copy). -/
@[inline] unsafe def dbgTraceIfNotExclusive (tag : String) (a : DataArray) : DataArray :=
  Grassmann.dbgTraceIfShared (s!"[DataArray] {tag}") a

/-- Panic if `a` is not exclusive. -/
@[inline] unsafe def dbgPanicIfNotExclusive (tag : String) (a : DataArray) : DataArray :=
  Grassmann.dbgPanicIfNotExclusive (s!"[DataArray] {tag}") a

/-- `set!` that asserts exclusivity first (debug). -/
@[inline] unsafe def set!Exclusive (tag : String) (a : DataArray) (i : Nat) (x : Float) : DataArray :=
  FloatArray.set! (dbgPanicIfNotExclusive tag a) i x

end DataArray

end Grassmann
