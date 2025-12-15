/-!
  Grassmann/Linearity.lean - Debugging linear (exclusive) usage

  Lean's `Array` and `String` operations can update in-place when the underlying
  object is *exclusive* (single-threaded and reference count = 1). This is a big
  part of getting "mutable performance with pure APIs".

  When a value is *not* used linearly (e.g. you keep another reference around),
  the runtime must copy before updating, and performance can silently tank.

  This module provides opt-in checks to make that failure mode loud.
-/

namespace Grassmann

/-! ## Exclusivity checks -/

/-- `true` when `a` is exclusive (single-threaded and RC(a)=1). -/
@[inline] unsafe def isExclusive (a : α) : Bool :=
  isExclusiveUnsafe a

/-- `dbgTraceIfShared`, but upgraded to complain when `a` is *not exclusive*.

    Lean's built-in `_root_.dbgTraceIfShared` fires only when RC(a) > 1.
    For "I expected destructive updates", the stronger predicate is *exclusivity*
    (RC(a)=1 and single-threaded).

    This definition intentionally lives in the `Grassmann` namespace so existing
    code can just write `dbgTraceIfShared "..." arr` and get the stronger check.
 -/
@[inline] unsafe def dbgTraceIfShared (msg : String) (a : α) : α :=
  if isExclusiveUnsafe a then
    a
  else
    let _ := _root_.dbgTraceIfShared msg a
    dbgTrace s!"non-exclusive (not linear): {msg}" (fun _ => a)

/-- Backwards-friendly alias. -/
@[inline] unsafe abbrev dbgTraceIfNotExclusive (msg : String) (a : α) : α :=
  dbgTraceIfShared msg a

/-- Debug helper: *panic* when `a` is not exclusive.

    This is the "make it impossible to miss" version of `dbgTraceIfNotExclusive`.
 -/
@[inline] unsafe def dbgPanicIfNotExclusive {α : Type u} [Inhabited α] (msg : String) (a : α) : α :=
  if isExclusiveUnsafe a then
    a
  else
    let _ := _root_.dbgTraceIfShared msg a
    panic s!"non-exclusive (not linear): {msg}"

end Grassmann

/-! ## Array helpers

These wrappers are useful when you start writing "buffer reuse" style kernels:
take an output buffer, mutate it (via `set!`/`modify`), and return it.

If the caller accidentally keeps an alias to the buffer, the update becomes
non-destructive and you allocate/copy instead. These helpers make that loud.
-/

namespace Array

/-- `Array.modify` that asserts the input array is exclusive. -/
@[inline] unsafe def modifyExclusive (msg : String) (as : Array α) (i : Nat) (f : α → α) : Array α :=
  let as := Grassmann.dbgPanicIfNotExclusive msg as
  as.modify i f

/-- `Array.set!` that asserts the input array is exclusive. -/
@[inline] unsafe def set!Exclusive (msg : String) (as : Array α) (i : Nat) (a : α) : Array α :=
  let as := Grassmann.dbgPanicIfNotExclusive msg as
  as.set! i a

end Array
