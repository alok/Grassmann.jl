import Bench.Grassmann.Common

/-!
# The allocation floor of a typed result (Lean only, `grassmann/floor/…`)

Every vector-valued typed result is a fresh `FloatArray` unless an operand of its size is
exclusive (docs/PERF.md). These cases take the cost of one result apart, at the storage sizes of
`ℝ3` chains (`d = 3`), `ℝ3` multivectors (`d = 8`) and `CGA3` multivectors (`d = 32`), over the
`K = 1024` operands of a ring (one "operation" per operand):

* `read`: sum the operand (no result: the harness's own cost);
* `in place`: write one entry of an exclusive array (the exclusivity check and the store, no
  allocation: what a kernel writing into an exclusive operand pays);
* `copy`: write one entry of a *shared* array, then sum it (`lean_copy_float_array`:
  allocate, `memcpy`, and free the copy after the sum: what every typed result pays);
* `push`: build a fresh array of `d` entries by `FloatArray.push` (the out-of-line
  `lean_float_array_push` per entry, the emitter's first design);
* `ctor`: allocate and free a three-`Float` structure (a small object without a copy).
-/

namespace Bench.Grassmann

open Bench

/-- Three unboxed floats in one heap object. -/
structure F3 where
  /-- First. -/
  a : Float
  /-- Second. -/
  b : Float
  /-- Third. -/
  c : Float

/-- A fresh `F3` (out of line, so the object is really allocated). -/
@[noinline] def mkF3 (x : Float) : F3 := ⟨x, x + 1, x + 2⟩

/-- `d` pushes onto an empty array. -/
@[specialize] def pushN (x : Float) : Nat → FloatArray → FloatArray
  | 0, a => a
  | k + 1, a => pushN x k (a.push x)

/-- Write entry `0` of an array `k` times (each write into the previous result). -/
@[specialize] def setN (a : FloatArray) : Nat → FloatArray
  | 0 => a
  | k + 1 => setN (a.set! 0 (a.get! 1)) k

/-- The floor cases at storage size `d`. -/
def floorCases (d : Nat) : BenchM Unit := do
  let p := s!"d={d}, K={ringSize}"
  let fs := randFloats (d * ringSize) (0xF100 + d.toUInt64) (-1) 1
  let xs : Array FloatArray := (Array.range ringSize).map fun i =>
    ⟨(Array.range d).map fun j => fs[i * d + j]!⟩
  let k (s : String) := s!"floor/{s} d={d}"
  case1 (k "read") (fun (a : FloatArray) => a.foldl (· + ·) 0) xs p
  bench (k "in place") (ops := ringSize) (param := p) fun s =>
    let a := FloatArray.mk (xs[s % ringSize]!.data)
    (setN a ringSize).foldl (· + ·) 0
  case1 (k "copy") (fun (a : FloatArray) => (a.set! 0 (a.get! 1)).foldl (· + ·) 0) xs p
  case1 (k "push") (fun (a : FloatArray) => (pushN (a.get! 0) d (FloatArray.emptyWithCapacity d)).foldl (· + ·) 0) xs p
  case1 (k "ctor") (fun (a : FloatArray) => let f := mkF3 (a.get! 0); f.a + f.b + f.c) xs p

/-- The suite's floor cases. -/
def floors : BenchM Unit := do
  floorCases 3
  floorCases 8
  floorCases 32

end Bench.Grassmann
