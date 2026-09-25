import JuliaBase.FloatLit

/-!
# Inline bit casts: `reinterpret` without a runtime call

Julia's scalar kernels (`base/special/*.jl`) read and build floats through their bit patterns
(`reinterpret(UInt64, x)`, `reinterpret(Float64, u)`) on every call. In compiled Lean,
`Float.toBits`/`Float.ofBits` (and the `Float32` ones) are **out-of-line** runtime functions
(`LEAN_EXPORT uint64_t lean_float_to_bits(double)` in the 4.35 `lean.h`): each use is a `bl`,
and around it the kernel spills its live floats and reloads its constants. Replacing the two
casts of `F64.log` by inline ones took it from 6.8 to 3.3 ns (Julia 2.9; `docs/PERF.md`).

`Bits.toBits`, `Bits.ofBits`, `Bits.toBits32`, `Bits.ofBits32` are those casts written as
`@[extern c inline]` C expressions (a union compound literal, which clang and gcc compile to a
single `fmov`), with **exactly the semantics of the core functions**, including their NaN
canonicalization (`lean_float_to_bits` returns `0x7ff8000000000000` for every NaN, and
`lean_float_of_bits` turns every NaN pattern into the quiet NaN): logically each one *is* the core
function (its Lean body), and the C agrees with the runtime's C bit for bit. No C file, no
`lakefile` change: the expression is pasted into the generated C of every caller.

**The interpreter.** An `@[extern]` declaration has no IR body, so Lean's interpreter (`#eval`,
`#guard`, elaboration-time evaluation, the editor) must find a native symbol for it, and our
package's objects are not loaded into the `lean` process. The interpreter looks for the boxed
symbol `<mangled>___boxed` first and then for the declaration's `@[export]` name
(`ir_interpreter.cpp`, `lookup_symbol`), which it calls with boxed arguments. So each cast is
also `@[export]`ed under the name of the **core runtime's boxed wrapper of the same function**,
`l_Float_toModel___boxed` for `Float.toModel` (the `extern "lean_float_to_bits"` projection of
`Float` onto its `UInt64` model, the same function as `Float.toBits`), and so on: the interpreter
then runs the runtime's own implementation (boxed float in, boxed bits out), and compiled code
runs the inline expression. `Tests/JuliaBase/Bits.lean` checks both (`#guard` in the
interpreter, and the compiled test driver).

The export only renames the (never emitted) C function of the `@[extern]` declaration: the C of a
module that calls a cast declares a prototype `uint64_t l_Float_toModel___boxed(double)`. A
module that *also* used `Float.toModel` itself as a first-class function (a closure, which the
compiler never builds for it in practice) would see two conflicting prototypes and fail to
compile; that is why the export names are the model projections and not `Float.toBits`.
-/

namespace JuliaBase

namespace Bits

/-- `reinterpret(UInt64, x)`: the bits of `x`, every NaN as `0x7ff8000000000000` (exactly
`Float.toBits`), as an inline C expression. -/
@[extern c inline
  "(__builtin_isnan(#1) ? 0x7ff8000000000000ULL : ((union { double d; uint64_t u; }){ .d = #1 }).u)",
  export l_Float_toModel___boxed]
def toBits (x : Float) : UInt64 := x.toBits

/-- `reinterpret(Float64, u)`: the float with bits `u`, every NaN pattern as the quiet NaN
(exactly `Float.ofBits`), as an inline C expression. -/
@[extern c inline
  "({ double _jb_d = ((union { uint64_t u; double d; }){ .u = #1 }).d; __builtin_isnan(_jb_d) ? __builtin_nan(\"\") : _jb_d; })",
  export l_Float_ofModel___boxed]
def ofBits (u : UInt64) : Float := Float.ofBits u

/-- `reinterpret(UInt32, x)` for a `Float32` (exactly `Float32.toBits`: NaN as `0x7fc00000`). -/
@[extern c inline
  "(__builtin_isnan(#1) ? 0x7fc00000U : ((union { float f; uint32_t u; }){ .f = #1 }).u)",
  export l_Float32_toModel___boxed]
def toBits32 (x : Float32) : UInt32 := x.toBits

/-- `reinterpret(Float32, u)` (exactly `Float32.ofBits`: NaN patterns as the quiet NaN). -/
@[extern c inline
  "({ float _jb_f = ((union { uint32_t u; float f; }){ .u = #1 }).f; __builtin_isnan(_jb_f) ? __builtin_nanf(\"\") : _jb_f; })",
  export l_Float32_ofModel___boxed]
def ofBits32 (u : UInt32) : Float32 := Float32.ofBits u

/-- `trunc(Int64, x)` for an integral `x` with `|x| < 2^51` (a rounded quadrant, a rounded
`N`): `x + 1.5·2^52` is then an exact integer in `(2^52, 2^53)`, converted by the inline
`Float.toUInt64` (`Float.toInt64` calls the out-of-line `lean_float_isnan`), and the offset is
subtracted with wrap-around. Outside that range the result is unspecified (but total). -/
@[inline] def toInt64Small (x : Float) : Int64 :=
  ((x + f64! 6755399441055744.0).toUInt64 - 6755399441055744).toInt64

end Bits

namespace FloatArray'

/-- `i < a.usize` bounds the index by the size (`usize` is the size modulo `2^w`). -/
theorem usize_lt_size {a : FloatArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := USize.lt_iff_toNat_lt.mp h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [FloatArray.usize, Nat.toUSize_eq]
    exact Nat.mod_le _ _
  omega

end FloatArray'

namespace Bits

/-- `a[i]` for a `USize` index, `0.0` past the end: one inline `size_t` comparison and an
unboxed read (`a[i]!` calls an out-of-line bounds-check closure, `a.get! i` boxes a `Nat`).
For a module-level table use `FTable`: `t.usize` of a constant `t` is a closed term, read
through an atomic once-cell on every call. -/
@[inline] def rd (a : FloatArray) (i : USize) : Float :=
  if h : i < a.usize then a.uget i (FloatArray'.usize_lt_size h) else f64! 0.0

end Bits

/-- A lookup table of `n` unboxed floats whose size is part of its type: a read compares the
index with the `USize` literal `n` (an immediate after inlining: no load of the size, and no
closed term, which `t.usize` of a module-level `t` would be). Julia's kernels index their tables
(`J_TABLE`, `t_log_Float64`, …) with values in range by construction, so the branch is never
taken. -/
structure FTable (n : USize) where
  /-- the entries -/
  data : FloatArray
  /-- the size is `n` -/
  size_eq : data.size = n.toNat

namespace FTable

/-- The table `reinterpret(Float64, f t[i])` (decoded once, when the module is initialized). -/
def ofBits {m : Nat} {α : Type} (t : Array α) (f : α → UInt64) (h : t.size = m)
    (hm : m < 4294967296 := by decide) : FTable (USize.ofNat m) :=
  ⟨⟨t.map fun b => Float.ofBits (f b)⟩, by simp [FloatArray.size, h, USize.toNat_ofNat_of_lt_32 hm]⟩

/-- Entry `i` (`0.0` for `i ≥ n`, which the kernels never produce). -/
@[inline] def get {n : USize} (t : FTable n) (i : USize) : Float :=
  if h : i < n then t.data.uget i (by rw [t.size_eq]; exact USize.lt_iff_toNat_lt.mp h) else f64! 0.0

end FTable

end JuliaBase
