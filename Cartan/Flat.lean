import Grassmann

/-!
# Flat `Float` loops with machine-word indices

The field kernels (`Cartan.Algebra`, `Cartan.Kernel`, `Cartan.Generated`) run over the flat
`FloatArray`s of whole fields. `FloatArray.get!`/`set!` take a `Nat` index: every access tests
that the index is a small (unboxed) number and bounds-checks it, and a `Nat` loop counter pays
overflow checks; `FloatArray.push` is an out-of-line runtime call (2.2 ns per element, measured).
The loops here use `USize` indices with `uget`/`uset` (the inline `lean_float_array_uget`/`uset`)
and are unrolled by four: the C compiler then merges the four exclusivity tests of `uset` into
one (the stores cannot alias the reference count), and a scalar map runs at 0.17 ns per
element, against 1.37 ns for the `Nat`/`set!` loop (docs/PERF.md, 2026-09-25).

**Output buffers.** A result is written *in place* over one of the operands
(`out := out.uset i (f out[i] …)`): the first write copies the operand when it is shared (one
`memcpy`, 0.1 ns per element), and when it is exclusive (a temporary, as in `(a + b) * 2`) nothing
is allocated. Results of another size are written over `zeros n`, a zero array that is cached
per size (the last size asked for), so a repeated operation copies it instead of pushing `n`
floats.

Bounds are carried as `Buf n = {a : FloatArray // a.size = n}` (erased at run time: a subtype is
represented by its value), so every index proof is arithmetic on `USize.toNat`.
-/

namespace Cartan.Flat

/-! ## Index lemmas -/

/-- `i < a.usize` bounds the index by the size (`usize` is the size modulo `2^w`). -/
theorem lt_size_of_lt_usize {a : FloatArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := USize.lt_iff_toNat_lt.mp h
  have h2 : a.usize.toNat = a.size % USize.size := by
    simp [FloatArray.usize, Nat.toUSize, USize.size]
  exact Nat.lt_of_lt_of_le (h2 ▸ h1) (Nat.mod_le _ _)

/-- `uset` keeps the size. -/
@[simp] theorem size_uset (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a; simp only [FloatArray.uset, FloatArray.size, Array.uset]; exact Array.size_set _

/-- The successor of an in-range index does not wrap around. -/
theorem toNat_succ {a : FloatArray} {i : USize} (h : i < a.usize) : (i + 1).toNat = i.toNat + 1 := by
  have h1 : i.toNat < a.usize.toNat := USize.lt_iff_toNat_lt.mp h
  have h2 : a.usize.toNat < 2 ^ System.Platform.numBits := USize.toNat_lt_two_pow_numBits _
  rw [USize.toNat_add, USize.toNat_one]
  exact Nat.mod_eq_of_lt (by omega)

/-- `(i + j).toNat ≤ i.toNat + j` (the sum may wrap, which only makes it smaller). -/
theorem toNat_add_le (i : USize) (j : Nat) : (i + USize.ofNat j).toNat ≤ i.toNat + j := by
  rw [USize.toNat_add]
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left USize.toNat_ofNat_le _)

/-- An index `i + j` below a bound that `i.toNat + j` is below. -/
theorem idx {n : Nat} {i : USize} {j : Nat} (h : i.toNat + j < n) : (i + USize.ofNat j).toNat < n :=
  Nat.lt_of_le_of_lt (toNat_add_le i j) h

/-- The first block of `k + 1` blocks of width `w` from `o` is in range. -/
theorem headLe {n : Nat} {o : USize} {w k : Nat} (h : o.toNat + w * (k + 1) ≤ n) :
    o.toNat + w ≤ n := by
  rw [Nat.mul_succ] at h; omega

/-- The other `k` blocks start at `o + w`. -/
theorem tailLe {n : Nat} {o : USize} {w k : Nat} (h : o.toNat + w * (k + 1) ≤ n) :
    (o + USize.ofNat w).toNat + w * k ≤ n :=
  Nat.le_trans (Nat.add_le_add_right (toNat_add_le o w) _) (by rw [Nat.mul_succ] at h; omega)

/-- Entry `j < w` of an in-range block of width `w` at `o`. -/
theorem idxW {n : Nat} {o : USize} {w : Nat} (h : o.toNat + w ≤ n) (j : Nat) (hj : j < w) :
    (o + USize.ofNat j).toNat < n :=
  idx (by omega)

/-! ## Sized buffers -/

/-- A `FloatArray` of length `n` (the proof is erased: at run time this is the array). -/
abbrev Buf (n : Nat) := {a : FloatArray // a.size = n}

namespace Buf

variable {n : Nat}

/-- Read entry `i`. -/
@[inline] def get (b : Buf n) (i : USize) (h : i.toNat < n) : Float := b.1.uget i (by rw [b.2]; exact h)

/-- Write entry `i` (in place when the buffer is exclusive). -/
@[inline] def set (b : Buf n) (i : USize) (x : Float) (h : i.toNat < n) : Buf n :=
  ⟨b.1.uset i x (by rw [b.2]; exact h), by rw [size_uset]; exact b.2⟩

end Buf

/-! ## Zero buffers -/

/-- `n` zeros, built without the cache: `FloatArray.mk (Array.replicate n 0)` (the runtime
unboxes the array in C, 1.4 ns per element; `n` pushes take 2.3 ns per element). -/
def zerosSlow (n : Nat) : FloatArray := ⟨Array.replicate n 0⟩

@[simp] theorem size_zerosSlow (n : Nat) : (zerosSlow n).size = n := by
  simp [zerosSlow, FloatArray.size]

/-- Sizes below this come from a table built once (a lookup is cheaper than the cache). -/
def zerosCacheMin : Nat := 64

/-- Number of sizes the zero cache keeps (most recently used first). -/
def zerosCacheSlots : Nat := 4

private unsafe def zerosCacheImpl : IO.Ref (Array FloatArray) := unsafeBaseIO (IO.mkRef #[])

/-- The zero arrays of the most recently used sizes. -/
@[implemented_by zerosCacheImpl]
private opaque zerosCache : IO.Ref (Array FloatArray)

/-- The zero arrays of the sizes below `zerosCacheMin`, built once (at initialization). -/
private def smallZeros : Array FloatArray := (Array.range zerosCacheMin).map zerosSlow

private unsafe def zerosImpl (n : Nat) : FloatArray :=
  if n < zerosCacheMin then smallZeros[n]! else unsafeBaseIO do
  let c ← zerosCache.get
  match c.findIdx? (·.size == n) with
  | some i =>
    let z := c[i]!
    if i != 0 then zerosCache.set (#[z] ++ c.eraseIdx! i)
    return z
  | none =>
    let z := zerosSlow n
    zerosCache.set ((#[z] ++ c).take zerosCacheSlots)
    return z

/-- `n` zeros (logically `zerosSlow n`). The arrays of the last `zerosCacheSlots` sizes asked for
are kept and returned shared, so the first write to one copies it (a `memcpy`, 0.1 ns per
element) and nothing is rebuilt; the cache is invisible to the logic. -/
@[implemented_by zerosImpl]
def zeros (n : Nat) : FloatArray := zerosSlow n

@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := size_zerosSlow n

/-- `zeros n` as a buffer. -/
@[inline] def zerosBuf (n : Nat) : Buf n := ⟨zeros n, size_zeros n⟩

/-! ## Maps and zips -/

/-- `out[j] := f out[j]` for `j ∈ [i, n)` (one element per step). -/
@[specialize] def mapTail {n : Nat} (f : Float → Float) (out : Buf n) (i : USize) : Buf n :=
  if hi : i < out.1.usize then
    have h := out.2 ▸ lt_size_of_lt_usize hi
    mapTail f (out.set i (f (out.get i h)) h) (i + 1)
  else out
termination_by n - i.toNat
decreasing_by rw [toNat_succ hi]; omega

/-- `out[j] := f out[j]` for the `4k` indices from `i`, four per step, then the tail. -/
@[specialize] def mapLoop {n : Nat} (f : Float → Float) :
    (k : Nat) → (out : Buf n) → (i : USize) → i.toNat + 4 * k ≤ n → Buf n
  | 0, out, i, _ => mapTail f out i
  | k + 1, out, i, h =>
    let x0 := out.get i (by omega)
    let x1 := out.get (i + 1) (idx (j := 1) (by omega))
    let x2 := out.get (i + 2) (idx (j := 2) (by omega))
    let x3 := out.get (i + 3) (idx (j := 3) (by omega))
    let o := out.set i (f x0) (by omega)
    let o := o.set (i + 1) (f x1) (idx (j := 1) (by omega))
    let o := o.set (i + 2) (f x2) (idx (j := 2) (by omega))
    let o := o.set (i + 3) (f x3) (idx (j := 3) (by omega))
    mapLoop f k o (i + 4) (Nat.le_trans (Nat.add_le_add_right (toNat_add_le i 4) _) (by omega))

/-- `[f a[j] | j < a.size]`, written over `a` (a copy of it when it is shared). -/
@[inline] def map (f : Float → Float) (a : FloatArray) : FloatArray :=
  (mapLoop (n := a.size) f (a.size / 4) ⟨a, rfl⟩ 0 (by simp; omega)).1

@[simp] theorem size_map (f : Float → Float) (a : FloatArray) : (map f a).size = a.size :=
  (mapLoop (n := a.size) f (a.size / 4) ⟨a, rfl⟩ 0 _).2

/-- `out[j] := f out[j] b[j]` for `j ∈ [i, n)`. -/
@[specialize] def zipTail {n : Nat} (f : Float → Float → Float) (b : Buf n) (out : Buf n)
    (i : USize) : Buf n :=
  if hi : i < out.1.usize then
    have h := out.2 ▸ lt_size_of_lt_usize hi
    zipTail f b (out.set i (f (out.get i h) (b.get i h)) h) (i + 1)
  else out
termination_by n - i.toNat
decreasing_by rw [toNat_succ hi]; omega

/-- `out[j] := f out[j] b[j]` for the `4k` indices from `i`, four per step, then the tail. -/
@[specialize] def zipLoop {n : Nat} (f : Float → Float → Float) (b : Buf n) :
    (k : Nat) → (out : Buf n) → (i : USize) → i.toNat + 4 * k ≤ n → Buf n
  | 0, out, i, _ => zipTail f b out i
  | k + 1, out, i, h =>
    let x0 := f (out.get i (by omega)) (b.get i (by omega))
    let x1 := f (out.get (i + 1) (idx (j := 1) (by omega))) (b.get (i + 1) (idx (j := 1) (by omega)))
    let x2 := f (out.get (i + 2) (idx (j := 2) (by omega))) (b.get (i + 2) (idx (j := 2) (by omega)))
    let x3 := f (out.get (i + 3) (idx (j := 3) (by omega))) (b.get (i + 3) (idx (j := 3) (by omega)))
    let o := out.set i x0 (by omega)
    let o := o.set (i + 1) x1 (idx (j := 1) (by omega))
    let o := o.set (i + 2) x2 (idx (j := 2) (by omega))
    let o := o.set (i + 3) x3 (idx (j := 3) (by omega))
    zipLoop f b k o (i + 4) (Nat.le_trans (Nat.add_le_add_right (toNat_add_le i 4) _) (by omega))

/-- `[f a[j] b[j] | j < a.size]` over `a` (in place when `a` is exclusive). If `b` has another
size, `a` is returned unchanged (field operands always agree). -/
@[inline] def zip (f : Float → Float → Float) (a b : FloatArray) : FloatArray :=
  if hb : b.size = a.size then
    (zipLoop (n := a.size) f ⟨b, hb⟩ (a.size / 4) ⟨a, rfl⟩ 0 (by simp; omega)).1
  else a

@[simp] theorem size_zip (f : Float → Float → Float) (a b : FloatArray) : (zip f a b).size = a.size := by
  unfold zip; split
  · exact (zipLoop (n := a.size) f _ _ _ 0 _).2
  · rfl

/-! ## Per-point loops (fibers of `w` floats) -/

/-- The components `j ∈ [w - r, w)` of the fiber at offset `o` combined with `x`. -/
@[specialize] def zipScalarComps {n : Nat} (w : Nat) (f : Float → Float → Float) (x : Float) :
    (r : Nat) → (out : Buf n) → (o : USize) → r ≤ w → o.toNat + w ≤ n → Buf n
  | 0, out, _, _, _ => out
  | r + 1, out, o, hr, ho =>
    let j := w - (r + 1)
    let out := out.set (o + USize.ofNat j) (f (out.get (o + USize.ofNat j) (idx (by omega))) x)
      (idx (by omega))
    zipScalarComps w f x r out o (by omega) ho

/-- One point of `zipScalar` for fibers of width `2`, `3`, `4` (unrolled). -/
@[inline] def zipScalar2 {n : Nat} (f : Float → Float → Float) (x : Float) (out : Buf n) (o : USize)
    (h : o.toNat + 2 ≤ n) : Buf n :=
  let y0 := f (out.get o (by omega)) x
  let y1 := f (out.get (o + 1) (idx (j := 1) (by omega))) x
  (out.set o y0 (by omega)).set (o + 1) y1 (idx (j := 1) (by omega))

@[inline, inherit_doc zipScalar2] def zipScalar3 {n : Nat} (f : Float → Float → Float) (x : Float)
    (out : Buf n) (o : USize) (h : o.toNat + 3 ≤ n) : Buf n :=
  let y0 := f (out.get o (by omega)) x
  let y1 := f (out.get (o + 1) (idx (j := 1) (by omega))) x
  let y2 := f (out.get (o + 2) (idx (j := 2) (by omega))) x
  ((out.set o y0 (by omega)).set (o + 1) y1 (idx (j := 1) (by omega))).set (o + 2) y2
    (idx (j := 2) (by omega))

@[inline, inherit_doc zipScalar2] def zipScalar4 {n : Nat} (f : Float → Float → Float) (x : Float)
    (out : Buf n) (o : USize) (h : o.toNat + 4 ≤ n) : Buf n :=
  let y0 := f (out.get o (by omega)) x
  let y1 := f (out.get (o + 1) (idx (j := 1) (by omega))) x
  let y2 := f (out.get (o + 2) (idx (j := 2) (by omega))) x
  let y3 := f (out.get (o + 3) (idx (j := 3) (by omega))) x
  (((out.set o y0 (by omega)).set (o + 1) y1 (idx (j := 1) (by omega))).set (o + 2) y2
    (idx (j := 2) (by omega))).set (o + 3) y3 (idx (j := 3) (by omega))

/-- `out[p·w + j] := f out[p·w + j] s[p]` for `k` points from point `p` at offset `o = p·w`
(every component of a fiber combined with that point's scalar); `pt` updates one point. -/
@[specialize] def zipScalarLoop {n m : Nat} (w : Nat) (s : Buf m)
    (pt : Float → (out : Buf n) → (o : USize) → o.toNat + w ≤ n → Buf n) :
    (k : Nat) → (out : Buf n) → (p o : USize) → p.toNat + k ≤ m → o.toNat + w * k ≤ n → Buf n
  | 0, out, _, _, _, _ => out
  | k + 1, out, p, o, hp, ho =>
    have ho' : o.toNat + w + w * k ≤ n := by rw [Nat.mul_succ] at ho; omega
    let out := pt (s.get p (by omega)) out o (by omega)
    zipScalarLoop w s pt k out (p + 1) (o + USize.ofNat w)
      (Nat.le_trans (Nat.add_le_add_right (toNat_add_le p 1) _) (by omega))
      (Nat.le_trans (Nat.add_le_add_right (toNat_add_le o w) _) (by omega))

/-- `zipScalarLoop` over all points of `a` with the per-point update `pt`. -/
@[inline] def zipScalarRun (w : Nat) (a s : FloatArray) (h : a.size = w * s.size)
    (pt : Float → (out : Buf a.size) → (o : USize) → o.toNat + w ≤ a.size → Buf a.size) :
    FloatArray :=
  (zipScalarLoop (n := a.size) (m := s.size) w ⟨s, rfl⟩ pt s.size ⟨a, rfl⟩ 0 0
    (by simp) (by simp [h])).1

theorem size_zipScalarRun (w : Nat) (a s : FloatArray) (h : a.size = w * s.size) pt :
    (zipScalarRun w a s h pt).size = a.size :=
  (zipScalarLoop (n := a.size) (m := s.size) w _ pt _ _ 0 0 _ _).2

/-- Combine every component of the fibers (`w` floats each) of `a` with the scalar of its point
in `s` (in place over `a`; unrolled per point for `w ≤ 4`). Unchanged if the sizes disagree. -/
@[inline] def zipScalar (w : Nat) (f : Float → Float → Float) (a s : FloatArray) : FloatArray :=
  if h : a.size = w * s.size then
    if w == 1 then zip f a s
    else if hw : w = 2 then zipScalarRun w a s h fun x out o ho => zipScalar2 f x out o (hw ▸ ho)
    else if hw : w = 3 then zipScalarRun w a s h fun x out o ho => zipScalar3 f x out o (hw ▸ ho)
    else if hw : w = 4 then zipScalarRun w a s h fun x out o ho => zipScalar4 f x out o (hw ▸ ho)
    else zipScalarRun w a s h fun x out o ho => zipScalarComps w f x w out o (Nat.le_refl w) ho
  else a

@[simp] theorem size_zipScalar (w : Nat) (f : Float → Float → Float) (a s : FloatArray) :
    (zipScalar w f a s).size = a.size := by
  unfold zipScalar; split
  · split
    · exact size_zip ..
    · split
      · exact size_zipScalarRun ..
      · split
        · exact size_zipScalarRun ..
        · split
          · exact size_zipScalarRun ..
          · exact size_zipScalarRun ..
  · rfl

/-! ## Norms -/

/-- Add the squares of the last `r` of the `w` components at offset `o` to `s`. -/
@[specialize] def sumSq {n : Nat} (w : Nat) (a : Buf n) (o : USize) (ho : o.toNat + w ≤ n) :
    (r : Nat) → Float → r < w → Float
  | 0, s, _ => s
  | r + 1, s, hr =>
    let x := a.get (o + USize.ofNat (w - (r + 1))) (idx (by omega))
    sumSq w a o ho r (s + x * x) (by omega)

/-- `√(x₀² + … + x_{w-1}²)` of the fiber at offset `o` (the sum left to right from `x₀²`, as
StaticVectors' `norm`). -/
@[inline] def normAt {n : Nat} (w : Nat) (a : Buf n) (o : USize) (h : o.toNat + w ≤ n) : Float :=
  if hw : w = 0 then f64! 0 else
  let x0 := a.get o (by omega)
  Float.sqrt (sumSq w a o h (w - 1) (x0 * x0) (by omega))

/-- `normAt` for `w = 2, 3, 4`, unrolled (the same sums, in the same order). -/
@[inline] def norm2 {n : Nat} (a : Buf n) (o : USize) (h : o.toNat + 2 ≤ n) : Float :=
  let x0 := a.get o (by omega)
  let x1 := a.get (o + 1) (idx (j := 1) (by omega))
  Float.sqrt (x0 * x0 + x1 * x1)

@[inline, inherit_doc norm2] def norm3 {n : Nat} (a : Buf n) (o : USize) (h : o.toNat + 3 ≤ n) : Float :=
  let x0 := a.get o (by omega)
  let x1 := a.get (o + 1) (idx (j := 1) (by omega))
  let x2 := a.get (o + 2) (idx (j := 2) (by omega))
  Float.sqrt (x0 * x0 + x1 * x1 + x2 * x2)

@[inline, inherit_doc norm2] def norm4 {n : Nat} (a : Buf n) (o : USize) (h : o.toNat + 4 ≤ n) : Float :=
  let x0 := a.get o (by omega)
  let x1 := a.get (o + 1) (idx (j := 1) (by omega))
  let x2 := a.get (o + 2) (idx (j := 2) (by omega))
  let x3 := a.get (o + 3) (idx (j := 3) (by omega))
  Float.sqrt (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3)

/-- `√(x₀²)` of the fiber at offset `o` (width 1). -/
@[inline] def norm1 {n : Nat} (a : Buf n) (o : USize) (h : o.toNat + 1 ≤ n) : Float :=
  let x := a.get o (by omega)
  Float.sqrt (x * x)

/-- The norms of `k` fibers (`w` floats each) of `a` from offset `o`, written to `out` from `p`. -/
@[specialize] def normLoop {n m : Nat} (w : Nat) (nrm : (a : Buf n) → (o : USize) → o.toNat + w ≤ n → Float)
    (a : Buf n) :
    (k : Nat) → (out : Buf m) → (p o : USize) → p.toNat + k ≤ m → o.toNat + w * k ≤ n → Buf m
  | 0, out, _, _, _, _ => out
  | k + 1, out, p, o, hp, ho =>
    have ho' : o.toNat + w + w * k ≤ n := by rw [Nat.mul_succ] at ho; omega
    let x := nrm a o (by omega)
    normLoop w nrm a k (out.set p x (by omega)) (p + 1) (o + USize.ofNat w)
      (Nat.le_trans (Nat.add_le_add_right (toNat_add_le p 1) _) (by omega))
      (Nat.le_trans (Nat.add_le_add_right (toNat_add_le o w) _) (by omega))

/-- `normLoop` over all `m` points of `a` with the per-point norm `nrm`. -/
@[inline] def normsRun (w m : Nat) (a : FloatArray) (h : a.size = w * m)
    (nrm : (a' : Buf a.size) → (o : USize) → o.toNat + w ≤ a.size → Float) : FloatArray :=
  (normLoop (n := a.size) (m := m) w nrm ⟨a, rfl⟩ m (zerosBuf m) 0 0 (by simp) (by simp [h])).1

theorem size_normsRun (w m : Nat) (a : FloatArray) (h : a.size = w * m) nrm :
    (normsRun w m a h nrm).size = m :=
  (normLoop (n := a.size) (m := m) w nrm _ _ _ 0 0 _ _).2

/-- The Euclidean norms `√(Σ xᵢ²)` of the `m` fibers of width `w` of `a` (`a.size = w * m`, else
zeros), unrolled per point for `w ≤ 4`. -/
@[inline] def norms (w m : Nat) (a : FloatArray) : FloatArray :=
  if h : a.size = w * m then
    if hw : w = 1 then normsRun w m a h fun b o ho => norm1 b o (hw ▸ ho)
    else if hw : w = 2 then normsRun w m a h fun b o ho => norm2 b o (hw ▸ ho)
    else if hw : w = 3 then normsRun w m a h fun b o ho => norm3 b o (hw ▸ ho)
    else if hw : w = 4 then normsRun w m a h fun b o ho => norm4 b o (hw ▸ ho)
    else normsRun w m a h fun b o ho => normAt w b o ho
  else zeros m

@[simp] theorem size_norms (w m : Nat) (a : FloatArray) : (norms w m a).size = m := by
  unfold norms; split
  · split
    · exact size_normsRun ..
    · split
      · exact size_normsRun ..
      · split
        · exact size_normsRun ..
        · split
          · exact size_normsRun ..
          · exact size_normsRun ..
  · simp

/-- Julia `max(acc, x)` (`isMax`) or `min(acc, x)` for a norm `x` (never `-0.0`): a NaN wins and
then stays, otherwise the larger (smaller) value. For such arguments this is `JuliaBase.F64.max`
(`min`), whose `isNaN`/sign-bit tests are out-of-line calls. -/
@[inline] def extStep (isMax : Bool) (acc x : Float) : Float :=
  if isMax then (if x > acc || x != x then x else acc)
  else (if x < acc || x != x then x else acc)

/-- `max(acc, ‖fiber‖)` over `k` points from offset `o` (Julia `maximum(norm, …)`) when `isMax`,
else `min` (Julia `minimum(norm, …)`), by `extStep`. -/
@[specialize] def extLoop {n : Nat} (isMax : Bool) (w : Nat)
    (nrm : (a : Buf n) → (o : USize) → o.toNat + w ≤ n → Float) (a : Buf n) :
    (k : Nat) → (o : USize) → o.toNat + w * k ≤ n → Float → Float
  | 0, _, _, acc => acc
  | k + 1, o, ho, acc =>
    have ho' : o.toNat + w + w * k ≤ n := by rw [Nat.mul_succ] at ho; omega
    let x := nrm a o (by omega)
    extLoop isMax w nrm a k (o + USize.ofNat w)
      (Nat.le_trans (Nat.add_le_add_right (toNat_add_le o w) _) (by omega))
      (extStep isMax acc x)

/-- `extLoop` over all `m` points of `a` with the per-point norm `nrm`. -/
@[inline] def extRun (isMax : Bool) (w m : Nat) (a : FloatArray) (h : a.size = w * m) (init : Float)
    (nrm : (a' : Buf a.size) → (o : USize) → o.toNat + w ≤ a.size → Float) : Float :=
  extLoop (n := a.size) isMax w nrm ⟨a, rfl⟩ m 0 (by simp [h]) init

/-- The largest (`isMax`) or smallest norm of the `m` fibers of width `w` of `a`, starting from
`init` (Julia `maximum(norm, v; init)`); `init` if the sizes disagree. -/
@[inline] def normExtremum (isMax : Bool) (w m : Nat) (a : FloatArray) (init : Float) : Float :=
  if h : a.size = w * m then
    if hw : w = 1 then extRun isMax w m a h init fun b o ho => norm1 b o (hw ▸ ho)
    else if hw : w = 2 then extRun isMax w m a h init fun b o ho => norm2 b o (hw ▸ ho)
    else if hw : w = 3 then extRun isMax w m a h init fun b o ho => norm3 b o (hw ▸ ho)
    else if hw : w = 4 then extRun isMax w m a h init fun b o ho => norm4 b o (hw ▸ ho)
    else extRun isMax w m a h init fun b o ho => normAt w b o ho
  else init

end Cartan.Flat

namespace Cartan.Flat

/-! ## Running generated kernels -/

/-- Run a generated binary field kernel over `k` points (`wa`, `wb`, `wc` floats each) from
offset `0`, writing into `zeros (wc * k)`; the offsets are proved in range once here, so the
kernel reads and writes without bounds checks. `zeros` if an operand is too short. -/
@[inline] def runBin (wa wb wc : Nat) (a b : FloatArray) (k : Nat)
    (kern : (0 : USize).toNat + wa * k ≤ a.size → (0 : USize).toNat + wb * k ≤ b.size →
      (0 : USize).toNat + wc * k ≤ wc * k → Buf (wc * k) → Buf (wc * k)) : FloatArray :=
  if ha : wa * k ≤ a.size then
    if hb : wb * k ≤ b.size then
      (kern (by simpa using ha) (by simpa using hb) (by simp) (zerosBuf (wc * k))).1
    else zeros (wc * k)
  else zeros (wc * k)

/-- Run a generated unary field kernel over `k` points (see `runBin`). -/
@[inline] def runUn (wa wc : Nat) (a : FloatArray) (k : Nat)
    (kern : (0 : USize).toNat + wa * k ≤ a.size → (0 : USize).toNat + wc * k ≤ wc * k →
      Buf (wc * k) → Buf (wc * k)) : FloatArray :=
  if ha : wa * k ≤ a.size then (kern (by simpa using ha) (by simp) (zerosBuf (wc * k))).1
  else zeros (wc * k)

/-! ## Checked word-indexed access (for generated code, where indices are not proved) -/

/-- `a[i]` for a `USize` index, `0.0` past the end (one compare, always predicted in kernels
whose indices are in range). -/
@[inline] def getU (a : FloatArray) (i : USize) : Float :=
  if h : i < a.usize then a.uget i (lt_size_of_lt_usize h) else f64! 0

/-- `a[i] := x` for a `USize` index (in place when exclusive); unchanged past the end. -/
@[inline] def putU (a : FloatArray) (i : USize) (x : Float) : FloatArray :=
  if h : i < a.usize then a.uset i x (lt_size_of_lt_usize h) else a

@[simp] theorem size_putU (a : FloatArray) (i : USize) (x : Float) : (putU a i x).size = a.size := by
  unfold putU; split
  · exact size_uset ..
  · rfl

end Cartan.Flat
