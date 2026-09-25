/-
Allocation-lean building blocks of the composite functions at `Float`.

The typed `Values Float n` operations (`map`, `zipWith`, `norm`, `replicate`) loop over the
type-level length `n`. Inside code that is generic over the space that length is
`Layout.size V.n`, computed at run time with `Nat` powers (a GMP allocation per call); the
kernel dispatch of an embedding (`Kernels.un` between layouts) falls back to interpreted
plans for layout pairs the code generator does not emit. The composite closed forms and
series run on these instead:

* `vmap`, `vzip`, `vnorm`, `vset`: loops over the run-time `FloatArray` size, in place when
  the array is not shared (`FloatArray.set` copies only a shared array);
* `gradeOffset`: where the blades of one grade start in a layout (grade-major storage, lex
  order within a grade), so a chain embeds in a spinor or a multivector by one block copy,
  and `embedChain` does that copy into the zero vector of the target layout (a closed term
  at a literal space: one allocation per call);
* `Tab`: the blade squares `e_b ⟑ e_b` and `⟨~e_b e_b⟩₀` of a layout of a plain signature
  space as `FloatArray`s (closed terms at a literal space), for the sums `Σ wᵢxᵢ²` of the
  closed forms.

All of it computes exactly what the typed operations compute (the same floating-point
operations in the same order); `Tests/Composite` checks the composite functions against Julia.
-/
import Grassmann.Composite.Scalar

namespace Grassmann.Composite

open DirectSum StaticVectors

/-! ## `FloatArray` loops -/

theorem size_set' (a : FloatArray) (i : Nat) (x : Float) (h : i < a.size) :
    (a.set i x h).size = a.size := by
  simp only [FloatArray.set, FloatArray.size]; exact Array.size_set ..

/-- The unchecked `USize` loop of `mapFrom` (the compiled form). -/
@[inline] unsafe def mapFromUnsafe (f : Float → Float) (a : FloatArray) (i : Nat) : FloatArray :=
  let n := a.usize
  let rec @[specialize] loop (j : USize) (a : FloatArray) : FloatArray :=
    if j < n then loop (j + 1) (a.uset j (f (a.uget j lcProof)) lcProof) else a
  loop i.toUSize a

/-- `a[j] := f a[j]` for `j ≥ i`, in place when `a` is not shared. -/
@[implemented_by mapFromUnsafe]
def mapFrom (f : Float → Float) (a : FloatArray) (i : Nat) : FloatArray :=
  if h : i < a.size then mapFrom f (a.set i (f a[i]) h) (i + 1) else a
termination_by a.size - i
decreasing_by rw [size_set']; omega

theorem size_mapFrom (f : Float → Float) (a : FloatArray) (i : Nat) : (mapFrom f a i).size = a.size := by
  fun_induction mapFrom f a i with
  | case1 a i h ih => rw [ih, size_set']
  | case2 => rfl

/-- The unchecked `USize` loop of `zipFrom` (the compiled form; `b` at least as long as `a`). -/
@[inline] unsafe def zipFromUnsafe (f : Float → Float → Float) (a b : FloatArray) (i : Nat) : FloatArray :=
  let n := if a.usize ≤ b.usize then a.usize else b.usize
  let rec @[specialize] loop (j : USize) (a : FloatArray) : FloatArray :=
    if j < n then loop (j + 1) (a.uset j (f (a.uget j lcProof) (b.uget j lcProof)) lcProof) else a
  loop i.toUSize a

/-- `a[j] := f a[j] b[j]` for `j ≥ i` (`b` at least as long), in place on `a`. -/
@[implemented_by zipFromUnsafe]
def zipFrom (f : Float → Float → Float) (a b : FloatArray) (i : Nat) : FloatArray :=
  if h : i < a.size then
    if h2 : i < b.size then zipFrom f (a.set i (f a[i] b[i]) h) b (i + 1) else a
  else a
termination_by a.size - i
decreasing_by rw [size_set']; omega

theorem size_zipFrom (f : Float → Float → Float) (a b : FloatArray) (i : Nat) :
    (zipFrom f a b i).size = a.size := by
  fun_induction zipFrom f a b i with
  | case1 a i h h2 ih => rw [ih, size_set']
  | case2 => rfl
  | case3 => rfl

/-- The unchecked `USize` loop of `sumSqFrom`. -/
@[inline] unsafe def sumSqFromUnsafe (a : FloatArray) (i : Nat) (acc : Float) : Float :=
  let n := a.usize
  let rec loop (j : USize) (acc : Float) : Float :=
    if j < n then let x := a.uget j lcProof; loop (j + 1) (acc + x * x) else acc
  loop i.toUSize acc

/-- `acc + Σ_{j ≥ i} a[j]²` (left to right). -/
@[implemented_by sumSqFromUnsafe]
def sumSqFrom (a : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < a.size then sumSqFrom a (i + 1) (acc + a[i] * a[i]) else acc
termination_by a.size - i

/-- `acc + Σ_{j ≥ i} (a[j]·a[j])·w[j]` (the weighted squares of the closed forms). -/
def wsumFrom (a w : FloatArray) (i : Nat) (acc : Float) : Float :=
  if h : i < a.size then
    if h2 : i < w.size then wsumFrom a w (i + 1) (acc + a[i] * a[i] * w[i]) else acc
  else acc
termination_by a.size - i

/-- `dst[off + j] := k·src[j]` for `j ≥ i` (in place on `dst`; `k = 1` copies). -/
def copyScaled (dst src : FloatArray) (k : Float) (off i : Nat) : FloatArray :=
  if h : i < src.size then
    if h2 : off + i < dst.size then copyScaled (dst.set (off + i) (k * src[i]) h2) src k off (i + 1)
    else dst
  else dst
termination_by src.size - i

theorem size_copyScaled (dst src : FloatArray) (k : Float) (off i : Nat) :
    (copyScaled dst src k off i).size = dst.size := by
  fun_induction copyScaled dst src k off i with
  | case1 dst i h h2 ih => rw [ih, size_set']
  | case2 => rfl
  | case3 => rfl

/-- `dst[off + j] := src[j]` for `j ≥ i` (a plain copy: `copyScaled` without the product). -/
def copyFrom (dst src : FloatArray) (off i : Nat) : FloatArray :=
  if h : i < src.size then
    if h2 : off + i < dst.size then copyFrom (dst.set (off + i) src[i] h2) src off (i + 1)
    else dst
  else dst
termination_by src.size - i

theorem size_copyFrom (dst src : FloatArray) (off i : Nat) : (copyFrom dst src off i).size = dst.size := by
  fun_induction copyFrom dst src off i with
  | case1 dst i h h2 ih => rw [ih, size_set']
  | case2 => rfl
  | case3 => rfl

/-- `dst[doff + j] := src[soff + j]` for `j < len` (from `j = i`). -/
def copyBlock (dst src : FloatArray) (doff soff len i : Nat) : FloatArray :=
  if i < len then
    if h : doff + i < dst.size then
      if h2 : soff + i < src.size then copyBlock (dst.set (doff + i) src[soff + i] h) src doff soff len (i + 1)
      else dst
    else dst
  else dst
termination_by len - i

theorem size_copyBlock (dst src : FloatArray) (doff soff len i : Nat) :
    (copyBlock dst src doff soff len i).size = dst.size := by
  fun_induction copyBlock dst src doff soff len i with
  | case1 dst i _ h h2 ih => rw [ih, size_set']
  | _ => rfl

/-! ## `Values Float n` without the type-level length at run time -/

variable {n : Nat}

/-- Elementwise `f` (Julia `map`), in place when the storage is not shared. -/
@[inline] def vmap (f : Float → Float) (v : Values Float n) : Values Float n :=
  ⟨mapFrom f v.data 0, (size_mapFrom ..).trans v.size_eq⟩

/-- Elementwise `f v w`, in place on `v`. -/
@[inline] def vzip (f : Float → Float → Float) (v w : Values Float n) : Values Float n :=
  ⟨zipFrom f v.data w.data 0, (size_zipFrom ..).trans v.size_eq⟩

/-- Julia `norm(v)`: `√Σ vᵢ²` (the order of `Values.norm`). -/
@[inline] def vnorm (v : Values Float n) : Float := Float.sqrt (sumSqFrom v.data 0 f0)

/-- `v` with entry `i` replaced by `x` (unchanged out of range). -/
@[inline] def vset (v : Values Float n) (i : Nat) (x : Float) : Values Float n :=
  if h : i < v.data.size then ⟨v.data.set i x h, (size_set' ..).trans v.size_eq⟩ else v

/-- Whether every entry from index `i` on is zero. -/
def zeroFrom (a : FloatArray) (i : Nat) : Bool :=
  if h : i < a.size then a[i] == f0 && zeroFrom a (i + 1) else true
termination_by a.size - i

/-- Whether `v` is exactly a multiple of its first entry (the scalar slot). -/
@[inline] def vScalarOnly (v : Values Float n) : Bool := zeroFrom v.data 1

/-- `Σ (vᵢ·vᵢ)·wᵢ`. -/
@[inline] def vwsum (v : Values Float n) (w : FloatArray) : Float := wsumFrom v.data w 0 f0

/-! ## Layouts -/

/-- The storage offset of the blades of grade `g` in layout `l` of an `n`-generator space:
the lower grades stored before it (all of them in `.full`, those of the parity of `g` in
`.even`/`.odd`, none in `.chain`). -/
def gradeOffset (n g : Nat) : Layout → Nat
  | .full => Leibniz.binomsum n g
  | .even | .odd => go 0 0
  | .chain _ => 0
where
  /-- Sum the binomials of the grades below `g` of its parity. -/
  go (k acc : Nat) : Nat :=
    if k < g then go (k + 1) (if k % 2 == g % 2 then acc + Leibniz.binomial n k else acc) else acc
  termination_by g - k

/-- `Layout.size n l` with shifts instead of `Nat` powers (`2 ^ k` is a GMP computation per
call at run time; DirectSum's `Layout.size` uses it). -/
@[inline] def fastSize (n : Nat) : Layout → Nat
  | .chain g => Layout.size n (.chain g)
  | .even => if n == 0 then 1 else 1 <<< (n - 1)
  | .odd => if n == 0 then 0 else 1 <<< (n - 1)
  | .full => 1 <<< n

theorem fastSize_eq (n : Nat) (l : Layout) : fastSize n l = l.size n := by
  cases l <;> simp [fastSize, Layout.size, Nat.shiftLeft_eq]

/-- The zero vector of layout `l` (sized with `fastSize`; a closed term at a literal space). -/
@[inline] def zeros (V : TensorBundle) (l : Layout) : Values Float (l.size V.n) :=
  (Values.replicate (n := fastSize V.n l) f0).cast (fastSize_eq V.n l)

/-- A grade-`g` chain's coefficients `x`, scaled by `k`, in layout `l` (which must store grade
`g`): one copy of the zero vector with the block at `gradeOffset`. -/
@[inline] def embedChain (V : TensorBundle) (g : Nat) (l : Layout) (k : Float)
    (x : Values Float ((Layout.chain g).size V.n)) : Values Float (l.size V.n) :=
  let z := zeros V l
  ⟨copyScaled z.data x.data k (gradeOffset V.n g l) 0, (size_copyScaled ..).trans z.size_eq⟩

/-- The grade-`g` block of coefficients stored in layout `l` (which must store grade `g`). -/
@[inline] def gradeBlock (V : TensorBundle) (g : Nat) (l : Layout) (x : Values Float (l.size V.n)) :
    Values Float ((Layout.chain g).size V.n) :=
  let z := zeros V (.chain g)
  ⟨copyBlock z.data x.data 0 (gradeOffset V.n g l) z.data.size 0, (size_copyBlock ..).trans z.size_eq⟩

/-- Whether layout `l` stores grade `g`. -/
@[inline] def storesGrade (g : Nat) : Layout → Bool
  | .full => true
  | .even => g % 2 == 0
  | .odd => g % 2 == 1
  | .chain h => g == h

/-- Grade by grade copy of the common grades of `la` into `lc` (the block form of
`convertLayout`). -/
def convertLoop (n : Nat) (la lc : Layout) (x dst : FloatArray) (g : Nat) : FloatArray :=
  if g ≤ n then
    let dst := if storesGrade g la && storesGrade g lc then
        copyBlock dst x (gradeOffset n g lc) (gradeOffset n g la) (Leibniz.binomial n g) 0
      else dst
    convertLoop n la lc x dst (g + 1)
  else dst
termination_by n + 1 - g

theorem size_convertLoop (n : Nat) (la lc : Layout) (x dst : FloatArray) (g : Nat) :
    (convertLoop n la lc x dst g).size = dst.size := by
  fun_induction convertLoop n la lc x dst g with
  | case1 dst g h dst' ih => rw [ih]; simp only [dst']; split <;> simp [size_copyBlock]
  | case2 => rfl

/-- The coefficients `x` of layout `la` in layout `lc` (the grades `lc` does not store are
dropped, the others zero): `convertLayout` by blocks. -/
@[inline] def convertFast (V : TensorBundle) (la lc : Layout) (x : Values Float (la.size V.n)) :
    Values Float (lc.size V.n) :=
  let z := zeros V lc
  ⟨convertLoop V.n la lc x.data z.data 0, (size_convertLoop ..).trans z.size_eq⟩

/-! ## Blade tables -/

/-- The blade squares of a layout: `sq[i] = e_bᵢ ⟑ e_bᵢ` and `a2[i] = ⟨~e_bᵢ e_bᵢ⟩₀`. -/
structure Tab where
  /-- `e_b ⟑ e_b` (a scalar in every metric). -/
  sq : FloatArray
  /-- `⟨~e_b ⟑ e_b⟩₀` (Julia `abs2_inv`). -/
  a2 : FloatArray

/-- The blade table of layout `l` of a plain signature space with `n` generators and
negative-generator mask `neg` (`plainNeg V`). Its arguments are numbers, so at a literal
space `tabPlain V.n (plainNeg V) l` is a closed term, computed once: a function of the space
itself is not, because inside a specialized loop the compiler may rebuild the space's
structure literal from a local `Bool` known equal to one of its fields. -/
def tabPlain (n : Nat) (neg : UInt64) (l : Layout) : Tab :=
  let bs := l.blades n
  ⟨⟨bs.map (plainSq neg)⟩, ⟨bs.map (plainAbs2 neg)⟩⟩

end Grassmann.Composite
