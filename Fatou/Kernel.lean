import Fatou.Define

/-!
# The escape-time kernel and `FilledSet`

Julia's per-pixel kernel `orbit(K, z0)` (`src/Fatou.jl:341-350`):

```
z  = mandel ? seed : (plane ? plane(z0) : z0)     # Mandelbrot ignores `plane`
c  = z0                                            # the raw pixel, in every mode
zn = 0
while (newt ? Q(z,c) > ϵ : Q(z,c) < ϵ) && zn < N   # strict; NaN stops; test before step
    z = F(z, c); zn += 1
return (zn, disk ? disk(z) : z)
```

and `FilledSet(K, Z)` stores `iter = zn`, the final iterates, and `mix = C.(z, zn ./ N, p)`
(`src/Fatou.jl:126-135`).

`Define.orbit` is that kernel, verbatim, as the reference semantics (with the bound
`orbit_iter_le`). The raster path fuses the per-pixel loop and the loop over pixels into one
tail-recursive `sweep` over unboxed `(zr, zi, cr, ci)` floats: the map `F` is a specialized
argument, so for a map known at compile time (a lambda, or a `Define` built inline) the
`Complex` values cancel and nothing is allocated per iteration. Rows are split into chunks
computed as parallel `Task`s (Julia uses `@threads` over rows), and the per-chunk
`ByteArray`/`FloatArray` outputs are concatenated. The sizes of the result are proved
(`sweep_sized` by functional induction over the fused loop, `spawnChunks_sizes` for the row
partition), which is what lets `fatou` return a `FilledSet rows cols` whose accessors skip
bounds checks.
-/

namespace Fatou

open JuliaBase

/-! ## Reference semantics -/

/-- The iteration loop of Julia `orbit(K, z0)` with `fuel` bounding the number of steps. -/
def orbitLoop (F : C64 → C64 → C64) (Q : C64 → C64 → Float) (newt : Bool) (ϵ : Float) (N : Nat)
    (c : C64) : Nat → C64 → Nat → Nat × C64
  | 0, z, n => (n, z)
  | fuel + 1, z, n =>
    if n < N then
      let q := Q z c
      if (if newt then q > ϵ else q < ϵ) then orbitLoop F Q newt ϵ N c fuel (F z c) (n + 1)
      else (n, z)
    else (n, z)

/-- The loop never counts past `N` (nor below its start). -/
theorem orbitLoop_fst_le (F : C64 → C64 → C64) (Q : C64 → C64 → Float) (newt : Bool) (ϵ : Float)
    (N : Nat) (c : C64) (fuel : Nat) (z : C64) (n : Nat) :
    (orbitLoop F Q newt ϵ N c fuel z n).1 ≤ max n N := by
  induction fuel generalizing z n with
  | zero => exact Nat.le_max_left ..
  | succ fuel ih =>
    simp only [orbitLoop]
    by_cases hn : n < N
    · rw [ite_eq_left hn]
      by_cases hq : (if newt then Q z c > ϵ else Q z c < ϵ)
      · rw [ite_eq_left hq]; have := ih (F z c) (n + 1); omega
      · rw [ite_eq_right hq]; exact Nat.le_max_left ..
    · rw [ite_eq_right hn]; exact Nat.le_max_left ..

/-- The start value of an orbit (`src/Fatou.jl:342`): `seed` in Mandelbrot mode, else the
pixel, mapped by `plane` if requested. -/
@[inline] def Spec.start (s : Spec) (z0 : C64) : C64 :=
  if s.mandel then s.seed else if s.plane then C64.plane z0 else z0

/-- The returned value of an orbit (`src/Fatou.jl:349`): `disk(z)` if requested. -/
@[inline] def Spec.finish (s : Spec) (z : C64) : C64 := if s.disk then C64.disk z else z

/-- Julia `orbit(K::Define, z0)` (`src/Fatou.jl:341-350`): the iteration count and the final
(possibly `disk`-mapped) iterate of the pixel `z0`. Reference semantics for the raster
kernel. -/
def Define.orbit (K : Define) (z0 : C64) : Nat × C64 :=
  let s := K.spec
  let r := orbitLoop K.F K.Q s.newt s.ϵ s.N.toNat z0 s.N.toNat (s.start z0) 0
  (r.1, s.finish r.2)

/-- Every iteration count is at most `N` (Julia's loop guard `K.N > zn`). -/
theorem Define.orbit_iter_le (K : Define) (z0 : C64) : (K.orbit z0).1 ≤ K.spec.N.toNat := by
  have := orbitLoop_fst_le K.F K.Q K.spec.newt K.spec.ϵ K.spec.N.toNat z0 K.spec.N.toNat
    (K.spec.start z0) 0
  simp only [Define.orbit]
  omega

/-- Julia's colouring value `C(z, iter/N, p)` of a pixel (`src/Fatou.jl:133`); `iter ./ N` is
a `Float64` division. -/
@[inline] def Define.mixOf (K : Define) (n : Nat) (z : C64) : Float :=
  K.C z (Float.ofNat n / Float.ofNat K.spec.N.toNat) K.spec.p

/-! ## The fused raster kernel -/

/-- The outputs of one chunk of pixels: little-endian `UInt16` iteration counts, final
iterates and colouring values. -/
structure Chunk where
  /-- iteration counts, two bytes per pixel -/
  iter : ByteArray
  /-- real parts of the final iterates -/
  zre : FloatArray
  /-- imaginary parts of the final iterates -/
  zim : FloatArray
  /-- colouring values `C(z, iter/N, p)` -/
  mix : FloatArray
  deriving Inhabited

/-- Loop-invariant parameters of the raster kernel (all scalars, so that nothing shared
between the parallel chunks is reference-counted per pixel). -/
structure SweepParams where
  /-- Mandelbrot mode -/
  mandel : Bool
  /-- disk → half-plane on input -/
  plane : Bool
  /-- half-plane → disk on output -/
  disk : Bool
  /-- real part of the Mandelbrot seed -/
  seedRe : Float
  /-- imaginary part of the Mandelbrot seed -/
  seedIm : Float
  /-- colouring exponent -/
  p : Float
  /-- `Float64(N)` -/
  Nf : Float
  /-- maximum iterations -/
  N : Nat
  /-- number of pixels in the chunk -/
  len : Nat

/-- Real part of the start value `mandel ? seed : (plane ? plane(c) : c)`. -/
@[inline] def startRe (mandel plane : Bool) (seedRe cr ci : Float) : Float :=
  if mandel then seedRe else if plane then (C64.plane ⟨cr, ci⟩).re else cr

/-- Imaginary part of the start value `mandel ? seed : (plane ? plane(c) : c)`. -/
@[inline] def startIm (mandel plane : Bool) (seedIm cr ci : Float) : Float :=
  if mandel then seedIm else if plane then (C64.plane ⟨cr, ci⟩).im else ci

/-- Where a raster's pixels come from: a separable grid `x' .+ im*y` (`sa` = the column real
parts, `sb` = the row imaginary parts) or a full complex raster (`sa`, `sb` = real and
imaginary parts, row-major). Plain data rather than a function, so specializing the kernel
on the map never copies (and re-evaluates) the pixel arrays. -/
structure Source where
  /-- column real parts, or all real parts -/
  sa : FloatArray
  /-- row imaginary parts, or all imaginary parts -/
  sb : FloatArray
  /-- number of columns -/
  cols : Nat
  /-- whether `sa`, `sb` are the two axes of a grid -/
  separable : Bool

namespace Source

/-- Real part of pixel `i` (row-major). -/
@[inline] def re (s : Source) (i : Nat) : Float :=
  if s.separable then s.sa.get! (i % s.cols) else s.sa.get! i

/-- Imaginary part of pixel `i` (row-major). -/
@[inline] def im (s : Source) (i : Nat) : Float :=
  if s.separable then s.sb.get! (i / s.cols) else s.sb.get! i

/-- Pixel `i` (row-major). -/
@[inline] def pixel (s : Source) (i : Nat) : C64 := ⟨s.re i, s.im i⟩

/-- The separable grid of a rectangle, `x' .+ im*y` (`src/Fatou.jl:174-177`). -/
def ofRectangle (r : Rectangle) : Source := ⟨r.xs, r.ys, r.cols, true⟩

/-- A complex raster. -/
def ofPlane {rows cols : Nat} (Z : Plane rows cols) : Source := ⟨Z.re, Z.im, cols, false⟩

end Source

/-- The iteration counter of the kernel is a `UInt32` (a machine register, not a boxed
`Nat`); below `N` it never wraps, so `N - n` decreases. -/
theorem u32_sub_succ_lt {n N : UInt32} (h : n < N) :
    N.toNat - (n + 1).toNat < N.toNat - n.toNat := by
  have h1 : n.toNat < N.toNat := UInt32.lt_iff_toNat_lt.mp h
  have h2 : N.toNat < 2 ^ 32 := UInt32.toNat_lt N
  have h3 : (n + 1).toNat = n.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_one]
    exact Nat.mod_eq_of_lt (by omega)
  omega

/-- Julia's kernel over `len` consecutive pixels of `src`, as one tail-recursive loop.
State: chunk pixel `j`, the absolute pixel `i` with its column `k` and row `r` (advanced
incrementally: no division per pixel), current iterate `zr + zi·i`, pixel `cr + ci·i`, count
`n`, and the outputs so far. `cont q ϵ` is the loop test (`q < ϵ`, or `q > ϵ` in Newton
mode), hoisted out as a specialized argument. Every complex value is taken apart into
unboxed floats, and the loop-invariant parameters are separate scalar arguments (so the hot
path reloads nothing). -/
@[specialize] def sweep (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source)
    (mandel plane disk : Bool) (seedRe seedIm p Nf ϵ : Float) (N : UInt32) (len : Nat)
    (j i k r : Nat) (zr zi cr ci : Float) (n : UInt32) (it : ByteArray) (re im mix : FloatArray) :
    Chunk :=
  if hn : n < N ∧ cont (Q ⟨zr, zi⟩ ⟨cr, ci⟩) ϵ = true then
    let w := F ⟨zr, zi⟩ ⟨cr, ci⟩
    sweep F Q C cont src mandel plane disk seedRe seedIm p Nf ϵ N len j i k r w.re w.im cr ci
      (n + 1) it re im mix
  else
    let fr := if disk then (C64.disk ⟨zr, zi⟩).re else zr
    let fi := if disk then (C64.disk ⟨zr, zi⟩).im else zi
    let it := setU16 it j n.toUInt16
    let re := re.set! j fr
    let im := im.set! j fi
    let mix := mix.set! j (C ⟨fr, fi⟩ (n.toFloat / Nf) p)
    if hj : j + 1 < len then
      let wrap := k + 1 == src.cols
      let k := if wrap then 0 else k + 1
      let r := if wrap then r + 1 else r
      let i := i + 1
      let cr := if src.separable then src.sa.get! k else src.sa.get! i
      let ci := if src.separable then src.sb.get! r else src.sb.get! i
      sweep F Q C cont src mandel plane disk seedRe seedIm p Nf ϵ N len (j + 1) i k r
        (startRe mandel plane seedRe cr ci) (startIm mandel plane seedIm cr ci) cr ci 0
        it re im mix
    else ⟨it, re, im, mix⟩
termination_by (len - j, N.toNat - n.toNat)
decreasing_by
  · exact Prod.Lex.right _ (u32_sub_succ_lt hn.1)
  · exact Prod.Lex.left _ _ (by omega)

/-- The four outputs of a chunk hold `len` pixels: two bytes of count, and one final iterate
(real and imaginary part) and one colouring value per pixel. -/
def Chunk.Sized (c : Chunk) (len : Nat) : Prop :=
  c.iter.size = 2 * len ∧ c.zre.size = len ∧ c.zim.size = len ∧ c.mix.size = len

/-- `sweep` writes into outputs preallocated for `len` pixels (in place: `set!` is an inline
store, where a `push` per output was an out-of-line runtime call), so it returns the outputs of
exactly `len` pixels. -/
theorem sweep_sized (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source)
    (mandel plane disk : Bool) (seedRe seedIm p Nf ϵ : Float) (N : UInt32) (len : Nat)
    (j i k r : Nat) (zr zi cr ci : Float) (n : UInt32) (it : ByteArray) (re im mix : FloatArray)
    (hit : it.size = 2 * len) (hre : re.size = len) (him : im.size = len)
    (hmix : mix.size = len) :
    (sweep F Q C cont src mandel plane disk seedRe seedIm p Nf ϵ N len j i k r zr zi cr ci n it re
      im mix).Sized len := by
  induction j, i, k, r, zr, zi, cr, ci, n, it, re, im, mix using
    sweep.induct F Q C cont src mandel plane disk seedRe seedIm p Nf ϵ N len with
  | case1 j i k r zr zi cr ci n it re im mix hn w ih =>
    rw [sweep]; simp only [hn]
    exact ih hit hre him hmix
  | case2 j i k r zr zi cr ci n it re im mix hn fr fi it' re' im' mix' hj' wrap k' r' i' cr' ci'
      ih =>
    rw [sweep]; simp only [hn, hj', ↓reduceDIte]
    exact ih (by simp [it', hit]) (by simp [re', hre]) (by simp [im', him]) (by simp [mix', hmix])
  | case3 j i k r zr zi cr ci n it re im mix hn hj' =>
    rw [sweep]; simp only [hn, hj', ↓reduceDIte]
    exact ⟨by simp [hit], by simp [hre], by simp [him], by simp [hmix]⟩

/-- Run the kernel on the `P.len` pixels of `src` starting at `lo`. -/
@[specialize] def runChunk (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source) (lo : Nat)
    (P : SweepParams) (ϵ : Float) : Chunk :=
  if P.len == 0 then ⟨.empty, .empty, .empty, .empty⟩
  else
    let cr := src.re lo
    let ci := src.im lo
    sweep F Q C cont src P.mandel P.plane P.disk P.seedRe P.seedIm P.p P.Nf ϵ P.N.toUInt32 P.len 0
      lo (lo % src.cols) (lo / src.cols)
      (startRe P.mandel P.plane P.seedRe cr ci) (startIm P.mandel P.plane P.seedIm cr ci) cr ci 0
      (zerosB (2 * P.len)) (zerosF P.len) (zerosF P.len) (zerosF P.len)

/-- A chunk of `P.len` pixels has `P.len` outputs. -/
theorem runChunk_sized (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source) (lo : Nat)
    (P : SweepParams) (ϵ : Float) : (runChunk F Q C cont src lo P ϵ).Sized P.len := by
  unfold runChunk
  split
  · rename_i h
    have h0 : P.len = 0 := by simpa using h
    rw [h0]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rename_i h
    have h0 : 0 < P.len := by simp at h; omega
    apply sweep_sized <;> simp

/-- The loop-invariant parameters of `s` for a chunk of `len` pixels. -/
def Spec.sweepParams (s : Spec) (len : Nat) : SweepParams :=
  { mandel := s.mandel, plane := s.plane, disk := s.disk, seedRe := s.seed.re,
    seedIm := s.seed.im, p := s.p, Nf := Float.ofNat s.N.toNat, N := s.N.toNat, len }

@[simp] theorem Spec.sweepParams_len (s : Spec) (len : Nat) : (s.sweepParams len).len = len := rfl

/-- A spawned task's value is its function's value (`Task.spawn fn = ⟨fn ()⟩`). -/
@[simp] theorem task_spawn_get {α : Type} (f : Unit → α) (prio : Task.Priority) :
    (Task.spawn f prio).get = f () := rfl

/-- The row chunks `[r0, r0 + step), [r0 + step, r0 + 2·step), …` of a `rows × cols` raster
(the last one shorter), each computed by its own `Task`. `fuel` bounds the number of chunks. -/
@[specialize] def spawnChunks (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source) (s : Spec)
    (rows cols step : Nat) : Nat → Nat → List (Task Chunk)
  | 0, _ => []
  | fuel + 1, r0 =>
    if r0 < rows then
      let r1 := min rows (r0 + step)
      Task.spawn (fun _ => runChunk F Q C cont src (r0 * cols) (s.sweepParams ((r1 - r0) * cols)) s.ϵ) ::
        spawnChunks F Q C cont src s rows cols step fuel r1
    else []

/-- Concatenate the float outputs `f c` of the chunks, in order, after `acc`. -/
def concatFloats (f : Chunk → FloatArray) : List Chunk → FloatArray → FloatArray
  | [], acc => acc
  | c :: cs, acc => concatFloats f cs (appendFloats acc (f c))

/-- Concatenate the iteration bytes of the chunks, in order, after `acc`. -/
def concatBytes : List Chunk → ByteArray → ByteArray
  | [], acc => acc
  | c :: cs, acc => concatBytes cs (acc ++ c.iter)

/-- Concatenation adds up the float-output sizes. -/
theorem size_concatFloats (f : Chunk → FloatArray) (cs : List Chunk) (acc : FloatArray) :
    (concatFloats f cs acc).size = acc.size + (cs.map fun c => (f c).size).sum := by
  induction cs generalizing acc with
  | nil => simp [concatFloats]
  | cons c cs ih => simp [concatFloats, ih]; omega

/-- Concatenation adds up the byte sizes. -/
theorem size_concatBytes (cs : List Chunk) (acc : ByteArray) :
    (concatBytes cs acc).size = acc.size + (cs.map fun c => c.iter.size).sum := by
  induction cs generalizing acc with
  | nil => simp [concatBytes]
  | cons c cs ih => simp [concatBytes, ih, ByteArray.size_append]; omega

/-- `concatFloats` over chunks still being computed: wait for each chunk in order and copy it
at once, so the copying overlaps the computation of the later chunks. -/
def concatFloatsT (f : Chunk → FloatArray) : List (Task Chunk) → FloatArray → FloatArray
  | [], acc => acc
  | t :: ts, acc => concatFloatsT f ts (appendFloats acc (f t.get))

theorem concatFloatsT_eq (f : Chunk → FloatArray) (ts : List (Task Chunk)) (acc : FloatArray) :
    concatFloatsT f ts acc = concatFloats f (ts.map Task.get) acc := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t ts ih => simp [concatFloatsT, concatFloats, ih]

/-- `concatBytes` over chunks still being computed (in order, as they finish). -/
def concatBytesT : List (Task Chunk) → ByteArray → ByteArray
  | [], acc => acc
  | t :: ts, acc => concatBytesT ts (acc ++ t.get.iter)

theorem concatBytesT_eq (ts : List (Task Chunk)) (acc : ByteArray) :
    concatBytesT ts acc = concatBytes (ts.map Task.get) acc := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t ts ih => simp [concatBytesT, concatBytes, ih]

/-- Concatenate the outputs of the chunk tasks in order. Each output is assembled by its own
dedicated thread that copies every chunk as soon as it is done, so the copying overlaps the
computation (`FloatArray` has no bulk copy: a copy costs about 1.5 ns per float). -/
def Chunk.concat (ts : List (Task Chunk)) (total : Nat) : Chunk :=
  let tre := Task.spawn (prio := .dedicated) fun _ =>
    concatFloatsT Chunk.zre ts (FloatArray.emptyWithCapacity total)
  let tim := Task.spawn (prio := .dedicated) fun _ =>
    concatFloatsT Chunk.zim ts (FloatArray.emptyWithCapacity total)
  let tmix := Task.spawn (prio := .dedicated) fun _ =>
    concatFloatsT Chunk.mix ts (FloatArray.emptyWithCapacity total)
  let iter := concatBytesT ts (ByteArray.emptyWithCapacity (2 * total))
  ⟨iter, tre.get, tim.get, tmix.get⟩

/-- The chunks of rows `r0 … rows-1` hold `(rows - r0)·cols` pixels in all. -/
theorem spawnChunks_sizes (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source) (s : Spec)
    (rows cols step : Nat) (hstep : 0 < step) (fuel r0 : Nat) (hfuel : rows - r0 ≤ fuel) :
    let cs := (spawnChunks F Q C cont src s rows cols step fuel r0).map Task.get
    (cs.map fun c => c.iter.size).sum = 2 * ((rows - r0) * cols) ∧
    (cs.map fun c => c.zre.size).sum = (rows - r0) * cols ∧
    (cs.map fun c => c.zim.size).sum = (rows - r0) * cols ∧
    (cs.map fun c => c.mix.size).sum = (rows - r0) * cols := by
  induction fuel generalizing r0 with
  | zero =>
    have : rows - r0 = 0 := by omega
    simp [spawnChunks, this]
  | succ fuel ih =>
    simp only [spawnChunks]
    split
    · rename_i hr
      obtain ⟨h1, h2, h3, h4⟩ := ih (min rows (r0 + step)) (by omega)
      obtain ⟨g1, g2, g3, g4⟩ := runChunk_sized F Q C cont src (r0 * cols)
        (s.sweepParams ((min rows (r0 + step) - r0) * cols)) s.ϵ
      simp only [Spec.sweepParams_len] at g1 g2 g3 g4
      have e : (min rows (r0 + step) - r0) * cols + (rows - min rows (r0 + step)) * cols =
          (rows - r0) * cols := by
        rw [← Nat.add_mul]; congr 1; omega
      simp only [List.map_cons, List.sum_cons, task_spawn_get, h1, h2, h3, h4]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [g1, ← Nat.mul_add, e]
      · rw [g2, e]
      · rw [g3, e]
      · rw [g4, e]
    · have : rows - r0 = 0 := by omega
      simp [this]

/-- Rows per parallel chunk: about 128 chunks per raster (enough to balance the uneven cost of
escape-time rows over the task pool, including its slower efficiency cores), and a single chunk
for small rasters or when `par` is off. -/
def chunkRows (par : Bool) (rows cols : Nat) : Nat :=
  if !par || rows * cols < 16384 then rows else max 1 ((rows + 127) / 128)

/-- The raster kernel over the `rows × cols` pixels of `src`, split into row chunks computed as
parallel tasks. The result has `rows·cols` pixels by construction (`sweep_sized`,
`spawnChunks_sizes`). -/
@[specialize] def computeRaster (F : C64 → C64 → C64) (Q : C64 → C64 → Float)
    (C : C64 → Float → Float → Float) (cont : Float → Float → Bool) (src : Source)
    (s : Spec) (rows cols : Nat) (par : Bool := true) : { c : Chunk // c.Sized (rows * cols) } :=
  let step := max 1 (chunkRows par rows cols)
  if step ≥ rows then
    ⟨runChunk F Q C cont src 0 (s.sweepParams (rows * cols)) s.ϵ,
      runChunk_sized F Q C cont src 0 (s.sweepParams (rows * cols)) s.ϵ⟩
  else
    ⟨Chunk.concat (spawnChunks F Q C cont src s rows cols step rows 0) (rows * cols), by
      obtain ⟨h1, h2, h3, h4⟩ := spawnChunks_sizes F Q C cont src s rows cols step
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)) rows 0 (by omega)
      simp only [Nat.sub_zero] at h1 h2 h3 h4
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [Chunk.concat, task_spawn_get, concatFloatsT_eq, concatBytesT_eq,
          size_concatBytes, size_concatFloats, size_byteEmpty, size_floatEmpty, Nat.zero_add,
          h1, h2, h3, h4]⟩

/-! ## `FilledSet` -/

/-- Julia `Fatou.FilledSet` (`src/Fatou.jl:126-135`): the computed raster, `rows × cols`,
row-major with row 0 at the top. -/
structure FilledSet (rows cols : Nat) where
  /-- the specification it was computed from (Julia `K.meta`) -/
  define : Define
  /-- the extent `[xa, xb, ya, yb]` (Julia `bounds(K)`) -/
  bounds : Bounds
  /-- iteration counts in `0 … N`, little-endian `UInt16` (Julia `iter::Matrix{UInt16}`) -/
  iter : ByteArray
  /-- real parts of the final iterates (Julia `set.Ω`) -/
  zre : FloatArray
  /-- imaginary parts of the final iterates -/
  zim : FloatArray
  /-- colouring values `C(z, iter/N, p)` (Julia `mix::Matrix{Float64}`; may be NaN) -/
  mix : FloatArray
  /-- two bytes per pixel -/
  size_iter : iter.size = 2 * (rows * cols)
  /-- one real part per pixel -/
  size_zre : zre.size = rows * cols
  /-- one imaginary part per pixel -/
  size_zim : zim.size = rows * cols
  /-- one colouring value per pixel -/
  size_mix : mix.size = rows * cols

namespace FilledSet

variable {rows cols : Nat}

/-- The iteration counts of `reference`, pushed for pixels `i, i+1, …` (`k` of them). -/
def referenceIter (K : Define) (pixel : Nat → C64) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | k + 1, i, acc => referenceIter K pixel k (i + 1) (pushU16 acc (K.orbit (pixel i)).1.toUInt16)

/-- The counts of `reference` take two bytes per pixel. -/
theorem size_referenceIter (K : Define) (pixel : Nat → C64) (k i : Nat) (acc : ByteArray) :
    (referenceIter K pixel k i acc).size = acc.size + 2 * k := by
  induction k generalizing i acc with
  | zero => rfl
  | succ k ih => simp only [referenceIter, ih, size_pushU16]; omega

/-- The reference construction: `Define.orbit` per pixel, written into size-tracked arrays
(the executable specification the parallel kernel is tested against). -/
def reference (K : Define) (bounds : Bounds) (pixel : Nat → C64) : FilledSet rows cols :=
  let res (i : Nat) : Nat × C64 := K.orbit (pixel i)
  { define := K, bounds,
    iter := referenceIter K pixel (rows * cols) 0 (ByteArray.emptyWithCapacity (2 * (rows * cols))),
    zre := floatArrayOfFn (rows * cols) fun i => (res i).2.re,
    zim := floatArrayOfFn (rows * cols) fun i => (res i).2.im,
    mix := floatArrayOfFn (rows * cols) fun i => let r := res i; K.mixOf r.1 r.2,
    size_iter := by
      rw [size_referenceIter]
      have : (ByteArray.emptyWithCapacity (2 * (rows * cols))).size = 0 := rfl
      omega,
    size_zre := by simp, size_zim := by simp, size_mix := by simp }

/-- Package raw outputs as a set, checking their sizes at runtime and falling back to
`reference` if one does not match. -/
def ofChunk (K : Define) (bounds : Bounds) (pixel : Nat → C64) (c : Chunk) : FilledSet rows cols :=
  if h : c.iter.size = 2 * (rows * cols) ∧ c.zre.size = rows * cols ∧ c.zim.size = rows * cols ∧
      c.mix.size = rows * cols then
    { define := K, bounds, iter := c.iter, zre := c.zre, zim := c.zim, mix := c.mix,
      size_iter := h.1, size_zre := h.2.1, size_zim := h.2.2.1, size_mix := h.2.2.2 }
  else reference K bounds pixel

end FilledSet

/-- Compute a Fatou set over the pixels of `src` with the given extent: the kernel specialized
on `K.F`, `K.Q`, `K.C`, with the loop test hoisted by mode. -/
@[inline] def Define.computeWith (K : Define) (rows cols : Nat) (bounds : Bounds) (src : Source)
    (par : Bool := true) : FilledSet rows cols :=
  let c :=
    if K.spec.newt then computeRaster K.F K.Q K.C (fun q ϵ => q > ϵ) src K.spec rows cols par
    else computeRaster K.F K.Q K.C (fun q ϵ => q < ϵ) src K.spec rows cols par
  { define := K, bounds, iter := c.1.iter, zre := c.1.zre, zim := c.1.zim, mix := c.1.mix,
    size_iter := c.2.1, size_zre := c.2.2.1, size_zim := c.2.2.2.1, size_mix := c.2.2.2.2 }

/-- Julia `fatou(K::Define)` (`src/Fatou.jl:170`): compute the set on the grid of
`K`'s rectangle (`x' .+ im*y`, bit for bit). Rows are computed by parallel tasks unless
`par := false`. -/
@[inline] def fatou (K : Define) (par : Bool := true) : FilledSet K.spec.rect.rows K.spec.rect.cols :=
  let r := K.spec.rect
  K.computeWith r.rows r.cols r.bounds (Source.ofRectangle r) par

/-- Julia `ComplexRectangle(Ω::Matrix{ComplexF64})` (`src/Fatou.jl:142`): a user raster gets
the pixel extent `[0, cols, 0, rows]`. -/
def Plane.pixelBounds (rows cols : Nat) : Bounds := ⟨0, Float.ofNat cols, 0, Float.ofNat rows⟩

/-- Julia `fatou(K::Define, Z::ComplexRectangle)` (`src/Fatou.jl:169`): iterate `K` from every
entry of the raster `Z` (which is also each pixel's `c`), keeping the extent `bounds` (by
default Julia's pixel extent of a bare matrix). -/
@[inline] def Define.onPlane {rows cols : Nat} (K : Define) (Z : Plane rows cols)
    (bounds : Bounds := Plane.pixelBounds rows cols) (par : Bool := true) : FilledSet rows cols :=
  K.computeWith rows cols bounds (Source.ofPlane Z) par

namespace FilledSet

variable {rows cols : Nat}

/-- Julia `ComplexRectangle(K::FilledSet)`: the final iterates as a raster (`K.set.Ω`). -/
def set (Z : FilledSet rows cols) : Plane rows cols :=
  ⟨Z.zre, Z.zim, Z.size_zre, Z.size_zim⟩

/-- Julia `fatou(K::Define, Z::FilledSet)` (`src/Fatou.jl:171`): **chain** `K` after `Z`,
iterating from `Z`'s final iterates (each also serving as `c`), with counts restarting at 0. -/
@[inline] def chain (K : Define) (Z : FilledSet rows cols) (par : Bool := true) :
    FilledSet rows cols :=
  K.onPlane Z.set Z.bounds par

/-- Julia `fatou(K::FilledSet)` (`src/Fatou.jl:173`): run `K.meta` (here `define`) again from `K`'s final
iterates. -/
@[inline] def refatou (Z : FilledSet rows cols) : FilledSet rows cols := chain Z.define Z

/-- The iteration count of pixel `(j, k)` (row `j` from the top, column `k`), unchecked. -/
@[inline] def iterAt (Z : FilledSet rows cols) (j : Fin rows) (k : Fin cols) : Nat :=
  have h := index_lt j.2 k.2
  let i := j.1 * cols + k.1
  (Z.iter[2 * i]'(by rw [Z.size_iter]; omega)).toNat +
    (Z.iter[2 * i + 1]'(by rw [Z.size_iter]; omega)).toNat * 256

/-- The iteration count at row-major position `i` (0 when out of range). -/
@[inline] def iterFlat (Z : FilledSet rows cols) (i : Nat) : Nat := (getU16 Z.iter i).toNat

/-- The colouring value of pixel `(j, k)`, unchecked. -/
@[inline] def mixAt (Z : FilledSet rows cols) (j : Fin rows) (k : Fin cols) : Float :=
  have h := index_lt j.2 k.2
  Z.mix[j.1 * cols + k.1]'(by rw [Z.size_mix]; exact h)

/-- The final iterate of pixel `(j, k)`, unchecked. -/
@[inline] def zAt (Z : FilledSet rows cols) (j : Fin rows) (k : Fin cols) : C64 := Z.set.get j k

/-- Julia `typeplot(K)`. -/
def typeplot (Z : FilledSet rows cols) : String := Z.define.typeplot

/-- Julia `String(K)`, the plain-text title. -/
def title (Z : FilledSet rows cols) : String := Z.define.title

/-- Histogram of the iteration counts, `h[k]` = number of pixels with `k` iterations,
`k = 0 … N`. -/
def iterHistogram (Z : FilledSet rows cols) : Array Nat :=
  go (rows * cols) 0 (Array.replicate (Z.define.spec.N.toNat + 1) 0)
where
  /-- count pixels `i, i+1, …` -/
  go : Nat → Nat → Array Nat → Array Nat
    | 0, _, h => h
    | k + 1, i, h => go k (i + 1) (h.modify (Z.iterFlat i) (· + 1))

/-- Julia `basin` index of each pixel (a Lean extension): the 1-based index of the first root
within `tol` of the final iterate (`|z - r| < tol`), or 0, one byte per pixel. -/
def basinIndex (Z : FilledSet rows cols) (roots : Array C64) (tol : Float) : ByteArray :=
  go (rows * cols) 0 (ByteArray.emptyWithCapacity (rows * cols))
where
  /-- the root index of one final iterate -/
  which (z : C64) : Nat := match roots.findIdx? fun r => (z - r).abs < tol with
    | some i => i + 1
    | none => 0
  /-- classify pixels `i, i+1, …` -/
  go : Nat → Nat → ByteArray → ByteArray
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) (acc.push (which ⟨Z.zre[i]!, Z.zim[i]!⟩).toUInt8)

end FilledSet

end Fatou
