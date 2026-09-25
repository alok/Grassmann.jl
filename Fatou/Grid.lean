import Fatou.Complex
import Fatou.Util

/-!
# Grids: `Rectangle`, raster sizes and the exact Julia pixel coordinates

Fatou.jl samples the complex plane on `x' .+ im*y` (`src/Fatou.jl:147-177`) with

* `x = range(xa + 0.0001, stop = xb, length = cols)`: note the `+0.0001` on the left edge,
  which keeps the default symmetric grids off `z = 0` (a pole of every Newton map);
* `y = range(yb, stop = ya, length = rows)`: row 1 is the **top** edge;
* `rows = round(UInt16, (yb - ya)/(xb - xa) * cols)` with ties to even (`Base.size`,
  `src/Fatou.jl:46`), so `n` counts **columns** (the README's "vertical grid points" is wrong).

Julia's `range` is a `TwicePrecision` `StepRangeLen`, ported bit for bit as
`JuliaBase.range`. The imaginary axis has one more twist: `im*y` rebuilds the range over
`Complex` double-doubles, which re-canonicalizes `ref` and `step` (`hi + lo` merged, losing
the bit truncation of `step.hi`), and indexing then rounds differently from `y[j]` in up to
~300 rows of a README grid (port-notes/fatou.md §4.2). `imAxis` replays that.

Rasters are stored **row-major** with row 0 at the top (`idx = j*cols + k`), the layout of
the oracle dumps and of `imshow(…, origin = "upper")`.
-/

namespace Fatou

open JuliaBase

/-- `Float64(π)`, Julia's `π` converted to a float. -/
def pi : Float := 3.141592653589793

/-- Julia `Rectangle.∂` (`src/Fatou.jl:29-37`): the bounds `[xa, xb, ya, yb]` of the sampled
region. -/
structure Bounds where
  /-- left edge (real part) -/
  xa : Float
  /-- right edge (real part) -/
  xb : Float
  /-- bottom edge (imaginary part) -/
  ya : Float
  /-- top edge (imaginary part) -/
  yb : Float
  deriving Repr, Inhabited, BEq

namespace Bounds

/-- Julia `Rectangle(∂)` for a scalar `∂` (`src/Fatou.jl:33`): `[-∂, ∂, -∂, ∂]`. -/
def square (s : Float) : Bounds := ⟨-s, s, -s, s⟩

/-- Julia `Rectangle(∂)` for a 2-vector `∂ = [a, b]` (`src/Fatou.jl:34`): the square
`[a, b, a, b]`, the same interval on both axes (not `[xa, xb]` with a default `y`). -/
def interval (a b : Float) : Bounds := ⟨a, b, a, b⟩

/-- The four numbers `[xa, xb, ya, yb]` (Julia `bounds(K)`), the `extent` of the image. -/
def toArray (b : Bounds) : Array Float := #[b.xa, b.xb, b.ya, b.yb]

/-- Julia's default `∂ = π/2`, i.e. `[-π/2, π/2, -π/2, π/2]`. -/
def default : Bounds := square (pi / 2)

end Bounds

/-- Julia `Rectangle` (`src/Fatou.jl:29-37`): bounds and the number of **columns** `n`
(horizontal grid points). The number of rows follows from the aspect ratio. -/
structure Rectangle where
  /-- `[xa, xb, ya, yb]` -/
  bounds : Bounds := .default
  /-- number of columns (Julia `n`, default 176) -/
  n : Nat := 176
  deriving Repr, Inhabited

namespace Rectangle

/-- Julia `(∂4 - ∂3)/(∂2 - ∂1) * n` rounded half to even (`Base.size`, `src/Fatou.jl:46`), as a
float (NaN or negative for degenerate bounds). -/
def rowsFloat (r : Rectangle) : Float :=
  F64.round (((r.bounds.yb - r.bounds.ya) / (r.bounds.xb - r.bounds.xa)) * Float.ofNat r.n)

/-- Number of rows, `size(Rectangle)[1]`. Julia throws `InexactError` when the rounded
aspect ratio is negative, NaN or above `typemax(UInt16)`; here those degenerate cases give
`0` rows (see `check`). -/
def rows (r : Rectangle) : Nat :=
  let f := r.rowsFloat
  if f.isNaN || f < 0 || f.isInf then 0 else (F64.toIntTrunc f).toNat

/-- Number of columns, `size(Rectangle)[2] = n`. -/
@[inline] def cols (r : Rectangle) : Nat := r.n

/-- Julia's argument checks, as an error message: `UInt16(n)` and
`round(UInt16, rows)` must not throw, and both axes need at least two points (a length-1
`range` with distinct endpoints throws). -/
def check (r : Rectangle) : Except String Unit := do
  let f := r.rowsFloat
  if r.n > 65535 then throw s!"InexactError: UInt16({r.n})"
  if f.isNaN || f < 0 || f > 65535 then throw s!"InexactError: round(UInt16, {f})"
  if r.n < 2 || r.rows < 2 then throw s!"degenerate grid {r.rows}×{r.n}"

/-- The x axis `range(xa + 0.0001, stop = xb, length = cols)` (`src/Fatou.jl:151`). -/
def xRange (r : Rectangle) : StepRangeLen :=
  JuliaBase.range (r.bounds.xa + 0.0001) r.bounds.xb r.cols

/-- The y axis `range(yb, stop = ya, length = rows)` (`src/Fatou.jl:152`), top to bottom. -/
def yRange (r : Rectangle) : StepRangeLen :=
  JuliaBase.range r.bounds.yb r.bounds.ya r.rows

end Rectangle

/-- The imaginary parts of `im * y` for a `TwicePrecision` range `y`: Julia's
`*(::Complex{Bool}, ::StepRangeLen)` rebuilds `ref` and `step` as complex double-doubles,
which canonicalizes each `(hi, lo)` pair. Indexing the result is ordinary
`StepRangeLen` indexing on the canonicalized pairs (port-notes/fatou.md §4.2, verified bit for
bit on 300 random Fatou grids). -/
def imAxis (y : StepRangeLen) : StepRangeLen :=
  { y with ref := TwicePrecision.canonicalize2 y.ref.hi y.ref.lo,
           step := TwicePrecision.canonicalize2 y.step.hi y.step.lo }

namespace Rectangle

/-- The real parts of the grid columns, `x[k]` for `k = 1..cols` (left to right). -/
def xs (r : Rectangle) : FloatArray :=
  let x := r.xRange
  floatArrayOfFn r.cols fun k => x.get (k + 1)

/-- The imaginary parts of the grid rows, `imag((im*y)[j])` for `j = 1..rows` (top to
bottom). -/
def ys (r : Rectangle) : FloatArray :=
  let y := imAxis r.yRange
  floatArrayOfFn r.rows fun j => y.get (j + 1)

/-- One real part per column. -/
@[simp] theorem size_xs (r : Rectangle) : r.xs.size = r.cols := by simp [xs]

/-- One imaginary part per row. -/
@[simp] theorem size_ys (r : Rectangle) : r.ys.size = r.rows := by simp [ys]

end Rectangle

/-- A `rows × cols` raster of complex numbers (Julia `ComplexRectangle.Ω`,
`Matrix{ComplexF64}`), stored row-major as two packed arrays. -/
structure Plane (rows cols : Nat) where
  /-- real parts, row-major -/
  re : FloatArray
  /-- imaginary parts, row-major -/
  im : FloatArray
  /-- `rows * cols` real parts -/
  size_re : re.size = rows * cols
  /-- `rows * cols` imaginary parts -/
  size_im : im.size = rows * cols

namespace Plane

variable {rows cols : Nat}

/-- The entry in row `j`, column `k` (both 0-based), without bounds checks. -/
@[inline] def get (P : Plane rows cols) (j : Fin rows) (k : Fin cols) : C64 :=
  have h := index_lt j.2 k.2
  ⟨P.re[j.1 * cols + k.1]'(by rw [P.size_re]; exact h),
   P.im[j.1 * cols + k.1]'(by rw [P.size_im]; exact h)⟩

/-- The entry at row-major position `i`. -/
@[inline] def getFlat (P : Plane rows cols) (i : Fin (rows * cols)) : C64 :=
  ⟨P.re[i.1]'(by rw [P.size_re]; exact i.2), P.im[i.1]'(by rw [P.size_im]; exact i.2)⟩

/-- The separable grid `x' .+ im*y` of axes `xs` (`cols` entries) and `ys` (`rows` entries):
entry `(j, k)` is `xs[k] + ys[j]·i` (Julia `x' .+ im*y`, `src/Fatou.jl:174-177`). -/
def ofAxes (xs ys : FloatArray) : Plane rows cols where
  re := floatArrayOfFn (rows * cols) fun i => xs[i % cols]!
  im := floatArrayOfFn (rows * cols) fun i => ys[i / cols]!
  size_re := by simp
  size_im := by simp

/-- Build a raster from a function of the row-major index. -/
def ofFn (f : Nat → C64) : Plane rows cols where
  re := floatArrayOfFn (rows * cols) fun i => (f i).re
  im := floatArrayOfFn (rows * cols) fun i => (f i).im
  size_re := by simp
  size_im := by simp

end Plane

/-- Julia `fatou(K::Rectangle)` (`src/Fatou.jl:174-177`): the coordinate grid `x' .+ im*y`
of a rectangle, bit for bit. -/
def Rectangle.grid (r : Rectangle) : Plane r.rows r.cols :=
  Plane.ofAxes r.xs r.ys

end Fatou
