import Adapode.Constants
import Cartan

/-!
# ODE states and the flat kernels of the integrators

Adapode integrates anything with `+`, scaling by a real and `abs.(value(·))`
(`src/Adapode.jl:224-241`): a Grassmann `Chain` (`Chain(10.0,10.0,10.0)` for Lorenz), a `Chain`
of `Chain`s (the position and velocity of a geodesic), or a whole Cartan `TensorField` (a curve
flowing in time). In every case the arithmetic is componentwise on the stored coefficients, which
Julia keeps inline (isbits `Values`) or in one array (a field's fiber array). `OdeState σ` is that
contract for Lean: a state is `dim` floats in one `FloatArray`, viewed without copying.

| state | `dim` |
|---|---|
| `Chain V G Float`, `Half V p Float`, `Multivector V Float` | the number of coefficients |
| `Values Float n` | `n` |
| `Phase V` (Julia `Chain(x, v)` of two vectors: geodesics) | `2n` |
| `TensorField m F` (a field state) | `width F * card m` |

The stepping loops work on the flat arrays (port notes §8.2): stage derivatives live in one
workspace (`ks`, stage-major, `s·d` floats), each combination is one tail-recursive pass per
component, and nothing is allocated per step beyond what the system itself returns. A system is
called in **destination-passing** form, `f h t x out`: `out` is a scratch state of the right size
that it may overwrite and return (then no allocation happens at all) or ignore (a Julia-style
`x -> Chain(…)` system, one allocation per evaluation).

**Operation order is Julia's** (bit-exact goldens, `Tests/Adapode`):

* `weights(h*c, fx)` (`Adapode.jl:224-230`) is `(h c₁) K₁ + (h c₂) K₂ + …`: each coefficient is
  multiplied by `h` first, the first product starts the sum, and the rest are added left to right
  (zero coefficients included: they decide the sign of zero results). A stage or a step is
  `x + weights(…)`.
* The error estimate of an embedded pair (`explicit!`, `Adapode.jl:434`) is
  `maximum(abs.(h * (db₁ K₁ + db₂ K₂ + …)))` (StaticVectors' `dot` is the same left fold), the
  one of an adaptive multistep method (`predictcorrect!`, `Adapode.jl:447`)
  `maximum(abs.((c - p) ./ c))`; `maximum` is Julia's NaN-propagating `max` (`F64.max`).
-/

namespace Adapode

open Grassmann DirectSum StaticVectors JuliaBase Cartan

/-! ## States -/

/-- An ODE state: `dim` floats stored contiguously (Julia: an isbits `Chain`/`Values`, or a
`TensorField`'s fiber array), with a zero-copy view (`toFlat`) and its inverse (`ofFlat`). -/
class OdeState (σ : Type) where
  /-- The number of floats of a state. -/
  dim : Nat
  /-- The coefficients (no copy). -/
  toFlat : σ → FloatArray
  /-- A state from its coefficients (no copy). -/
  ofFlat : (a : FloatArray) → a.size = dim → σ
  /-- Every state has `dim` coefficients. -/
  size_toFlat (x : σ) : (toFlat x).size = dim

export OdeState (toFlat)

attribute [simp] OdeState.size_toFlat

namespace OdeState

variable {σ : Type} [OdeState σ]

/-- `ofFlat` against a runtime dimension `d = dim` (the loops carry `d` in a register): a
mismatched array (which the integrators never produce) gives the state of `fallback`. -/
@[inline] def wrap (d : Nat) (hd : d = dim σ) (a : FloatArray) (fallback : σ) : σ :=
  if h : a.size = d then ofFlat a (h.trans hd) else fallback

end OdeState

instance {n : Nat} : OdeState (Values Float n) where
  dim := n
  toFlat v := v.data
  ofFlat a h := ⟨a, h⟩
  size_toFlat v := v.size_eq

section Grassmann

variable {V : TensorBundle} {G : Nat} {p : Bool}

instance : OdeState (Chain V G Float) where
  dim := Leibniz.binomial V.n G
  toFlat c := c.v.data
  ofFlat a h := ⟨⟨a, h⟩⟩
  size_toFlat c := c.v.size_eq

instance : OdeState (Half V p Float) where
  dim := halfDim V.n p
  toFlat c := c.v.data
  ofFlat a h := ⟨⟨a, h⟩⟩
  size_toFlat c := c.v.size_eq

instance : OdeState (Multivector V Float) where
  dim := 2 ^ V.n
  toFlat c := c.v.data
  ofFlat a h := ⟨⟨a, h⟩⟩
  size_toFlat c := c.v.size_eq

end Grassmann

/-- A field as a state: its fiber array (Julia's `TensorField` arithmetic is pointwise on the
fibers). The lazy-range tag is dropped: an ODE state is data. -/
instance {M : Type} [FrameBundle M] {m : M} {F : Type} [FlatFiber F] : OdeState (TensorField m F) where
  dim := FlatFiber.width F * card m
  toFlat t := t.data
  ofFlat a h := ⟨a, h, none⟩
  size_toFlat t := t.size_data

/-! ## Flat buffers -/

/-- `n` zeros. Built from `Array.replicate` (one shared boxed `0.0`, unboxed by `FloatArray.mk`): three
times faster than `n` pushes, and it touches the pages of a large trajectory buffer up front. -/
@[inline] def zeros (n : Nat) : FloatArray := ⟨Array.replicate n 0⟩

@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := by simp [zeros, FloatArray.size]

/-- `dst[off + j] := src[j]` for `j < k` (in place when `dst` is unshared). -/
def copyLoop (src : FloatArray) (off : Nat) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, dst => dst
  | k + 1, j, dst => copyLoop src off k (j + 1) (dst.set! (off + j) (src.get! j))

@[simp] theorem size_copyLoop (src : FloatArray) (off : Nat) :
    ∀ (k j : Nat) (dst : FloatArray), (copyLoop src off k j dst).size = dst.size
  | 0, _, _ => rfl
  | k + 1, j, dst => by rw [copyLoop, size_copyLoop src off k (j + 1), FloatArray.size_set!']

/-- Push `src[j], …, src[j+k-1]` onto `dst`. -/
def appendLoop (src : FloatArray) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, dst => dst
  | k + 1, j, dst => appendLoop src k (j + 1) (dst.push (src.get! j))

@[simp] theorem size_appendLoop (src : FloatArray) :
    ∀ (k j : Nat) (dst : FloatArray), (appendLoop src k j dst).size = dst.size + k
  | 0, _, _ => rfl
  | k + 1, j, dst => by rw [appendLoop, size_appendLoop src k (j + 1), FloatArray.size_push']; omega

/-- Write the `d` floats of `src` at `dst[off …]`. -/
@[inline] def copyInto (dst : FloatArray) (off d : Nat) (src : FloatArray) : FloatArray :=
  copyLoop src off d 0 dst

/-- `dst[j] := src[off + j]` for `j < k`. -/
def sliceLoop (src : FloatArray) (off : Nat) : (k j : Nat) → FloatArray → FloatArray
  | 0, _, dst => dst
  | k + 1, j, dst => sliceLoop src off k (j + 1) (dst.set! j (src.get! (off + j)))

@[simp] theorem size_sliceLoop (src : FloatArray) (off : Nat) :
    ∀ (k j : Nat) (dst : FloatArray), (sliceLoop src off k j dst).size = dst.size
  | 0, _, _ => rfl
  | k + 1, j, dst => by rw [sliceLoop, size_sliceLoop src off k (j + 1), FloatArray.size_set!']

/-- Overwrite `dst[0 … d)` with `src[off … off + d)`. -/
@[inline] def loadFrom (dst : FloatArray) (src : FloatArray) (off d : Nat) : FloatArray :=
  sliceLoop src off d 0 dst

/-- A fresh copy of `src[off … off + d)`. -/
@[inline] def slice (src : FloatArray) (off d : Nat) : FloatArray := loadFrom (zeros d) src off d

@[simp] theorem size_slice (src : FloatArray) (off d : Nat) : (slice src off d).size = d := by
  simp [slice, loadFrom]

/-! ## Phase states: a position and a velocity (Julia `Chain(x, v)`) -/

/-- Julia `Chain(x, v)` of two vectors of `V` (the state of a geodesic, `Adapode.jl:611-614`),
stored as the `n` position coefficients followed by the `n` velocity coefficients, as Julia's
isbits `Chain` of `Chain`s is. -/
structure Phase (V : TensorBundle) where
  /-- `x₁ … xₙ v₁ … vₙ`. -/
  data : FloatArray
  /-- Two vectors' worth of coefficients. -/
  size_data : data.size = 2 * Leibniz.binomial V.n 1

namespace Phase

variable {V : TensorBundle}

/-- Julia `Chain(x, v)`. -/
def mk' (x v : Chain V 1 Float) : Phase V :=
  ⟨copyInto (copyInto (zeros (2 * Leibniz.binomial V.n 1)) 0 (Leibniz.binomial V.n 1) x.v.data)
    (Leibniz.binomial V.n 1) (Leibniz.binomial V.n 1) v.v.data, by simp [copyInto]⟩

/-- The position (Julia `X[1]`). -/
def pos (s : Phase V) : Chain V 1 Float :=
  Chain.ofFn fun i => s.data.get! i.1

/-- The velocity (Julia `X[2]`). -/
def vel (s : Phase V) : Chain V 1 Float :=
  Chain.ofFn fun i => s.data.get! (Leibniz.binomial V.n 1 + i.1)

instance : Inhabited (Phase V) := ⟨⟨zeros (2 * Leibniz.binomial V.n 1), size_zeros _⟩⟩

instance : OdeState (Phase V) where
  dim := 2 * Leibniz.binomial V.n 1
  toFlat s := s.data
  ofFlat a h := ⟨a, h⟩
  size_toFlat s := s.size_data

/-- Two vectors, flat. -/
instance : FlatFiber (Phase V) where
  width := 2 * Leibniz.binomial V.n 1
  read a off := ⟨slice a off (2 * Leibniz.binomial V.n 1), size_slice _ _ _⟩
  push a s := appendLoop s.data (2 * Leibniz.binomial V.n 1) 0 a
  size_push a s := by simp

end Phase

/-! ## Julia's `weights` and the step combinations

`linComb` is Julia's `x + weights(h*w, K)` (`Adapode.jl:224-241`): component by component,
`x[j] + (((c₀ K₀[j] + c₁ K₁[j]) + c₂ K₂[j]) + …)` with `cₗ = h·w[l]`. The stage values `K_l` sit in
one flat array at offsets `oₗ` (stage-major for Runge–Kutta, ring slots for Adams). For up to
seven terms (every table of Adapode) the sum is unrolled, with the coefficients and offsets
computed once per combination (the same products Julia forms in `h*c`), so a combination is one
tight loop over the components. -/

section Lin

/-- `y[j] := x[j] + c₀K[o₀+j]`. -/
def lin1Loop (c0 : Float) (o0 : Nat) (K x : FloatArray) : (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y => lin1Loop c0 o0 K x n (j + 1) (y.set! j (x.get! j + c0 * K.get! (o0 + j)))

/-- Two terms. -/
def lin2Loop (c0 c1 : Float) (o0 o1 : Nat) (K x : FloatArray) : (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    lin2Loop c0 c1 o0 o1 K x n (j + 1)
      (y.set! j (x.get! j + (c0 * K.get! (o0 + j) + c1 * K.get! (o1 + j))))

/-- Three terms. -/
def lin3Loop (c0 c1 c2 : Float) (o0 o1 o2 : Nat) (K x : FloatArray) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    lin3Loop c0 c1 c2 o0 o1 o2 K x n (j + 1)
      (y.set! j (x.get! j + ((c0 * K.get! (o0 + j) + c1 * K.get! (o1 + j)) + c2 * K.get! (o2 + j))))

/-- Four terms. -/
def lin4Loop (c0 c1 c2 c3 : Float) (o0 o1 o2 o3 : Nat) (K x : FloatArray) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    lin4Loop c0 c1 c2 c3 o0 o1 o2 o3 K x n (j + 1)
      (y.set! j (x.get! j + (((c0 * K.get! (o0 + j) + c1 * K.get! (o1 + j)) + c2 * K.get! (o2 + j))
        + c3 * K.get! (o3 + j))))

/-- Five terms. -/
def lin5Loop (c0 c1 c2 c3 c4 : Float) (o0 o1 o2 o3 o4 : Nat) (K x : FloatArray) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    lin5Loop c0 c1 c2 c3 c4 o0 o1 o2 o3 o4 K x n (j + 1)
      (y.set! j (x.get! j + ((((c0 * K.get! (o0 + j) + c1 * K.get! (o1 + j)) + c2 * K.get! (o2 + j))
        + c3 * K.get! (o3 + j)) + c4 * K.get! (o4 + j))))

/-- Six terms. -/
def lin6Loop (c0 c1 c2 c3 c4 c5 : Float) (o0 o1 o2 o3 o4 o5 : Nat) (K x : FloatArray) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    lin6Loop c0 c1 c2 c3 c4 c5 o0 o1 o2 o3 o4 o5 K x n (j + 1)
      (y.set! j (x.get! j + (((((c0 * K.get! (o0 + j) + c1 * K.get! (o1 + j)) + c2 * K.get! (o2 + j))
        + c3 * K.get! (o3 + j)) + c4 * K.get! (o4 + j)) + c5 * K.get! (o5 + j))))

/-- Seven terms. -/
def lin7Loop (c0 c1 c2 c3 c4 c5 c6 : Float) (o0 o1 o2 o3 o4 o5 o6 : Nat) (K x : FloatArray) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    lin7Loop c0 c1 c2 c3 c4 c5 c6 o0 o1 o2 o3 o4 o5 o6 K x n (j + 1)
      (y.set! j (x.get! j + ((((((c0 * K.get! (o0 + j) + c1 * K.get! (o1 + j)) + c2 * K.get! (o2 + j))
        + c3 * K.get! (o3 + j)) + c4 * K.get! (o4 + j)) + c5 * K.get! (o5 + j)) + c6 * K.get! (o6 + j))))

/-- The offset of term `l`: `((l + base) mod m)·d` for `l + base < 2m` (stage `l` of a Runge–Kutta
workspace with `base = 0`, `m = k`; ring slot `(l + s + 1) mod (o + 1)` of an Adams ring, `s ≤ o + 1`).
A formula rather than a function argument, so that no closure is built per combination, and a
conditional subtraction rather than a division. -/
@[inline] def termOffset (base m d l : Nat) : Nat :=
  let q := l + base
  (if q < m then q else q - m) * d

/-- The tail of the sum for component `j` beyond seven terms: `acc + cₗK[off l + j]`. -/
def linTailLoop (h : Float) (w : FloatArray) (wo base m d : Nat) (K : FloatArray) (j : Nat) :
    (k l : Nat) → Float → Float
  | 0, _, acc => acc
  | k + 1, l, acc =>
    linTailLoop h w wo base m d K j k (l + 1)
      (acc + (h * w.get! (wo + l)) * K.get! (termOffset base m d l + j))

/-- Any number `k ≥ 1` of terms (the generic path; Adapode's tables have at most seven). -/
def linAnyLoop (h : Float) (w : FloatArray) (wo base m d : Nat) (K x : FloatArray) (k : Nat) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    let acc := linTailLoop h w wo base m d K j (k - 1) 1
      ((h * w.get! wo) * K.get! (termOffset base m d 0 + j))
    linAnyLoop h w wo base m d K x k n (j + 1) (y.set! j (x.get! j + acc))

/-- Julia `x + weights(h*w, K)` over `d` components: `y[j] := x[j] + Σₗ (h·w[wo+l]) K[oₗ + j]` for
`l < k` (`k ≥ 1`, `oₗ = termOffset base m d l`), the first product starting the sum and the rest
added left to right. -/
@[inline] def linComb (h : Float) (w : FloatArray) (wo base m : Nat) (K x : FloatArray)
    (d k : Nat) (y : FloatArray) : FloatArray :=
  let c (l : Nat) := h * w.get! (wo + l)
  let off (l : Nat) := termOffset base m d l
  match k with
  | 1 => lin1Loop (c 0) (off 0) K x d 0 y
  | 2 => lin2Loop (c 0) (c 1) (off 0) (off 1) K x d 0 y
  | 3 => lin3Loop (c 0) (c 1) (c 2) (off 0) (off 1) (off 2) K x d 0 y
  | 4 => lin4Loop (c 0) (c 1) (c 2) (c 3) (off 0) (off 1) (off 2) (off 3) K x d 0 y
  | 5 => lin5Loop (c 0) (c 1) (c 2) (c 3) (c 4) (off 0) (off 1) (off 2) (off 3) (off 4) K x d 0 y
  | 6 => lin6Loop (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (off 0) (off 1) (off 2) (off 3) (off 4) (off 5) K x d 0 y
  | 7 => lin7Loop (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (off 0) (off 1) (off 2) (off 3) (off 4)
      (off 5) (off 6) K x d 0 y
  | _ => linAnyLoop h w wo base m d K x k d 0 y

/-- A Runge–Kutta combination: the stages at `ks[l·d …]`. -/
@[inline] def comb (h : Float) (w : FloatArray) (wo : Nat) (ks x : FloatArray) (d k : Nat)
    (y : FloatArray) : FloatArray :=
  linComb h w wo 0 (Nat.max k 1) ks x d k y

end Lin

/-- `max(acc, |h z[j]|)` over the components from `j` on (Julia's NaN-propagating `max`). -/
def maxAbsScaledLoop (h : Float) (z : FloatArray) : (n j : Nat) → Float → Float
  | 0, _, acc => acc
  | n + 1, j, acc => maxAbsScaledLoop h z n (j + 1) (F64.max acc (h * z.get! j).abs)

/-- The embedded-pair error of `explicit!` (`Adapode.jl:434`): `maximum(abs.(h * (db · K)))`, with
`db · K` StaticVectors' `dot` (the same left fold as `weights`). `z` is scratch and `zero` a zero
state: `z = 0 + db·K` has the value of `db·K` up to the sign of a zero, which `abs` removes. (A
maximum started at `0` equals Julia's, started at the first element, on values `≥ 0` and `NaN`.) -/
@[inline] def errEmbedded (h : Float) (db ks zero : FloatArray) (d s : Nat) (z : FloatArray) :
    Float × FloatArray :=
  let z := comb 1 db 0 ks zero d s z
  (maxAbsScaledLoop h z d 0 0, z)

/-- `a[i]` with a machine-word index (`0` past the end): one comparison, no `Nat` tagging. -/
@[inline] def rdU (a : FloatArray) (i : USize) : Float := if h : i.toNat < a.size then a.uget i h else 0

/-- `a[i] := v` with a machine-word index (no change past the end; in place when unshared). -/
@[inline] def wrU (a : FloatArray) (i : USize) (v : Float) : FloatArray :=
  if h : i.toNat < a.size then a.uset i v h else a

/-- Heun's final combination (`heun`, `Adapode.jl:243-246`): `x[j] + (h K₁[j] + h K₂[j]) / 2`, the
division by `2` as Grassmann's `* (1/2)`. -/
def heunLoop (h : Float) (K1 K2 x : FloatArray) : (n : Nat) → (j : USize) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    heunLoop h K1 K2 x n (j + 1) (wrU y j (rdU x j + (h * rdU K1 j + h * rdU K2 j) * f64! 0.5))

/-- `y[j] := x[j] + h K[off + j]` (Euler; Heun's predictor `x + hfx`). -/
def eulerLoop (h : Float) (ks : FloatArray) (off : USize) (x : FloatArray) :
    (n : Nat) → (j : USize) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y => eulerLoop h ks off x n (j + 1) (wrU y j (rdU x j + h * rdU ks (off + j)))

/-! ## Adams ring buffers -/

/-- Julia `shift(Val(m), Val(l), i+(m-l))` (`Adapode.jl:233, 238-241`): the ring slot (0-based)
of the `q`-th oldest of the `o` values ending at the 1-based slot `s`, in a ring of `o + 1`. -/
@[inline] def ringSlot (o s q : Nat) : Nat := (q + s + 1) % (o + 1)

/-- Julia `x + explicit(x, h, w, fx, s)` (`multistep!`, `Adapode.jl:238-241, 298-301`):
`x + weights(h*w, F)` over the `o` ring values ending at slot `s`, oldest first. -/
@[inline] def adamsComb (h : Float) (w F x : FloatArray) (o s d : Nat) (y : FloatArray) : FloatArray :=
  linComb h w 0 (s + 1) (o + 1) F x d o y

/-- `max(acc, |(c[j] - p[j]) / c[j]|)` over the components from `j` on: the relative
predictor–corrector gap `maximum(abs.(value(c-p)./value(c)))` of `predictcorrect!`
(`Adapode.jl:447, 457`), started at `0` (as `maxAbsScaledLoop`). -/
def relGapLoop (c p : FloatArray) : (n j : Nat) → Float → Float
  | 0, _, e => e
  | n + 1, j, e =>
    let cj := c.get! j
    relGapLoop c p n (j + 1) (F64.max e ((cj - p.get! j) / cj).abs)

/-! ## Time grids -/

/-- Element `i` (0-based) of Julia's `StepRangeLen` `r` (`Axis.stepLenGet`), with the index
conversion done in `Float` (`offF = Float64(r.offset)`: `i + 1 - offset` is a small integer, so the
difference of the two exact conversions is Julia's `convert(Float64, i - offset)`). -/
@[inline] def rangeAt (r : StepRangeLen) (offF : Float) (i : Nat) : Float :=
  let u := (i + 1).toUInt64.toFloat - offF
  let x := TwicePrecision.add12 r.ref.hi (u * r.step.hi)
  x.hi + (x.lo + (u * r.step.lo + r.ref.lo))

/-- `Float64(r.offset)`. -/
@[inline] def rangeOffset (r : StepRangeLen) : Float := Axis.intToFloat r.offset

/-! ## Systems -/

/-- A system at the level of flat arrays: `f h t x out` writes `f(t ↦ x)` into (a reuse of)
`out`. `h` is the step, passed for Julia's `FlowApprox` systems (`f(x, h)`). -/
abbrev FlatSystem := Float → Float → FloatArray → FloatArray → FloatArray

/-- The flat form of a typed system (`d = dim σ`; `fallback` is never used by the integrators,
which only pass arrays of `d` floats). -/
@[inline] def flatSystem {σ : Type} [OdeState σ] (d : Nat) (hd : d = OdeState.dim σ) (fallback : σ)
    (f : Float → Float → σ → σ → σ) : FlatSystem :=
  fun h t x out =>
    toFlat (f h t (OdeState.wrap d hd x fallback) (OdeState.wrap d hd out fallback))

end Adapode
