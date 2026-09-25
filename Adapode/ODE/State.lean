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

/-- Append `n` zeros. -/
def pushZeros : Nat → FloatArray → FloatArray
  | 0, a => a
  | n + 1, a => pushZeros n (a.push 0)

@[simp] theorem size_pushZeros : ∀ (n : Nat) (a : FloatArray), (pushZeros n a).size = a.size + n
  | 0, _ => rfl
  | n + 1, a => by rw [pushZeros, size_pushZeros n, FloatArray.size_push']; omega

/-- `n` zeros (unboxed from the start). -/
@[inline] def zeros (n : Nat) : FloatArray := pushZeros n (FloatArray.emptyWithCapacity n)

@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := by
  simp [zeros]; rfl

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

/-! ## Julia's `weights` and the step combinations -/

/-- The tail of Julia's `weights(h*c, fx)` for component `j`: `acc + (h c[co+l]) K_l[j]` for the
remaining stages, left to right (`K_l` at `ks[l·d …]`). -/
def wsumLoop (h : Float) (c : FloatArray) (co : Nat) (ks : FloatArray) (d j : Nat) :
    (k l : Nat) → Float → Float
  | 0, _, acc => acc
  | k + 1, l, acc => wsumLoop h c co ks d j k (l + 1) (acc + (h * c.get! (co + l)) * ks.get! (l * d + j))

/-- Julia `weights(h*c, fx)` (`Adapode.jl:224-230`) for component `j`, over the first `k ≥ 1`
stages: `(h c₀) K₀[j] + (h c₁) K₁[j] + …`. -/
@[inline] def wsum (h : Float) (c : FloatArray) (co : Nat) (ks : FloatArray) (d j k : Nat) : Float :=
  wsumLoop h c co ks d j (k - 1) 1 ((h * c.get! co) * ks.get! j)

/-- `y[j] := x[j] + weights(h*c, K)[j]` for every component (Julia `explicit(x, h, c, fx)`,
`Adapode.jl:234-237`). -/
def combLoop (h : Float) (c : FloatArray) (co : Nat) (ks x : FloatArray) (d k : Nat) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    combLoop h c co ks x d k n (j + 1) (y.set! j (x.get! j + wsum h c co ks d j k))

@[simp] theorem size_combLoop (h : Float) (c : FloatArray) (co : Nat) (ks x : FloatArray) (d k : Nat) :
    ∀ (n j : Nat) (y : FloatArray), (combLoop h c co ks x d k n j y).size = y.size
  | 0, _, _ => rfl
  | n + 1, j, y => by rw [combLoop, size_combLoop h c co ks x d k n (j + 1), FloatArray.size_set!']

/-- `y := x + weights(h*c[co …], K₀ … K_{k-1})`. -/
@[inline] def comb (h : Float) (c : FloatArray) (co : Nat) (ks x : FloatArray) (d k : Nat)
    (y : FloatArray) : FloatArray :=
  combLoop h c co ks x d k d 0 y

/-- The embedded-pair error of `explicit!` (`Adapode.jl:434`), from component `j` on:
`max(acc, |h · (db₀ K₀[j] + db₁ K₁[j] + …)|)` (StaticVectors' `dot`, a left fold, then the step). -/
def errLoop (h : Float) (db ks : FloatArray) (d s : Nat) : (n j : Nat) → Float → Float
  | 0, _, acc => acc
  | n + 1, j, acc =>
    let dot := wsumLoop 1 db 0 ks d j (s - 1) 1 (db.get! 0 * ks.get! j)
    errLoop h db ks d s n (j + 1) (F64.max acc (h * dot).abs)

/-- Julia `maximum(abs.(step(t)*value(b[end]⋅fx)))` over the `d` components (`s` stages). The
first component starts the maximum. -/
@[inline] def errEmbedded (h : Float) (db ks : FloatArray) (d s : Nat) : Float :=
  if d = 0 then 0
  else
    let dot0 := wsumLoop 1 db 0 ks d 0 (s - 1) 1 (db.get! 0 * ks.get! 0)
    errLoop h db ks d s (d - 1) 1 (h * dot0).abs

/-- Heun's final combination, from component `j` on: `x[j] + (h K₀[j] + h K₁[j]) / 2`
(`heun`, `Adapode.jl:243-246`; Grassmann divides by `2` as `* (1/2)`). -/
def heunLoop (h : Float) (ks x : FloatArray) (d : Nat) : (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y =>
    heunLoop h ks x d n (j + 1) (y.set! j (x.get! j + (h * ks.get! j + h * ks.get! (d + j)) * f64! 0.5))

@[simp] theorem size_heunLoop (h : Float) (ks x : FloatArray) (d : Nat) :
    ∀ (n j : Nat) (y : FloatArray), (heunLoop h ks x d n j y).size = y.size
  | 0, _, _ => rfl
  | n + 1, j, y => by rw [heunLoop, size_heunLoop h ks x d n (j + 1), FloatArray.size_set!']

/-- `y[j] := x[j] + h K[j]` (Euler; Heun's predictor `x + hfx`), `K` at `ks[off …]`. -/
def eulerLoop (h : Float) (ks : FloatArray) (off : Nat) (x : FloatArray) :
    (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y => eulerLoop h ks off x n (j + 1) (y.set! j (x.get! j + h * ks.get! (off + j)))

@[simp] theorem size_eulerLoop (h : Float) (ks : FloatArray) (off : Nat) (x : FloatArray) :
    ∀ (n j : Nat) (y : FloatArray), (eulerLoop h ks off x n j y).size = y.size
  | 0, _, _ => rfl
  | n + 1, j, y => by rw [eulerLoop, size_eulerLoop h ks off x n (j + 1), FloatArray.size_set!']

/-! ## Adams ring buffers -/

/-- Julia `shift(Val(m), Val(l), i+(m-l))` (`Adapode.jl:233, 238-241`): the ring slot (0-based)
of the `q`-th oldest of the `o` values ending at the 1-based slot `s`, in a ring of `o + 1`. -/
@[inline] def ringSlot (o s q : Nat) : Nat := (q + s + 1) % (o + 1)

/-- The tail of the Adams sum for component `j`: `acc + (h w[q]) F[slot(q)][j]`. -/
def adamsLoop (h : Float) (w F : FloatArray) (o s d j : Nat) : (k q : Nat) → Float → Float
  | 0, _, acc => acc
  | k + 1, q, acc =>
    adamsLoop h w F o s d j k (q + 1) (acc + (h * w.get! q) * F.get! (ringSlot o s q * d + j))

/-- Julia `explicit(x, h, c, fx, i)` (`Adapode.jl:238-241`) for component `j`: `weights(h*w, F)`
over the `o` ring values ending at slot `s`, oldest first. -/
@[inline] def adamsSum (h : Float) (w F : FloatArray) (o s d j : Nat) : Float :=
  adamsLoop h w F o s d j (o - 1) 1 ((h * w.get! 0) * F.get! (ringSlot o s 0 * d + j))

/-- The Adams–Bashforth predictor `y := x + Σ` (`multistep!` with `CAB`, `Adapode.jl:298-301`). -/
def predictLoop (h : Float) (w F x : FloatArray) (o s d : Nat) : (n j : Nat) → FloatArray → FloatArray
  | 0, _, y => y
  | n + 1, j, y => predictLoop h w F x o s d n (j + 1) (y.set! j (x.get! j + adamsSum h w F o s d j))

@[simp] theorem size_predictLoop (h : Float) (w F x : FloatArray) (o s d : Nat) :
    ∀ (n j : Nat) (y : FloatArray), (predictLoop h w F x o s d n j y).size = y.size
  | 0, _, _ => rfl
  | n + 1, j, y => by rw [predictLoop, size_predictLoop h w F x o s d n (j + 1), FloatArray.size_set!']

/-- The Adams–Moulton corrector over the predictor held in `y`: `y[j] := c[j] = x[j] + Σ`, and the
running error `max |(c[j] - p[j]) / c[j]|` (`predictcorrect!`, `Adapode.jl:437-447`). -/
def correctLoop (h : Float) (w F x : FloatArray) (o s d : Nat) :
    (n j : Nat) → FloatArray → Float → FloatArray × Float
  | 0, _, y, e => (y, e)
  | n + 1, j, y, e =>
    let p := y.get! j
    let c := x.get! j + adamsSum h w F o s d j
    correctLoop h w F x o s d n (j + 1) (y.set! j c) (F64.max e ((c - p) / c).abs)

theorem size_correctLoop (h : Float) (w F x : FloatArray) (o s d : Nat) :
    ∀ (n j : Nat) (y : FloatArray) (e : Float), (correctLoop h w F x o s d n j y e).1.size = y.size
  | 0, _, _, _ => rfl
  | n + 1, j, y, e => by
    rw [correctLoop, size_correctLoop h w F x o s d n (j + 1), FloatArray.size_set!']

/-- The relative predictor–corrector gap `maximum(abs.((c - p) ./ c))` for the Euler/backward-Euler
pair (`predictcorrect!` at `Val(1)`, `Adapode.jl:449-458`), `c` in `x'`, `p` in `y`. -/
def relGapLoop (c p : FloatArray) : (n j : Nat) → Float → Float
  | 0, _, e => e
  | n + 1, j, e =>
    let cj := c.get! j
    relGapLoop c p n (j + 1) (F64.max e ((cj - p.get! j) / cj).abs)

/-- `maximum(abs.((c - p) ./ c))` over `d ≥ 1` components (the first starts the maximum). -/
@[inline] def relGap (c p : FloatArray) (d : Nat) : Float :=
  if d = 0 then 0
  else
    let c0 := c.get! 0
    relGapLoop c p (d - 1) 1 ((c0 - p.get! 0) / c0).abs

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
