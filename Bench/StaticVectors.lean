import Bench.Harness
import StaticVectors

/-!
# `staticvectors`: small static vectors (`Values`)

Julia twin: `oracle/bench/staticvectors.jl` (`StaticVectors.Values{n,Float64}`, an isbits
tuple). ns per vector operation over arrays of 1000 random vectors (identical on both sides):
accumulation (`add`), `dot`, `cross`, `norm`, `normalize`, and a scalar multiple, at `n = 3`
and `n = 16`. In Lean a `Values Float n` is a packed `FloatArray`: one heap object per vector,
so every operation that returns a vector allocates.
-/

namespace Bench.StaticVectors

open _root_.StaticVectors Bench

/-- `m` vectors of length `k` from a flat array. -/
def vecs (k m : Nat) (xs : FloatArray) : Array (Values Float k) :=
  (Array.range m).map fun i => Values.ofFn fun j => xs[i * k + j.1]!

/-- The loop of `sumPair`: `acc + ∑_{j ≥ i} f as[j] bs[j]`. `@[specialize]` on the recursive
function itself, so every call site gets a copy with `f` inlined (a `where`-local loop of a
specialized function is not specialized: it called `f` as a closure returning a boxed `Float`,
an allocation per vector, as the Julia twin's `sv_sumpair(f::F, …) where {F}` does not). -/
@[specialize] def sumPairLoop {k : Nat} (f : Values Float k → Values Float k → Float)
    (as bs : Array (Values Float k)) (i : Nat) (acc : Float) : Nat → Float
  | 0 => acc
  | fuel + 1 =>
    if h : i < as.size then
      if h' : i < bs.size then sumPairLoop f as bs (i + 1) (acc + f as[i] bs[i]) fuel else acc
    else acc

/-- `∑ f as[i] bs[i]`. -/
@[inline] def sumPair {k : Nat} (f : Values Float k → Values Float k → Float)
    (as bs : Array (Values Float k)) : Float :=
  sumPairLoop f as bs 0 0 as.size

/-- The loop of `sumOne` (specialized per call site, see `sumPairLoop`). -/
@[specialize] def sumOneLoop {k : Nat} (f : Values Float k → Float) (as : Array (Values Float k))
    (i : Nat) (acc : Float) : Nat → Float
  | 0 => acc
  | fuel + 1 => if h : i < as.size then sumOneLoop f as (i + 1) (acc + f as[i]) fuel else acc

/-- `∑ f as[i]`. -/
@[inline] def sumOne {k : Nat} (f : Values Float k → Float) (as : Array (Values Float k)) : Float :=
  sumOneLoop f as 0 0 as.size

/-- `sum(foldl(+, as))`: accumulate the vectors, then sum the components. -/
def addAll {k : Nat} (as : Array (Values Float k)) : Float :=
  (as.foldl (· + ·) (Values.replicate 0)).sum

/-- First component of the cross product. -/
@[inline] def cross1 (a b : Values Float 3) : Float := (Values.cross a b).get 0

/-- First component of the normalized vector. -/
@[inline] def normalize1 {k : Nat} (a : Values Float (k + 1)) : Float := (Values.normalize a).get 0

/-- The scale factor `2.5`, a top-level constant (a literal inlined into the specialized loop
stays a run-time `Float.ofScientific` call, docs/PERF.md; Julia folds its literal). -/
def scaleFactor : Float := 2.5

/-- First component of `a * 2.5` (Julia `(a * 2.5)[1]`). -/
@[inline] def scale1 {k : Nat} (a : Values Float (k + 1)) : Float := (a * scaleFactor).get 0

/-- Cases at dimension `k + 1`. Inlined at each literal `k`, so every operation is compiled for
a static length (as Julia's `Values{3,Float64}` is); with a runtime `k` the operations run as
generic loops through closures, about 2× slower still. -/
@[inline] def dimCases (k : Nat) (m : Nat) : BenchM Unit := do
  let d := k + 1
  let p := s!"{m}×{d}"
  let as := vecs d m (randFloats (d * m) 0xA11CE (-1) 1)
  let bs := vecs d m (randFloats (d * m) 0xB0B0 (-1) 1)
  bench s!"add{d}" (ops := m) (param := p) fun s => addAll (blackBox s as)
  bench s!"dot{d}" (ops := m) (param := p) fun s => sumPair (fun a b => a.dot b) (blackBox s as) bs
  bench s!"norm{d}" (ops := m) (param := p) fun s => sumOne (fun a => a.norm) (blackBox s as)
  bench s!"normalize{d}" (ops := m) (param := p) fun s => sumOne normalize1 (blackBox s as)
  bench s!"scale{d}" (ops := m) (param := p) fun s => sumOne scale1 (blackBox s as)

/-- The suite. -/
def suite : Suite := ⟨"staticvectors", do
  let m := 1000
  dimCases 2 m
  let as := vecs 3 m (randFloats (3 * m) 0xA11CE (-1) 1)
  let bs := vecs 3 m (randFloats (3 * m) 0xB0B0 (-1) 1)
  bench "cross3" (ops := m) (param := s!"{m}×3") fun s => sumPair cross1 (blackBox s as) bs
  dimCases 15 m⟩

end Bench.StaticVectors
