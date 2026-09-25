import Fatou.Define

/-!
# Real orbits and cobweb plots

Julia `orbit(K::Define)` (`src/orbitplot.jl:17-21`) draws, for the real map
`x ↦ F(x, 0)`: the diagonal `y = x`, the map and its compositions up to `depth`, the
cobweb path of the orbit from `x0`, and the orbit as a time series. `real_orb`
(`src/orbitplot.jl:23-54`) computes the data; the backends (`ext/PyPlotExt.jl:42-73`,
`ext/UnicodePlotsExt.jl:19-45`) add limits, titles and legends. This module reproduces the
data and the strings; drawing is LeanPlot's job.
-/

namespace Fatou

open JuliaBase

/-- The data of Julia `real_orb(E, f, bi, orb, depth, incr)` (`src/orbitplot.jl:23-54`). -/
structure RealOrbit where
  /-- the `incr` sample points `range(a, stop = b, length = incr)` (no `+0.0001` here) -/
  x : FloatArray
  /-- the columns of Julia's `N` matrix: `x`, `f.(x)`, `f.(f.(x))`, … (`depth + 1` of them) -/
  comps : Array FloatArray
  /-- Julia `N2`: the orbit `x0, f(x0), …, f^orb(x0)` (`orb + 1` values; `x0 = 0` if unset) -/
  orbit : FloatArray
  /-- x coordinates of the cobweb polyline (`3·orb` points) -/
  cobwebX : FloatArray
  /-- y coordinates of the cobweb polyline -/
  cobwebY : FloatArray
  /-- Julia `bis = [a, b, x0 or 0]` -/
  bis : Float × Float × Float

/-- Apply `f` to every element (Julia `broadcast(f, v)`). -/
def mapFloats (f : Float → Float) (v : FloatArray) : FloatArray :=
  floatArrayOfFn v.size fun i => f v[i]!

/-- The orbit `x0, f(x0), …` with `orb + 1` entries (Julia `N2`, `src/orbitplot.jl:40-46`). -/
def iterateOrbit (f : Float → Float) (x0 : Float) (orb : Nat) : FloatArray :=
  go orb x0 (FloatArray.emptyWithCapacity (orb + 1))
where
  /-- push the current value and step -/
  go : Nat → Float → FloatArray → FloatArray
    | 0, x, acc => acc.push x
    | k + 1, x, acc => go k (f x) (acc.push x)

/-- The orbit loop pushes the `k` steps and the final value. -/
theorem iterateOrbit.size_go (f : Float → Float) (k : Nat) (x : Float) (acc : FloatArray) :
    (iterateOrbit.go f k x acc).size = acc.size + k + 1 := by
  induction k generalizing x acc with
  | zero => simp [iterateOrbit.go, FloatArray.size_push]
  | succ k ih => simp [iterateOrbit.go, ih, FloatArray.size_push]; omega

/-- The orbit has `orb + 1` points `x0, f(x0), …, f^orb(x0)`. -/
@[simp] theorem size_iterateOrbit (f : Float → Float) (x0 : Float) (orb : Nat) :
    (iterateOrbit f x0 orb).size = orb + 1 := by
  simp [iterateOrbit, iterateOrbit.size_go]

/-- Julia `real_orb` (`src/orbitplot.jl:23-54`): sample `[a, b]` at `incr` points, compose `f`
`depth` times, and follow the orbit of `x0` (or of `0.0`) for `orb` steps, with its cobweb
polyline `(x_k, x_k), (x_k, x_{k+1}), (x_{k+1}, x_{k+1})` for `k = 0 … orb-1`. -/
def realOrb (f : Float → Float) (a b : Float) (x0 : Option Float) (orb depth incr : Nat) :
    RealOrbit :=
  let r := JuliaBase.range a b incr
  let x := floatArrayOfFn incr fun i => r.get (i + 1)
  let comps := (List.range depth).foldl (fun (cs : Array FloatArray) _ =>
    cs.push (mapFloats f cs.back!)) #[x]
  let s := x0.getD 0
  let n2 := iterateOrbit f s orb
  let at_ (k : Nat) : Float := n2[k]!
  let cx := floatArrayOfFn (3 * orb) fun i => let k := i / 3; if i % 3 == 2 then at_ (k + 1) else at_ k
  let cy := floatArrayOfFn (3 * orb) fun i => let k := i / 3; if i % 3 == 0 then at_ k else at_ (k + 1)
  { x, comps, orbit := n2, cobwebX := cx, cobwebY := cy, bis := (a, b, s) }

/-- The shape of Julia's `real_orb` output: `incr` samples, `orb + 1` orbit points and a
`3·orb`-point cobweb (`src/orbitplot.jl:47-53`). -/
theorem realOrb_sizes (f : Float → Float) (a b : Float) (x0 : Option Float) (orb depth incr : Nat) :
    let o := realOrb f a b x0 orb depth incr
    o.x.size = incr ∧ o.orbit.size = orb + 1 ∧ o.cobwebX.size = 3 * orb ∧ o.cobwebY.size = 3 * orb := by
  simp [realOrb]

namespace RealOrbit

/-- The y-limits every backend uses (`ext/PyPlotExt.jl:62-64`):
`(min(1.07·minimum(f(x)), 0), max(1.07·maximum(f(x)), 0))`, NaN-propagating like Julia's
`minimum`/`maximum`. -/
def ylim (o : RealOrbit) : Float × Float :=
  let v := o.comps[1]?.getD o.x
  let lo := v.foldl (fun m y => F64.min m y) F64.inf
  let hi := v.foldl (fun m y => F64.max m y) (-F64.inf)
  (F64.min (1.07 * lo) 0, F64.max (1.07 * hi) 0)

/-- The x-limits, `(a, b)`. -/
def xlim (o : RealOrbit) : Float × Float := (o.bis.1, o.bis.2.1)

/-- The abscissae of the orbit time series, `range(a, stop = b, length = orb + 1)`
(`ext/PyPlotExt.jl:53`): the orbit is drawn stretched across the x range. -/
def orbitXs (o : RealOrbit) : FloatArray :=
  let r := JuliaBase.range o.bis.1 o.bis.2.1 o.orbit.size
  floatArrayOfFn o.orbit.size fun i => r.get (i + 1)

end RealOrbit

/-- Julia `orbit(K::Define)` (`src/orbitplot.jl:17-21`): the cobweb data of `K`'s real map on
`[xa, xb]` with `incr = n` samples. -/
def Define.realOrbit (K : Define) : RealOrbit :=
  realOrb K.real K.spec.rect.bounds.xa K.spec.rect.bounds.xb K.spec.x0 K.spec.orbit K.spec.depth
    K.spec.rect.n

/-! ## Strings -/

/-- LaTeXStrings' `latexstring(s)` (`_maybe_wrap_equation`): wrap `s` in `$…$` unless it
already contains an unescaped `$` (one at the start, or after a character other than `\` or
`%`). -/
def latexstring (s : String) : String :=
  let cs := s.toList
  let hasMath := match cs with
    | '$' :: _ => true
    | _ => (cs.zip cs.tail).any fun (a, b) => b == '$' && a != '\\' && a != '%'
  if hasMath then s else "$" ++ s ++ "$"

/-- The UnicodePlots title of an orbit plot (`ext/UnicodePlotsExt.jl:39-43`):
`"z ↦ E, IC: z₀ = x0, n∈0:orb"` (the suffix only when `orb ≠ 0`). -/
def Define.orbitTitle (K : Define) : String :=
  let x0 := K.spec.x0.getD 0
  let funt := if K.spec.orbit != 0 then s!", IC: z₀ = {F64.showString x0}, n∈0:{K.spec.orbit}" else ""
  s!"z ↦ {K.label}{funt}"

/-- The PyPlot title of an orbit plot (`ext/PyPlotExt.jl:55-66`):
`latexstring("$ x \mapsto E$" * funt)` with `funt = ", IC: $ x_0 = x0$, $ n\in0:orb$"`. -/
def Define.orbitLatexTitle (K : Define) : String :=
  let x0 := K.spec.x0.getD 0
  let funt := if K.spec.orbit != 0 then
    s!", IC: $ x_0 = {F64.showString x0}$, $ n\\in0:{K.spec.orbit}$" else ""
  latexstring s!"$ x \\mapsto {K.latex}${funt}"

/-- The PyPlot legend of an orbit plot (`ext/PyPlotExt.jl:68`), one entry per series in
drawing order: `y=x`, `ϕ(x)`, the cobweb, `ϕ^k(x)` for `k = 2 … depth`, and the orbit
series when `orb ≠ 0`. -/
def Define.orbitLatexLegend (K : Define) : Array String :=
  let base := #[latexstring "$y=x$", latexstring "$\\phi(x)$", latexstring "(x_n,\\phi(x_n))"]
  let comps := ((List.range (K.spec.depth - 1)).map fun i =>
    latexstring s!"\\phi^\{{i + 2}}(x)").toArray
  let orb := if K.spec.orbit != 0 then #[latexstring s!"\\phi(x_\{0:{K.spec.orbit}})"] else #[]
  base ++ comps ++ orb

/-- The UnicodePlots series names of an orbit plot (`ext/UnicodePlotsExt.jl:25-37`). -/
def Define.orbitLegend (K : Define) : Array String :=
  let base := #["y=real(z)", "ϕ(real(z))", "(zₙ,ϕ(zₙ))"]
  let comps := ((List.range (K.spec.depth - 1)).map fun i => s!"ϕ^\{{i + 2}}(z)").toArray
  let orb := if K.spec.orbit != 0 then #[s!"ϕ(z_\{0:{K.spec.orbit}})"] else #[]
  base ++ comps ++ orb

end Fatou
