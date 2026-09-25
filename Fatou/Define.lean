import Fatou.Grid

/-!
# `Define`: the specification of a Fatou set

Julia's `Fatou.Define(E; kw...)` (`src/Fatou.jl:73-119`) takes a symbolic expression `E`,
compiles it (and, in Newton mode, REDUCE's symbolic derivative) with `SyntaxTree.genlatest`,
and stores the closures with the keyword options. The Lean port replaces the symbolic layer
by ordinary Lean functions:

* the map `f : C64 → C64 → C64` (`(z, c) ↦ E`), and in Newton mode its `z`-derivative `df`;
* optionally the Newton map itself (to reproduce REDUCE's rational form bit for bit);
* a `label`, Julia's `string(E)`, used in titles (`String(K)`, `src/Fatou.jl:369-372`), and an
  optional LaTeX form for the PyPlot title.

The three front-ends keep Julia's **per-front-end defaults** (port-notes/fatou.md §2.3):

| option | `juliafill` | `mandelbrot` | `newton` |
|---|---|---|---|
| colouring `C` | `angle(z)/(2π)·n^p` | `exp(-abs(z))·n^p` | `angle(z)/(2π)·n^p` |
| `ϵ` | 4 | 4 | 0.01 |
| `m` | 0 | 0 | 1 |
| escape `Q` | `abs2(z)` | `abs2(z)` | `abs(f(z))` (fixed) |

Maps are written against the Julia-exact operations of `Fatou.C64`
(e.g. `fun z c => z^2 + c`, `fun z _ => (2 : Float) * z ^ 3 + (1 : Float)`): real constants
are `Float`s, so that `2 * z` scales and `z + 1` adds to the real part exactly as Julia's
mixed real/complex methods do. For a fast raster:

* keep the `Define` visible to the compiler (build it inline in the `fatou` call or bind it
  with `@[inline] def`/`abbrev`), so the kernel specializes on the map and the loop runs on
  unboxed floats;
* give decimal constants a top-level definition (`def c₀ : C64 := ⟨-0.06, 0.67⟩`) rather than
  writing the literal inside the map: an inlined decimal literal can be re-parsed on every
  iteration (docs/PERF.md). Integer-valued literals such as `(2 : Float)` are cheap.

Not ported: Julia's symbolic front-end (maps are Lean functions; titles take the `label`),
`juliafill(E; newt = true)` (use `newton`), and the `@time` printing of `Compute`.
-/

namespace Fatou

open JuliaBase

/-- A Julia `Number` as Fatou prints it: the multiplicity `m` keeps its Julia type
(`1`, `1.5`, `1 - 1im`, `-0.5 + 2.0im`) because `String(K)` interpolates it with `print`. -/
inductive Number where
  /-- a Julia `Int` -/
  | int (n : Int)
  /-- a Julia `Float64` -/
  | float (x : Float)
  /-- a Julia `Complex{Int}`, e.g. `1 - 1im` -/
  | complexInt (re im : Int)
  /-- a Julia `ComplexF64`, e.g. `-0.5 + 2.0im` -/
  | complexFloat (re im : Float)
  deriving Repr, Inhabited

namespace Number

/-- The value as a `ComplexF64`. -/
def toC64 : Number → C64
  | .int n => ⟨Float.ofInt n, 0⟩
  | .float x => ⟨x, 0⟩
  | .complexInt a b => ⟨Float.ofInt a, Float.ofInt b⟩
  | .complexFloat a b => ⟨a, b⟩

/-- Julia `print(m)` / `"$(m)"`. -/
def toJulia : Number → String
  | .int n => toString n
  | .float x => F64.showString x
  | .complexInt a b => showComplex false (⟨a, b⟩ : Complex Int)
  | .complexFloat a b => showComplex false (⟨a, b⟩ : Complex Float)

/-- Julia `m == 1` (true for `1`, `1.0`, `1 + 0im`, …). -/
def isOne (m : Number) : Bool := let z := m.toC64; z.re == 1 && z.im == 0

/-- Julia `m ≠ 0`. -/
def isNonzero (m : Number) : Bool := let z := m.toC64; z.re != 0 || z.im != 0

/-- Whether the value is real (an `Int` or `Float64`). -/
def isReal : Number → Bool
  | .int _ | .float _ => true
  | _ => false

instance {n : Nat} : OfNat Number n := ⟨.int n⟩
instance : OfScientific Number := ⟨fun m s e => .float (OfScientific.ofScientific m s e)⟩
instance : Neg Number where
  neg
    | .int n => .int (-n)
    | .float x => .float (-x)
    | .complexInt a b => .complexInt (-a) (-b)
    | .complexFloat a b => .complexFloat (-a) (-b)
instance : ToString Number := ⟨toJulia⟩

end Number

/-- The numeric options of a Fatou set, Julia `Define`'s non-function fields
(`src/Fatou.jl:74-92`). -/
structure Spec where
  /-- bounds and number of columns (Julia `Ω::Rectangle`, from `∂` and `n`) -/
  rect : Rectangle := {}
  /-- maximum number of iterations (Julia `N::UInt16`) -/
  N : UInt16 := 35
  /-- escape (or, in Newton mode, convergence) threshold (Julia `ϵ`) -/
  ϵ : Float := 4
  /-- plot the iteration count rather than the colouring `mix` -/
  iter : Bool := false
  /-- exponent of the iteration factor in the colouring (Julia `p`) -/
  p : Float := 0
  /-- Newton mode: iterate while `|f(z)| > ϵ` -/
  newt : Bool := false
  /-- Newton multiplicity factor (any Julia `Number`) -/
  m : Number := 0
  /-- Mandelbrot mode: start every orbit at `seed`, with `c` the pixel -/
  mandel : Bool := false
  /-- Mandelbrot start value -/
  seed : C64 := ⟨0, 0⟩
  /-- cobweb start point (`nothing` in Julia when absent) -/
  x0 : Option Float := none
  /-- number of cobweb steps -/
  orbit : Nat := 0
  /-- highest composition power drawn in the orbit plot -/
  depth : Nat := 1
  /-- colormap name (resolved by the plotting backend) -/
  cmap : String := ""
  /-- map the input disk to the upper half-plane (`plane`) before iterating -/
  plane : Bool := false
  /-- map the output half-plane to the disk (`disk`) after iterating -/
  disk : Bool := false
  deriving Inhabited

/-- Julia `Fatou.Define` (`src/Fatou.jl:73-119`): the options plus the compiled functions. -/
structure Define where
  /-- numeric options -/
  spec : Spec
  /-- Julia `string(E)`, the map as printed in `String(K)` (e.g. `"z ^ 2 + c"`) -/
  label : String := ""
  /-- the LaTeX of `E` for the PyPlot title (Julia `rdpm(latex(E))`, from REDUCE) -/
  latex : String := label
  /-- the iterated map `(z, c) ↦ z'`: `E` itself, or the Newton map in Newton mode -/
  F : C64 → C64 → C64
  /-- the escape functional `(z, c) ↦ Q`: `abs2(z)` by default, `abs(E)` in Newton mode -/
  Q : C64 → C64 → Float
  /-- the colouring `(z, n, p) ↦ C` with `n = iter/N` -/
  C : C64 → Float → Float → Float
  /-- the real map `x ↦ F(x, 0)` for the cobweb plot (`src/orbitplot.jl:20`). Julia evaluates
  it with real arithmetic, which can round differently from the complex map. -/
  real : Float → Float := fun x => (F ⟨x, 0⟩ ⟨0, 0⟩).re
  /-- Julia `string(E)` when the set was defined from an expression (`Fatou.Symbolic`); used by
  `Define.basinOf` to derive the basin LaTeX as Julia's `basin(K, j)` does -/
  expr : Option String := none

/-! ## Defaults -/

/-- `2π` as Julia evaluates it: `2 * Float64(π)`. -/
def twoPi : Float := 2 * pi

/-- Julia `n^p` for `Float64` arguments (`0^0 = 1`). -/
@[inline] def powF (n p : Float) : Float := if p == f64! 0.0 then f64! 1.0 else F64.pow n p

/-- Julia's default escape criterion `Q = :(abs2(z))`. -/
@[inline] def abs2Q (z _c : C64) : Float := z.abs2

/-- Julia's default colouring for `juliafill`/`newton`, `C = :((angle(z)/(2π))*n^p)`, with
values in `(-0.5, 0.5]` when `p = 0`. -/
@[inline] def angleColor (z : C64) (n p : Float) : Float := (z.angle / twoPi) * powF n p

/-- Julia's default colouring for `mandelbrot`, `C = :(exp(-abs(z))*n^p)`, in `(0, 1]`. -/
@[inline] def mandelColor (z : C64) (n p : Float) : Float := F64.exp (-z.abs) * powF n p

/-- The generalized Newton map `z ↦ z - m·f(z)/f'(z)` (Julia builds it symbolically with
REDUCE, `src/internals.jl:9-12`, and then factors it; this is the unfactored form). A real
`m` scales, a complex `m` multiplies. -/
@[inline] def newtonMap (f df : C64 → C64 → C64) (m : Number) : C64 → C64 → C64 :=
  match m with
  | .int _ | .float _ =>
    let r := m.toC64.re
    fun z c => z - C64.scale r (C64.div (f z c) (df z c))
  | _ =>
    let w := m.toC64
    fun z c => z - w * C64.div (f z c) (df z c)

/-! ## Front-ends -/

/-- Keyword options shared by the front-ends (Julia's `∂, n, N, ϵ, iter, p, m, seed, x0,
orbit, depth, cmap, plane, disk`). `ϵ` and `m` default per front-end when left `none`. -/
structure Options where
  /-- Julia `∂`: `Bounds.square s`, `Bounds.interval a b`, or explicit `[xa, xb, ya, yb]` -/
  bounds : Bounds := .default
  /-- number of columns -/
  n : Nat := 176
  /-- maximum iterations -/
  N : UInt16 := 35
  /-- threshold (default 4, or 0.01 for `newton`) -/
  ϵ : Option Float := none
  /-- plot iteration counts -/
  iter : Bool := false
  /-- colouring exponent -/
  p : Float := 0
  /-- Newton multiplicity (default 0, or 1 for `newton`) -/
  m : Option Number := none
  /-- Mandelbrot seed -/
  seed : C64 := ⟨0, 0⟩
  /-- cobweb start point -/
  x0 : Option Float := none
  /-- cobweb steps -/
  orbit : Nat := 0
  /-- composition depth of the orbit plot -/
  depth : Nat := 1
  /-- colormap name -/
  cmap : String := ""
  /-- disk → half-plane on input -/
  plane : Bool := false
  /-- half-plane → disk on output -/
  disk : Bool := false
  /-- Julia `string(E)` for titles -/
  label : String := ""
  /-- LaTeX of `E` for the PyPlot title (defaults to `label`) -/
  latex : Option String := none
  deriving Inhabited

/-- The `Spec` of a front-end call, given its mode flags and defaults for `ϵ`, `m`. -/
@[inline] def Options.toSpec (o : Options) (newt mandel : Bool) (ϵ : Float) (m : Number) : Spec :=
  { rect := { bounds := o.bounds, n := o.n }, N := o.N, ϵ := o.ϵ.getD ϵ, iter := o.iter,
    p := o.p, newt, m := o.m.getD m, mandel, seed := o.seed, x0 := o.x0, orbit := o.orbit,
    depth := o.depth, cmap := o.cmap, plane := o.plane, disk := o.disk }

/-- Julia `juliafill(E; …)` (`src/Fatou.jl:203-222`): the filled Julia set of
`z ↦ f(z, c)`, iterated from each pixel `z₀` with `c = z₀` too. -/
@[inline] def juliafill (f : C64 → C64 → C64) (o : Options := {}) (Q : C64 → C64 → Float := abs2Q)
    (C : C64 → Float → Float → Float := angleColor) (real : Option (Float → Float) := none) :
    Define :=
  { spec := o.toSpec false false 4 0, label := o.label, latex := o.latex.getD o.label,
    F := f, Q, C, real := real.getD fun x => (f ⟨x, 0⟩ ⟨0, 0⟩).re }

/-- Julia `mandelbrot(E; …)` (`src/Fatou.jl:250-271`): every orbit starts at `seed` and `c` is
the pixel. Julia switches to Newton mode when `m ≠ 0` (`:269`); that needs the derivative
`df`, so it happens here only when `df` is given. -/
@[inline] def mandelbrot (f : C64 → C64 → C64) (o : Options := {}) (Q : C64 → C64 → Float := abs2Q)
    (C : C64 → Float → Float → Float := mandelColor) (df : Option (C64 → C64 → C64) := none)
    (real : Option (Float → Float) := none) : Define :=
  let m := o.m.getD 0
  match df with
  | some df =>
    if m.isNonzero then
      let F := newtonMap f df m
      { spec := o.toSpec true true 4 0, label := o.label, latex := o.latex.getD o.label,
        F, Q := fun z c => (f z c).abs, C, real := real.getD fun x => (F ⟨x, 0⟩ ⟨0, 0⟩).re }
    else
      { spec := o.toSpec false true 4 0, label := o.label, latex := o.latex.getD o.label,
        F := f, Q, C, real := real.getD fun x => (f ⟨x, 0⟩ ⟨0, 0⟩).re }
  | none =>
    { spec := o.toSpec false true 4 0, label := o.label, latex := o.latex.getD o.label,
      F := f, Q, C, real := real.getD fun x => (f ⟨x, 0⟩ ⟨0, 0⟩).re }

/-- Julia `newton(E; …)` (`src/Fatou.jl:299-318`): the (generalized) Newton fractal of `f`,
iterating `z ↦ z - m·f(z)/f'(z)` while `|f(z)| > ϵ`. `map` overrides the Newton map (e.g.
with REDUCE's factored rational form, which rounds differently); `mandel` starts every orbit
at `seed` as in Julia's `newton(E; mandel = true)`. -/
@[inline] def newton (f df : C64 → C64 → C64) (o : Options := {})
    (C : C64 → Float → Float → Float := angleColor) (map : Option (C64 → C64 → C64) := none)
    (mandel : Bool := false) (real : Option (Float → Float) := none) : Define :=
  let m := o.m.getD 1
  let F := map.getD (newtonMap f df m)
  { spec := o.toSpec true mandel 0.01 1, label := o.label, latex := o.latex.getD o.label,
    F, Q := fun z c => (f z c).abs, C, real := real.getD fun x => (F ⟨x, 0⟩ ⟨0, 0⟩).re }

/-! ## Titles and labels -/

namespace Define

/-- Julia `typeplot(K)` (`src/Fatou.jl:367`): `"iter."` when plotting iteration counts,
otherwise `"roots"` if `m == 1` (even outside Newton mode: a Julia quirk kept for title
parity) and `"limit"` else. -/
def typeplot (K : Define) : String :=
  if K.spec.iter then "iter." else if K.spec.m.isOne then "roots" else "limit"

/-- Julia `String(K::FilledSet)` (`src/Fatou.jl:369-372`), the plain-text title:
`"f : z ↦ E, m = m, typeplot"` in Newton mode, `"f : z ↦ E, typeplot"` otherwise. -/
def title (K : Define) : String :=
  let text := s!"f : z ↦ {K.label},"
  if K.spec.newt then s!"{text} m = {K.spec.m}, {K.typeplot}" else s!"{text} {K.typeplot}"

/-- The PyPlot title (`ext/PyPlotExt.jl:30-40`): `latexstring("f:z\mapsto E,\, m = m, ") * t`
in Newton mode and `latexstring("f:z\mapsto E,\,") * t` otherwise (the `$…$` of the first
part, then the typeplot text). -/
def latexTitle (K : Define) : String :=
  let text := s!"f:z\\mapsto {K.latex},\\,"
  if K.spec.newt then s!"${text} m = {K.spec.m}, ${K.typeplot}" else s!"${text}${K.typeplot}"

/-- The PyPlot y-label of Newton-mode figures (`ext/PyPlotExt.jl:34`), or `none`. -/
def latexYLabel (K : Define) : Option String :=
  if K.spec.newt then some "$Fatou\\,set:\\,$$z\\,↦\\,z-m\\,×\\,f(z)\\,/\\,f\\,'(z)$" else none

/-- The plain-text y-label (Makie's `"Fatou set: z ↦ z-m×f(z)/f'(z)"`) of Newton-mode figures. -/
def yLabel (K : Define) : Option String :=
  if K.spec.newt then some "Fatou set: z ↦ z-m×f(z)/f'(z)" else none

end Define

/-! ## `basin` LaTeX (`src/internals.jl:22-32`) -/

/-- `set0` of `src/internals.jl:23`. -/
def basinSet0 : String := "D_0(\\epsilon) = \\left\\{ z\\in\\mathbb{C}: \\left|\\,z"

/-- `setj(j)` of `src/internals.jl:24`. -/
def basinSetJ (j : Nat) : String :=
  "\\displaystyle D_" ++ toString j ++ "(\\epsilon) = \\left\\{z\\in\\mathbb{C}:\\left|\\,"

/-- `nsetstr` of `src/internals.jl:25` (Newton basins: within `ϵ` of a root). -/
def basinNewtonSuffix : String :=
  "- r_i\\,\\right|<\\epsilon,\\,\\forall r_i(\\,f(r_i)=0 )\\right\\}"

/-- `jsetstr` of `src/internals.jl:26` (escape sets: beyond `ϵ`). -/
def basinJuliaSuffix : String := "\\,\\right|>\\epsilon\\right\\}"

/-- Julia `basin(K, j)` (`src/Fatou.jl:335`, `src/internals.jl:29-32`): the LaTeX set notation
of the `j`-th basin, `$…$`. Julia derives `body`, the LaTeX of the `j`-fold composition of
the (Newton) map with `c = 0`, from REDUCE; here the caller supplies it (ignored for `j = 0`). -/
def basin (newt : Bool) (j : Nat) (body : String) : String :=
  let suffix := if newt then basinNewtonSuffix else basinJuliaSuffix
  if j == 0 then s!"${basinSet0} {suffix}$" else s!"${basinSetJ j}{body} {suffix}$"

end Fatou
