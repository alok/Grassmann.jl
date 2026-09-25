# Fatou.jl → Lean 4 porting spec

Source: `/Users/alokbeniwal/chakravala/Fatou.jl` @ `0311284` (tag v1.2.4, 2025-10-18, "fixed Julia 1.12 world age #15").
All `file:line` references are relative to that repo unless prefixed. The Julia oracle is Julia 1.13.0 (aarch64, Apple M4 Max) with the env
`scratchpad/juliaenv` (Fatou 1.2.4, Reduce 1.2.17, SyntaxTree 1.0.1, ColorSchemes 3.31.0, Grassmann 0.8.46).
`scratchpad` below means `/private/tmp/claude-502/-Users-alokbeniwal-Grassmann/c6cc2308-bfca-4b9a-ad33-d89b110132a8/scratchpad`.

Supporting material produced while writing this spec (all verified by running them):

| path | what |
|---|---|
| `scratchpad/fatou/jrange.jl` | standalone re-implementation of Julia's `range(a, stop=b, length=n)` + Fatou's grid axes using only IEEE primitives. Verified bit-exact against Base on 4000 random ranges and 300 random Fatou grids (`t6.jl`). Transliterate this into Lean. |
| `scratchpad/fatou/dump_golden.jl` | prototype oracle dumper (JSON metadata + raw little-endian row-major arrays) |
| `scratchpad/fatou/render_golden.py` | prototype visual oracle: re-renders dumps with matplotlib exactly like `PyPlotExt` |
| `scratchpad/fatou/compare_readme.png` | README images (left) vs oracle re-render (right): they match; this proves the dump → render pipeline |
| `scratchpad/fatou/golden/` | dumped README goldens (`readme_*.{json,iter.u16,mix.f64,zre.f64,zim.f64,gx.f64,gy.f64,png}`) |
| `scratchpad/fatou/wiki/` | clone of the GitHub wiki (`Explore-Fatou-sets-&-fractals.md` + 57 images): 34 more examples |
| `scratchpad/fatou/sheet_*.png` | contact sheets of all wiki images |
| `scratchpad/fatou/t*.jl` | probe scripts that produced the numbers quoted here |

---

## 1. Purpose & scope

Fatou.jl (~930 LOC total, of which ~500 are core) renders **escape-time / limit-value fractals** for holomorphic maps:

* **Julia / filled-Julia sets** (`juliafill`): iterate `z ↦ F(z, c)` from each grid pixel `z0`, with `c = z0` also available.
* **Mandelbrot-type parameter sets** (`mandelbrot`): iterate from a fixed seed `z = seed` with `c = pixel`.
* **(Generalized) Newton fractals** (`newton`): iterate the Newton map `z ↦ z − m·f(z)/f'(z)`. The derivative is computed **symbolically** by the REDUCE CAS (`Reduce.jl`), then simplified and factored. `m` may be complex ("generalized Newton").
* **Real cobweb orbit plots** (`orbit`): for a real map `x ↦ F(x, 0)`, plot `y = x`, `F`, the iterates `F^k` up to `depth`, a cobweb path from `x0`, and the orbit as a time series.
* **LaTeX set notation** for the `j`-th basin (`basin`), produced by substitution plus REDUCE's LaTeX printer.
* Optional **Poincaré maps**: the input disk is mapped to the half-plane (`plane`), and the output half-plane to the disk (`disk`).
* Optional **generalized "complex" numbers** via Grassmann `Couple{V,B}`, meaning `a + b·B` for a basis blade `B` with `B² ∈ {−1, 0, +1}` (`ext/GrassmannExt.jl`). **This is currently broken** (see §4.10).

Two output channels:
* `iter::Matrix{UInt16}`: the iteration count per pixel.
* `mix::Matrix{Float64}`: a user coloring function `C(z_final, n = iter/N, p)` per pixel.

The `iter` flag picks which one a plot shows.

Scope of this spec: everything in `src/`, `ext/`, `README.md`, `img/`, `test/`, plus the wiki examples (the README links to them as "detailed examples"). Plotting backends (PyPlot, Makie, UnicodePlots, ImageInTerminal) are described as **output contracts** for LeanPlot. They are not code to port.

---

## 2. Public API inventory

### 2.1 Exports

* `src/Fatou.jl:25` exports `fatou, juliafill, mandelbrot, newton, basin, plot`.
* `src/orbitplot.jl:4` exports `orbit`.
* **`plot` is exported but never defined in `Fatou`.** `isdefined(Fatou, :plot) == false` (verified). README's `plot(...)` resolves to `PyPlot.plot` extended in `ext/PyPlotExt.jl:19`. The Lean port should define its own `plot`/`render`.
* No unicode operators or macros are exported. The only unicode identifiers are keyword names (`∂`, `ϵ`) and field names (`Ω`). ASCII aliases for Lean: `∂ → bounds`, `ϵ → eps`, `Ω → grid/values`, `N → maxIter`, `n → width` (pixels).

### 2.2 Types

| name | file:line | definition / meaning |
|---|---|---|
| `abstract type ComplexBundle` | `src/Fatou.jl:27` | supertype of everything below. Dispatch only; drop it in Lean. |
| `struct Rectangle <: ComplexBundle` | `src/Fatou.jl:29-37` | `∂::Vector{Float64}` = bounds `[xa, xb, ya, yb]`; `n::UInt16` = number of **columns** (horizontal grid points). Constructor `Rectangle(∂=π/2, n=176)`. A non-Array `∂` becomes `[-float(∂), ∂, -∂, ∂]`. A length-2 `∂` becomes `[∂1, ∂2, ∂1, ∂2]`, so a 2-vector means a **square with the same interval on both axes**, not `[xa, xb]` with default y. `n` is converted by `UInt16(n)` and throws `InexactError` if > 65535. |
| `struct ComplexRectangle <: ComplexBundle` | `src/Fatou.jl:39-42` | `∂::Rectangle`, `Ω::Matrix{ComplexF64}` (rows × cols). Holds either the input grid or the **final iterates** (see `FilledSet.set`). |
| `struct Define{FT,QT,CT,M,N,P,D,B} <: ComplexBundle` | `src/Fatou.jl:73-119` | fractal specification; field table in §3.2 |
| `struct FilledSet{FT,QT,CT,M,N,P,D,B} <: ComplexBundle` | `src/Fatou.jl:126-135` | result: `meta::Define`, `set::ComplexRectangle` (**final iterates**, not the input grid), `iter::Matrix{UInt16}`, `mix::Matrix{Float64}` |

### 2.3 Constructors / front-end functions

All three front-ends forward keywords to `Define`. The table lists every keyword with its default. **Defaults differ between front-ends.**

| kw | `Define` (`:93-112`) | `juliafill` (`:203-222`) | `mandelbrot` (`:250-271`) | `newton` (`:299-318`) | meaning |
|---|---|---|---|---|---|
| `E` (positional) | | | | | map expression in `z`, `c` (`Expr`/`Symbol`/number; String is broken, §4.11) |
| `Q` | `:(abs2(z))` | `:(abs2(z))` | `:(abs2(z))` | — (not accepted) | escape criterion `(z,c) ↦ Real` |
| `C` | `:((angle(z)/(2π))*n^p)` | same | **`:(exp(-abs(z))*n^p)`** | `:((angle(z)/(2π))*n^p)` | coloring `(z, n, p) ↦ Real` |
| `∂` | `π/2` | `π/2` | `π/2` | `π/2` | bounds |
| `n` | 176 | 176 | 176 | 176 | columns |
| `N` | 35 | 35 | 35 | 35 | max iterations (UInt16) |
| `ϵ` | 4 | 4 | 4 | **0.01** | threshold |
| `iter` | false | false | false | false | plot iteration count instead of `mix` |
| `p` | 0 | 0 | 0 | 0 | exponent in coloring |
| `newt` | false | false | false (forced true if `m ≠ 0`, `:269`) | **true** (hard-coded) | Newton mode |
| `m` | 0 | 0 | 0 | **1** | Newton multiplicity (any `Number`, complex allowed) |
| `mandel` | false | — (not passed ⇒ false) | **true** (hard-coded) | false | Mandelbrot mode |
| `seed` | `0.0+0.0im` | — | `0.0+0.0im` | `0.0+0.0im` | Mandelbrot start value |
| `x0` | `nothing` | `nothing` | `nothing` | `nothing` | cobweb start (orbit plot only) |
| `orbit` | 0 | 0 | 0 | 0 | cobweb length |
| `depth` | 1 | 1 | 1 | 1 | max composition power shown in orbit plot |
| `cmap` | `""` | `""` | `""` | `""` | colormap name (backend-resolved) |
| `plane` | false | false | false | false | map input disk → upper half-plane |
| `disk` | false | false | false | false | map output half-plane → disk |
| `B` | `im` | `im` | `im` | `im` | "imaginary unit" (Grassmann blade; type parameter) |

Notes:
* `juliafill` accepts `newt` and `m` (`:212-213`) although its docstring omits them. `juliafill(E, newt=true)` is Newton mode with `ϵ=4`.
* `newton` has no `Q` keyword. In Newton mode `Q` is always `abs(E)` (`:114`).
* The README keyword block (`README.md:31-48`) says `n` is "vertical grid points". **The code makes it horizontal (columns)**, and the docstring (`:54`) agrees with the code.

### 2.4 Functions

| signature | file:line | semantics |
|---|---|---|
| `Define(E; kw...)` | `src/Fatou.jl:93-118` | Builds the closures. Non-Newton: `F = genlatest(E,[:z,:c])`, `Q = genlatest(Q,[:z,:c])`. Newton: `F = genlatest(newton_raphson(E,m),[:z,:c])`, `Q = genlatest(:(abs($E)),[:z,:c])`. Always `C = genlatest(C,[:z,:n,:p])`. Stores `E` (parsed if String; broken). Type params: `M=mandel, N=newt, P=plane, D=disk, B=B`. Converts `N→UInt16`, `ϵ→float`, `p→float`. |
| `juliafill(E; ...)` | `:203-222` | `Define(E; ...)`, `mandel=false` |
| `mandelbrot(E; ...)` | `:250-271` | `m ≠ 0 && (newt = true)`, then `Define(...; mandel=true)` |
| `newton(E; ...)` | `:299-318` | `Define(...; newt=true)` |
| `fatou(K::Define, Z::ComplexRectangle)` | `:169` | compute `FilledSet(K, Z)`: iterate every entry of `Z.Ω` |
| `fatou(K::Define, Z::Rectangle=Rectangle(K))` | `:170` | `fatou(K, fatou(Z))` (build grid first) |
| `fatou(K::Define, Z::FilledSet)` | `:171` | **chaining**: iterate `K` starting from `Z`'s **final iterates** |
| `fatou(K::Define, Z::Define)` | `:172` | `fatou(K, fatou(Z))`: compute `Z` first, then continue with `K` |
| `fatou(K::FilledSet, Z=ComplexRectangle(K))` | `:173` | re-run `K.meta` from `K`'s final iterates (continue another `N` steps; counts restart at 0) |
| `fatou(K::Rectangle)` | `:174-177` | coordinate grid: `ComplexRectangle(K, x' .+ im*y)` with `x, y = ranges(K)` (exact semantics §4.2) |
| `(K::Define)(Z)`, `(K::FilledSet)(Z)` | `:156-157` | call syntax, same as `fatou(K, Z)` |
| `bounds(::Rectangle/ComplexRectangle/Define/FilledSet)` | `:44-45, 144-145` | `∂` vector |
| `Base.size(::Rectangle)` | `:46` | `(round(UInt16, (∂4-∂3)/(∂2-∂1)*n), n)`, i.e. `(rows, cols)` as UInt16. Rounding is **ties-to-even**. |
| `Base.size(::ComplexRectangle)` | `:47` | `size(R.Ω)` |
| `Rectangle(K::Define)` | `:137` | `K.Ω` |
| `Rectangle(K::FilledSet)` / `Rectangle(R::ComplexRectangle)` | `:138-139` | `R.∂` |
| `ComplexRectangle(K::FilledSet)` | `:141` | `K.set` |
| `ComplexRectangle(Ω::Matrix{ComplexF64})` | `:142` | wraps a user matrix with pixel bounds `Rectangle([0, ncols, 0, nrows], ncols)` |
| `ranges(::FilledSet/Define/Rectangle)` | `:147-154` | `x = range(∂1+0.0001, stop=∂2, length=cols)`, `y = range(∂4, stop=∂3, length=rows)`. **Note the `+0.0001` on the left edge** and that **y descends** (row 1 = top). |
| `basin(K::Define, j)` | `:335` | `K.newt ? nrset(K.E, K.m, j) : jset(K.E, j)` returns a `LaTeXString` (§5.4) |
| `plane(z::Complex)` | `:337` | `(2x/(x²+(1−y)²)) + i(1−x²−y²)/(x²+(1−y)²)` = Möbius `(z+i)/(1+iz)`: unit disk → upper half-plane (`0↦i`, `−i↦0`, `i↦∞`) |
| `disk(z::Complex)` | `:338` | `(2x/(x²+(1+y)²)) + i(x²+y²−1)/(x²+(1+y)²)` = `(z−i)/(1−iz)`, the inverse of `plane` (verified `disk(plane(0.3+0.4i)) = 0.29999999999999993+0.39999999999999997i`) |
| `orbit(K::Define{…,im}, z0::ComplexF64) :: (UInt16, ComplexF64)` | `:341-350` | **the per-pixel kernel** (§4.4) |
| `orbit(K::Define{…,B}, Z0::ComplexF64)` | `ext/GrassmannExt.jl:19-30` | kernel over Grassmann `Couple{V,B}` (broken return type, §4.10) |
| `Compute(K::Define, Z::ComplexRectangle) :: (Matrix{UInt16}, ComplexRectangle)` | `:357-364` | `@time @threads` over rows; per pixel `orbit(K, Z.Ω[j,k])`. **Prints a `@time` line to stdout on every call.** |
| `typeplot(K::FilledSet)` | `:367` | `"iter."` if `K.meta.iter`, else `"roots"` if `K.meta.m == 1`, else `"limit"` |
| `Base.String(K::FilledSet)` | `:369-372` | title text (§5.1) |
| `nonan(x)` | `:375` | `isnan(x) ? 0.0 : x` |
| `(C::ColorSchemes.ColorScheme)(K::FilledSet) :: Matrix{RGB{Float64}}` | `:376-390` | pixel colors (§4.8) |
| `__init__()` | `:396-405` | prints `"Fatou detected $(nthreads()) julia threads."`; on pre-1.9 Julia uses `Requires` |
| `Reduce.stop()` | `:407` | stops the REDUCE subprocess at module load (precompile hygiene) |
| `orbit(K::Define)` | `src/orbitplot.jl:17-21` | real cobweb plot. `bi = [∂1, ∂2]` or `[∂1, ∂2, x0]`. Calls backend `orbit(K.E, z->K.F(z,0), bi, K.orbit, K.depth, Int(K.Ω.n))`. **Needs a plotting backend.** Without one it throws `MethodError` (verified). |
| `real_orb(E, f, bi::Matrix{Float64}, orb=0, depth=1, incr=384)` | `src/orbitplot.jl:23-54` | orbit data (§4.9). Internal, not exported. |
| `orbit(E, f::Function, bi, orb=0, depth=1, incr=384)` | `ext/PyPlotExt.jl:42-73`, `ext/UnicodePlotsExt.jl:19-45`, `ext/MakieExt.jl:50-78` (dead) | backend cobweb renderers (§5.3) |

Internals (`src/internals.jl`):

| name | line | semantics |
|---|---|---|
| `rdpm(tex)` | `:6` | strip `"\\begin{displaymath}\n"` … `"\n\\end{displaymath}"` from REDUCE LaTeX output |
| `newton_raphson(F, m)` | `:9-12` | `factor(z − m*(f/df(f,z)))` in REDUCE, parsed back to a Julia `Expr` |
| `recomp(E, x, j)` | `:15` | `sub(z = (j>1 ? recomp(E,x,j−1) : x), c = 0, E)`. This is the `j`-fold composition `E∘…∘E` evaluated at `x`, **with `c := 0`**. |
| `nL(E,m,j)`, `jL(E,j)` | `:18-19` | LaTeX of `recomp(newton_raphson(E,m), :z, j)` / `recomp(E, :z, j)` |
| `ds, set0, setj(j), nsetstr, jsetstr, nset0, jset0` | `:22-28` | LaTeX template fragments (§5.4) |
| `nrset(f,m,j)`, `jset(f,j)` | `:29-32` | assemble `basin` strings |

Extensions (`Project.toml:13-25`):
* `GrassmannExt`: generalized kernel.
* `ImageInTerminalExt`: `Base.show(io, K::FilledSet; c="", bare=false)`.
* `PyPlotExt`: `PyPlot.plot(K; c="", bare=false)`, `PyPlot.imshow(K; cmap="", bare=false)`, `PyPlot.title(K)`, `Fatou.orbit(E, f, bi, orb, depth, incr)`.
* `UnicodePlotsExt`: `Fatou.orbit(...)`.
* `ext/MakieExt.jl` is **not a module** and is commented out in `Project.toml:15,22`, so it is dead code. It still documents the intended Makie API: `plot/heatmap/contour/contourf(K; bare)`, `heatmap!/contour!/contourf!(ax, K)`, `surface(K)`, `arrows(K)`, `orbit(...)`.

---

## 3. Data representations

### 3.1 `Rectangle` / grid

* `∂ = [xa, xb, ya, yb]` (Float64). There is **no validation**. Reversed bounds give a negative aspect ratio, and `round(UInt16, negative)` throws `InexactError`.
* `size = (rows, cols) = (round_ties_even(((yb−ya)/(xb−xa))*n) :: UInt16, n)`. The order of operations is exactly `((∂4−∂3)/(∂2−∂1))*Float64(n)`.
* Storage: Julia `Matrix` is **column-major** (`Ω[j,k]`, `j` = row index = y, `k` = column index = x).
  * Row `j=1` is the **top** (`imag = yb`) and row `rows` is the bottom (`imag = ya`).
  * Column `k=1` is the left edge (`real = xa + 0.0001`) and column `cols` is the right edge (`real = xb`).
  * PyPlot `imshow(M, extent=[xa,xb,ya,yb])` with default `origin='upper'` puts row 1 at the top, which is consistent.
  * **Lean convention recommendation:** store row-major (`idx = j*cols + k`, 0-based), row 0 = top. The oracle dumps row-major.
* Real parts are constant down each column and imaginary parts constant along each row (verified).

Sizes for all README examples (verified):

| example | ∂ | n | (rows, cols) |
|---|---|---|---|
| default | π/2 → [−π/2, π/2, −π/2, π/2] | 176 | (176, 176) |
| filled-julia | [−1.5, 1.5, −1, 1] | 1501 | (1001, 1501) |
| mandelbrot | [−1.91, 0.51, −1.21, 1.21] | 800 | (800, 800) |
| newton | π/2 | 800 | (800, 800) |
| generalized-newton | [−2π/3, −π/3, −π/6, π/6] | 500 | (500, 500) |
| orbit | [−1.25, 1.5] → [−1.25, 1.5, −1.25, 1.5] | 147 | (147, 147) |

### 3.2 `Define{FT,QT,CT,M,N,P,D,B}` fields (`src/Fatou.jl:74-92`)

| field | type | compile-time? | notes |
|---|---|---|---|
| `E` | Any | runtime | original expression (Expr) |
| `F` | `FT<:Function` | type of closure (but `genlatest` closures all share one type, see §8) | map `(z,c) ↦ z'` |
| `Q` | `QT` | same | escape functional `(z,c) ↦ Float64` |
| `C` | `CT` | same | coloring `(z, n, p) ↦ Float64` |
| `Ω` | `Rectangle` | runtime | bounds + width |
| `N` | UInt16 | runtime | max iterations |
| `ϵ` | Float64 | runtime | threshold |
| `iter` | Bool | runtime | plot mode |
| `p` | Float64 | runtime | coloring exponent |
| `newt` | Bool | **also type param `N`** | Newton mode |
| `m` | Number (abstract!) | runtime | multiplicity; used only symbolically and in titles |
| `mandel` | Bool | **also type param `M`** | Mandelbrot mode |
| `seed` | Number (abstract) | runtime | Mandelbrot start |
| `x0` | Any (`nothing` or Real) | runtime | orbit start |
| `orbit` | Int | runtime | cobweb steps |
| `depth` | Int | runtime | composition depth |
| `cmap` | String | runtime | colormap name |
| `plane` | Bool | **also type param `P`** | disk → half-plane on input |
| `disk` | Bool | **also type param `D`** | half-plane → disk on output |
| (B) | — | **type param only** | unit blade; `im` for ordinary complex |

`FilledSet` fields (`:126-130`):
* `meta` is the Define.
* `set` is a `ComplexRectangle(Rectangle(Z), matF)` where `matF` holds the **final iterates** (after the `disk` map if `D`).
* `iter` is a `Matrix{UInt16}` in `[0, N]`.
* `mix = C.(matF, float.(iter ./ N), p)` (`:133`). Note `iter ./ N` is UInt16/UInt16, which Julia promotes to Float64 division.

Invariants:
* `0 ≤ iter[j,k] ≤ N`, because the loop guard is `K.N > zn` (`:344`).
* `size(iter) == size(mix) == size(set.Ω) == size(input grid)`.
* `mix` can be `NaN` (Newton singularities, overflow of `exp`). Verified: the wiki's `newton(:(exp(z)+1),…)` at 64×64 gives 1306 NaNs.

### 3.3 Orbit-plot data (`real_orb`)

* `x`: a length-`incr` range over `[bi1, bi2]`.
* `N`: an `incr × (depth+1)` Float64 matrix. Column 1 is `x`, and column `t+1` is `f` applied to column `t`.
* `N2`: the `orb+1` orbit values.
* `orbit`: a `(3·orb) × 2` cobweb polyline.
* `bis`: a 3-vector `[bi1, bi2, x0 or 0]`.

---

## 4. Algorithms

### 4.1 Pipeline

```
Define(E; kw)            -- symbolic prep: Newton map via CAS (if newt), compile F, Q, C
  └─ fatou(K)            -- = fatou(K, fatou(Rectangle(K)))
       ├─ grid = x' .+ im*y   (§4.2, exact Julia range semantics)
       ├─ Compute: for each pixel z0: (zn, zf) = orbit(K, z0)     (§4.4)  [@threads over rows]
       └─ FilledSet(meta=K, set=zf-matrix, iter=zn-matrix, mix = C.(zf, zn/N, p))
```

### 4.2 Grid axes: exact Julia semantics (needed for bit-exact goldens)

`fatou(R::Rectangle)` evaluates `x' .+ im*y` where `x = range(xa+0.0001, stop=xb, length=cols)` and `y = range(yb, stop=ya, length=rows)`.

* **Real part of column k** = `x[k]`, Julia's `StepRangeLen{Float64,TwicePrecision}` getindex.
* **Imaginary part of row j** is **not** `y[j]`. `im*y` builds a `StepRangeLen{ComplexF64,TwicePrecision{ComplexF64}}`. The multiplication by `im` re-canonicalizes `ref` and `step` (`hi+lo` merged, so the bit-truncation of `step.hi` is lost), and indexing then rounds differently. Example: `rows=10, [yb,ya]=[2,−2]` gives `imag(Ω[1,1]) = 2.0000000000000004` while `y[1] = 2.0` (verified, `t3.jl`). Over README grids, 37 to 298 rows differ by 1 ulp from `y` (`t4.jl`).
* A naive `a + i*(b−a)/(n−1)` differs from Julia by up to 17197 ulp on the x axis (filled-julia, because `−1.4999` is a decimal whose rational form Julia recovers).

**Verified algorithm** (full source: `scratchpad/fatou/jrange.jl`, 0 mismatches in 4000 random ranges + 300 random Fatou grids). Primitives:

```
canonicalize2(big, little): h = big+little; return (h, (big−h)+little)
add12(x, y): if |y| > |x| swap; return canonicalize2(x, y)
mul12(x, y): p = x*y; return (p, fma(x, y, −p))          -- exact product error; Lean: extern fma or Veltkamp/Dekker split
truncbits(x, nb) = bits(x) & (0xFFFF_FFFF_FFFF_FFFF << nb)
top_set_bit(v) = v ≤ 0 ? 0 : 64 − clz(v)
nbitslen(len, off) = len < 2 ? 0 : min(27, top_set_bit(max(off−1, len−off) − 1) + 1)
tp_div((xh,xl),(yh,yl)):  hi = xh/yh; (uh,ul) = mul12(hi, yh)
                           lo = ((((xh−uh)−ul)+xl) − hi*yl)/yh
                           return (hi==0 || !finite(hi)) ? (hi,hi) : canonicalize2(hi, lo)
tp_int(i::Int128):  hi = truncbits(Float64(i), 27); return canonicalize2(hi, Float64(i − Int128(hi)))
tp_rat(n, d) = tp_div(tp_int(n), (Float64(d), 0.0))
tp_trunc((h,l), nb): t = truncbits(h, nb); return (t, (h−t)+l)
rat(x):  -- continued fraction, m = 16777216 (= maxintfloat(Float32))
  y=x; a=d=1; b=c=0
  while |y| ≤ m:
     f = trunc(y); y −= f; (a,c) = (f*a+c, a); (b,d) = (f*b+d, b)
     if max(|a|,|b|) > m: return (c, d)
     if Float64(a)/Float64(b) == x: break
     y = 1/y
  return (a, b)
```

`jrange(start, stop, len)` for `len ≥ 2` returns `(ref_hi, ref_lo, step_hi, step_lo, offset)`:

```
if start == stop: return (start, 0, 0, 0, 1)
(sn,sd) = rat(start); (en,ed) = rat(stop)
if sd≠0 && ed≠0:
   den = sd * (ed ÷ gcd(sd,ed));  M = 2^53
   if den≠0 && |den*start| ≤ M && |den*stop| ≤ M:           -- Float64 products
      sn2 = round_ties_even(den*start); en2 = round_ties_even(den*stop)
      if Float64(sn2)/Float64(den) == start && Float64(en2)/Float64(den) == stop:
         -- rational path
         tmin = −sn2 / (Float64(en2) − Float64(sn2))
         imin = clamp(round_ties_even(tmin*(len−1)+1), 1, len)
         ref_num = Int128(len−imin)*sn2 + Int128(imin−1)*en2;  ref_den = Int128(len−1)*den
         (rh, rl) = tp_rat(ref_num, ref_den)
         (sh, sl) = tp_trunc(tp_rat(en2 − sn2, ref_den), nbitslen(len, imin))
         return (rh, rl, sh, sl, imin)
-- float path
Δ, Δfac = stop−start, 1;  if !finite(Δ): Δ, Δfac = stop/len − start/len, len
tmin = −(start/Δ)/Δfac;  imin = round_ties_even(tmin*(len−1) + 1)
if 1 < imin < len: t = (imin−1)/(len−1); ref = (1−t)*start + t*stop
                   step = imin−1 < len−imin ? (ref−start)/(imin−1) : (stop−ref)/(len−imin)
elif imin ≤ 1: imin=1; ref=start; step=(Δ/(len−1))*Δfac
else:          imin=len; ref=stop; step=(Δ/(len−1))*Δfac
m = prevfloat(floatmax); k = max(imin−1, len−imin)
step_hi = truncbits(clamp(step, max(−(m+ref)/k, (−m+ref)/k), min((m−ref)/k, (m+ref)/k)), nbitslen(len, imin))
(x1h,x1l) = add12((1−imin)*step_hi, ref);  (x2h,x2l) = add12((len−imin)*step_hi, ref)
a = (start−x1h)−x1l;  b = (stop−x2h)−x2l
step_lo = (b−a)/(len−1);  ref_lo = a − (1−imin)*step_lo
return (ref, ref_lo, step_hi, 0.0+step_lo, imin)
```

Indexing (`Base.unsafe_getindex`, `base/twiceprecision.jl:478-484`):

```
getidx((rh,rl,sh,sl,off), i):  u = i − off;  (xh, xl) = add12(rh, u*sh);  return xh + (xl + (u*sl + rl))
```

Fatou axes:

```
xr = jrange(xa + 0.0001, xb, cols);   gx[k] = getidx(xr, k)                       k = 1..cols
yr = jrange(yb, ya, rows)
yc = (canonicalize2(yr.ref_hi, yr.ref_lo)..., canonicalize2(yr.step_hi, yr.step_lo)..., yr.offset)   -- the `im*` quirk
gy[j] = getidx(yc, j)                                                               j = 1..rows
grid[j,k] = gx[k] + i·gy[j]
```

Edge notes:
* The `len < 2` path (`_linspace1`) never runs because Rectangle forces `n ≥ 1` and rows can be 1 (`rows=1` gives a `range(yb, stop=ya, length=1)`, which throws unless `yb == ya`). Treat `rows < 2` or `cols < 2` as an error in Lean.
* `round_ties_even` is required. Lean's `Float.round` is half-away-from-zero. Implement `rte x := let r := x.round; if (r − x).abs == 0.5 then 2 * (x/2).round else r`, which is exact.

### 4.3 Expression compilation (Julia: `SyntaxTree.genlatest`)

`genlatest(expr, [:z,:c])` does `eval(:(function g(z,c) expr end))` and returns `(a,b)->Base.invokelatest(g,a,b)` (`~/.julia/packages/SyntaxTree/Adq4Y/src/SyntaxTree.jl:172-191`). Consequences:
* The function body is **ordinary Julia semantics** of the expression. Julia's parsing and lowering rules therefore matter for bit-exactness:
  * `z^2` with a literal integer exponent lowers to `Base.literal_pow(^, z, Val(2))` = `z*z`.
  * `z^3` → `(z*z)*z`.
  * `z^0` → `one(z)`, `z^1` → `z`, `z^-1` → `inv(z)`, `z^-2` → `(i=inv(z); i*i)`.
  * `z^n` for other literal n ≥ 4 → `power_by_squaring(z, n)` (§4.6).
  * `a-b+c` parses as `(a-b)+c`.
  * `2z` is `2*z`.
  * `0.67im` is `ComplexF64(0.0, 0.67)`.
  * `ℯ^z` → `exp(z)`.
  * `%` is `rem` (real-only).
* **Every call goes through `invokelatest`** (dynamic dispatch, boxing), which is Fatou 1.2.4's world-age fix. This is why it is slow (§8.3).
* If `E` is a `String`, `genlatest` compiles a function **returning the string literal**. `Define` then fails at `parse(E)` (`:116`, `MethodError: no method matching parse(::String)` on Julia ≥ 0.7). String input is broken; see §4.11.

### 4.4 The per-pixel kernel `orbit(K, z0)` (`src/Fatou.jl:341-350`)

```
function orbit(K, z0):                           # M=mandel, N=newt, P=plane, D=disk (compile-time flags)
    z  = M ? K.seed : (P ? plane(z0) : z0)       # Mandelbrot ignores `plane` for the start value
    c  = z0                                      # ALWAYS the raw pixel (never plane-mapped), in every mode
    zn = 0 :: UInt16
    while (N ? Q(z,c) > ϵ : Q(z,c) < ϵ) && zn < K.N:     # strict comparisons; NaN ⇒ false ⇒ stop
        z  = F(z, c)
        zn += 1
    return (zn, D ? disk(z) : z)
```

Exact behavior points:
* **The test happens before each step.** If `Q(z0) ≥ ϵ` (Julia mode), `zn = 0` and `z = z0`.
* **Strict `<` / `>`**: `abs2(z) == 4` counts as escaped. Golden: `mandelbrot(:(z^2+c), N=20)` at `c=−2` gives `(1, −2+0i)`.
* In Julia mode `c` is the pixel too, so `juliafill(:(z^2+c))` iterates `z ↦ z²+z0`, which is a Mandelbrot-like picture with `z` starting at the pixel.
* Newton mode: `F` = CAS Newton map, `Q = |f(z)|` (the original function, via `hypot`), and it iterates **while** `|f(z)| > ϵ`. `ϵ = 0` means "never converge" (the wiki uses `ϵ=0` to get the full `N` iterations).
* Newton + Mandelbrot (`mandelbrot(E, m≠0)`): start at `seed`, `c = pixel`, and differentiate w.r.t. `z` only (`c` is a REDUCE constant).
* NaN handling: e.g. Newton `z^3−1` at `z0 = 0` gives `F(0) = 1/(0+0i)` → complex division yields `NaN+NaN·i`, then `Q = hypot(NaN,NaN) = NaN`, `NaN > ϵ` is false, so it stops with `(1, NaN+NaN·i)` and `mix = NaN`. **The `+0.0001` x-offset in `ranges` exists so the default symmetric grids never hit `z0 = 0` exactly.**
* `Q(...)::Float64` is type-asserted. A complex-valued `Q` would error.

Verified per-point goldens (`t15.jl`, full precision):

| K | z0 | (zn, z_final) | C value |
|---|---|---|---|
| mandelbrot `z^2+c`, N=20 | 0 | (20, 0+0i) | 1.0 |
| same | −1 | (20, 0+0i) | 1.0 |
| same | 1+1i | (2, 1.0+3.0i) | 0.04232921962320499 |
| same | 0.3+0.5i | (20, −0.1050085983962668+0.0018976393931155466i) | 0.9003013454887451 |
| same | −0.75+0.1i | (20, −0.46399822512713945−0.2222609679149343i) | 0.5978086913652962 |
| same | 0.25 | (20, 0.4599437228607871+0i) | 0.6313191733442202 |
| same | −2 | (1, −2+0i) | 0.1353352832366127 |
| juliafill `z^2+(−0.06+0.67i)`, N=80, iter | 0 | (54, 0.26568170827230425−2.075025126211045i) | −0.22973242029832544 |
| same | 0.5+0.5i | (4, 2.0944355506368244−2.169796784187192i) | −0.12781243220832691 |
| same | 1 | (3, −3.6429560700000008+2.1160422399999996i) | 0.41624853071302825 |
| same | −0.2−0.3i | (80, −0.47364177907317057+0.5087937401374358i) | 0.3693077966876138 |
| newton `z^3−1`, ϵ=0.1, N=25 | 2.1 | (3, 1.015805042940846+0i) | 0.0 |
| same | 0 | (1, NaN+NaN·i) | NaN |
| same | 1 | (0, 1+0i) | 0.0 |
| same | −1 | (6, 1.0065370824568558+0i) | 0.0 |
| same | 0.3+0.7i | (9, 1.0043627160990787−0.01569546754535097i) | −0.0024869580336499713 |
| newton `sin(z)−1`, m=1−i, ϵ=0.05, N=33 | −1.5+0.1i | (29, 14.07759963533618−0.22485779781234527i) | −0.0025419239047796633 |
| same | −2 | (9, −11.024900014979625−0.2728938570133225i) | −0.49606132125134633 |
| same | −1.2−0.3i | (9, 7.962999227413278+0.1952348929545369i) | 0.0039013408779779452 |
| juliafill `z^2+c₀`, plane=true (defaults) | 0 | (35, −0.058037613098142204+0.6513116845938646i) | 0.264144749260282 |
| same | 0.3+0.4i | (0, 1.3333333333333335+1.6666666666666667i) | 0.14261164373863863 |
| juliafill `z^2+c₀`, disk=true | 0 | (35, −0.3212586195350736−0.15340922030351722i) | −0.42909535960778944 |
| same | 0.3+0.4i | (10, 0.5742411074378835+0.6676970859534406i) | 0.13695389673709749 |

Real Newton sequence (the wiki claim): `F = newton_raphson(z^3−1, 1)` from 2.1 gives `[2.1, 1.4755857898715043, 1.1368149152160596, 1.015805042940846, 1.0002446373252254]`.

### 4.5 Newton map construction (REDUCE; `src/internals.jl:9-12`)

`newton_raphson(F, m) = parse(factor(z − m*(f / df(f, z))))`. Here `df` is REDUCE's derivative, and `factor(x)` means "evaluate `x` with the REDUCE `factor` switch on". The result is a single rational expression over a common denominator, with numerator and denominator factored over ℤ[i]. Verified outputs (`string(Expr)`):

| E, m | Newton map Expr |
|---|---|
| `z^3-1`, 1 | `(2 * z ^ 3 + 1) / (3 * z ^ 2)` |
| `z^3-1`, 2 | `(z ^ 3 + 2) / (3 * z ^ 2)` |
| `z^3-1`, −0.5 | `(7 * z ^ 3 - 1) / (6 * z ^ 2)` |
| `z^4-1`, 1 | `(3 * z ^ 4 + 1) / (4 * z ^ 3)` |
| `z^3-2z+2`, 1 | `(2 * (z ^ 2 + z + 1) * (z - 1)) / (3 * z ^ 2 - 2)` |
| `z^3-2z-5`, 1 | `(2 * z ^ 3 + 5) / (3 * z ^ 2 - 2)` |
| `sin(z)-1`, 1−1im | `((sin(z) - 1) * (im - 1) + cos(z) * z) / cos(z)` |
| `z^2-1`, 1+1im | `(1 - ((im * z ^ 2 - im) - z ^ 2)) / (2z)` |
| `z^2-im`, −0.5+2im | `((4im - 1) * (im - z ^ 2) + 4 * z ^ 2) / (4z)` |
| `z^8-15z^4-16`, 1.5 | `((13 * z ^ 8 - 75 * z ^ 4) + 48) / (8 * (2 * z ^ 4 - 15) * z ^ 3)` |
| `z^8-15z^4-16`, −0.5+2im | `-(((((4 * im * z ^ 8 - 60 * im * z ^ 4) - 64im) - 17 * z ^ 8) + 135 * z ^ 4 + 16)) / (8 * (2 * z ^ 4 - 15) * z ^ 3)` |
| `sin(z)`, 1 | `(cos(z) * z - sin(z)) / cos(z)` |
| `z^6+z^3-1`, 1−0.4im | `((2im - 5) * ((z ^ 6 + z ^ 3) - 1) + 15 * (2 * z ^ 3 + 1) * z ^ 3) / (15 * (2 * z ^ 3 + 1) * z ^ 2)` |
| `cos(z)-1`, −0.5+2im | `((cos(z) - 1) * (4im - 1) + 2 * sin(z) * z) / (2 * sin(z))` |
| `cos(z)-1`, 1 | `((sin(z) * z - 1) + cos(z)) / sin(z)` |
| `z^5-3im*z^3-(5+2im)z^2+3z+1`, 1−0.24im | `((((((6 * im * z ^ 5 - 150 * im * z ^ 3) - 80 * im * z ^ 2) + 18 * im * z + 6im + 100 * z ^ 5 + 18 * z ^ 3) - 113 * z ^ 2) - 25) / (25 * (((5 * z ^ 4 - 10z) + 3) - (9z + 4) * im * z))` |
| `log(z)`, 1+1im | `(1 - (im + 1) * log(z)) * z` |
| `z^(4.0+3.0im)-1`, 2.1 | `(z ^ (3im) * (30im + 19) * z ^ 4 + 21) / (10 * z ^ (3im) * (3im + 4) * z ^ 3)` |
| `exp(z)+1`, 1 | `(ℯ ^ z * (z - 1) - 1) / ℯ ^ z` |
| `z^2-z-4`, 1 | `(z ^ 2 + 4) / (2z - 1)` |

Observations:
* REDUCE rationalizes floats: `m=1.5` becomes `3/2`, and `−0.4im` becomes `2/5`. The float `m` therefore never appears in `F`; only small integers and `im` do. `im` is Julia's `Complex{Bool}`, and `im - 1` evaluates to `Complex{Int}(-1,1)`.
* The Lean port **cannot and should not** reproduce REDUCE's canonical forms in general (§8.5). For bit-exact goldens the oracle dumps this string and the Lean test parses and evaluates it.

### 4.6 Julia complex arithmetic that `F`/`Q`/`C` rely on (bit-exact spec)

All definitions are in `$(JULIA)/share/julia/base/complex.jl` (Julia 1.13). **No FMA contraction**: I inspected the native code of `z*z+c` on aarch64, and it uses `fmul/fsub/fadd`, with no `fmadd`.

* `z*w = (zr*wr − zi*wi) + i(zr*wi + zi*wr)` (`complex.jl:290`).
* `z±w` componentwise.
* `x+z` (real + complex) = `Complex(x + zr, zi)`.
* `z−x` = `Complex(zr − x, zi)`.
* `x*z` = `Complex(x*zr, x*zi)`.
* `z/x` = `Complex(zr/x, zi/x)`.
* `x/z` = `x*inv(z)`.
* `abs2(z) = zr*zr + zi*zi` (`:278`).
* `abs(z) = hypot(zr, zi)` (`:277`). Julia's own `_hypot` (`base/math.jl:748-801`):
  ```
  ax=|x|, ay=|y|; if isinf(ax)||isinf(ay) return Inf; if ay>ax swap
  if ay ≤ ax*sqrt(eps/2) return ax                   # also covers ay == 0
  scale: if ax > sqrt(floatmax/2): ax,ay *= s; s=1/s   (s = eps*sqrt(floatmin))
         elif ay < sqrt(floatmin): ax,ay /= s          else s = 1
  h = sqrt(fma(ax,ax, ay*ay))                          # muladd fuses on aarch64
  hsq = h*h; axsq = ax*ax
  h -= (fma(−ay,ay, hsq−axsq) + fma(h,h,−hsq) − fma(ax,ax,−axsq))/(2h)   # have_fma branch ⇒ correctly rounded
  return h*s
  ```
  Because the result is correctly rounded, **any correctly-rounded hypot matches**.
* `angle(z) = atan(zi, zr)` (`:641`). Julia's own atan2 is an openlibm port and may differ from libm by 1 ulp.
* `z/w` for ComplexF64 (`:390-464`) is the robust Baudin–Smith division:
  ```
  a,b = z; c,d = w; ab = max(|a|,|b|); cd = max(|c|,|d|)
  if isinf(c)|isinf(d): return isfinite(z) ? complex(0.0*sign(a)*sign(c), −0.0*sign(b)*sign(d)) : NaN+NaN·i
  halfov = 0.5*floatmax; twounϵ = floatmin*2/eps
  if ab≥halfov || ab≤twounϵ || cd≥halfov || cd≤twounϵ:    # scaling_cdiv
      s=1; if ab≥halfov: a,b*=0.5; s*=2   elif ab≤twounϵ: a,b*=bs; s/=bs      (bs = 2/eps²)
           if cd≥halfov: c,d*=0.5; s*=0.5 elif cd≤twounϵ: c,d*=bs; s*=bs
      (p,q) = cdiv(a,b,c,d); return (p*s, q*s)
  return cdiv(a,b,c,d)
  cdiv: if |d| ≤ |c|: robust_cdiv1(a,b,c,d) else (p,q)=robust_cdiv1(b,a,d,c); q=−q
  robust_cdiv1(a,b,c,d): r=d/c; t=1/(c+d*r); p=cdiv2(a,b,c,d,r,t); q=cdiv2(b,−a,c,d,r,t)
  cdiv2(a,b,c,d,r,t): if r≠0: br=b*r; return br≠0 ? (a+br)*t : a*t+(b*t)*r
                      else: return (a + d*(b/c))*t
  ```
  Division by `0+0i` gives `cd=0 ≤ twounϵ` → scaling → `r = 0/0 = NaN` → `NaN+NaN·i`.
* `z^n` for integer `n` not handled by `literal_pow`: `n ≥ 0 ? power_by_squaring(z,n) : power_by_squaring(inv(z),−n)` (`:874-875`). `power_by_squaring` (`base/intfuncs.jl:394-438`):
  ```
  p==1: z; p==0: 1; p==2: z*z
  t = trailing_zeros(p)+1; p >>= t; x = z
  (square once reused) if (t−=1)>0: x = z*z;  while (t−=1)>0: x = x*x
  y = x
  while p>0: t = trailing_zeros(p)+1; p >>= t; repeat t times: x = x*x; y = y*x
  return y
  ```
  (Exact order matters for bit-exactness. Transliterate.)
* `sin(z) = sin(zr)cosh(zi) + i cos(zr)sinh(zi)` with `zr==0` / non-finite special cases (`:887-903`).
* `cos(z) = cos(zr)cosh(zi) − i sin(zr)sinh(zi)` (`:905-923`).
* `exp(z) = e^zr (cos zi + i sin zi)` with the `zi==0` short-cut `Complex(e^zr, zi)` (`:694-714`).
* `log(z)` (`:643`), `sqrt(z)` (`:523`), and `z^w` complex (`_cpow`) are only needed for wiki examples (tolerance tier).

### 4.7 Coloring (`mix`)

* `mix[j,k] = C(zf[j,k], iter[j,k]/N, p)`.
* Defaults:
  * `angle(z)/(2π) * n^p`, with range `(−0.5, 0.5]`.
  * Mandelbrot: `exp(−abs(z)) * n^p`, with range `(0, 1]`.
* Julia `0^0 = 1`, so with `p = 0` the factor is 1 even for `iter = 0`.
* With `p > 0`, pixels with `iter = 0` get `mix = 0` (or `NaN` if the first factor is NaN).
* User `C` is an expression in `z, n, p`. The wiki example (11) uses `C="(-angle(z)/(2π))*n^e"`, which is broken (string, and the undefined `e`).

### 4.8 Colormap semantics: three different backends

1. **`(C::ColorScheme)(K)`** (`src/Fatou.jl:376-390`), used by the ImageInTerminal display:
   * `iter` mode: `M = length(C)/(maximum(iter)+1)`, and `H[x,y] = C[ceil(Int, M*(iter[x,y]+1))]`, an integer index into the stop array. There is no interpolation, and the maximum iteration maps to the last color.
   * `mix` mode: `H = get(C, nonan(mix))` with ColorSchemes' default `rangescale = (0,1)` (`~/.julia/packages/ColorSchemes/3BWhh/src/ColorSchemes.jl:317-331`):
     ```
     x = clamp(v, 0, 1); f = x*(L−1)+1; b = floor(f); a = min(b+1, L); t = f−b
     color = (1−t)*colors[b] + t*colors[a]         # computed as w*c1 + (1−w)*c2 with w = 1−t
     ```
     **Negative `mix` (half of all angle values) clamps to the first color.** This is a Julia quirk; keep it for parity mode.
   * The default scheme when `cmap == ""` is `:balance` (`ext/ImageInTerminalExt.jl:22`). Scheme lengths (ColorSchemes 3.31): balance 256, gnuplot 100, gist_earth 101, jet **9**, cubehelix 256, nipy_spectral 101, brg 100, RdGy 11, hsv 101, ocean 100, YlGnBu 9, gist_stern 101, terrain 101, viridis 256.
2. **PyPlot `imshow`** (`ext/PyPlotExt.jl:21-28`). All README/wiki images use this path.
   * matplotlib auto-normalization `Normalize(vmin=min(data), vmax=max(data))`, then a 256-entry LUT: `idx = clip(floor(x*256), 0, 255)`.
   * NaN is the "bad" color, which defaults to transparent `(0,0,0,0)` and shows as white.
   * The default cmap when `cmap == ""` is `viridis`.
   * `origin='upper'`, `extent = bounds(K)`, and the default interpolation is `'auto'` (antialiased resampling when downscaling).
   * matplotlib 3.11 LUTs are reproducible with `uv run --with matplotlib python` (verified available). Use that as the colormap oracle for LeanPlot.
3. **Makie** (dead ext): `heatmap(r1, r2, reverse(transpose(Z), dims=2))`, `colormap = Symbol(cmap)`.

### 4.9 Real orbit / cobweb data (`src/orbitplot.jl:23-54`)

```
real_orb(E, f, bi, orb=0, depth=1, incr=384):
  N = zeros(incr, depth+1); bis = zeros(3); bis[1:length(bi)] = bi
  x = range(bi[1], stop=bi[2], length=incr)        # plain Julia range, NO +0.0001 here
  N[:,1] = x;  for t in 1:depth: N[:,t+1] = f.(N[:,t])
  N2 = zeros(orb+1); N2[1] = bis[3]                 # x0, or 0.0 if x0 == nothing
  for t in 1:orb: N2[t+1] = f(N2[t])
  siz = 3*orb; orbit = zeros(siz, 2)
  for k in 0:orb−1:                                 # rows 3k+1, 3k+2, 3k+3 (1-based)
     orbit[3k+1,:] = (N2[k], N2[k])                 # on the diagonal
     orbit[3k+2,:] = (N2[k], N2[k+1])               # vertical to the graph
     orbit[3k+3,:] = (N2[k+1], N2[k+1])             # horizontal back to the diagonal
  return x, N, N2, orbit, bis
```

Other details:
* `f = z -> K.F(z, 0)` (`src/orbitplot.jl:20`) is called on **real Float64** values, so real arithmetic applies (e.g. `x^2 − 0.67`).
* `incr = Int(K.Ω.n)`, so the README uses 147 samples and the default is 176. The `real_orb` default of 384 is only used when calling the backend directly.
* Y-limits used by every backend: `ylim = (min(1.07*min(N[:,2]), 0), max(1.07*max(N[:,2]), 0))`, and xlim `= (bi1, bi2)`.

Golden, README orbit `juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147)` (`t12.jl`):
* `x[1:3] = −1.25, −1.231164383561644, −1.2123287671232876` (step 0.018835616438356163), `x[end] = 1.5`.
* `N[1,:] = [−1.25, 0.8925, 0.12655624999999993, −0.6539835155859376]`.
* `N2 = [1.25, 0.8925, 0.12655624999999993, −0.6539835155859376, −0.24230556134185777, −0.6112880149428073, −0.29632696278728227, −0.5821903311252646, −0.33105441834425475, −0.5604029720947472, −0.355948508867374, −0.5433006590350931, −0.3748243938920336, −0.5295066737434697, −0.38962268246112675, −0.5181941653117961, −0.401474807036811, −0.5088179793147554]`.
* `orbit` is 51×2. Rows 1..7 are `(1.25,1.25),(1.25,0.8925),(0.8925,0.8925),(0.8925,0.8925),(0.8925,0.12655624999999993),(0.12655624999999993,0.12655624999999993),(0.12655624999999993,0.12655624999999993)`.
* `ylim = (−0.7168498029649091, 1.6906)`. `min N[:,2] = −0.6699530868830925` at `x = −0.00684931506849315`.
* Without `x0`: `N2 = [0.0]`, `orbit` is 0×2, `bis = [−1.25, 1.5, 0.0]`, `N` is 176×2.

### 4.10 Generalized units via Grassmann (`ext/GrassmannExt.jl:19-30`)

For `B ≠ im` (e.g. `B = Λ(S"+-").v12`), the kernel lifts:
* `z0 = Couple{V,B}(Z0)`, meaning `a + b·B`;
* `z = Couple(seed)` or `Couple(plane(Z0))` or `z0`;
* the loop uses `value(Q(z,z0))`.

Couple semantics:
* `B² = s`: `S"++"` and `S"--"` give `v12² = −1` (complex); `S"+-"` and `S"-+"` give `v12² = +1` (split-complex).
* `(a+bB)(c+dB) = (ac + s·bd) + (ad+bc)B`.
* `abs2 = a² + b²·abs2_inv(B)`, where `abs2_inv(v12) = −s`. The complex case gives `a²+b²` and the split case gives `a² − b²`, which **can be negative**.

**Bug:** the final `Grassmann.value(z)` returns `Values{2,Float64}`, but it is type-asserted as `ComplexF64`, so every `fatou` with `B≠im` throws `TypeError` (verified). The intended semantics are `Complex(value(z)...)`. With that monkey-patch (`t8.jl`), `mandelbrot(:(z^2+c), B=Λ(S"++").v12, n=40, N=20)` reproduces the complex histogram exactly, and `S"+-"` gives the hyperbolic Mandelbrot histogram `[0,0,184,194,116,80,94,52,39,7,202,135,52,35,15,11,3,0,0,9,372]`. Dual numbers (`s=0`) are not reachable through Grassmann signature strings (`"0+"` parses as `⟨++⟩`).

### 4.11 String input (broken in Julia 1.x)

Docstrings and the wiki use strings (`juliafill("z^2-0.06+0.67im", …)`, `newton("z^3-1", …)`). `Define` calls `parse(E)` (`:116`), which does not exist on String in Julia ≥ 0.7 (verified `MethodError`). The Lean port should accept strings through its own parser, which is an improvement. **For oracle runs, convert with `Meta.parse`.** Additional wiki breakages:
* the undefined `e` in `e^z` (use `exp`);
* `C="..."` strings;
* the old orbit signature `orbit(z->nf.F(z,0), [-π 2π -1], 17, 3, 147)`, which is now `orbit(E, f, bi, orb, depth, incr)`.

---

## 5. Display / printing

### 5.1 `String(K::FilledSet)` (`src/Fatou.jl:369-372`)

```
text = "f : z ↦ $(K.meta.E),"          # Julia Expr printing
t    = typeplot(K)                      # "iter." | "roots" | "limit"
newt ? "$text m = $(K.meta.m), $t" : "$text $t"
```

Verified strings:
* `"f : z ↦ z ^ 3 - 1, m = 1, roots"`
* `"f : z ↦ z ^ 3 - 1, m = 1, iter."`
* `"f : z ↦ z ^ 2 + c, limit"`
* `"f : z ↦ z ^ 2 + c, iter."`
* `"f : z ↦ (z ^ 2 - 0.06) + 0.67im, limit"` for `:(z^2-0.06+0.67im)`
* `"f : z ↦ z ^ 2 + (-0.06 + 0.67im), iter."` for `:(z^2+$c)`
* `"f : z ↦ sin(z) - 1, m = 1 - 1im, limit"`
* `"f : z ↦ z ^ 3 - 1, m = -0.5, limit"`
* `"f : z ↦ z ^ 2 - im, m = -0.5 + 2.0im, limit"`
* `"f : z ↦ (z ^ 3 - 2z) - 5, m = 1, roots"`
* `"f : z ↦ (z ^ 8 - 15 * z ^ 4) - 16, m = 1.5, limit"`
* `"f : z ↦ ((z ^ 5 - (3im) * z ^ 3) - (5 + 2im) * z ^ 2) + 3z + 1, m = 1.0 - 0.24im, iter."`
* `"f : z ↦ (-3 / 2) * z ^ 2 + (5z) / 2 + 1, iter."`
* `"f : z ↦ z ^ 2 + 1.0, limit"`
* `"f : z ↦ sqrt(z), limit"`
* `"f : z ↦ 3z + 2, limit"`

Julia `Expr` printing rules to replicate in a `toJuliaString`:
* spaces around binary operators, including `^`;
* left-nested `+`/`-` chains are parenthesized: `(a - b) + c`. `a + b + c` stays flat because it is n-ary;
* juxtaposed numeric coefficient forms (`2z`, `3im`) are preserved from the source;
* a Complex literal prints as `(-0.06 + 0.67im)` when it is an operand;
* `Complex{Int}` `m` prints as `1 - 1im`.

Julia's printing algorithm is intricate. The Lean port only needs a faithful printer for its own AST, and exact parity with Julia's `show(Expr)` is optional (tests can compare titles modulo whitespace and parentheses).

### 5.2 PyPlot figure contract (`ext/PyPlotExt.jl:19-40`)

* `plot(K; c="", bare=false)` → `imshow(K; cmap=c, bare)`.
* `imshow` does:
  * `figure()`;
  * `cmap = cmap=="" ? K.meta.cmap : cmap`;
  * `imshow(iter ? K.iter : K.mix, [cmap], extent=bounds(K))`;
  * `tight_layout()`;
  * if `!bare`, `title(K)`.
* `title(K)` does:
  * `"f:z\mapsto " * rdpm(latex(K.meta.E)) * ",\,"` followed by `typeplot`;
  * for Newton, the title is `"...,\, m = $(m), " * typeplot`, and the ylabel is `L"Fatou\,set:\," * L"z\,↦\,z-m\,×\,f(z)\,/\,f\,'(z)"`;
  * then `tight_layout(); colorbar()`.
  * **So `bare=true` also suppresses the colorbar.**
* Title LaTeX from current REDUCE (`t9.jl`):
  * `z^2+c` → `c+z^{2}` (REDUCE reorders);
  * `z^3-1` → `z^{3}-1`;
  * `sin(z)-1` → `\sin \,z-1`;
  * `z^2-0.67` → `\left(100 z^{2}-67\right)/100` (rationalized; the README orbit image was rendered by an older version and shows `x² − 0.67`);
  * `(z^2-0.06)+0.67im` → `\left(67 i+100 z^{2}-6\right)/100`.
  * **Recommendation:** the Lean LaTeX printer should print decimals verbatim (`z^{2}-0.67`), not REDUCE's rational form. Titles are cosmetic.

### 5.3 Orbit plot contract

PyPlot (`ext/PyPlotExt.jl:42-73`):
* `figure()`.
* Lines:
  * `plot(x, N[:,1], "k--")` for `y=x` (black dashed);
  * `plot(x, N[:,2])` for ϕ (default cycle C0 = `#1f77b4`);
  * the cobweb `plot(orbit[:,1], orbit[:,2], "r")`;
  * for `h ∈ 3:depth+1`, `plot(x, N[:,h], lw=1)`, which takes the next cycle colors: C1 `#ff7f0e`, C2 `#2ca02c`, C3 `#d62728`, C4 `#9467bd`, …;
  * if `orb≠0`: `plot(range(bi1,bi2,length=orb+1), N2, "gray", marker="x", linestyle=":", lw=1)`. This is the orbit as a time series on evenly spaced x.
* `xlim(bi1,bi2)`, and `ylim` as in §4.9.
* Title: `"$ x \mapsto $(rdpm(latex(E)))$" * (orb≠0 ? ", IC: $ x_0 = $(x0)$, $ n\in0:$orb$" : "")`.
* Legend: `["$y=x$", "$\phi(x)$", "(x_n,\phi(x_n))", "\phi^{2}(x)", …, "\phi^{depth}(x)", (orb≠0 ? "\phi(x_{0:$orb})" : nothing)]`.
* `tight_layout()`.

UnicodePlots (`ext/UnicodePlotsExt.jl:19-45`):
* `lineplot(x, N[:,1], xlim, ylim, color=:magenta, name="y=real(z)")`;
* `lineplot!(…, N[:,2], :blue, "ϕ(real(z))")`;
* `scatterplot!(orbit…, :red, "(zₙ,ϕ(zₙ))")`;
* for `h ∈ 3:depth+1`, `lineplot!(…, color = isodd(h) ? :yellow : :green, name = "ϕ^{h-1}(z)")`;
* if `orb≠0`, `lineplot!(range…, N2, :cyan, "ϕ(z_{0:$orb})")`;
* `title!("z ↦ $E" * (orb≠0 ? ", IC: z₀ = $(bis[3]), n∈0:$orb" : ""))`, where `$E` is Julia `Expr` printing.

Makie (dead code, `ext/MakieExt.jl:50-78`): same data, title `"x ↦ $E$funt"`, `tab10` colors.

### 5.4 `basin` LaTeX (`src/internals.jl:22-32`)

Templates (literal Julia strings; `\\` is one backslash):

```
set0    = "D_0(\epsilon) = \left\{ z\in\mathbb{C}: \left|\,z"
setj(j) = "\displaystyle D_$j(\epsilon) = \left\{z\in\mathbb{C}:\left|\,"
nsetstr = "- r_i\,\right|<\epsilon,\,\forall r_i(\,f(r_i)=0 )\right\}"
jsetstr = "\,\right|>\epsilon\right\}"
nrset(f,m,j) = latexstring(j==0 ? "$set0 $nsetstr" : "$(setj(j))$(nL(f,m,j)) $nsetstr")
jset(f,j)    = latexstring(j==0 ? "$set0 $jsetstr" : "$(setj(j))$(jL(f,j)) $jsetstr")
```

`latexstring` wraps the result in `$…$`. Current outputs (`t9.jl`, REDUCE 1.2.17 with the `rlfi` package loaded; REDUCE inserts hard `\n` line-wraps near 80 columns):

* `basin(newton(:(z^3-1)),0)` = `$D_0(\epsilon) = \left\{ z\in\mathbb{C}: \left|\,z - r_i\,\right|<\epsilon,\,\forall r_i(\,f(r_i)=0 )\right\}$`
* `basin(newton(:(z^3-1)),1)` = `$\displaystyle D_1(\epsilon) = \left\{z\in\mathbb{C}:\left|\,\left(2 z^{3}+1\right)/\left(3 z^{2}\right) - r_i\,\right|<\epsilon,\,\forall r_i(\,f(r_i)=0 )\right\}$`
* `basin(newton(:(z^3-1)),2)`: numerator `2 (2z^3+1)^3 + 27 z^6`, denominator `9 (2z^3+1)^2 z^2` (with an embedded `\n`)
* `basin(juliafill(:(z^3-1)),1)` = `$\displaystyle D_1(\epsilon) = \left\{z\in\mathbb{C}:\left|\,z^{3}-1 \,\right|>\epsilon\right\}$`
* `basin(juliafill(:(z^3-1)),2)` body = `\left(z^{3}-1\right)^{3}-1`
* `basin(juliafill(:(z^2+c)),2)` body = `z^{4}` (**`c` is substituted by 0**)
* `recomp(:(z^2+c), :z, 2)` = `:(z ^ 4)`
* `recomp(newton_raphson(:(z^3-1),1), :z, 2)` = `:((2 * (2 * z ^ 3 + 1) ^ 3 + 27 * z ^ 6) / (9 * (2 * z ^ 3 + 1) ^ 2 * z ^ 2))`

The README's `D_1…D_3` images come from an older SymPy-era version, with the unsimplified form `z − (z³−1)/(3z²)`, and **do not match the current output**. The Lean port should define its own LaTeX (structural tests), not match REDUCE.

### 5.5 Terminal display (`ext/ImageInTerminalExt.jl:20-24`)

`show(io, K::FilledSet; c="", bare=false)` does `display(ColorSchemes.<c or K.meta.cmap or :balance>(K))` and, unless `bare`, `print(io, String(K))`. Without ImageInTerminal, `show` is Julia's default struct dump.

---

## 6. Examples & goldens

### 6.1 Tests (`test/runtests.jl`)

```
Fatou.Reduce.load_package(:rlfi)                                   # :6  enables REDUCE LaTeX
@test newton(:(z^3-1)) |> typeof <: Fatou.Define                    # :7
@test basin(juliafill(:(z^3-1)),1) |> typeof == LaTeXString         # :10
@test basin(newton(:(z^3-1)),1) |> typeof == LaTeXString            # :11
@test newton(:(z^3-1)) |> fatou |> typeof <: Fatou.FilledSet        # :12
@test mandelbrot(:(z^2+c)) |> fatou |> typeof <: Fatou.FilledSet    # :13
@test juliafill(:(z^2-0.06+0.67im)) |> fatou |> typeof <: Fatou.FilledSet   # :14
```

Lines 8-9 and 15 are commented out (the old `orbit` signature and the `recomp` numeric test, "fix for case k ∈ 2:4+").

### 6.2 README examples (images in `img/`), with verified oracle stats

All stats come from `t10.jl` (Julia 1.13, 1 thread; `fnv` = FNV-1a-64 over row-major UInt16 little-endian bytes of `iter`).

**(R1) Cobweb orbit**, `README.md:60-64` → `img/orbit.png` (630×470 RGBA, PyPlot)

```julia
juliafill(:(z^2-0.67),∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3,n=147) |> orbit
```

* Title `x ↦ x² − 0.67, IC: x₀ = 1.25, n ∈ 0:17`.
* Axes x ∈ [−1.25, 1.5], y ∈ [−0.717, 1.691].
* Curves:
  * black dashed diagonal `y=x`;
  * blue parabola ϕ with its minimum −0.67 near x=0;
  * orange ϕ² (quartic, W-shaped);
  * green ϕ³ (degree-8 wiggle);
  * a red cobweb starting at (1.25, 1.25) that steps down the parabola and diagonal, then spirals into a tight nested-square pattern around the attracting 2-cycle near x ≈ −0.4…−0.5;
  * a gray dotted polyline with × markers (18 points evenly spaced over x) showing the orbit time series zig-zagging between ≈ −0.3 and −0.6.
* Legend box at upper center with 6 entries.
* Data is in §4.9.

**(R2) Filled Julia set**, `README.md:68-74` → `img/filled-julia.png` (630×413, PyPlot, `bare=true`, so no title or colorbar)

```julia
c = -0.06 + 0.67im
nf = juliafill(:(z^2+$c),∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="gnuplot",iter=true)
plot(fatou(nf), bare=true)
```

* Picture: extent x ∈ [−1.5, 1.5], y ∈ [−1, 1], and an elongated, rotated (NW–SE diagonal) filled Julia set built from double spirals.
* Colors:
  * interior (iter = 80) is **yellow** (gnuplot top);
  * the boundary shows red/orange/purple bands;
  * the exterior is black fading to dark purple/maroon in smooth elliptical level-set bands.
* Oracle stats:
  * size (1001, 1501), typeplot `iter.`, `String` = `"f : z ↦ z ^ 2 + (-0.06 + 0.67im), iter."`;
  * iter max 80, min 1, sum 30001428, fnv `0xd7605d2089529229`;
  * histogram for k = 0..80: `[0, 253485, 309975, 157632, 101882, 64266, 42341, 29094, 21278, 15714, 12202, 9678, 7836, 6504, 5509, 4820, 4322, 3914, 3705, 3453, 3601, 3696, 3845, 4490, 4920, 5646, 6566, 7180, 7738, 8315, 8263, 8036, 7835, 7374, 7010, 6483, 5904, 5493, 4925, 4585, 4330, 3817, 3619, 3445, 3149, 3123, 2954, 2975, 2874, 2896, 3129, 3204, 3490, 4096, 4935, 5363, 5790, 5943, 6055, 5800, 5571, 5182, 4760, 4506, 4120, 3768, 3469, 3238, 3049, 2801, 2649, 2507, 2431, 2295, 2284, 2215, 2216, 2345, 2520, 2475, 177598]`;
  * mix: 0 NaN, min −0.4999982362149309, max 0.4999999371844062, sum 182609.88486171205;
  * pixel [501,751] (1-based) iter 54, final z `0.2656834832915705 − 2.075027039524735i`;
  * pixel [1,1]: iter 1, final z `1.1897000100000001 − 2.3298i`, mix −0.17485864522084552.
* Time: Fatou 3.20 s at 1 thread and 2.59 s at 8 threads. A handwritten non-`invokelatest` kernel gives **identical `iter` and final `z`** in 0.068 s (1 thread) and 0.018 s (8 threads), `t11.jl`.

**(R3) Mandelbrot**, `README.md:78-82` → `img/mandelbrot.png` (546×470, title + colorbar)

```julia
mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap="gist_earth") |> fatou |> plot
```

* Title `f: z ↦ c + z², limit` (REDUCE reorders the terms).
* Colors come from gist_earth on `mix = exp(−|z_20|)`:
  * the main cardioid and period-2 bulb are olive→pink-white, brightest (≈1) where the final iterate ≈ 0, i.e. at the cardioid center and the bulb center (−1, 0);
  * the exterior is dark navy with lighter blue filament contours, and an outer black/dark-blue circular band of radius ≈ 2 around c = 0 (pixels escaping at iteration 1).
* Colorbar ≈ 0.003 to 0.999.
* Oracle stats:
  * size (800, 800), `"f : z ↦ z ^ 2 + c, limit"`;
  * iter max 20, min 1, sum 5953108, fnv `0x403251fa209bfc85`;
  * hist `[0, 18596, 37718, 151442, 78408, 49158, 30056, 20996, 14062, 10794, 8010, 6508, 4994, 4334, 3450, 3030, 2568, 2214, 1788, 1720, 190154]`;
  * mix min 0.0028333113112599144, max 0.9991629886828892, sum 161467.0172305601;
  * [1,1]: iter 1, mix 0.10425317162872262.
* Time 0.65 s.

**(R4) Newton z³−1, iteration count**, `README.md:98-104` → `img/newton.png` (564×470)

```julia
nf = newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap="jet")
nf |> fatou |> plot
basin(nf,3)
```

* Title `f: z ↦ z³ − 1, m = 1, iter.`, ylabel `Fatou set: z ↦ z − m × f(z) / f'(z)`, colorbar 0…25 (jet).
* Picture: three dark-blue basins centered on the cube roots of unity (1, e^{±2πi/3}), with small dark dots at the roots (iter 0). Level-set rings in lighter blues surround the roots. The fractal basin boundary forms three arms radiating from 0 along the rays at angles π, ±π/3, as cyan/yellow/red chains of bulbs, with red six-pointed "stars" (iter 25) at 0 and at the preimages along the arms.
* Oracle stats:
  * size (800, 800), `"f : z ↦ z ^ 3 - 1, m = 1, iter."`;
  * iter max 25, min 0, sum 3003400, fnv `0x8610e251146353c5`;
  * hist `[660, 20280, 113158, 173746, 96086, 65516, 46034, 31696, 22982, 17036, 12956, 9738, 7438, 5478, 4236, 3080, 2464, 1862, 1346, 1020, 812, 572, 444, 360, 252, 748]`;
  * mix min −0.4902124835650034, max 0.4902124835650034, 0 NaN;
  * [1,1]: iter 4, final z `−0.49907658892315937+0.8650475774183132i`, mix 0.33328380567417415.
* Time 0.44 s.

**(R5) Generalized Newton sin(z)−1, m = 1−i**, `README.md:108-116` → `img/generalized-newton.png` (568×470)

```julia
nf = newton(:(sin(z)-1),m=1-1im,∂=[-2π/3,-π/3,-π/6,π/6],n=500,N=33,iter=true,ϵ=0.05,cmap="cubehelix")
```

* Title `f: z ↦ sin(z) − 1, m = 1 − 1im, iter.`, same ylabel, cubehelix colorbar ≈1…33.
* Picture: centered at z ≈ −π/2 (where f' = cos z = 0), there is a saturated white blob (iter 33) elongated NW–SE, with pink/white spiral arms winding out. Four large arcs of beaded "pearl necklace" chains cross the square. The background is dark green/teal with darker round spots (fast convergence).
* Oracle stats:
  * size (500, 500), `"f : z ↦ sin(z) - 1, m = 1 - 1im, iter."`;
  * iter max 33, min 1, sum 2799500, fnv `0x1a37eb0404e662db`;
  * hist `[0, 199, 652, 1250, 2615, 7501, 20131, 22920, 23779, 31969, 29743, 24478, 18036, 13513, 10263, 7667, 6004, 4656, 3684, 2870, 2440, 1955, 1640, 1351, 1142, 956, 818, 724, 631, 524, 511, 417, 397, 4564]`;
  * mix 6 NaN.
* Time 0.56 s.

**Defaults** (176×176):

| call | iter sum | fnv | max | hist (k=0..35) |
|---|---|---|---|---|
| `newton(:(z^3-1))` (ϵ=0.01, typeplot `roots`) | 168408 | `0xeec29a9be22e0d35` | 35 | `[0,98,1694,6978,7556,4130,2912,2006,1424,1054,754,640,428,282,242,190,158,100,86,66,36,42,22,24,16,10,10,4,2,4,4,0,0,0,0,4]` |
| `mandelbrot(:(z^2+c))` (`limit`) | 272766 | `0xc97fd12993547bc5` | 35 | `[0,708,12514,5652,2206,1416,752,572,388,294,218,166,148,130,86,94,58,74,46,38,40,40,48,28,18,36,24,14,16,20,22,12,14,10,20,5054]` |
| `juliafill(:(z^2-0.06+0.67im))` (`limit`) | 248336 | `0xb5cfaeaa9c6bcd05` | 35 | `[708,11338,6269,2700,1425,817,536,377,280,186,166,105,112,86,52,59,58,45,53,34,58,43,45,50,72,66,76,104,94,96,88,110,109,81,99,4379]` |

The README `basin` images (`README.md:90-94,116`) are external codecogs SVGs of old-version LaTeX (see §5.4).

**Visual parity already demonstrated.** `scratchpad/fatou/compare_readme.png` shows README image (left) vs `dump_golden.jl` + `render_golden.py` (right) for R2–R5. They are visually identical; only the title typesetting differs (plain text vs TeX).

### 6.3 Docstring examples

* `Define` docstring: none.
* `juliafill("z^2-0.06+0.67im",∂=[-1.5,1.5,-1,1],N=80,n=1501,cmap="RdGy")` (`src/Fatou.jl:200`): String, broken; the wiki's `filled-julia.png` is this call with RdGy (dark-red exterior, black/gray interior).
* `mandelbrot(:(z^2+c),n=800,N=20,∂=[-1.91,0.51,-1.21,1.21],cmap="nipy_spectral")` (`:247`): works.
* `newton("z^3-1",n=800,cmap="brg")` (`:296`): String, broken.
* `basin(newton("z^3-1"),2)` (`:331-332`): shows an old output string; the current output differs (§5.4).
* `juliafill("z^2-0.67",∂=[-1.25,1.5],x0=1.25,orbit=17,depth=3) |> orbit` (`src/orbitplot.jl:14`): String, broken (use Expr).

### 6.4 Wiki examples (`scratchpad/fatou/wiki/Explore-Fatou-sets-&-fractals.md`, images in `wiki/img/`, contact sheets `sheet_0..6.png`)

All run on current Julia after converting strings with `Meta.parse` and `e^z` to `exp(z)` (`t13.jl`, 64×64 smoke test). Each row gives the call, the image, and a visual description.

| id | call | image: what it shows |
|---|---|---|
| nf1-orbit | `newton(:(z^3-1),∂=[0.4,2.5],x0=2.1,orbit=4,depth=2,n=42) \|> orbit` | cobweb of the Newton map, converging monotonically to 1 from 2.1 (staircase) |
| nf1-roots | `newton(:(z^3-1),ϵ=0.001,n=800,cmap="brg")` | three flat regions (red right, green upper-left, blue lower-left) = arg of the root reached; the classic Newton boundary |
| nf1-iter | `newton(:(z^3-1),n=800,ϵ=0.1,N=25,iter=true,cmap="jet")` | same as README R4 |
| nf2-orbit / nf2-iter | `newton(:(z^3-1),m=2,n=800,N=37,ϵ=0.27,iter=true,cmap="ocean",orbit=17,depth=3)` | white fractal "snowflake" lattice on blue, with green blobs at attracting points |
| nf3-limit / nf3-orbit | `newton(:(z^3-1),m=-0.5,n=800,N=10,cmap="hsv",x0=0.9,orbit=17,depth=4)` | hsv hue wheel of arg z_final around the origin, with a three-armed fractal star at the center |
| nf4-orbit / nf4-roots | `newton(:(z^3-2z-5),n=800,p=0.3,cmap="RdGy")` | gray/salmon basins with ringed level sets (p=0.3 shading) |
| nf5-limit | `newton(:(z^2-1),m=1+1im,∂=π/2.4,n=800,N=10,cmap="hsv")` | a jagged fractal band along the anti-diagonal on a hue gradient |
| nf6-limit | `newton(:(z^2-im),m=-0.5+2im,n=800,N=10,cmap="hsv")` | a hue swirl with two small fractal clusters along the ±45° line |
| nf7-limit / orbit | `newton(:(z^8-15z^4-16),m=1.5,∂=[-2π/3,0,-π/3,π/3],n=1501,N=17,cmap="gist_stern",x0=-1,orbit=17,depth=3)` | maroon/khaki/lilac basins with checkerboard fractal fans |
| nf8-limit | `newton(:(z^8-15z^4-16),m=-0.5+2im,∂=[-2π/3,0,-π/3,π/3],n=500,N=10,cmap="hsv")` | a hue field with small spiral fractal clusters |
| nf9-iter / orbit | `newton(:(sin(z)),m=1,∂=[-2π/3,-π/3,-π/6,π/6],n=800,N=17,iter=true,cmap="gist_earth",x0=-1.5,orbit=17,depth=3)` | bright white singular point at −π/2, bead-chain loops, a vertical necklace |
| nf10-iter | README R5 but n=800 | as R5 |
| nf11-limit | `newton(:(z^6+z^3-1),m=(1-0.4im),∂=[-0.5,0.5,-1,0],n=800,N=33,ϵ=1e-7,p=0.7,cmap="YlGnBu",C="(-angle(z)/(2π))*n^e")` | (C string broken; use `C=:((-angle(z)/(2π))*n^p)`) teal/yellow feathery tendrils |
| nf12-limit / alt | `newton(:(cos(z)-1),m=∓0.5±2im,n=350,N=15,ϵ=0,cmap="hsv")` | limit: an orange/blue two-region split with a fractal boundary. alt: noisy red/cyan speckle with rosettes |
| nf13-roots / orbit | `newton(:(cos(z)-1),m=1,∂=π,n=500,N=35,ϵ=0,cmap="YlGnBu",x0=-2,orbit=17,depth=3)` | noisy upper/lower split with fractal edges on the left and right |
| nf14-iter | `newton(:(z^5-3im*z^3-(5+2im)z^2+3z+1),m=1-0.24im,∂=2.0,n=800,ϵ=0.01,iter=true,N=27,cmap="brg")` | red fractal boundary curves on a blue/purple background |
| nf15-limit | `newton(:(log(z)),m=1+1im,∂=2π,n=500,N=27,cmap="brg")` | radial red/green/blue sectors with a noisy center |
| nf16-limit | `newton(:(z^(4.0+3.0im)-1),m=2.1,∂=π,n=500,N=27,cmap="terrain")` | circles of flat color with a spiral fractal and a branch-cut discontinuity along −x |
| nf17-iter / orbit | `newton(:(exp(z)+1),m=1,∂=2π,n=800,iter=true,N=27,cmap="brg",x0=5,orbit=11,depth=3)` | horizontal stripes of period 2π; green (max-iter/NaN) lobes on the left; red fractal fringes |
| o1-orbit, o1-orbit2 | `juliafill(:(z*exp(1.5*(1-z^2/50))),∂=[0,15],x0=1,orbit=24) \|> orbit`; `…x0=0.1,orbit=10,depth=3` | chaotic cobweb over a hump map |
| o2-orbit | `juliafill(:(z*exp(1.5*(1-z/50))),∂=[0,64],x0=1,orbit=10,depth=2)` | cobweb converging to a fixed point near 50 |
| o3-orbit / o3-iter | `juliafill(:(z^2-1),∂=[-2,2],x0=0,orbit=10,depth=5)`; `juliafill(:(z^2-1),∂=[-2,2],iter=true,n=800)` | the 2-cycle 0↔−1; the "basilica" Julia set in yellow on viridis purple |
| o4-limit | `juliafill(:(z^2+1.),∂=[-2,2],n=800,cmap="hsv")` | hsv angle field; a disk of radius ~1.5 with 4 small fractal clusters inside |
| o5-orbit / limit | `juliafill(:(cos(z)),∂=[0,2],x0=1.7,orbit=17,depth=3)`; `juliafill(:(cos(z)),∂=[0.5,2],n=500)` | the Dottie-number fixed point ≈0.739; viridis angle field |
| o6-orbit / limit | `juliafill(:(z^2-1),∂=[-2,2],x0=sqrt(2),orbit=10,depth=5)`; `…cmap="hsv",n=800` | basilica in the hsv angle field (red/cyan interior) |
| o7-limit | `juliafill(:(sin(z)),∂=[0,2],n=700)` | viridis field with a dark lower-right quarter disk |
| o8-orbit/limit/roots | `juliafill(:(z^2-z-4),∂=[-4,4],x0=0.99999999+sqrt(5),orbit=37,depth=3)`; `juliafill(:(z^2-z-4),∂=[-3,3],n=500,cmap="gist_earth")`; `newton(:(z^2-z-4),∂=[-4,0],n=700,cmap="RdGy",p=0.5)` | quartered disk (yin-yang-like) pattern; banded red/gray rays |
| o9-orbit / iter | `juliafill(:((-3/2)*z^2+5z/2+1),∂=[-0.7,2.5],x0=0.001,orbit=37,depth=3)`; `…n=800,iter=true` | thin lens-shaped iteration bands along the real axis |
| o10-orbit / limit | `juliafill(:(z^2-2),∂=[-2.5,2.5],x0=0.01,orbit=100)`; `…n=500,p=0.1,cmap="ocean"` | c = −2 (segment Julia set): a disk with an interleaved green/white checker pattern along the real axis |
| o11-orbit-1/2 | `juliafill(:(2z%1),∂=[0,1],x0=0.3 / 1/9,orbit=70,depth=3)` | doubling-map cobwebs (sawtooth ϕ) |
| o12-limit | `juliafill(:(z^3),∂=[0,2],n=500,cmap="ocean")` | quarter annuli with angle shading |
| o13-limit | `juliafill(:(sqrt(z)),∂=[-3.2,6.4],cmap="ocean",n=500)` | smooth field with a disk of radius 2 and a branch cut |
| o14 / o15 / o16 / o17 | `juliafill(:(z^2+1),∂=[-2.5,2.5],n=500,cmap="nipy_spectral")`, `…z^2-2…`, `juliafill(:(sin(2z)),∂=[-0.35pi,0.7pi],n=800,cmap="nipy_spectral")`, `juliafill(:(3z+2),∂=[-pi,pi],n=500)` | angle-field rainbow disks; sin(2z) checkerboard; the affine map 3z+2 gives a smooth arg field around the fixed point −1 |

(The wiki file names o13/o15 are swapped relative to the text; see the contact sheet.)

---

## 7. Dependencies on other chakravala (and third-party) packages

| package | kind | symbols used | where | Lean replacement |
|---|---|---|---|---|
| **SyntaxTree.jl** (chakravala) | dep | `genlatest(expr, args)` (eval + `invokelatest` closure) | `src/Fatou.jl:3,113-115`; commented in `test/runtests.jl:15` | the `Fatou.Expr` AST, a compile-time elaborator (`fatou_map%`), and a runtime register VM (§8.4) |
| **Reduce.jl** (chakravala; wraps the REDUCE CSL binary) | dep | `RExpr`, `Algebra.:-`, `Algebra.:*`, `Algebra.:/`, `Algebra.df`, `factor` (switch), `parse(::RExpr)`, `Algebra.sub((z=…, c=0), E)`, `Algebra.latex`, `Reduce.load_package(:rlfi)`, `Reduce.stop()` | `src/internals.jl:9-19`, `src/Fatou.jl:407`, `ext/PyPlotExt.jl:31,67`, `test/runtests.jl:6` | a mini-CAS: derivative, simplifier, rational-form normalizer, substitution, LaTeX printer (§8.5) |
| **Grassmann.jl** (chakravala) | weakdep/ext | `Grassmann.Manifold(B)`, `Grassmann.Couple{V,B}(::Complex)`, `Grassmann.value`, `Couple` arithmetic (`*`, `+`, `abs2`) | `ext/GrassmannExt.jl:17-29` | `Couple (s : Int)` in Lean (§8.6); later a bridge to the Lean Grassmann port's `Couple` |
| LaTeXStrings | dep | `latexstring`, `LaTeXString`, `L"…"` | `src/internals.jl:27-32`, `ext/PyPlotExt.jl` | plain `String` newtype `LaTeX` |
| ColorSchemes | dep | `ColorScheme` (callable), `get`, indexing `C[i]`, `length`, named schemes via `getproperty(ColorSchemes, Symbol(name))`, `RGB` | `src/Fatou.jl:374-390`, `ext/ImageInTerminalExt.jl:19-22` | LeanPlot colormap module with embedded tables (dumped by the oracle) |
| Base.Threads | stdlib | `@threads`, `nthreads` | `src/Fatou.jl:360,397` | `Task.spawn` row chunks |
| Requires | dep (legacy) | `@require` | `src/Fatou.jl:392-405` | none |
| PyPlot, UnicodePlots, ImageInTerminal, (Makie) | weakdeps | see §5 | `ext/*` | LeanPlot backends (SVG/PNG, terminal ANSI/sixel) |

Other chakravala packages are **not** used (no AbstractTensors/DirectSum except indirectly through Grassmann).

---

## 8. Lean 4 porting notes

### 8.1 Compile-time indices vs runtime values

| Julia | Lean recommendation | cost |
|---|---|---|
| `M, N, P, D` Bool type params | `structure Mode where mandel newt plane disk : Bool`. Pass the mode to an `@[inline]` kernel. **Hoist the branches out of the loop**: build the start function and continue-predicate once. Optionally generate 16 specializations with `match mode with …` around `@[specialize]` calls. Do **not** make them type indices: they buy no safety and cost API friction. | zero after specialization |
| `FT, QT, CT` closure types | `@[specialize]` higher-order kernel with lambda-literal call sites. This is Lean's analog of Julia specializing on `typeof(F)`. The elaborator macro produces those lambdas. | zero |
| `B` (unit blade) | `Couple (s : Int)` type index (or `Fin 3` coded {−1,0,1}), instances `Mul (Couple s)` etc. `s` is known at compile time, so it folds. `Complex := Couple (-1)`, or a dedicated `Complex` for maximal speed. | zero |
| grid dims (rows, cols) | **dependent index**: `structure Grid (rows cols : Nat) where re im : FloatArray; hre : re.size = rows*cols; him : …`. Index with `Fin rows × Fin cols`, using the lemma `i*cols + j < rows*cols` once (a `Nat` lemma, since omega can't do nonlinear), then `uget`/`get` without bounds checks. | zero (the proof is erased) |
| `iter ≤ N` | `FilledSet` stores `iter : UInt16Array` (ByteArray-backed) or `Array UInt16` (tagged scalars, no alloc), plus the theorem `∀ i, iter[i] ≤ N` proved from the kernel loop. | zero |
| `N::UInt16`, `n::UInt16` | `UInt16` fields with smart constructors that validate (`Except String`). | – |
| bounds `[xa,xb,ya,yb]` | `structure Bounds where xa xb ya yb : Float`. Float proofs are impractical; validate at runtime (`xa ≠ xb`, `ya ≠ yb`, rows in 2..65535). | – |

### 8.2 Performance: where Julia gets (and loses) speed

* **Julia's intended fast path**: `Define` stores `F/Q/C` concretely typed (`FT,QT,CT`), and `orbit` is specialized on the flags `M,N,P,D,B`, so the loop compiles to straight-line float code. `Compute` threads over rows.
* **Actual 1.2.4 behavior**: `genlatest` returns `(a,b)->invokelatest(g,a,b)`. Every `F`, `Q`, `C` call is a dynamic dispatch with boxing. Measured on the R2 example: Fatou takes **3.0 s (1 thread) / 2.6 s (8 threads)**. The equivalent handwritten kernel takes **0.068 s / 0.018 s** with bit-identical output. Threads barely help Fatou (allocation/GC bound).
* **Perf target for Lean**: at least the handwritten-Julia numbers. That is ≈ 30 M complex iterations in ~70 ms single-thread (≈2.2 ns/iteration).

**Lean hazards**
* A Lean `structure Complex (re im : Float)` is a heap object. A loop-carried `Complex` param forces an **allocation per iteration**, so the kernel loop must carry `(zr zi : Float)` separately.
* The step function must be inlined (`@[inline]` lambda via `@[specialize]`) so `Complex.mk`/projections cancel in LCNF. Verify with `set_option trace.compiler.ir.result true`: no `ctor`/`alloc` in the loop body.

**Parallelism**
* Split rows into chunks (≈4× cores) and use `Task.spawn` (pure) with per-chunk `FloatArray`/`ByteArray` outputs, then concatenate.
* Each pixel is independent, so order does not affect results.

**No FMA contraction**
* Lean emits each float op as a separate C statement through `static inline` helpers, so clang (`-ffp-contract=on`) will not fuse across statements.
* Julia also does not fuse (verified on aarch64). Keep it that way. Add a CI golden that would catch a fused `re = a*a − b*b`.

### 8.3 Bit-exactness plan (which layer can match Julia exactly)

| layer | exact? | how |
|---|---|---|
| grid axes | **yes** | transliterate `jrange.jl` (§4.2). Needs `roundTiesEven`, `truncbits` (via `Float.toBits`/`ofBits`), and `two_mul`: Lean core has **no `Float.fma`**, so declare `@[extern "fma"] opaque Float.fma : Float → Float → Float → Float` (links to libm) or use Dekker/Veltkamp splitting (exact without overflow). Int128 arithmetic: use `Int` (bignum). |
| `+ − *`, `abs2`, literal powers, `power_by_squaring`, real/complex mixing | **yes** | §4.6 formulas verbatim |
| complex `/` | **yes** | port Baudin–Smith `cdiv` verbatim |
| `abs` (hypot) | **yes** | port Julia `_hypot` with fma (correctly rounded) |
| `angle` (atan2), `exp`, `sin/cos/sinh/cosh`, `log`, `sqrt` | ≤1–2 ulp | Lean `Float.atan2` etc. call C libm. Julia uses its own openlibm-derived implementations. Use a tolerance, or optionally port Julia's `atan`/`exp`. |
| iteration counts, rational maps (R2–R4, Mandelbrot) | **yes** (given exact grid + ops) | proven by the handwritten Julia kernel's identical output |
| iteration counts, transcendental maps (R5, wiki) | near (boundary pixels may differ) | mismatch-fraction threshold |
| Newton map | only when fed REDUCE's expression | the oracle provides `F` as a string. The Lean-native symbolic/AD map is a separate, tolerance-level test. |

Julia/Lean semantic gotchas:
* `round` is ties-to-even in Julia and half-away in Lean.
* `UInt16(x)` throws in Julia, while Lean's `Float.toUInt16` saturates.
* `trunc(Int, y)` maps to Lean `Float.toInt64` (C cast, truncation).
* Julia `0^0 = 1`; C `pow(0,0) = 1` too.
* Comparisons with NaN are false in both.
* Lean `Float` NaN is canonicalized in the logical model; this is irrelevant for comparisons.

### 8.4 Expression front-end (replaces `genlatest` + Julia parser)

* `Fatou/Expr.lean`: an AST with
  * `num : Float`, `cnum : Float × Float`, `int : Int`, `rat : Int × Nat`;
  * `var : Var` (`z | c | n | p`);
  * `add/sub/mul/div/neg`, `pow (base) (exp : Expr)` with an `ipow (k : Int)` special form (to reproduce `literal_pow`/`power_by_squaring` exactly);
  * `app : Fn → Expr → Expr` for `sin cos tan exp log sqrt abs abs2 angle conj real imag sinh cosh tanh`;
  * `rem` (real-only).
* **Parser** for Julia-flavored syntax: precedence `+ − < * / < unary − < ^` (right-assoc); juxtaposition `2z`, `3im`, `0.67im`, `2π`, `π`, `pi`, `ℯ`, `im`, `%`.
* **Printer** `toJulia` (titles, §5.1) and `toLaTeX` (§5.4).
* **Compilation, two tiers:**
  1. `fatou_map% z^2 + c` is a term elaborator that parses at compile time and produces `fun zr zi cr ci => …` over unboxed floats. It also runs the symbolic derivative at elaboration time for `newton%`. This is the zero-overhead path and the "standout" feature: the analog of Julia's `@eval` specialization, with no world-age problems.
  2. Runtime strings (CLI/REPL) lower the AST to a linear SSA **register program** over a scratch `FloatArray` (pairs re/im per register), interpreted by a tight `@[specialize]`-free loop. There is no allocation per op; expect ~5–10× slower than tier 1 but ≫ Julia's `invokelatest`.

### 8.5 Mini-CAS (replaces REDUCE)

Needed operations:
* `deriv : Expr → Expr` (w.r.t. `z`; `c` constant; chain rule for `Fn`s; `z^w` with constant complex `w`);
* `simp` (constant folding, `0/1` identities, flatten);
* `newtonMap m f := z − m * f / f'`;
* optional `together` (single fraction), for pretty LaTeX and parity with REDUCE's `(2z³+1)/(3z²)` shape;
* `subst` (for `recomp`: `z := e`, `c := 0`);
* `toLaTeX`.

Alternatives and design decisions:
* **Dual-number AD alternative** for evaluation: evaluate `f` and `f'` together with `(value, derivative)` complex pairs, then `N(z) = z − m·f/f'`. No symbolic blow-up for deep compositions, and it is exact math. Its rounding differs from REDUCE's rational form, so it belongs in the tolerance tier.
* Do **not** try to replicate REDUCE `factor` output or its `\n`-wrapped LaTeX. `basin` tests are structural (parse your own LaTeX back, or compare ASTs).

### 8.6 Tricky semantics checklist

1. A 2-element `∂` means a square `[a,b,a,b]`; a scalar means `[−s,s,−s,s]`.
2. `n` is **columns**; rows = `rte((yb−ya)/(xb−xa)*n)`.
3. The x axis starts at `xa + 0.0001`. The y axis descends and has the `im*range` quirk.
4. `c = pixel` in all modes. Mandelbrot ignores `plane` for the start value.
5. Strict comparisons; test before step; `zn ∈ [0, N]`; NaN terminates.
6. Newton `Q = |f(z)|` via hypot with the original `f`, not `|z − root|`.
7. `mix = C(z_final, iter/N, p)`. The ImageInTerminal color path clamps `mix` to [0,1] (negative angles lose their color); matplotlib auto-scales min..max.
8. `typeplot` (`src/Fatou.jl:367`) tests `m == 1` without checking `newt`. Non-Newton front-ends default to `m=0`, so they print `"limit"`, but `juliafill(E, m=1)` (not Newton) would print `"roots"`. This is a quirk: reproduce it for title parity.
9. `fatou` chaining continues from **final** iterates and resets counts. `FilledSet.set` holds final iterates, not the input grid.
10. `Compute` prints `@time` output on every call (side effect; drop it or put it behind a flag).
11. `basin` substitutes `c = 0` (so the Mandelbrot `z^2+c` basin shows `z^4` for j=2).
12. Grassmann ext: broken return; intended `Complex(value(z)...)`. For split-complex, `abs2` can be negative.
13. `plot` is exported and undefined. `orbit(K)` without a backend throws `MethodError`.
14. `orbit(K)` evaluates `F(x, 0)` on **reals**, so a map containing `im` fails in Julia. In Lean, take `re` of a complex evaluation or restrict to a real AST.

### 8.7 What to skip / redesign

* Skip: `Requires`, `__init__` printing, `Reduce.stop`, `@time` inside `Compute`, `invokelatest`/world-age machinery, `LaTeXStrings` type, Makie dead code, the String→`parse` bug (replace with a real parser), the `ComplexBundle` hierarchy.
* Redesign:
  * `Define` becomes a plain `structure FatouSpec` plus compiled-map fields.
  * `FilledSet` becomes `FilledSet (rows cols)`.
  * `plot`/`imshow`/`orbit` become **LeanPlot figure specs**: a heatmap with extent, colormap name, colorbar, title, ylabel, and a `bare` flag; a line plot with styles (`dashed`, `dotted`, marker `x`), a color cycle (tab10), legend, xlim/ylim; a terminal image and terminal line plot.
  * Colormap semantics are a LeanPlot concern with two modes: `matplotlib` (Normalize + 256-LUT + bad color) and `colorschemes` (clamp [0,1] + linear interpolation over stops; iter-index formula).

### 8.8 Proof opportunities (weave in, cheap, useful)

* `orbit_iter_le : (orbit spec z0).iter ≤ spec.N` (loop invariant, induction on fuel).
* `grid_index_lt : i < rows → j < cols → i*cols + j < rows*cols` (enables unchecked indexing everywhere).
* `cobweb_shape`: `(cobweb N2).size = 3*orb`, and row pattern lemmas (§4.9) by construction.
* **Symbolic derivative soundness** over an abstract commutative ring with dual numbers: `eval_dual e (z + ε) = eval e z + ε * eval (deriv e) z` by structural induction (`grind` ring normalization; no Mathlib needed for the polynomial/rational fragment with a `Field`-like class). Corollary: `newtonMap` fixes every simple root in an exact field model.
* `subst_eval : eval (subst e z e') = eval e (eval e')` (justifies `recomp`/`basin`).
* `colorIndex_bounds`: the Nat version of the ColorSchemes iter index `⌈L(k+1)/(kmax+1)⌉ ∈ [1, L]` for `k ≤ kmax` (the Julia code computes it in Float; document the rare float-rounding edge).
* Optional with Mathlib: `disk ∘ plane = id` on ℂ \ {i}, over exact complex numbers.

### 8.9 Suggested module decomposition (≈ 4.3 k LOC excluding generated colormap tables)

| module | contents | LOC |
|---|---|---|
| `Fatou/Float/Julia.lean` | `roundTiesEven`, `truncbits`, `fma` extern + Veltkamp fallback, `twoSum/twoProd`, `canonicalize2`, `add12`, `mul12`, `topSetBit` | 150 |
| `Fatou/Float/Range.lean` | `rat`, TwicePrecision ops, `jrange`, `getidx`, `imAxis` quirk (from `jrange.jl`) | 200 |
| `Fatou/Complex.lean` | unboxed-friendly `Complex`: ops, Baudin–Smith `cdiv`, Julia `hypot`, `angle`, `powBySquaring`, `literalPow`, `exp/log/sin/cos/sqrt/cpow` (Julia formulas over libm) | 350 |
| `Fatou/Couple.lean` | `Couple (s : Int)` generalized units + instances | 150 |
| `Fatou/Grid.lean` | `Bounds`, `Rectangle` normalization (scalar / 2-vec / 4-vec), `size`, `Grid rows cols`, axes, row-major layout + index lemmas | 220 |
| `Fatou/Expr/Syntax.lean` | AST, parser (Julia-ish), `toJulia` printer | 450 |
| `Fatou/Expr/CAS.lean` | `deriv`, `simp`, `together`, `subst`, `newtonMap`, `recomp` | 400 |
| `Fatou/Expr/LaTeX.lean` | LaTeX printer, `basin` templates (§5.4) | 150 |
| `Fatou/Expr/Compile.lean` | `fatou_map%`/`newton%` elaborators; runtime register VM | 400 |
| `Fatou/Spec.lean` | `FatouSpec`, `Mode`, `juliafill/mandelbrot/newton` smart constructors with **per-front-end defaults** (§2.3) | 200 |
| `Fatou/Kernel.lean` | `orbit` loop (unboxed, specialized), `compute` (parallel), `FilledSet rows cols`, chaining, `typeplot`, `title` | 300 |
| `Fatou/Color.lean` | ColorSchemes-mode and matplotlib-mode colorization, NaN handling; tables in `Fatou/Color/Data.lean` (generated) | 250 (+data) |
| `Fatou/Orbit.lean` | `realOrb` data + cobweb + ylim rule | 120 |
| `Fatou/Plot.lean` | LeanPlot figure builders (heatmap fig, orbit fig, terminal) | 250 |
| `Fatou/Proofs/*.lean` | §8.8 | 300 |
| `test/Fatou/*.lean` + oracle harness | golden loaders (JSON + raw arrays), comparators, perf benches | 450 |

---

## 9. Oracle test plan (Julia = ground truth)

Run with `julia --startup-file=no --project=scratchpad/juliaenv`.
* Seed all RNGs (`Random.seed!(0xFA70)`).
* Floats go to JSON as shortest round-trip reprs (JSON.jl does this), and large arrays as raw little-endian row-major files next to the JSON (prototype: `dump_golden.jl`).
* Also emit bit patterns (`reinterpret(UInt64, x)` as hex) for exact-tier values, so NaN/−0.0 survive.

### 9.1 Dumps

| # | function(s) | inputs / distribution | stored | Lean comparison |
|---|---|---|---|---|
| G1 | `range(a, stop=b, length=n)` internals + values | 2000 cases. 25% decimals with 1–4 digits in [−4,4]; 25% `k·π/d` (k∈1..7, d∈1..8); 25% uniform random floats; 25% edge cases: `a=0` or `b=0`, `a=−b`, tiny spans 1e−6, huge 1e12, n ∈ {2,3,10,176,800,1001,1501,2000,65535} | `(ref.hi, ref.lo, step.hi, step.lo, offset)` hex; all values hex for n ≤ 64, else 16 sampled indices + FNV of all bits | **bit-exact** |
| G2 | `size(Rectangle(∂,n))` | README/wiki bounds; random bounds; constructed **ties** (e.g. `[0,2,0,1]`, n odd) | `(rows, cols)` | exact |
| G3 | grid axes (`fatou(Rectangle)`) | 300 random 4-vector bounds with k-digit decimals, the scalar form, the 2-vector form, n ∈ 2..600 | `gx`, `gy` hex | **bit-exact** |
| G4 | complex primitives: `*`, `/` (cdiv), `abs`(hypot), `abs2`, `z^k` for k=−3..12 via `literal_pow` and `power_by_squaring`, `angle`, `exp`, `sin`, `cos`, `log`, `sqrt` | 10k random pairs: log-uniform magnitudes 1e−310..1e308 (to hit the cdiv scaling branch), plus zeros, ±0.0, Inf, NaN, denormals | hex | exact for the first five; ≤2 ulp for transcendentals |
| G5 | kernel `Fatou.orbit(K, z0)` | Catalog K below × 500 z0 each: 60% uniform in bounds, 30% on grid points, 10% specials (0, roots, exact escape radius like `c=−2`, NaN-producing points) | `(zn, re, im)` hex + `mix` | exact for the rational catalog; tolerance otherwise |
| G6 | full images `fatou(K)` | Catalog K at n=64, 128, 256; the README examples at full size | `iter.u16`, `mix.f64`, `zre/zim.f64`, grid, JSON meta (`E`, **Newton `F` string**, bounds, N, ϵ, flags, `title`, `typeplot`) | rational: `iter` exact, `z` exact, `mix` ≤2 ulp. Transcendental: `iter` mismatch fraction ≤ 1e−3; `mix` compared only where `iter` agrees, abs tol 1e−12 |
| G7 | `newton_raphson(E, m)` | the §4.5 table + 30 random polynomials (deg 2–8, Gaussian-integer coefficients) × m ∈ {1, 2, −0.5, 1±i, 1.5} | `string(Expr)` + evaluation at 20 points (hex) | Lean parses the string and evaluates exactly; Lean's own `newtonMap` agrees within 1e−12 relative away from poles |
| G8 | `recomp(E,:z,j)`, `basin(K,j)` | j=0..3 for 10 maps | strings | informational (structural/AST checks only) |
| G9 | `String(K)`, `typeplot` | the whole catalog | strings | Lean `title` equal modulo whitespace/parens (or exact if implementing Julia Expr printing) |
| G10 | `real_orb` | README orbit + all wiki orbit calls (Expr-converted), plus random `x0` | `x`, `N`, `N2`, `orbit`, `bis`, `ylim` hex | exact for polynomial maps; tolerance for exp/sin/cos |
| G11 | `ColorScheme(K)` functor | K ∈ {8×8, 32×32} × {iter, mix} × schemes {balance, gnuplot, jet, cubehelix, RdGy} | RGB Float64 hex | exact (simple formulas) |
| G12 | ColorSchemes tables | every scheme named in README/wiki + balance, viridis | `colors` arrays | embed |
| G13 | matplotlib LUTs (Python oracle via `uv run --with matplotlib`) | same names, N=256; plus `Normalize` + `bad` behavior | RGBA arrays | LeanPlot parity |
| G14 | `plane`, `disk` | 5k random points in \|z\|<1.5 and the half-plane | hex | exact |
| G15 | Grassmann Couple kernel (with the §4.10 monkey-patch) | `mandelbrot(:(z^2+c), B=Λ(S"+-").v12)` and `S"++"` at n=40..128 | iter/mix | exact vs Lean `Couple 1` / `Couple (−1)` |
| G16 | perf baselines | README R2–R5: Fatou time and handwritten kernel time at 1/8 threads | seconds | Lean bench target ≤ handwritten Julia |

**Catalog K**
* Rational (exact tier):
  * `mandelbrot(z^2+c)` with N ∈ {20, 35};
  * `juliafill(z^2 + (−0.06+0.67i))`, iter and non-iter;
  * `juliafill(z^2−1)`, `juliafill(z^3)`, `juliafill(3z+2)`;
  * `newton(z^3−1)` with m ∈ {1, 2, −0.5}, ϵ ∈ {0.01, 0.1, 0};
  * `newton(z^3−2z−5)`, `newton(z^8−15z^4−16, m=1.5)`, `newton(z^2−im, m=−0.5+2im)`, `newton(z^5−3im*z^3−(5+2im)z^2+3z+1, m=1−0.24im)`;
  * `mandelbrot(z^3+c)`;
  * mode variants `plane=true`, `disk=true`, `p ∈ {0, 0.3, 0.7}`, and custom `C = :(exp(-abs(z))*n^p)`.
* Transcendental (tolerance tier): `newton(sin(z)−1, m=1−1im)`, `newton(sin z)`, `newton(cos(z)−1, …)`, `newton(exp(z)+1)`, `newton(log z, m=1+1im)`, `newton(z^(4+3i)−1, m=2.1)`, `juliafill(cos z)`, `juliafill(sin z)`, `juliafill(sqrt z)`, `juliafill(sin(2z))`.

**Chaining tests**
* `fatou(K2, fatou(K1))`: continuation from final iterates.
* `fatou(fatou(K))`: re-iterate.

### 9.2 Visual cross-tests with LeanPlot

For every G6 case at full README/wiki size:
* Render with the Python oracle (`render_golden.py`, i.e. matplotlib `imshow(extent, cmap, colorbar, title)`).
* Render with LeanPlot from the Lean-computed arrays.
* Compare:
  * **(a)** data equality before rendering, which is the primary check;
  * **(b)** image-level: resize both to the same size and require mean |ΔRGB| < 2/255 inside the axes area, plus a perceptual hash;
  * **(c)** keep side-by-side sheets like `compare_readme.png` for human/AI review.

Orbit figures: compare the polyline data (G10) plus the legend/title strings. Visual comparison against `img/orbit.png` and the wiki `*-orbit.png` is qualitative.

### 9.3 Known oracle caveats

* Wiki/docstring String inputs need `Meta.parse`. Replace `e^z` with `exp(z)`. Replace the `C` string with an Expr. Use the current `orbit(E, f, bi, orb, depth, incr)` signature.
* README `basin`/title images come from older versions. Do not use them as text goldens.
* PyPlot is not usable in the env (Conda broken, see `juliaenv/julia_setup.log`). Use the Python/matplotlib re-render instead; it has been shown to match the README images.
* `Compute` prints `@time` lines. Filter stdout (`rg -v '^\s+[0-9.]+ seconds'`).
