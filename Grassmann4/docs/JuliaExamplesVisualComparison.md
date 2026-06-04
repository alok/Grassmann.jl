# Grassmann.jl Plot Examples Visual Comparison

This note records the comparison harness for the plot-producing Julia examples in
`docs/src/algebra.md`.

## Regeneration

From the repository root:

```bash
lake exe jlexamples
```

This writes Lean-generated SVGs to:

```text
.generated/julia-examples/lean/
```

It also writes a side-by-side visual comparison page and a machine-readable
manifest. The manifest includes CGA witness samples for the orbit translation
path, comparing the fast plotted coordinates against Lean's `CGA.transform`:

```text
.generated/julia-examples/index.html
.generated/julia-examples/manifest.json
```

The same executable is also available from the nested Lean package:

```bash
cd Grassmann4
lake exe jlexamples
```

Nested runs write to `Grassmann4/.generated/`, which is ignored by
`Grassmann4/.gitignore`.

For a single reproducible visual audit, run:

```bash
cd Grassmann4
scripts/compare_julia_examples.sh
```

That command regenerates the Lean SVGs, downloads the canonical Julia/Makie PNG
references, renders the Lean SVGs to PNG, and writes a side-by-side contact
sheet:

```text
.generated/julia-examples/contact-sheet/contact.png
```

Each row in the contact sheet is labeled with the example name and left/right
source. The same run also writes diagnostic raster metrics:

```text
.generated/julia-examples/contact-sheet/metrics.tsv
```

The metrics file records grayscale standard deviation for each rendered Lean and
Julia frame plus ImageMagick RMSE diagnostics. The script now enforces a
conservative visual smoke gate: all documented `paper/img/*.png` examples in
`docs/src/algebra.md` must be covered, all twelve expected Lean SVGs must be
generated, the manifest must list every expected example, each Lean and Julia
frame must have grayscale standard deviation of at least `1200`, and the
normalized RMSE must stay at or below `0.25`. Treat the RMSE bound as a sanity
check for blank or badly framed images, not as an exact visual oracle; several
examples are qualitative Lean counterparts rather than exact Grassmann.jl
renderings.

The generated `summary.json` repeats the gate thresholds and records the
observed extrema for the run: minimum Lean frame standard deviation, minimum
Julia frame standard deviation, maximum normalized RMSE, and maximum CGA witness
difference.

It requires `curl`, `jq`, `rsvg-convert`, and ImageMagick's `magick` command.

## Julia Reference Images

The local Julia project can load `Grassmann` with automatic precompile disabled:

```bash
JULIA_PKG_PRECOMPILE_AUTO=0 julia --project=. --startup-file=no -e 'using Grassmann'
```

Local Makie rendering is not available in this checkout because `Makie`,
`CairoMakie`, `GLMakie`, and `GeometryBasics` are not installed in the project.
For visual comparison, use the canonical images already linked from the Julia
docs:

```text
https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img/<name>.png
```

The comparison run used these reference names:

```text
plane-1 plane-2 plane-3 plane-4 plane-5 plane-6
torus helix orb wave orbit-2 orbit-4
```

## Current Match

The Lean generator emits twelve visualizations with the same grayscale/white
plot palette as the Julia/Makie references.

Open `.generated/julia-examples/index.html` after regeneration to visually
inspect every Lean SVG next to its canonical Julia reference image.
The contact-sheet script provides the same comparison in one local image.

| Example set | Lean status | Notes |
| --- | --- | --- |
| `plane-1` through `plane-6` | Direct linear-field counterparts | Euclidean rotations/reflections and hyperbolic boosts match the reference topology. Arrow glyphs and line density are approximate Makie-style matches. |
| `torus`, `helix` | Parametric counterparts | Captures the same 3D line-plot style and broad geometry, but not a proof of identical Grassmann.jl conformal motor output. |
| `orb`, `wave` | Qualitative vector-field counterparts | Uses deterministic Lean vector fields styled to match Makie. Exact CGA streamplot parity remains future work. |
| `orbit-2`, `orbit-4` | CGA-checked orbit counterparts | The plotted translation leg uses the fast closed-form coordinates and the manifest records sample checks against Lean `CGA.point`/`CGA.translator`/`CGA.transform`; `orbit-4` applies an explicit Euclidean `z` rotation after translation. Exact pointwise parity against the full Grassmann.jl CGA plotting pipeline remains future work. |

Separately from the fast SVG generator, `lake exe oracletests` now checks exact
sample coordinates for the documented `S"∞+++"` projective formulas for
`torus`, `orbit-2`, and `orbit-4` against Grassmann.jl. Those oracle-backed
evaluators live in `Grassmann.JuliaExamples` and intentionally avoid replacing
the SVG paths until plot-time performance is acceptable over the full sample
range.

## 2026-06-04 Audit

The comparison harness was rerun from `Grassmann4` and covered all twelve
documented Julia plot images. The smoke gate passed with every rendered Lean and
Julia frame above the `1200` grayscale standard-deviation floor, every
normalized RMSE at or below `0.25`, and all ten CGA orbit witnesses within
`1e-6` max absolute difference.

The observed normalized RMSE values were:

| Example | Normalized RMSE |
| --- | ---: |
| `plane-1` | `0.109350` |
| `plane-2` | `0.121803` |
| `plane-3` | `0.111175` |
| `plane-4` | `0.105751` |
| `plane-5` | `0.121607` |
| `plane-6` | `0.129301` |
| `torus` | `0.106073` |
| `helix` | `0.099739` |
| `orbit-2` | `0.087348` |
| `orbit-4` | `0.108997` |
| `orb` | `0.151953` |
| `wave` | `0.120565` |

Exact pointwise torus parity is still intentionally not claimed. A direct local
Julia oracle for the documented conformal torus expression loads and returns
finite coordinate samples, but the Lean generator currently keeps the torus as a
qualitative parametric counterpart. The existing closed-form `Multivector`
bivector exponential is not valid for the mixed conformal torus generator,
because that generator does not square to a scalar. A dense Taylor/scaling
attempt was too slow for plot generation, and importing the packed `MV`
implementation into `jlexamples` currently pulls LeanBLAS/SciLean linkage into
the executable, which fails without configured CBLAS symbols. A future exact
port should use a small standalone CGA motor exponential kernel or fix the
LeanBLAS link path before replacing the qualitative torus/helix plots.

## Verified Commands

These commands were run successfully from the repository root:

```bash
lake exe jlexamples
JULIA_PKG_PRECOMPILE_AUTO=0 julia --project=. --startup-file=no -e 'using Grassmann; basis"2"; println(exp(pi*v12/2)); @basis S"+-"; println(exp((pi/8)*v12/2))'
```

The generator wrote `12` Lean visualizations plus the comparison index and
manifest.

The CGA smoke check also ran using the exact conformal basis syntax from
`docs/src/algebra.md`; the command is not repeated here because it contains the
non-ASCII infinity basis character.

These commands were also run successfully from `Grassmann4`:

```bash
lake exe jlexamples
scripts/compare_julia_examples.sh
```

The browser comparison page reported `12` example sections and `24/24` loaded
images: one Lean SVG and one Julia/Makie reference PNG for each example.
The contact-sheet script additionally passed the automated coverage and visual
smoke checks for the same twelve examples.

The Julia oracle suite was later extended with exact `S"∞+++"` projective
samples for `orbit-2` and `orbit-4`, in addition to the existing torus samples.
It passed with `109/109` checks.
