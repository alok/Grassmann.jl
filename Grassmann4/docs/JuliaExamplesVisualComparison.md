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
manifest. The manifest includes numerical witness samples for two non-visual
checks: the auxiliary CGA orbit translation path is compared against Lean's
`CGA.transform`, and the plotted projective `torus`, `orbit-2`, and `orbit-4`
curves are compared against their documented projective evaluators:

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
renderings. The same run also checks formula witnesses: the CGA translation
helper path, exact projective plot curves, the conformal helix motor, and the
projective `orb`/`wave` stream-field motor all have `1e-6` max absolute
difference gates.

The generated `summary.json` repeats the gate thresholds and records the
observed extrema for the run: minimum Lean frame standard deviation, minimum
Julia frame standard deviation, maximum normalized RMSE, maximum CGA witness
difference, maximum projective plot formula witness difference, maximum
conformal plot formula witness difference, and maximum projective stream-field
witness difference.

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
| `torus` | Exact documented projective curve | Renders `documentedProjectiveTorusPoint` directly. Oracle tests and manifest witnesses sample-check the plotted path against the documented `S"∞+++"` evaluator; camera, grid, and stroke rendering remain approximate Makie-style matches. |
| `helix` | Exact documented conformal curve | Renders the closed form of the documented `S"∞∅+++"` conformal helix. Manifest witnesses and property tests sample-check the plotted path against a sparse CGA motor evaluator; the helix-specific camera projection remains an approximate Makie-style view. |
| `orb`, `wave` | Documented projective stream fields | Uses the documented `exp((π/4) * (v12 + v∞3))` projective motor. Manifest witnesses sample-check the factored motor used for rendering against a local Taylor expansion of the whole documented exponential; stream seed placement, integration, camera, and stroke rendering remain approximate Makie-style matches. |
| `orbit-2`, `orbit-4` | Exact documented projective curves | Render `documentedProjectiveOrbit2Point` and `documentedProjectiveOrbit4Point` directly. Oracle tests and manifest witnesses sample-check the plotted paths against the documented `S"∞+++"` evaluators. The manifest also keeps the auxiliary CGA translation witnesses for the separate fast closed-form helper path. |

`lake exe oracletests` checks exact sample coordinates across the plotted
parameter range for the documented `S"∞+++"` projective formulas for `torus`,
`orbit-2`, and `orbit-4` against Grassmann.jl. Those oracle-backed evaluators
live in `Grassmann.JuliaExamples`; the same functions now feed the SVG paths for
those three examples.

The conformal `helix` path is checked separately because the local Grassmann.jl
checkout currently does not provide a stable direct oracle for the null-basis
`S"∞∅+++"` snippet. Lean renders the derived closed form and compares it against
the equivalent sparse CGA motor evaluator in both manifest witnesses and
property tests.

## 2026-06-05 Audit

The comparison harness was rerun from `Grassmann4` and covered all twelve
documented Julia plot images. The smoke gate passed with every rendered Lean and
Julia frame above the `1200` grayscale standard-deviation floor, every
normalized RMSE at or below `0.25`, all ten CGA orbit witnesses within `1e-6`
max absolute difference, all fifteen projective plot formula witnesses within
`1e-6` max absolute difference, all five conformal helix plot witnesses within
`1e-6` max absolute difference, and all ten projective stream-field witnesses
within `1e-6` max absolute difference.

The observed normalized RMSE values were:

| Example | Normalized RMSE |
| --- | ---: |
| `plane-1` | `0.109350` |
| `plane-2` | `0.121803` |
| `plane-3` | `0.111175` |
| `plane-4` | `0.105751` |
| `plane-5` | `0.121607` |
| `plane-6` | `0.129301` |
| `torus` | `0.105856` |
| `helix` | `0.092560` |
| `orbit-2` | `0.095822` |
| `orbit-4` | `0.112861` |
| `orb` | `0.153940` |
| `wave` | `0.124561` |

The visual gate is still a smoke test rather than a pixel oracle: Makie camera
framing, grid projection, antialiasing, and stroke alpha differ from the SVG
renderer. Exact pointwise parity is now claimed for the documented projective
`torus`, `orbit-2`, and `orbit-4` coordinate formulas sampled by the oracle and
manifest witnesses. The documented conformal `helix` is checked against the
sparse CGA motor evaluator. The documented projective `orb`/`wave` stream
fields are now generated from the same projective motor in Lean and checked
against a local Taylor expansion of the whole documented exponential; exact
Makie streamplot raster parity remains future work because the streamline
integrator, seed placement, camera, antialiasing, and stroke alpha still differ.

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
lake exe propertytests
lake exe oracletests
```

The generated browser comparison page contains `12` example sections: one Lean
SVG and one Julia/Makie reference PNG for each example.
The contact-sheet script additionally passed the automated coverage and visual
smoke checks for the same twelve examples, plus the CGA, projective plot,
conformal helix, and projective stream-field witness gates.

The Julia oracle suite checks exact `S"∞+++"` projective samples for `torus`,
`orbit-2`, and `orbit-4` across
`[-2π, -π, -1, -0.5, 0, 0.5, 1, π, 2π]`. It passed with `145/145` checks.
