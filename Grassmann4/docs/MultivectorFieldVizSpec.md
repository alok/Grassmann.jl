# Multivector Field InfoView Demo Specification

Status: implementation contract for ALOK-793  
Audience: SF Lean meetup, 15-minute live demonstration  
Primary claim: Lean is an ordinary programming language that can compute,
validate, serialize, and interactively display a geometric-algebra program.

## 1. Scope and claim boundary

The demo visualizes a small field of full `Cl(3, 0)` multivectors. Lean owns
the domain model, the geometric-algebra computation, sampling, validation, and
the complete JSON payload. A local ProofWidgets component owns only camera and
SVG presentation concerns.

This is a runtime-computation demo, not a theorem-proof demo. Float results are
ordinary machine computations. The talk must not describe a rendered frame as
a formally proved mathematical fact. The useful contrast is that the same Lean
source can contain executable code, tests, and proofs without changing
languages.

The demo is intentionally self-contained:

- no network requests;
- no CDN assets;
- no Three.js, Ganja.js, or LeanPlot runtime;
- no WebGL requirement;
- no JavaScript implementation of Clifford multiplication;
- no JavaScript resampling or interpolation between Lean-computed frames.

## 2. Lake-library boundaries

The outer repository Lake package is authoritative for distribution. The
nested `Grassmann4` Lake package mirrors its toolchain, mathlib pin, and public
library boundary because editors resolve a source file against the nearest
Lake workspace. The stale nested `Grassmann4/.git` metadata is not
authoritative.

Both Lake entry points expose five importable libraries. The outer
`lakefile.toml` uses the shared `Grassmann4` source directory; the nested
package uses that directory as its root:

| Lake library | Root module | Responsibility |
| --- | --- | --- |
| `Grassmann` | `Grassmann.lean` | Existing packed geometric-algebra runtime |
| `GrassmannReference` | `GrassmannReference.lean` | Opt-in dense representations and extended geometric-algebra API |
| `GrassmannFields` | `GrassmannFields.lean` | Pure field geometry, grade projection, sampling, validation, and example data |
| `GrassmannViz` | `GrassmannViz.lean` | ProofWidgets props and offline InfoView renderer |
| `GrassmannTests` | `GrassmannTests.lean` | Broad validation aggregate for repository and downstream smoke checks |

The intended module dependency graph is:

```text
Grassmann.MV
    |
    v
GrassmannFields.R3 -----> GrassmannFields.Examples.MixedRotor
    |                                  |
    +----------------------------------+
                                       v
                              GrassmannViz.Scene
                                       |
                                       v
                              GrassmannViz.InfoView
                                       |
                                       v
                           MultivectorFieldDemo.lean
```

`GrassmannFields` must not import ProofWidgets. `GrassmannViz` consumes only
semantic records exported by `GrassmannFields`; it must not inspect `DataArray`
or depend on the packed storage layout. Downstream users can therefore sample
fields without acquiring a UI abstraction, and can replace the renderer while
preserving the scene schema. `GrassmannReference` and `GrassmannTests` remain
opt-in so ordinary runtime users do not acquire dense models or validation
modules transitively.

The implementation must not modify `Grassmann/MV.lean` or
`RunPackedMVBench.lean`.

## 3. Public pure-data API

The field library exports JSON-independent values equivalent to the following
shapes (final names may include a namespace prefix):

```lean
structure Vec3 where
  x : Float
  y : Float
  z : Float

structure R3Grades where
  scalar : Float
  vector : Vec3
  bivectorNormal : Vec3
  pseudoscalar : Float

structure PlanarGrid where
  xMin : Float
  xMax : Float
  yMin : Float
  yMax : Float
  z : Float := 0.0
  xCount : Nat
  yCount : Nat

abbrev Field3 (M : Type) := Vec3 -> M

structure Sample3 where
  position : Vec3
  value : R3Grades

structure Frame3 where
  parameter : Float
  samples : Array Sample3
```

Sampling and scene construction return `Except String ...`; invalid values do
not silently reach the renderer. Types are public and documented so another
Lake package can construct its own `Field3`, `PlanarGrid`, and frames.

## 4. Exact `Cl(3, 0)` grade mapping

`MV R3 .full` coefficients use logical blade masks. The semantic adapter reads
only `MV.coeff`, never packed indices:

| Semantic component | Blade | Logical mask | Exported value |
| --- | ---: | ---: | ---: |
| scalar | `1` | `0` | `coeff 0` |
| vector x | `e1` | `1` | `coeff 1` |
| vector y | `e2` | `2` | `coeff 2` |
| vector z | `e3` | `4` | `coeff 4` |
| bivector normal x | `e23` | `6` | `coeff 6` |
| bivector normal y | `e31 = -e13` | `5` | `-coeff 5` |
| bivector normal z | `e12` | `3` | `coeff 3` |
| pseudoscalar | `e123` | `7` | `coeff 7` |

The bivector record is deliberately named `bivectorNormal`: its `(x, y, z)`
components are the dual plane normal in the right-handed `e1,e2,e3` basis.
This makes the renderer's oriented disk convention explicit and preserves the
existing `R3Utils` axis-to-plane convention
`nx*e23 - ny*e13 + nz*e12`.

The primary adapter accepts the library's packed full-storage runtime,
`MV R3 .full`. If a dense/reference adapter is supplied for tests, the packed
and reference adapters must agree coefficient-for-coefficient; reference data
is not the production source.

## 5. Demonstration field

Let

```text
p(x,y) = x e1 + y e2
v(x,y) = (-y + 0.35) e1 + x e2 + 0.25 e3
tau(x,y) = 0.20 sin(pi (x + y))
I = e123
F0(x,y) = v(x,y) + p(x,y) v(x,y) + tau(x,y) I
```

`p*v` is the geometric product. It contributes both a scalar dot part and a
bivector wedge part, so the one expression contains all four grades:

```text
scalar       = 0.35 x
vector       = (-y + 0.35, x, 0.25)
bivector     = (0.25 y) e23 + (0.25 x) e13
              + (x^2 + y^2 - 0.35 y) e12
pseudoscalar = 0.20 sin(pi (x + y))
```

For frame parameter `theta`, Lean constructs the unit rotor

```text
R(theta) = cos(theta/2) - sin(theta/2) e12
```

and computes

```text
Ftheta(x,y) = R(theta) F0(x,y) reverse(R(theta)).
```

This rotates every grade of the multivector value about the `e3` axis while
leaving the sample lattice fixed, making grade-preserving conjugation visible.
The checked-in demo uses a 5-by-5 grid and 24 precomputed frames over one turn.
The JavaScript slider selects one of those frames; it does not evaluate this
formula.

## 6. Renderer ownership and visual grammar

Lean sends a versioned scene with title, formula label, frames, initial frame,
and optional explanatory text. Each sample contains its exact Float position
and four semantic grade values.

The embedded React/SVG component may:

- project 3D points through a local orbit camera;
- depth-sort SVG glyph groups;
- map signed magnitudes to colors and clamped display sizes;
- respond to pointer drag, wheel zoom, reset, play/pause, slider, and grade
  visibility controls;
- display the selected sample's exact coefficients as provided by Lean.

It must not:

- manufacture coefficients or field samples;
- multiply, rotate, or otherwise transform multivectors;
- interpolate between adjacent frames;
- fetch code, fonts, data, or images;
- use `eval`, dynamic script injection, canvas, or WebGL.

The visual grammar is fixed:

| Grade | SVG glyph | Magnitude | Sign/orientation |
| --- | --- | --- | --- |
| 0 scalar | filled circle at the sample | radius | warm/cool color |
| 1 vector | shaft plus arrow head | shaft length | 3D direction |
| 2 bivector | translucent oriented ellipse/disk plus normal needle | disk radius | dual-normal direction and sign color |
| 3 pseudoscalar | translucent halo/ring | radius and stroke width | warm/cool color |

Near-zero values are omitted using one documented view-layer epsilon. Display
lengths are clamped so one outlier cannot make the field illegible; the exact
unclamped values remain available in the inspector.

## 7. Validation contract

Lean rejects a scene before it is passed to `Html.ofComponent` when any of the
following holds:

- a grid axis has fewer than two samples;
- a grid axis is inverted or has zero width;
- a grid endpoint or fixed `z` is NaN or infinite;
- the sample count exceeds the documented stage-safe cap;
- a frame parameter, sample position, or grade coefficient is NaN or infinite;
- the frame array is empty;
- frames disagree on sample count or sample positions;
- `initialFrame` is outside the frame array;
- a scene schema version is unsupported.

The default cap is small enough for an InfoView demo (at most 4,096 samples per
frame and at most 240 frames). Validation errors are human-readable and name
the rejected field. Error HTML is local and explicit rather than a blank panel.

## 8. Stage choreography

The 15-minute route is:

1. **0:00-2:00 — thesis.** Open the demo module and state the claim boundary:
   ordinary Float computation in Lean, rendered in the editor.
2. **2:00-5:00 — ordinary data and functions.** Show `Vec3`, `PlanarGrid`, the
   reusable `Field3` sampler, and an `#eval` summary. Emphasize that this is a
   Lake library API rather than a one-off generated HTML string.
3. **5:00-8:00 — geometric algebra.** Show `F0` and the rotor sandwich. Point at
   the grade mapping test, especially `e31 = -e13`.
4. **8:00-11:30 — InfoView reveal.** Place the cursor on the prepared `#html`
   command. Drag, zoom, toggle each grade, and click one glyph to inspect the
   Lean-computed coefficients.
5. **11:30-13:30 — one safe live edit.** Change the pseudoscalar amplitude from
   `0.20` to `0.35` (or the grid from 5-by-5 to 6-by-6), wait for elaboration,
   and show the updated halos. Revert using the editor rather than Git.
6. **13:30-15:00 — close.** Scrub the rotor frames and summarize ownership:
   Lean computes/validates; a tiny local SVG view presents.

Stage preflight keeps the demo file and InfoView already elaborated, disables
network access, runs the source-freshness and static-offline checks, and leaves
the editor zoomed so the title and controls are readable from the back of the
room.

Fallback order, without changing the talk's claim, is:

1. use the already-rendered InfoView if a fresh elaboration is slow;
2. use the non-interactive fallback SVG generated from the same default Lean
   scene if the editor webview resets;
3. show the executable scene summary and grade-mapping tests if all webview
   rendering is unavailable.

The fallback SVG must be checked in under `Grassmann4/docs/` and must display
the same four-grade legend. It is a presentation backup, not independent
evidence that the live widget works.

## 9. Validation and test plan

Focused Lean tests cover:

- each of the eight grade-map coefficients;
- the mixed anchor
  `2 + 3e1 + 4e2 + 5e3 + 13e12 + 11e13 + 7e23 + 17e123`, whose exported
  record is scalar `2`, vector `(3,4,5)`, bivector normal `(7,-11,13)`, and
  pseudoscalar `17`;
- packed/runtime values against an independently constructed expected record;
- 5-by-5 sample count and deterministic row-major order;
- invalid, non-finite, and oversized grid rejection;
- frame count, shared sample positions, and finite coefficients;
- JSON round-trip for widget props;
- out-of-range initial-frame rejection.

Renderer guards cover:

- JavaScript syntax with `node --check`;
- absence of URL schemes, `fetch`, `XMLHttpRequest`, WebSocket, Three.js,
  Ganja.js, LeanPlot, WebGL, and dynamic `eval`;
- byte-for-byte equality between the checked-in JavaScript and the source
  embedded by `include_str` in the built OLean.

## 10. Acceptance criteria

The milestone is complete when all of the following are true:

- `lake build Grassmann GrassmannReference GrassmannFields GrassmannViz
  GrassmannTests` succeeds from both the repository root and `Grassmann4`;
- `lake build GrassmannFields` succeeds;
- `lake build GrassmannViz` succeeds;
- the focused field/scene test executable succeeds;
- from `Grassmann4`, `lake env lean MultivectorFieldDemo.lean` succeeds and a
  compatible editor's Lean LSP displays the widget from its `#html` command;
- the renderer-source freshness check succeeds after a clean widget rebuild;
- JavaScript syntax and offline static guards succeed;
- a separate downstream Lake package imports `Grassmann`,
  `GrassmannReference`, `GrassmannFields`, `GrassmannViz`, and `GrassmannTests`
  without private-path imports;
- the default scene contains 24 frames of 25 finite samples and every frame has
  identical positions;
- grade toggles, orbit drag, wheel zoom, reset, frame scrubber, playback, and
  sample inspection work without network access;
- a checked-in fallback SVG is legible and names all four grades;
- no unrelated source files, especially `Grassmann/MV.lean` and
  `RunPackedMVBench.lean`, are changed.
