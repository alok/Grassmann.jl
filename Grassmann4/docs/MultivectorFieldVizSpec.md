# Multivector Field InfoView Demo Specification

Status: implementation contract for ALOK-793
Audience: SF Lean meetup, 15-minute live demonstration
Primary claim: Lean is an ordinary programming language that can compute,
validate, serialize, and interactively display a geometric-algebra program.

## 1. Scope and claim boundary

The demo visualizes a small field of full `Cl(3, 0)` multivectors. Lean owns
the domain model, geometric-algebra computation, sampling, validation, and the
complete serialized props. A local ProofWidgets component owns view-layer
presentation and interaction: guide inference for the validated lattice,
display normalization, glyph geometry, selection, camera projection,
depth-sorting, and SVG painting.

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

This rotates the vector and bivector grades about the `e3` axis while leaving
the scalar, pseudoscalar, and sample lattice invariant. The result makes
grade-preserving conjugation visible.
The checked-in demo uses a 5-by-5 grid and 24 precomputed frames over one turn.
The JavaScript slider selects one of those frames; it does not evaluate this
formula.

## 6. Renderer ownership and visual grammar

Lean sends a versioned scene with title, formula, generic frame-parameter label,
frames, initial frame, initial selected sample, and optional explanatory text.
Each sample contains its serialized Float position and four semantic grade
values. The default meetup scene selects off-center sample 9, whose four grades
are nonzero, rather than asking JavaScript to guess an interesting sample.

The embedded React/SVG component may:

- infer rectangular guide lines from the validated planar lattice;
- project 3D points through a local orbit camera;
- depth-sort SVG glyph groups;
- derive tangent bases and glyph geometry from semantic grade records;
- normalize each frame for clamped display sizes and map scalar/pseudoscalar
  signs to colors;
- respond to pointer drag, wheel zoom, reset, play/pause, slider, and grade
  visibility controls;
- display the selected sample's serialized coefficients as provided by Lean.

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
| 2 bivector | translucent oriented ellipse/disk plus normal needle | disk radius | dual-normal direction; fixed orange grade color |
| 3 pseudoscalar | translucent halo/ring | radius and stroke width | warm/cool color |

Near-zero values are omitted using one documented view-layer epsilon. Display
lengths are clamped so one outlier cannot make the field illegible; the
unclamped serialized values remain available in the inspector.

## 7. Validation contract

Lean rejects a scene before it is passed to `Html.ofComponent` when any of the
following holds:

- a grid axis has fewer than two samples;
- a grid axis is inverted or has zero width;
- a grid endpoint or fixed `z` is NaN or infinite;
- the per-frame sample count exceeds its hard safety ceiling;
- total samples across all frames exceed 8,192;
- a frame parameter, sample position, or grade coefficient is NaN or infinite;
- the frame array is empty;
- frames disagree on sample count or sample positions;
- the first frame is not one complete rectangular lattice at a shared `z`;
- the generic frame-parameter label is empty;
- `initialFrame` is outside the frame array;
- `initialSample` is outside the selected frame's sample array;
- a scene schema version is unsupported.

These are hard denial-of-service ceilings, not recommended display sizes: at
most 4,096 samples per frame, 240 frames, and 8,192 total serialized samples.
The rehearsed scene is intentionally much smaller at 24 frames by 25 samples.
Validation errors are human-readable and name the rejected field. Error HTML
is local and explicit rather than a blank panel.

## 8. Stage choreography

The talk uses a rehearsed 12-minute core and reserves the last three minutes
for recovery or questions:

1. **0:00-0:55 — cold-open visual.** State the Float/not-proof boundary and
   orbit once from empty SVG background.
2. **0:55-2:55 — ordinary data and loops.** Show `Vec3`, `PlanarGrid`, and the
   reusable `Field3` sampler. Keep the downstream consumer for questions.
3. **2:55-4:25 — geometric algebra.** Show `F0` and the rotor sandwich,
   including the `e31 = -e13` semantic mapping.
4. **4:25-5:15 — typed presentation boundary.** Show the scene props and
   validation of both initial indices.
5. **5:15-7:35 — focused interaction.** Use the rich selected sample, toggle
   only grades two and three, play/pause/scrub, orbit, and restore every grade.
6. **7:35-9:20 — one safe live edit.** Change the grid from 5-by-5 to 6-by-5,
   wait for elaboration, and leave the successful 30-sample view on screen.
7. **9:20-12:00 — ownership and close.** Briefly show the three imports, then
   return to and close on the visual. Revert to 5-by-5 after the talk.
8. **12:00-15:00 — recovery or questions.** Use the consumer and tests only if
   a question calls for them.

Stage preflight keeps the demo file and InfoView already elaborated, runs the
source-freshness and static-offline checks, and rehearses once with network
access disabled. It leaves the editor zoomed so the title and controls are
readable from the back of the room.

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
- JSON round-trip for widget props within `1e-5`, because core `Float` JSON
  uses a decimal `Float.toString` representation rather than bit encoding;
- rejection of nonplanar and incomplete rectangular scenes;
- a quarter-turn vector and bivector-normal rotation anchor;
- out-of-range initial-frame rejection.

Renderer guards cover:

- JavaScript syntax with `node --check`;
- absence of URL schemes, `fetch`, `XMLHttpRequest`, WebSocket, Three.js,
  Ganja.js, LeanPlot, WebGL, and dynamic `eval`;
- a Lake input-file dependency from `GrassmannViz` to the JavaScript embedded
  by `include_str`, so renderer edits invalidate the owning OLean;
- byte-for-byte equality between the checked-in JavaScript and the source
  embedded by `include_str` in the built OLean;
- stable `data-region`, `data-grade`, `data-glyph`, and `data-sample-index`
  attributes for interaction and layout QA.

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
