# SF Lean: Lean Is an Ordinary Programming Language

Format: 15 minutes, live demo

Stage anchor: `Grassmann4/MultivectorFieldDemo.lean`

Static backup: `Grassmann4/docs/MultivectorFieldFallback.svg`

## One-sentence thesis

Here Lean is the ordinary programming language that represents, computes,
validates, tests, serializes, and displays a rotating Clifford-algebra field
inside its editor.

This is an executable `Float` demonstration, not a formal proof. Say that once
near the beginning and once in the closing ownership summary.

## Preflight before leaving for the meetup

From the authoritative outer repository root:

```bash
Grassmann4/scripts/multivector_meetup_preflight.sh
```

The script deliberately enters the portable nested `Grassmann4` package—the
same package root that Cursor selects for these files. Its final line must
begin with `PASS`. It builds all five public Lake roots—`Grassmann`,
`GrassmannReference`, `GrassmannFields`, `GrassmannViz`, and `GrassmannTests`—
then checks grade/rotation and validation tests, a stage-root consumer module,
JavaScript syntax and the
offline policy, embedded-source freshness, generated SVG freshness, and the
actual `#html` stage file.

Then prepare the editor:

1. Dismiss any Cursor update or notification toast and close unrelated side
   panels. Then open these tabs in order: `GrassmannFields/R3.lean`,
   `GrassmannFields/Examples/MixedRotor.lean`, and
   `MultivectorFieldDemo.lean`.
2. Put the cursor on the final `#html` line and wait for the InfoView to show
   the title, four grade buttons, field, inspector, and frame slider.
   If Cursor says that imports are out of date after the preflight rebuild,
   click its `Restart File` button once and wait for this view; do not reload
   the whole editor.
3. Drag the empty SVG background, wheel, click a sample, toggle each grade,
   press Play, pause, and scrub. Restore all four grade toggles before leaving
   the rehearsal view.
4. Set the editor font to 18 px. Make the InfoView at least 60 percent of the
   window and confirm title, controls, field, and inspector are readable.
5. Confirm the InfoView is updating rather than paused or pinned. Moving
   between `#eval` and `#html` must change the displayed output.
6. Turn networking off and repeat the reveal. Nothing in the demo uses it.
7. Open `docs/MultivectorFieldFallback.svg` in a browser tab or Preview, fit it
   to the window, and leave it available behind Cursor.

Do not update dependencies, rebuild caches, or switch toolchains on the venue
network. The preflight materializes the local `.olean` files that the editor
and direct Lean checks need.

## The 12-minute core, with 3 minutes of recovery or questions

### 0:00-0:55 — cold-open on the destination

Start on `MultivectorFieldDemo.lean`, with the visualization already visible.
Say:

> This is a field of full three-dimensional multivectors. Lean computed all
> 600 multivector samples before this local SVG component received them. It is
> ordinary floating-point program output, not a theorem.

Point at the badges: 24 Lean frames and 25 samples. The inspector opens on
sample 9, an off-center value with all four grades nonzero. Drag once on empty
SVG background—not on a glyph—so the audience immediately understands that
the InfoView is the output surface.

### 0:55-2:55 — ordinary types, loops, and errors

Switch to `GrassmannFields/R3.lean`. Show only:

- `Vec3`, `R3Grades`, and `Field3`;
- `PlanarGrid.points` as an ordinary deterministic loop;
- `samplePlanarWith` returning `Except String` and rejecting non-finite data.

The useful line is: “Nothing here knows about widgets. Another Lake package
can import this library and sample its own field.” The downstream consumer is
available for questions; do not spend the scripted core opening another file.

### 2:55-4:25 — one geometric product gives four visible grades

Switch to `GrassmannFields/Examples/MixedRotor.lean`. Walk through:

```text
F0(p) = v(p) + p*v(p) + tau(p) I
Ftheta(p) = R(theta) F0(p) reverse(R(theta))
```

`p*v` is the geometric product, so it contributes both scalar and bivector
parts. `v` supplies grade one and `tau I` supplies grade three. The rotor
sandwich uses the production packed `MV R3 .full` runtime: vector and bivector
grades rotate, while scalar and pseudoscalar grades stay invariant. Keep the
explanation to those two ideas; blade-mask detail is available for questions.

If you show the semantic adapter, point out its one non-obvious convention:
the displayed bivector normal is `(e23, e31, e12)`, so `e31 = -e13`.

### 4:25-5:15 — show the typed presentation boundary

Open `GrassmannViz/Scene.lean` only long enough to show
`MultivectorFieldProps`, `initialFrame`, `initialSample`, and `validate`.
Say: “The visual receives a versioned value that Lean has already checked.”
The opening sample is data, not a JavaScript guess; invalid frame or sample
indices are rejected before rendering.

### 5:15-7:35 — make the field legible

Return to the `#html` line:

1. Point at the already-selected rich sample and its four serialized grade
   rows.
2. Toggle grade 2 off and on: orange oriented disks plus dual-normal needles.
3. Toggle grade 3 off and on: signed pseudoscalar halos.
4. Press Play, pause, and scrub once.
5. Drag empty SVG background to orbit and wheel once to zoom.
6. Confirm all four grade buttons are on before the live edit.

Narrate ownership while interacting: Lean does the Clifford products, rotor
sandwiches, sampling, and validation. The component infers guide lines from
the validated rectangular lattice, normalizes display scales, constructs disk
and arrow geometry, projects, depth-sorts, colors, and paints SVG. It never
interpolates frames or computes a coefficient.

### 7:35-9:20 — one safe live edit

In `MultivectorFieldDemo.lean`, change only:

```lean
xCount := 5
```

to:

```lean
xCount := 6
```

Press Escape to dismiss any inline completion, then put the cursor back on the
`#html` line. The summary changes from 25 to 30 samples per frame and the
InfoView gains one column. Say: “That changed an ordinary input value; Lean
reran the program, revalidated 720 multivectors, serialized them, and refreshed
its own editor view.” Leave the successful 6-by-5 visualization displayed;
do not spend a second compilation reverting it on stage.

Apply a hard five-second rule. If the new 30-sample badge has not appeared in
five seconds, undo once and put the cursor on `#html`. If that does not restore
the rehearsed view immediately, switch to the pre-opened fallback. Do not
diagnose the language server, reload the editor, or attempt a second edit on
stage.

### 9:20-12:00 — close on the visual and the reusable split

Briefly show the three public layers behind the stage program. The tiny stage
anchor imports only the `GrassmannViz` facade, which follows this dependency
chain; the package also exposes `GrassmannReference` and `GrassmannTests` for
opt-in reference and test APIs:

```lean
import Grassmann       -- packed Clifford-algebra runtime
import GrassmannFields -- pure field and semantic-grade API
import GrassmannViz    -- validated offline InfoView presentation
```

Then return to the 6-by-5 visual and close there:

> The point is not that Lean has a special Clifford-algebra widget. The point
> is that Lean is the language of the data model, numerical program, tests,
> validation boundary, and editor extension—and those are ordinary libraries.

Use 12:00-15:00 for questions. The downstream consumer, grade-mapping test,
and fallback are ready if a question calls for them; otherwise keep the final
visual on screen.

After the talk, change `xCount := 6` back to `xCount := 5` and save. This is a
post-talk cleanup step, not part of the timed demo.

## Five-second recovery ladder

Use the first step that restores momentum; do not debug in front of the room.

1. **Visualization stale after the live edit:** undo, save, and put the cursor
   back on `#html`.
2. **InfoView pane disappeared:** run Command Palette →
   `Lean 4: InfoView: Toggle InfoView`, then click `#html` once. If it is not
   visible immediately, stop there.
3. **InfoView blank or editor webview unhappy:** point at the adjacent `#eval`
   result. It still reports schema, frames, samples, and the total number of
   Lean-computed values.
4. **No interactive view after five seconds:** switch to the already-open
   `MultivectorFieldFallback.svg`. It was generated from the same default Lean
   scene and shows all four grades and the ownership boundary.
5. **Editor itself is unusable:** use the fallback SVG for the visual story,
   read the two formulas from this runbook, and skip the live edit.

The fallback is intentionally static. Do not call it a screenshot of the
widget; it is a separate Lean SVG renderer over the same validated scene.

## Claims to keep precise

- The numbers are Lean `Float` runtime evidence, not proved real-number facts.
- Lean computes all field samples and all 24 rotor frames.
- Rotor conjugation rotates vector and bivector grades; scalar and
  pseudoscalar grades are invariant.
- JSON serialization prints finite decimal values; the inspector shows those
  serialized Lean-provided coefficients, not bit-level `Float` encodings.
- JavaScript is a local view layer. It does not perform Clifford multiplication,
  resampling, rotation, or interpolation.
- The scene schema accepts complete rectangular lattices at one shared `z`;
  the guide grid is not inferred for arbitrary point clouds.
- The demo makes no network request and needs no CDN, Ganja.js, Three.js,
  LeanPlot, canvas, or WebGL.
- `GrassmannFields` has no ProofWidgets dependency; consumers that only need
  field sampling do not import the visualization layer.

## Exact rebuild command if the renderer freshness check fails

From the nested `Grassmann4` package root:

```bash
LAKE_ARTIFACT_CACHE=false lake build +GrassmannViz.InfoView
lake env lean MultivectorWidgetCheck.lean
```

`GrassmannViz` declares the JavaScript as a Lake input, so changing it
invalidates the module containing `include_str`. The final check compares the
source file with the string in the rebuilt OLean byte-for-byte.
