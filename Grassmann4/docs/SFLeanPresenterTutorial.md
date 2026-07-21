# Presenter tutorial: Lean’s unfair advantage

This is the “understand what was built” guide, not the on-stage script. Read it
once end-to-end, then present from the [one-screen cue card](../cue-card/).
Source links below are replaced with immutable commit links when the public site
is built.

## The talk in one paragraph

Scarf’s recent [Haskell-to-Python account](https://avi.press/posts/2026-07-10-after-7-years-in-production-scarf-has-reluctantly-moved-away-from-haskell.html)
is a 30-second hook. It is not the argument. Haskell’s reliability, types, and
performance held up. Scarf moved new API work to Python because the development
loop became expensive. Then leave Scarf behind.

The central comparison is a choice of direction. For a conventional
application, use Python. If you choose type-driven functional programming for
mathematical software, go farther than Haskell. Lean is an
[ordinary functional programming language](https://lean-lang.org/functional_programming_in_lean/Introduction/)
with dependent types and an integrated prover. In this program, the types carry
dimension, metric signature, and parity through the multilinear algebra. A
proof belongs in the development loop only when later code can reuse the fact.
Lean also exposes elaborated program state to `#check`, `#eval`, InfoView, and
metaprograms. AI can use the same source, types, diagnostics, values, and goals.
Together these tools can shorten the edit-to-feedback loop.
The demo starts with records, functions, arrays, and explicit errors. It then
sends the output of a packed multivector program to an editor view.

Your exact closing claim is:

> The point is not to prove everything. The point is to make the next change
> easier.

## What now exists

There are four deliverables, all built from one source tree:

1. A Verso slide deck whose Lean code block is checked while the deck compiles.
2. A 47-line beginner demo with one safe edit and an explicit failure value.
3. An InfoView multivector-field demo, plus the same React/SVG component mounted
   as a standalone public browser demo from Lean-generated JSON.
4. This tutorial, a one-screen cue card, and a static SVG parachute for a dead
   editor or webview.

The reusable part remains three actual Lake libraries:

```lean
import Grassmann       -- packed Clifford runtime
import GrassmannFields -- renderer-neutral fields, grids, sampling, validation
import GrassmannViz    -- versioned scene plus opt-in InfoView component
```

The Verso dependencies and React package do **not** enter those library import
closures. They live in the nested `Grassmann4/slides` presentation package.

## How the audience uses the website

The opening slide contains a QR code and the short URL
`alok.github.io/talks/lean-unfair-advantage/`. Tell the audience:

> Open the address on your phone. Swipe through the slides, or tap Demo. In the
> demo, drag an empty part of the field to orbit it. Tap a sample to inspect its
> coefficients. Toggle grade 2, scrub the timeline, or tap Play. The Code links
> open the Lean source.

The site is a companion to the live editor. It is not an online Lean editor.
Lean generated and validated the complete scene before deployment. The browser
draws the values and handles the controls. The same renderer also runs in
InfoView during the live demo.

## The architecture to keep in your head

```text
ordinary Lean values
    ↓
packed Clifford field or semantic teaching record
    ↓
validated Array of samples and frames
    ↓
typed, versioned scene props
    ↓
validated JSON data
    ↓
local React/SVG view: glyphs, camera, animation, interaction
```

That diagram encodes the most important claim boundary:

- **Lean computes:** positions, Clifford products, rotor actions, all grade
  coefficients, 24 frames, validation, and serialization.
- **JavaScript presents:** display normalization, glyph geometry, camera
  projection, depth sorting, SVG painting, and interaction.
- **This visual uses `Float`:** tests cover its numerical behavior. It is not a
  theorem about exact real arithmetic.

Do not say “Lean does the 3D rendering.” Say “Lean computes and validates the
field; the local component turns those values into an interactive SVG.”

## Part I — the ordinary program

Open [`OrdinaryProgrammingDemo.lean`, lines 15–47](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L15-L47).
It imports only `GrassmannFields`, not the visualization package.

### A record value

[`tinyGrid`, lines 15–23](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L15-L23)
is an ordinary configuration record. It has floating-point bounds, a fixed
plane, and natural-number dimensions. `#eval tinyGrid` evaluates and prints it.

The only on-stage edit is line 21:

```lean
xCount := 3  -- change only this 3 to 4
```

Why this edit is safe: the sample count is simply `xCount * yCount`. The initial
3×3 grid produces `Except.ok 9`; the 4×3 grid produces `Except.ok 12`. Undo it
immediately after showing 12, so the checkout returns to the rehearsed state.

### A normal function

[`swirlField`, lines 28–33](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L28-L33)
has the type `Vec3 → R3Grades`. Explain that notation plainly: “give it a point;
it returns one value with four named parts.” The parts are:

- grade 0, `scalar`: a signed number;
- grade 1, `vector`: an arrow;
- grade 2, `bivectorNormal`: an oriented plane, represented by its dual normal;
- grade 3, `pseudoscalar`: an oriented volume element.

`#check swirlField` shows the type without running the function. The next
`#eval` runs it at one concrete point. This is useful pedagogically: the editor
is both a type-oriented explanation surface and a normal REPL-like evaluator.

### An array computation with explicit errors

[`sampleCount`, lines 40–47](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L40-L47)
uses `do` notation, calls a library function returning an array, and returns its
size inside `Except String Nat`.

Read that return type aloud as: “either a human-readable error string, or a
natural-number result.” The last `#eval` changes `xCount` to 1 and produces:

```text
Except.error "grid.xCount must be at least 2"
```

This is not an uncaught exception and not a proof. It is ordinary typed error
handling. That modesty is part of the talk’s credibility.

## Part II — what the field library contributes

The teaching file is small because it consumes a real library. The library’s
semantic boundary begins with [`Vec3` and `R3Grades`](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L15-L76).

The important design choice is that a renderer never sees internal packed blade
indices. [`R3Grades`, lines 55–61](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L55-L61)
names the four semantic grades. [`R3Grades.ofMV`, lines 65–71](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L65-L71)
is the adapter from packed storage to those meanings.

The other key definitions are:

- [`PlanarGrid`, lines 81–89](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L81-L89),
  the reusable grid record;
- [`Field3`, line 92](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L92),
  literally the ordinary function type `Vec3 → M`;
- [`Sample3` and `Frame3`, lines 95–104](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L95-L104),
  renderer-neutral sampled data;
- [`PlanarGrid.validate`, lines 120–135](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L120-L135),
  finite bounds, minimum dimensions, increasing ranges, and a size ceiling;
- [`PlanarGrid.points`, lines 142–153](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L142-L153),
  deterministic row-major point generation;
- [`samplePlanarWith`, lines 156–164](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L156-L164),
  generic sampling plus finite-coefficient validation;
- the semantic and packed entry points at
  [`samplePlanar` and `samplePlanarMV`, lines 167–174](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L167-L174).

The reusable pattern is worth understanding: an ordinary field can already
return `R3Grades`; a Clifford field can return a packed `MV`; both enter one
sampling pipeline through an adapter to semantic grades.

## Part III — where dependent types become concrete

This section shows which facts are in types and which facts have proofs.

[`Signature (n : ℕ)`, lines 39–44](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/Manifold.lean#L39-L44)
contains `BitVec n` metric data. The dimension is not a comment or a runtime
integer floating beside the value; the metric is indexed by it. Euclidean
three-space is [`R3 : Signature 3`, line 120](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/Manifold.lean#L117-L121).

[`Parity`, lines 27–42](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/MV.lean#L27-L42)
is another type-level index: even grades, odd grades, or a full mixed value.
[`MV sig p`, lines 81–93](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/MV.lean#L81-L93)
is the central multivector type. Most importantly, the multiplication instance
computes the output parity in its result type:

[`HMul (MV sig p1) (MV sig p2) (MV sig (p1 * p2))`, lines 1591–1594](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/MV.lean#L1591-L1594).

The sentence to say is:

> Multiplying even by odd does not set a runtime flag. The result type is
> computed as odd.

There are also ordinary theorems adjacent to the runtime representation. The
packed-index decoder is at
[`unpackIdxValid`, lines 154–166](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/MV.lean#L154-L166),
and [`unpackIdxValid_lt`, lines 168–201](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/MV.lean#L168-L201)
proves that any packed rank inside its physical buffer decodes to a valid dense
blade mask.

Be precise: not every invariant is dependent. Grid and scene checks return
`Except` at runtime. The physical `DataArray` length is protected through
checked and private construction boundaries, not represented as a dependent
vector. Lean lets one codebase combine these confidence levels without
pretending they are the same thing.

## Part IV — the multivector field

The algebra-heavy example is compact, but keep it verbal during the timed core.
It is excellent Q&A material.

[`MixedRotor.lean`, lines 19–44](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L19-L44)
defines:

1. a position vector `p`;
2. a swirling velocity vector `v(p)`;
3. a varying pseudoscalar term `τ(p)I`;
4. the base field `v(p) + p*v(p) + τ(p)I`;
5. an even rotor `Rθ`;
6. the rotated field `Rθ F(p) reverse(Rθ)`.

The geometric product is the `*` on
[`MixedRotor.lean`, line 34](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L30-L35).
For two vectors, it contributes a scalar inner-product part and a bivector
oriented-plane part. Adding `v` and `τI` makes all four grades available.

The rotor sandwich is one line at
[`MixedRotor.lean`, lines 43–44](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L43-L44).
Its general library type says an even rotor acting on `MV sig p` returns the same
parity `p`: [`mvSandwich`, lines 1670–1685](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/Grassmann/MV.lean#L1670-L1685).

The scene uses a 5×5 grid and 24 frames:

- [`defaultGrid`, lines 46–56](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L46-L56);
- [`defaultFrameCount`, line 59](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L58-L59);
- [`buildFrame`, lines 70–75](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L70-L75);
- [`buildFrames`, lines 77–93](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/Examples/MixedRotor.lean#L77-L93).

That is where “600 Lean-computed multivectors” comes from: 24 × 25. It is a
different demo from the 3×3 teaching grid; the live 3→4 edit yields 12, not 600.

## Part V — the versioned scene and exact wire boundary

The visualization library begins with a normal JSON-facing data model.
[`Scene.lean`, lines 16–34](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/Scene.lean#L16-L34)
derives JSON encoders for renderer-neutral records, declares schema version 2,
and defines complete widget props.

[`MultivectorFieldProps.validate`, lines 56–71](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/Scene.lean#L56-L71)
checks schema, labels, frame validity, rectangular-lattice shape, and initial
selection bounds.

The subtle part is
[`prepareForWidget`, lines 80–92](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/Scene.lean#L80-L92).
Lean validates once, encodes and decodes through the same decimal JSON boundary
the widget will receive, and validates again. Why? Two distinct finite source
`Float` coordinates can round to one wire coordinate. Source-valid data could
otherwise become an overlapping lattice after serialization.

This is runtime validation, not a theorem. It is still valuable: the browser
never receives a malformed scene from this constructor path.

The final scene constructor is
[`defaultScene`, lines 121–131](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/Scene.lean#L121-L131),
and the stage-safe textual summary is
[`MultivectorFieldProps.summary`, lines 134–139](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/Scene.lean#L134-L139).

## Part VI — InfoView ownership

The editor bridge is intentionally tiny. At
[`InfoView.lean`, lines 16–19](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/InfoView.lean#L16-L19),
`@[widget_module]` declares a local component and `include_str` embeds its
JavaScript at build time. At
[`InfoView.lean`, lines 32–42](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/InfoView.lean#L32-L42),
Lean either constructs the component from validated props or renders an explicit
local error panel.

The stage entry points are only:

- [`#eval`, line 24](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/MultivectorFieldDemo.lean#L21-L26),
  which prints the executable summary;
- [`#html`, line 26](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/MultivectorFieldDemo.lean#L24-L26),
  which asks the InfoView to display the component produced from the Lean value.

The React source begins at
[`multivectorField.js`, line 1](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L1).
Its responsibilities are visible in the source:

- overflow-resistant display direction at
  [lines 13–39](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L13-L39);
- lattice fitting at
  [lines 69–98](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L69-L98);
- camera projection at
  [lines 100–117](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L100-L117);
- four-grade glyph construction at
  [lines 218–347](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L218-L347);
- component state at
  [lines 405–425](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L405-L425);
- orbit and zoom at
  [lines 447–479](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L447-L479);
- controls, SVG, inspector, and timeline at
  [lines 542–637](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L542-L637).

The source states its own boundary at
[`multivectorField.js`, line 641](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/multivectorField.js#L641):
Lean supplied validated values; the view infers guides, normalizes display
scales, constructs glyphs, projects, depth-sorts, and paints them.

## Part VII — how the public browser demo stays honest

The InfoView supplies React automatically. A normal web page does not, so the
public site has a tiny browser entrypoint that bundles React and mounts the
**same** component. It does not duplicate the renderer.

Lean exports the data through
[`ExportMultivectorScene.lean`, lines 16–30](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/ExportMultivectorScene.lean#L16-L30):

1. compute `defaultScene`;
2. run `prepareForWidget`—including the JSON round-trip validation;
3. write the resulting `ToJson` value;
4. print the same 24×25 summary.

The browser entry then fetches `scene.json`, checks schema 2 and nonempty frame
shape, and passes the props to `MultivectorField`. Those browser checks are a
defensive loading guard; the authoritative computation and validation already
happened in Lean.

This gives you three related visual surfaces:

- **InfoView:** the editor-native live demo and the point of the talk;
- **standalone browser:** the same component and Lean-generated scene, useful to
  the audience after the talk;
- **static fallback SVG:** a separate Lean renderer over the first validated
  frame, with no interaction.

The fallback is generated at
[`FallbackSvg.lean`, lines 199–235](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannViz/FallbackSvg.lean#L199-L235)
and checked byte-for-byte against the committed artifact by
[`MultivectorFallbackCheck.lean`, lines 5–16](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/MultivectorFallbackCheck.lean#L5-L16).

## Part VIII — why Verso matters here

The slide deck is a Lean package, not a pile of screenshots.
[`SFLeanTalk.lean`, lines 9–210](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/slides/SFLeanTalk.lean#L9-L210)
contains ordinary prose, raw HTML layouts, speaker notes, fragments, and Lean
code blocks. The [VersoSlides](https://github.com/leanprover/verso-slides)
executable compiles that document into a fully local Reveal.js deck.
The deck vendors Reveal, KaTeX, fonts, highlighting, and its code-info panel, so
presentation does not depend on a CDN.

The deck deliberately uses Lean 4.32 in a nested package because the reusable
Grassmann libraries support their existing Lean 4.27 workspace. Presentation
dependencies therefore cannot leak into the consumer-facing library graph.
The isolated output configuration is visible in
[`Main.lean`, lines 8–30](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/slides/Main.lean#L8-L30).

When you see the miniature `PlanarGrid` on slide 5, call it what it is: a
typechecked teaching example inside the deck. The real complete grid begins at
[`R3.lean`, line 81](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/GrassmannFields/R3.lean#L81-L89).

## The exact 12-minute choreography

### 0:00–3:15 — deck

1. **Title:** record → function → error → array → InfoView.
2. **Scarf:** one recent Haskell exit. Give the facts in 30 seconds, then leave it.
3. **Direction:** use Python for the conventional route; if types are the tool,
   go farther with Lean.
4. **Programming tools:** routine Lean code plus `MV signature parity`.
5. **Core values:** hover the four small data types in the Verso code panel.
6. **Checked code:** one record, `Except`, and two `#eval`s; Lean compiles the
   slide source.

### 3:15–5:45 — ordinary Cursor demo

Follow `OrdinaryProgrammingDemo.lean` top to bottom. Show the grid, function,
sample count, 9→12 edit, immediate undo, and invalid-grid error. If anything
takes more than five seconds to update, narrate the expected result and move on.

### 5:45–6:15 — verbal bridge only

Say:

> The teaching field returns a named grade record. The visual returns a packed
> multivector. Its type records the dimension, metric signature, and parity. The
> grid, function, validation, and array shape stay the same.

Do not open `MixedRotor.lean` in the timed core. It is Q&A material.

### 6:15–9:15 — InfoView

Show the summary first: 24 frames, 25 samples per frame, 600 Lean-computed
multivectors. Say, “The animation uses floating-point computation. It is not a
theorem about real numbers.” Then perform only:

1. grade 2 off and on;
2. Play, then Pause;
3. one empty-background drag;
4. Reset view;
5. point at the already-selected coefficient inspector.

The rehearsal tests wheel zoom, grade 3, and scrubbing too; the talk does not
need every motor action.

### 9:15–12:00 — deck and stop

Explain the three libraries and the ownership boundary. Then show the four
places that remove repeated work: `MV sig p`, computed output parity, generic
fields, and one reusable packed-index lemma. Stop at 12 minutes. Use the
remaining three minutes for questions.

## Likely questions and short answers

### “Is Lean really a general-purpose language?”

Yes: this demo uses ordinary strict functional code, mutable-array-style loops
inside `do`, native `Float` computation, `Except`, IO executables, JSON, Lake
libraries, and an editor component. The more interesting question is ecosystem
and ergonomics, not whether the language can execute programs.

### “Why is this easier than Haskell here?”

Do not make a universal claim. In this program, `MV sig p` carries the
signature and parity. Multiplication computes its output parity in the type.
Field sampling stays generic. A packed-index lemma gives kernel code one fact to
reuse. These features remove explicit tags, repeated checks, and repeated
boundary arguments from later code. That is the development-speed claim.

### “What here is actually proved?”

Dimension, signature, and parity live in types; multiplication computes output
parity; packed-index bounds have a theorem. Grid validity, finite floats, scene
shape, and JSON stability are runtime checks. The visual rotor field itself is
numerical `Float` evidence backed by regression tests.

### “Does JavaScript compute the Clifford algebra?”

No. It receives all positions and grade coefficients for every frame. It does
display math—normalization, glyph geometry, camera projection, and depth sorting.
That is real work, but not the field or Clifford product.

### “Why not WebGL or Ganja.js?”

The goal was an offline, inspectable InfoView extension with a stage-safe
dependency surface. Local SVG makes the ownership boundary visible and supports
direct coefficient inspection. Ganja.js is the aesthetic inspiration, not a
runtime dependency.

### “Are the libraries real?”

Yes. The Lake roots are separate and an independent downstream package consumes
them through a path dependency. See
[`lakefile.toml`, lines 18–34](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/lakefile.toml#L18-L34)
and the external consumer at
[`tests/downstream/Main.lean`, lines 1–19](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/tests/downstream/Main.lean#L1-L19).
Its independent package declares the repository as a
[`path` dependency](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/tests/downstream/lakefile.toml#L5-L7).

## What not to say

- Not “Scarf deleted Haskell.” New API work moved to Python while the Haskell
  server continued and its footprint shrank gradually.
- Not “Haskell’s types failed.” The report says reliability and type checking
  were strengths.
- Not “Lean proved this animation.” It computed and validated `Float` values.
- Not “Lean renders the 3D geometry.” JavaScript builds and projects glyphs.
- Not “JSON is typed.” Lean has typed scene props which are serialized into a
  JSON data.
- Not “the 3→4 edit makes 600 values.” It makes 12 samples; the separate visual
  has 24×25 = 600 multivectors.
- Not “all invariants are dependent.” The code intentionally combines types,
  proofs, runtime validation, and tests.

## Build, rehearse, and recover

From `Grassmann4`:

```bash
./scripts/multivector_meetup_preflight.sh
```

From `Grassmann4/slides`:

```bash
./preflight.sh
uv run python -m http.server 8765 --directory _site
```

Then open `http://127.0.0.1:8765`. The public site exposes the same paths under
the talk URL: `/slides/`, `/demo/`, `/tutorial/`, and `/cue-card/`.

If Cursor is stale, use **Restart File** once. If the visual is not back in five
seconds, switch to the static fallback. If the deck fails, present from the cue
card. Never turn the talk into a live debugging session.

## Final mental model

The project is a small software system:

```text
dependent indices and theorems
        +
ordinary executable numerical code
        +
runtime validation and tests
        +
versioned serialization
        +
an editor extension and public visual surface
```

Routine code, indexed types, proofs, tooling, and a domain-specific interface
use one set of Lean definitions. That is the point of the demo.
