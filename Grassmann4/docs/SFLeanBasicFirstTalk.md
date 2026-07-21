# SF Lean: Basic-First 15-Minute Route

This is the recommended route: **12 minutes speaking, 3 minutes questions**.
The Verso deck is the spine. Cursor is one contained excursion with one safe
edit; the multivector field is the visual payoff. Present from the
[one-screen cue card](SFLeanBasicFirstCueCard.md), and use this document to
rehearse.

## Talk order

1. `Grassmann4/slides/_site/slides/index.html` — framing and typechecked warm-up;
2. `Grassmann4/OrdinaryProgrammingDemo.lean` — routine live program;
3. `Grassmann4/MultivectorFieldDemo.lean` — InfoView payoff;
4. return to the deck for ownership and the closing claim.

`GrassmannFields/Examples/MixedRotor.lean` is **Q&A only**. The static backup is
`Grassmann4/docs/MultivectorFieldFallback.svg`.

## The whole pipeline

```text
record + function → validated Array → typed scene props → JSON wire payload → local SVG
```

The warm-up is a hand-written semantic grade record chosen for teaching. The
flagship is stronger: a packed Clifford runtime computes its field, geometric
products, rotor sandwiches, and 24 frames. Keep those two demos distinct.

Lean owns the data types, numerical program, error handling, validation, and
typed widget boundary. A local React/SVG component presents the values inside
Lean’s InfoView. The numerical visual is `Float` runtime evidence, not a proof
about exact real arithmetic.

## Preparation

From the outer repository root:

```bash
Grassmann4/scripts/multivector_meetup_preflight.sh
```

From the slide package:

```bash
cd Grassmann4/slides
./preflight.sh
uv run python -m http.server 8765 --directory _site
```

Do not present unless both commands end with a line beginning `PASS`.

### Tab-opening order

Open these surfaces left to right, then return to the deck:

1. browser deck at `http://127.0.0.1:8765/slides/`;
2. `OrdinaryProgrammingDemo.lean`;
3. `MultivectorFieldDemo.lean`, already focused on `#html` with the widget loaded;
4. public browser demo or fallback SVG.

In Cursor, use an 18 px editor font, hide Explorer and the Agent sidebar, and
give the visual roughly 1080×720 CSS pixels. Verify these five ordinary-demo
anchors before leaving:

1. the grid record;
2. `swirlField : Vec3 → R3Grades` from `#check`;
3. the concrete field value;
4. `Except.ok 9`;
5. `Except.error "grid.xCount must be at least 2"`.

Rehearse Play, slider, grades 0–3, drag, wheel, Reset, and a sample click. On
stage use only grade 2, Play/Pause, one drag, Reset, and the inspector. Restore
all grades, frame 1, the default camera, and `tinyGrid.xCount := 3` afterward.

## Exact 12-minute script

### 0:00–0:20 — slide 1: title

> This is a talk about Lean as a normal programming language. The spicy version
> is that Lean may be better positioned than Haskell—not because it is a better
> Haskell, but because it has a second job that is much harder to replace.

### 0:20–1:05 — slide 2: the Scarf story, accurately

> Haskell ran in Scarf production for seven years. Its reliability, type
> checking, and performance held up. Scarf now puts new API work in Python while
> the old Haskell server continues and shrinks gradually. The reported tax was
> build time, ecosystem friction, and slower feedback—especially with parallel
> coding agents.

Do not say “Scarf deleted Haskell” or “Haskell’s types failed.”

### 1:05–1:40 — slide 3: label the inference

> This next part is my inference, not Scarf’s. When code generation makes an
> application cheap to port, what distinctive value is hard to substitute? My
> bet is that Lean has a stronger answer.

Reveal the answer: executable model → checked specification → proof.

### 1:40–2:10 — slide 4: one language, two jobs

> Lean’s first job is normal strict functional programming: arrays, loops, IO,
> errors, native executables, and Lake libraries. Its second job is dependent
> types, propositions, proofs, and a small kernel checking the result. Lean only
> earns that second advantage if job one is real.

### 2:10–2:35 — slide 5: the boring part

Point at the record, `Except`, and the two `#eval`s.

> This slide is a Lean source file; Verso checked this block while building the
> deck. A record, a function, an explicit error, and evaluated results. The
> boring part is the point. Now I’ll run the less toy version live.

### 2:35–3:15 — Cursor: a record is a record

Switch to `OrdinaryProgrammingDemo.lean`. Show `tinyGrid`, then `#eval tinyGrid`.

> This is a normal configuration record: floating-point coordinates and two
> natural-number counts. `#eval` runs it and the InfoView shows the value.

### 3:15–4:10 — Cursor: a field is a function

Show `swirlField`, `#check swirlField`, then its concrete `#eval`.

> A field is just a function from a point to a value. This value has scalar,
> vector, oriented-plane, and pseudoscalar channels: number, arrow, plane,
> volume. Lean shows the type and executes the function at a concrete point.

### 4:10–4:45 — Cursor: arrays and explicit errors

Show `sampleCount` and `Except.ok 9`.

> `samplePlanar` runs the field over a validated grid and returns an array or a
> string error. This `do` block propagates an error or returns the array size.
> Three by three gives `Except.ok 9`.

### 4:45–5:20 — the only live edit

Change only `xCount := 3` on line 21 to `4`, dismiss inline completion, and put
the cursor on line 44. Show `Except.ok 12`, then **undo immediately**.

> I changed an ordinary input. Lean reran the program, and nine samples became
> twelve.

If 12 does not appear in five seconds, undo, narrate it, and continue.

### 5:20–5:50 — failure is a value

Put the cursor on line 47.

> A one-column grid cannot support this sampler, so the same program returns an
> explicit error before any renderer sees the input. Invalid input is data too.

### 5:50–6:30 — verbal Clifford bridge only

> The visual uses the same grid, function, array, and error pipeline. The key
> difference is that its function returns a packed Clifford multivector. One
> geometric product contributes scalar and oriented-plane parts; one even rotor
> sandwich transforms the complete mixed-grade value.

Do not open `MixedRotor.lean` in the core. It is available for questions.

### 6:30–9:45 — InfoView payoff

Switch to `MultivectorFieldDemo.lean`. Point first at the textual summary:

> Twenty-four frames, 25 samples per frame: 600 Lean-computed multivector
> samples. These are floating-point runtime results, not a formal theorem.

Click `#html`, then do only:

1. point at the selected sample and its four exact grade rows;
2. grade 2 off, then on;
3. Play, then Pause;
4. one empty-background drag;
5. Reset view.

Say:

> Lean already supplied every position and coefficient for every frame. This
> local component constructs glyphs, projects, depth-sorts, handles interaction,
> and paints SVG. It does not multiply multivectors or interpolate frames.

### 9:45–10:45 — slide 7: three reusable boundaries

Return to the deck.

> The basic file imports only `GrassmannFields`; it has no widget dependency.
> `Grassmann` is the packed numerical runtime. `GrassmannFields` owns
> renderer-neutral functions, grids, sampling, and validation. `GrassmannViz`
> opts into the typed scene and local InfoView component. They are actual Lake
> libraries exercised by an independent downstream package.

Explain only one algebraic fact: `p*v` contributes scalar and oriented-plane
parts. Leave packed masks and kernels for Q&A.

### 10:45–12:00 — slide 8: close and stop

> My claim is narrower than “Lean beats Haskell at everything,” and more
> interesting. Lean is better differentiated. You can start with records,
> functions, arrays, errors, and a UI; then move selected invariants into
> dependent types and proofs without changing languages. Lean is an ordinary
> language whose second job is not ordinary.

Repeat “runtime evidence, not formal proof.” Stop. Use 12:00–15:00 for questions.

## Seven-minute rescue route

1. Slides 1–5 in two minutes.
2. Show `tinyGrid`, `swirlField`, `Except.ok 9`, and the explicit error in two
   minutes. **Skip the live edit and all internal Clifford code.**
3. Show the loaded widget, toggle grade 2, Play/Pause, and point at one inspector
   value in two minutes.
4. Give the ownership boundary and closing line in one minute.

## Short Q&A answers

**What is a multivector?** A value that can carry scalar, vector,
oriented-plane, and oriented-volume parts together. In 3D that is eight logical
coefficients.

**What is proved?** Dimension, metric signature, and parity occur in types;
there are checked theorems around packed indexing. Grid/scene validity is
runtime `Except` validation. The `Float` animation is numerical evidence backed
by regression tests.

**Is JavaScript doing the algebra?** No. Lean computes positions, products,
coefficients, validation, and every frame. JavaScript does display geometry,
projection, depth sorting, interaction, and SVG.

**Why not Haskell plus tests?** That can be an excellent engineering choice.
The distinction is that a Lean application can also be its checked
specification; selected invariants can move from tests into types and proofs
without changing languages.

**Can I use the field code without the widget?** Yes. `GrassmannFields` is
renderer-neutral; `GrassmannViz` is opt-in.

## Recovery rules

- Five seconds maximum on any failure.
- Stale `#eval`: undo, narrate the expected result, continue.
- Blank InfoView: toggle it once and click `#html`; if still blank, switch to
  the pre-opened static SVG or public browser demo.
- Broken deck: speak from the one-screen cue card.
- Never update dependencies, rebuild caches, or diagnose the language server on
  stage.
- End with `tinyGrid.xCount := 3`, frame 1, all grades visible, default camera,
  paused.

For a source-by-source explanation, read
[`SFLeanPresenterTutorial.md`](SFLeanPresenterTutorial.md). For the algebra-heavy
optional route, see `SFLeanMultivectorFieldDemo.md`.
