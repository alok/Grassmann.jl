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
record + function → validated Array → typed scene → JSON data → local SVG
```

The warm-up is a hand-written semantic grade record chosen for teaching. The
visual demo uses a packed multivector runtime to compute its field, geometric
products, rotor sandwiches, and 24 frames. Keep those two demos distinct.

Lean owns the data types, numerical program, error handling, validation, and
typed widget boundary. A local React/SVG component presents the values inside
Lean’s InfoView. The animation uses `Float`. It is tested numerical computation,
not a proof about exact real arithmetic.

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

### What the audience can do on the website

The opening slide links to `alok.github.io/talks/lean-unfair-advantage/` and
shows the same address as a QR code. On a phone, people can swipe through the
deck or open **Demo**. In the demo they can drag an empty part of the field to
orbit it, tap a sample to inspect its coefficients, toggle grade 2, scrub the
timeline, and play or pause. The
**Code** links open the exact Lean source; **Tutorial** explains the definitions.

Be clear about the boundary: this is not an online Lean editor. Lean generated
the complete scene. The browser draws and interacts with those values.

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

> I want to show Lean doing ordinary programming: a record, a function, an
> error, an array, and a small interactive view. My claim is about development
> speed: Lean’s types can remove bookkeeping from mathematical code.

### 0:20–0:50 — slide 2: one recent Haskell exit

> Haskell ran in Scarf production for seven years. Its reliability, type
> checking, and performance held up. Scarf now puts new API work in Python while
> the old Haskell server continues and shrinks gradually. The reported tax was
> build time, ecosystem friction, and slower feedback—especially with parallel
> coding agents.

Do not say “Scarf deleted Haskell” or “Haskell’s types failed.”
Do not build the talk on Scarf. It is a current example. Move on.

### 0:50–1:30 — slide 3: if you start, go all the way

> If I want the conventional route, I can use Python. If I start with types for
> mathematical software, I want to go farther than Haskell. Lean gives me
> dependent types, proofs when they save later work, and editor views built
> around the same values.

### 1:40–2:10 — slide 4: types as programming tools

> Lean has data, functions, arrays, loops, IO, errors, executables, and
> libraries. For this program, `MV sig p` also carries the algebraic context.
> The caller does not pass separate dimension, metric, and parity tags. The
> development loop is edit, elaborate, evaluate, inspect. Metaprograms,
> InfoView, and AI can work against that typed program state.

### 2:10–2:50 — slide 5: the values

Hover `Vec3`, `R3Grades`, `Field3`, and `Sample3` in Verso’s code panel.

> A field is a function: point in, value out. This value has four named parts: a
> number, a directed segment, an oriented plane segment, and an oriented volume.
> That is enough algebra to read the picture.

### 2:50–3:15 — slide 6: checked code in the deck

Point at the record, `Except`, and the two `#eval`s.

> This deck is a Lean source file. Verso checked this record, function, explicit
> error, and both evaluations when it built the slides.

### 3:15–3:50 — Cursor: a record is a record

Switch to `OrdinaryProgrammingDemo.lean`. Show `tinyGrid`, then `#eval tinyGrid`.

> This is a normal configuration record: floating-point coordinates and two
> natural-number counts. `#eval` runs it and the InfoView shows the value.

### 3:50–4:30 — Cursor: a field is a function

Show `swirlField`, `#check swirlField`, then its concrete `#eval`.

> A field is a function: give it a point and it returns a value. Lean shows the
> type and executes the function at a concrete point.

### 4:30–4:55 — Cursor: arrays and explicit errors

Show `sampleCount` and `Except.ok 9`.

> The sampler validates the grid and returns either a string error or an array.
> This function returns the array size. Three by three gives `Except.ok 9`.

### 4:55–5:20 — the only live edit

Change only `xCount := 3` on line 21 to `4`, dismiss inline completion, and put
the cursor on line 44. Show `Except.ok 12`, then **undo immediately**.

> Four by three: twelve.

If 12 does not appear in five seconds, undo, narrate it, and continue.

### 5:20–5:45 — explicit failure

Put the cursor on line 47.

> One column fails validation. Because failure is in the return type, the caller
> has to deal with it.

### 5:45–6:15 — verbal bridge only

> The visual keeps the same program shape: grid, field function, validation,
> array. It replaces the teaching record with the packed multivector type. That
> type records the dimension, metric signature, and parity.

Do not open `MixedRotor.lean` in the core. It is available for questions.

### 6:15–9:15 — InfoView

Switch to `MultivectorFieldDemo.lean`. Point first at the textual summary:

> Twenty-four frames, 25 samples per frame: 600 multivectors. Lean computed all
> of these values before the widget opened.

Click `#html`, then do only:

1. point at the selected sample and its four exact grade rows;
2. grade 2 off, then on;
3. Play, then Pause;
4. one empty-background drag;
5. Reset view.

Say:

> Lean computes and validates the values. The view draws them and handles the
> camera and controls. It does not compute the field. The animation uses
> floating-point computation; it is not a theorem about real numbers.

### 9:15–10:15 — slide 8: three libraries and one view boundary

Return to the deck.

> `Grassmann` contains the packed arithmetic. `GrassmannFields` contains the
> renderer-independent grid, functions, sampling, and validation.
> `GrassmannViz` packages the values for InfoView. They are separate Lake
> libraries exercised by an independent downstream package.

### 10:15–12:00 — slide 9: types that remove bookkeeping

> `MV sig p` carries dimension, metric, and parity. Multiplication computes the
> result parity. `Field3 M` keeps sampling generic. One packed-index lemma gives
> the kernel code a bound it can reuse.

Close:

> The point is not to prove everything. The point is to make the next change
> easier. This demo is the evidence: edit, elaborate, evaluate, inspect, and
> extend the editor in one typed loop.

Stop. Use 12:00–15:00 for questions.

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
runtime `Except` validation. The `Float` animation is computation covered by
regression tests, not a proof about exact real arithmetic.

**Is JavaScript doing the algebra?** No. Lean computes positions, products,
coefficients, validation, and every frame. JavaScript does display geometry,
projection, depth sorting, interaction, and SVG.

**Why is this easier than Haskell here?** The claim is local to this program.
Lean lets the API index a multivector by signature and parity, compute output
parity in the multiplication type, and use a small proof as a reusable kernel
fact. That removes explicit tags and repeated boundary reasoning from later
code. Add a proof only when this saves programming work.

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
