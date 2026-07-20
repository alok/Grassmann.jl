# SF Lean: Basic-First 15-Minute Route

This is the recommended stage route. It keeps the A1 multivector visual, but
the live coding is deliberately routine: a record, a function, an array, an
explicit error, and one small edit. No Clifford-algebra derivation is required.

Stage files, in this order:

1. `Grassmann4/MultivectorFieldDemo.lean` — the visual destination;
2. `Grassmann4/OrdinaryProgrammingDemo.lean` — the basic live program;
3. `Grassmann4/GrassmannFields/Examples/MixedRotor.lean` — optional depth only.

Static backup: `Grassmann4/docs/MultivectorFieldFallback.svg`

## The whole argument in one line

```text
record + function -> validated Array -> typed JSON -> local SVG in the InfoView
```

The warm-up field is a small hand-written grade record chosen for teaching.
The flagship visual is the stronger example: its samples and 24 animation
frames come from the packed Clifford-algebra runtime. Keep that distinction
clear.

## What to prepare

From the authoritative outer repository root, run:

```bash
Grassmann4/scripts/multivector_meetup_preflight.sh
```

Do not present until its last status line begins with `PASS`. The preflight now
compiles both stage files as well as the public libraries, tests, offline
renderer checks, and static fallback.

In Cursor:

1. Open `OrdinaryProgrammingDemo.lean`, `MixedRotor.lean`, and
   `MultivectorFieldDemo.lean` in that order. End on the final file.
2. Put the cursor on `#html` and wait for the visual to finish loading.
3. Set the editor font to 18 px. Hide Explorer and the Agent sidebar. Give the
   visual about 1080 by 720 CSS pixels and verify that the ownership sentence
   at the bottom is visible without scrolling.
4. Exercise Play, the slider, one grade toggle, one drag, one wheel zoom, and
   Reset. Restore all four grades and reset the camera.
5. In `OrdinaryProgrammingDemo.lean`, verify the four useful InfoView results:
   the grid record, the field value, `Except.ok 9`, and the explicit invalid
   grid error.
6. Open the fallback SVG in Preview or a browser and leave it one app switch
   away. Repeat the reveal with networking disabled.
7. Restore `tinyGrid.xCount` to `3` after every rehearsal. A clean tree is part
   of the preflight contract.

## Exact 12-minute script

The core ends at 12 minutes. The remaining 3 minutes are for questions or
recovery. Actions are marked **Do**; the quoted text is safe to say nearly
verbatim.

### 0:00-0:40 — show the destination first

**Do:** Start with the cursor on `#html`. Drag the empty background once.

> This is program output inside Lean's editor: a field of three-dimensional
> multivectors. Lean computed 24 frames times 25 points—600 values—and then a
> local SVG component displayed them.

Do not define a multivector yet. Let the result create the question.

### 0:40-1:10 — state the claim boundary

> My claim is very ordinary: Lean can own the data types, numerical program,
> error handling, tests, serialization, and editor UI. These are floating-point
> computations, not formally proved real-number facts.

That is enough proof-theory discussion for the core talk.

### 1:10-2:10 — a record is a record

**Do:** Switch to `OrdinaryProgrammingDemo.lean`. Show `tinyGrid`, then put the
cursor on `#eval tinyGrid`.

> This is a normal configuration record: five floating-point coordinates and
> two natural-number counts. `#eval` runs it and the InfoView shows the value.

If useful, point at `PlanarGrid` and say “roughly, a struct.” Do not open its
library definition unless someone asks.

### 2:10-3:25 — a field is a function

**Do:** Show `swirlField`, then put the cursor on `#check swirlField` and finally
on its `#eval`.

> Here a field is just a function from a point to a value. The value is another
> record with scalar, vector, oriented-plane, and pseudoscalar channels. Lean
> infers and displays the function's type, and it can execute the function at a
> concrete point.

For a basic audience, translate the four channels once:

> Think number, arrow, oriented plane, and oriented volume. We do not need the
> algebra behind them yet.

### 3:25-4:35 — ordinary arrays and explicit errors

**Do:** Show `sampleCount` and put the cursor on `#eval sampleCount tinyGrid`.

> `samplePlanar` accepts the grid and the function. It runs nested loops,
> returns an array of samples, and can report a string error. The `do` block
> propagates an error or returns the array size. Three by three gives
> `Except.ok 9`.

The only concepts needed are function application, an array, and a result type
that distinguishes success from failure.

### 4:35-5:20 — the one live edit

**Do:** Change only `xCount := 3` to `xCount := 4`. Press Escape to dismiss any
inline completion, then return the cursor to `#eval sampleCount tinyGrid`.

> I changed an ordinary input value. Lean reran the program, and nine samples
> became twelve.

Use a five-second rule. If `Except.ok 12` does not appear, undo once and move
on. This edit is the required live coding; the larger visual does not need a
live source edit.

### 5:20-6:05 — failure is a value

**Do:** Put the cursor on the final invalid-grid `#eval`.

> A one-column grid cannot support this sampler, so the same program returns
> `Except.error` with a useful message. The invalid state is handled before any
> renderer sees it.

This is the most basic and strongest “ordinary language” moment in the talk.

### 6:05-7:00 — connect the toy program to the real one

The safe route is verbal; no tab switch is necessary:

> The visual uses the same grid, function, array, and error pipeline. The one
> difference is that its field function returns a packed Clifford-algebra
> value. One geometric product supplies scalar and oriented-plane parts; a
> rotor sandwich supplies the animation.

If the room wants code, briefly open `MixedRotor.lean` and show only these
definitions:

```lean
def baseField (p : Vec3) : MV R3 .full :=
  let position := positionMV p
  let velocity := velocityMV p
  let product : MV R3 .full := position * velocity
  velocity + product + pseudoscalarMV p

def fieldAt (theta : Float) (p : Vec3) : MV R3 .full :=
  mvSandwich (rotor theta) (baseField p)
```

Say “one multiplication and one sandwich,” then leave. Do not explain blade
masks, storage parity, or the sign table in the scripted core.

### 7:00-9:25 — make the output legible

**Do:** Return to `MultivectorFieldDemo.lean` and click `#html`.

1. Point at the selected sample and its four grade rows.
2. Turn grade 2 off and on to isolate the orange oriented planes.
3. Turn grade 3 off and on to isolate the signed halos.
4. Press Play, pause, and move the frame slider once.
5. Drag the empty background, wheel once, and press Reset.

Narrate with plain ownership language:

> Lean already supplied every position and coefficient for every frame. The
> local component only turns those values into arrows, disks, halos, colors,
> projection, and SVG. It does not multiply multivectors or interpolate frames.

### 9:25-10:30 — show that these are libraries

**Do:** Keep the visual on screen if the room is engaged. You can state the
split without opening more source:

```lean
import Grassmann       -- packed numerical runtime
import GrassmannFields -- records, functions, grids, sampling, validation
import GrassmannViz    -- typed scene plus offline InfoView component
```

> The basic file imports only `GrassmannFields`; it has no widget dependency.
> The visual layer is a separate Lake library, and a downstream project can use
> either boundary.

### 10:30-12:00 — close on the thesis

**Do:** Leave the working visual visible.

> The unusual object here is a multivector field. The programming story is not
> unusual: records, functions, arrays, errors, libraries, tests, JSON, and a UI.
> Lean is the ordinary language joining those pieces. The numerical output is
> runtime evidence; Lean can add proofs where the application actually needs
> them.

Stop. Use 12:00-15:00 for questions.

## Seven-minute rescue version

If the previous speaker runs long or the editor becomes stressful:

1. Show the visual and say the 600-value sentence — 45 seconds.
2. Show `tinyGrid`, `swirlField`, and `Except.ok 9` — 2 minutes.
3. Show the explicit invalid-grid error — 45 seconds.
4. Return to the visual; toggle grade 2, press Play, and inspect one sample —
   2 minutes.
5. Give the records/functions/arrays/errors/libraries closing — 1 minute.

Skip both live edits and all internal Clifford code. This still demonstrates
the thesis.

## Five likely questions, in plain language

**What is a multivector?**

A typed value that can hold scalar, vector, oriented-plane, and oriented-volume
parts together. In three dimensions those are eight logical coefficients.

**Is JavaScript doing the algebra?**

No. Lean computes the grid, Clifford products, grade coefficients, validation,
and all frames. The embedded local component does camera and SVG presentation.

**What is formally proved here?**

The visual itself makes a numerical runtime claim, not a formal theorem. The
talk is about using Lean for an ordinary executable software pipeline while
retaining the option to prove selected properties.

**Why use Lean rather than another language?**

For this talk, the concrete answer is one environment for typed libraries,
execution, validation, tests, serialization, and an extensible editor. Do not
claim that every numerical UI should be rewritten in Lean.

**Can the field library be used without the widget?**

Yes. `GrassmannFields` is renderer-neutral and does not depend on ProofWidgets.
`GrassmannViz` is an opt-in presentation library.

## Recovery rules

- If a basic `#eval` result is stale, undo the edit, save, and click the command
  once. Then continue without live coding.
- If the InfoView visual disappears, run `Lean 4: InfoView: Toggle InfoView`
  once and click `#html`.
- If the visual does not return within five seconds, switch to the pre-opened
  fallback SVG. It is a separate Lean renderer over the same default scene,
  not a screenshot.
- Do not reload Cursor, update dependencies, or diagnose the language server
  in front of the room.
- After the talk, restore `tinyGrid.xCount` to `3` before running preflight or
  committing anything.

For the more algebra-heavy route and exact view-layer claim boundaries, see
`SFLeanMultivectorFieldDemo.md`.
