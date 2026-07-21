# Lean’s unfair advantage — one-screen cue card

**Timing:** Speak for 12 minutes. Reserve 3 minutes for questions. Make one
source edit. Use the slides for most of the talk. Open Cursor only for the live
demo. Do not teach the algebra.

| Time | Surface | Do / say |
|---:|---|---|
| 0:00 | Slides 1–4 | Scarf is a 30-second example of leaving Haskell for Python. Then leave it. “For a conventional app, use Python. If I start with types for mathematical software, I want to go all the way to Lean.” |
| 1:40 | Slide 5 | `Vec3` and `R3Grades` are plain view data. In Cursor, hover `fieldAt : Float → Vec3 → MV R3 .full`. This is the one dependent type in the demo. |
| 2:20 | Slide 6 | Point at the checked record, `Except`, and two `#eval`s. Verso checked this code when it built the deck. |
| 2:50 | Cursor · ordinary | [`tinyGrid`, line 15](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L15-L25): configuration record. |
| 3:30 | Cursor · ordinary | [`swirlField`, line 28](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L28-L37): “A field is a function: point in, value out.” |
| 4:15 | Cursor · ordinary | [`sampleCount`, line 40](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L40-L47): returns either an error or an array size. Show `Except.ok 9`. |
| 4:45 | **Only edit** | [`xCount := 3`, line 21](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L21) → `4`; show `Except.ok 12`; **undo immediately**. |
| 5:15 | Cursor · ordinary | Line 47: `Except.error "grid.xCount must be at least 2"`. Failure is in the return type, so the caller must handle it. |
| 5:45 | Verbal bridge | The visual keeps the same grid → function → validation → array shape, but returns the packed multivector type. Dimension, signature, and parity are in its type. |
| 6:15 | Cursor · `#html` | Show `24 frames; 25 samples/frame; 600 Lean-computed multivectors`, then open the view. |
| 6:45 | InfoView | Grade 2 off/on → Play/Pause → one drag → Reset. Point at one sample. “Lean computes and validates the values. The view draws them.” |
| 9:15 | Slides 8–9 | Three Lake libraries. Then show how `MV sig p`, result parity, generic fields, and one reusable index lemma remove repeated work. |
| 10:45 | Close | “The point is not to prove everything. The point is to make the next change easier. This demo is the evidence: edit, elaborate, evaluate, inspect.” |
| 12:00 | Stop | Questions. Do not fill the three-minute buffer with another demo. |

## Four factual anchors

1. **Program:** record → function → `Except` → `Array`.
2. **Multivector:** number · directed segment · oriented plane · oriented volume.
3. **UI boundary:** Lean computes and validates · view draws and interacts.
4. **Development speed:** edit → elaborate → evaluate → inspect · metaprograms
   and AI use the same typed program state.

State the numerical boundary once, beside the visual: “The animation uses
floating-point computation. It is not a theorem about real numbers.”

## Audience website

- QR / short URL: `alok.github.io/talks/lean-unfair-advantage/`
- On a phone: open **Slides** and swipe left to advance. Then open **Demo**.
  Drag an empty part of the field to orbit. Tap a sample to inspect its
  coefficients. Use the grade buttons and timeline controls.
- **Code** links open the exact Lean source. **Tutorial** explains the program
  and cites the definitions.
- The public demo is not an online editor. Lean generated its scene; the browser
  draws and interacts with those values.

## Five-second recovery rule

- Edit does not update: undo, say the expected `9 → 12`, continue.
- InfoView is blank: use [`fallback.svg`](../demo/fallback.svg) or the public demo.
- Deck fails: speak from this card; ordinary program → visual → boundaries →
  four claim levels.
- Never debug live for more than five seconds.

## Before and after

- Tabs, left to right: deck; `OrdinaryProgrammingDemo.lean`;
  `MultivectorFieldDemo.lean` already on `#html`; fallback SVG.
- Start with the deck, not Cursor.
- End with `xCount := 3`, frame 1, all grades visible, default camera, paused.
