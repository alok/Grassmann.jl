# Lean’s unfair advantage — one-screen cue card

**Contract:** 12 minutes speaking + 3 minutes questions. One source edit. No
internal kernel walkthrough. The browser deck is the spine; Cursor is one
contained excursion.

| Time | Surface | Do / say |
|---:|---|---|
| 0:00 | Slides 1–4 | “Lean is a normal language with a second job.” Scarf’s strengths held; the organizational tax changed. “Better positioned” is **my inference**. |
| 2:10 | Slide 5 | Point at the typechecked record, `Except`, and two `#eval`s. “The boring part is the point.” |
| 2:35 | Cursor · ordinary | [`tinyGrid`, line 15](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L15-L25): ordinary configuration record. |
| 3:15 | Cursor · ordinary | [`swirlField`, line 28](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L28-L37): function `Vec3 → R3Grades`; say number, arrow, plane, volume. |
| 4:10 | Cursor · ordinary | [`sampleCount`, line 40](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L40-L47): array-producing program with explicit errors. Show `Except.ok 9`. |
| 4:45 | **Only edit** | [`xCount := 3`, line 21](https://github.com/alok/Grassmann.jl/blob/__SOURCE_COMMIT__/Grassmann4/OrdinaryProgrammingDemo.lean#L21) → `4`; move cursor to line 44; show `Except.ok 12`; **undo immediately**. |
| 5:20 | Cursor · ordinary | Line 47: show `Except.error "grid.xCount must be at least 2"`. “Invalid input is ordinary data.” |
| 5:50 | Verbal bridge | “The flagship swaps the teaching record for a packed Clifford multivector. `p*v` supplies scalar + oriented-plane parts; one even rotor sandwich moves the whole value.” **Do not open kernel code.** |
| 6:30 | Cursor · `#html` | Point at `24 frames; 25 samples/frame; 600 Lean-computed multivectors`. Say once: “Float runtime evidence, not a theorem.” |
| 7:00 | InfoView | Grade 2 off/on → Play/Pause → one empty-background drag → Reset. Point at inspector. |
| 9:45 | Slides 7–8 | Three Lake roots. Lean owns values + validation; local JS owns glyphs + projection + interaction. Close: “Lean is an ordinary language whose second job is not ordinary.” |
| 12:00 | Stop | Questions. Do not spend the three-minute buffer adding another demo. |

## Five phrases worth memorizing

1. “The boring part is the point.”
2. “A field is just an ordinary function from a point to a value.”
3. “The dimension, metric signature, and parity are in the type.”
4. “Lean computes the field; the local component paints it.”
5. “This visual is runtime evidence, not a formal proof.”

## Five-second recovery rule

- Edit does not update: undo, say the expected `9 → 12`, continue.
- InfoView is blank: use [`fallback.svg`](../demo/fallback.svg) or the public fallback link.
- Deck fails: speak from this card; the order is ordinary → packed field → ownership → thesis.
- **Never debug live for more than five seconds.**

## Before and after

- Tabs, left to right: deck; `OrdinaryProgrammingDemo.lean`;
  `MultivectorFieldDemo.lean` already on `#html`; fallback SVG.
- Start with the deck, not Cursor.
- End with `xCount := 3`, frame 1, all grades visible, default camera, paused.
