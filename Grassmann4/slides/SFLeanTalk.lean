import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 1000
set_option verso.slides.panel true

#doc (Slides) "Lean's Unfair Advantage" =>

# Lean's unfair advantage

```html
<p class="eyebrow">SF LEAN · ALOK SINGH · JULY 21, 2026</p>
<p class="hero">record → function → error → array → InfoView</p>
<div class="follow-along">
  <img src="../follow-along.svg" alt="QR code for the public talk site">
  <p><b>Follow along</b><br><span>alok.github.io/talks/lean-unfair-advantage/</span></p>
</div>
```

:::notes
0:00-0:20. Open with the title, not the Scarf conclusion.

Say: “I want to show you Lean before the theorem prover becomes visible.”
:::

# A recent Haskell exit

```html
<div class="fact-grid">
  <div class="fact"><b>7 years</b><span>Haskell in Scarf production</span></div>
  <div class="fact"><b>it worked</b><span>reliable code, useful types, good performance</span></div>
  <div class="fact accent"><b>new API work</b><span>is now written in Python</span></div>
  <div class="fact"><b>why</b><span>build time, libraries, and a slower development loop</span></div>
</div>
<p class="correction">The Haskell server still runs. Its share of the system is shrinking.</p>
<p class="source"><a href="https://avi.press/posts/2026-07-10-after-7-years-in-production-scarf-has-reluctantly-moved-away-from-haskell.html">Avi Press, “After 7 years in production, Scarf has reluctantly moved away from Haskell,” July 10, 2026</a></p>
```

:::notes
0:20-0:50. This is only the hook. Be exact. Avi Press says Haskell delivered reliable code, caught
real bugs, and performed well. Scarf started putting new API work in a Python
server; the existing Haskell server still runs and is being reduced gradually.
The stated costs were compilation time and ecosystem friction, amplified by
parallel agent workflows.

The types did not fail. The development loop became too expensive. Move on.
:::

# If you start with types, go all the way

```html
<p class="hot-take">For a conventional application: <span>use Python.</span></p>
<div class="question">For type-driven mathematical software: dependent types, reusable proved facts, and programmable editor views.</div>
```

:::fragment fadeUp
The provocation: go farther than Haskell. Use Lean.
:::

:::notes
0:50-1:30.

Say: “Scarf is only a recent example. My claim is this: if I want the
conventional route, I can use Python. If I start with types for mathematical
software, I want to go farther. Lean gives me dependent types, proofs when they
save later work, and editor views built around the same values.”
:::

# Types as programming tools

```html
<div class="jobs">
  <div class="job">
    <p class="job-kicker">ROUTINE LEAN</p>
    <h3>Write and run the program</h3>
    <p>records and functions</p>
    <p><code>Array</code>, <code>Except</code>, loops, IO</p>
    <p><code>#check</code>, <code>#eval</code>, InfoView</p>
  </div>
  <div class="plus">+</div>
  <div class="job proof-job">
    <p class="job-kicker">DOMAIN TYPES</p>
    <h3>Let types carry the algebra</h3>
    <p><code>MV R3 .full</code></p>
    <p>multiplication computes result parity</p>
    <p>the renderer receives a plain projection</p>
  </div>
</div>
<div class="ownership"><b>Loop:</b> edit → elaborate → evaluate → inspect.<br><b>Tools:</b> metaprograms and AI can act on the same typed program state.</div>
<p class="source"><a href="https://lean-lang.org/">Lean is officially described as both a programming language and proof assistant · lean-lang.org</a></p>
```

:::notes
1:40-2:10.

Say: “This is why I find Lean easier for this program. I can write routine
functional code, but the domain types carry facts that I would otherwise pass,
check, and keep synchronized by hand.”
:::

# Plain view data; one typed algebra

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

abbrev Field3 (M : Type) := Vec3 → M

structure Sample3 where
  position : Vec3
  value : R3Grades
```

```html
<div class="ownership"><b>Computed field:</b> <code>fieldAt : Float → Vec3 → MV R3 .full</code><br><b>View boundary:</b> <code>MV R3 p → R3Grades</code></div>
<p class="slide-meta">Hover the ordinary view types here. In Cursor, hover <code>fieldAt</code> for the one dependent type used by the computation.</p>
```

:::notes
2:10-2:50. Open Verso's code panel and hover `Vec3`, `R3Grades`, `Field3`, and
`Sample3`. Call these plain renderer-facing types, not dependent types. In
Cursor, `#check fieldAt` shows `Float → Vec3 → MV R3 .full`.

Say: “A field is just a function from a point to a value. Here the value can
hold a number, a directed segment, an oriented plane segment, and an oriented
volume. The computation returns `MV R3 .full`; one adapter projects that value
to this plain record for the renderer. That is the only dependent-typing move
I need for this demo.”
:::

# Start with the program

```lean
structure PlanarGrid where
  xCount : Nat
  yCount : Nat

def sampleCount (grid : PlanarGrid) : Except String Nat := do
  if grid.xCount < 2 then
    throw "xCount must be at least 2"
  return grid.xCount * grid.yCount

#eval sampleCount { xCount := 3, yCount := 3 }
#eval sampleCount { xCount := 1, yCount := 3 }
```

```html
<p class="slide-meta">This slide is a Lean file. Verso type-checked the code while building the deck.</p>
```

:::notes
2:50-3:15. Click `sampleCount` if you want Verso's code info panel, but do not
linger. This slide is also the fallback if the editor is unavailable.

Say: “A record, a function, an explicit error, and a result. Lean runs it. The
deck is also a Lean file, so Verso checked this block when it built the slides.”
:::

# Live: ordinary programming

```html
<p class="live"><code>PlanarGrid</code> → function → <code>Except String (Array Sample)</code></p>
<div class="live-steps">
  <span>read the result</span>
  <span>change 3 × 3 to 4 × 3</span>
  <span>run invalid input and read the error</span>
</div>
<p class="switch">Switch to Cursor · <code>OrdinaryProgrammingDemo.lean</code></p>
```

:::notes
3:15-9:45. Switch to Cursor.

1. In `OrdinaryProgrammingDemo.lean`, show `tinyGrid`, `swirlField`, and
   `sampleCount`.
2. Put the cursor on the successful `#eval`: `Except.ok 9`.
3. Edit only `xCount := 3` to `xCount := 4`; show `Except.ok 12`.
4. Show the final invalid-grid command and its explicit error.
5. Switch to `MultivectorFieldDemo.lean`, click `#html`, toggle grade 2 off/on,
   play/pause, drag the empty background once, and reset.

If someone asks what the picture establishes, say: “Lean computed these
numbers; I am not claiming the picture is a proof.”

After the visual, return to this deck and advance once.
:::

# What Lean and the view do

```lean
import Grassmann       -- packed multivector arithmetic
import GrassmannFields -- functions, grids, sampling, validation
import GrassmannViz    -- typed scene and offline InfoView
```

```html
<div class="ownership"><b>Lean computes and validates</b> the field values.<br><b>The view draws</b> them and handles the camera and controls.</div>
```

:::notes
9:45-10:45.

Say: “`GrassmannFields` does not know about the renderer. `GrassmannViz` adds
the scene and InfoView. Lean sends positions and coefficients; the view turns
them into marks on the screen.”
:::

# The one dependent type in this demo

```html
<div class="fact-grid">
  <div class="fact"><b><code>MV R3 .full</code></b><span>this field has the R3 metric and may contain every grade</span></div>
  <div class="fact"><b><code>MV R3 .even</code></b><span>the rotor can contain only even grades</span></div>
  <div class="fact"><b><code>.even * .full = .full</code></b><span>multiplication computes the result parity</span></div>
  <div class="fact accent"><b><code>R3Grades.ofMV</code></b><span>one explicit boundary produces plain view data</span></div>
</div>
```

:::fragment fadeUp
[browser demo](../demo/) · [presenter tutorial](../tutorial/) · [one-screen cue card](../cue-card/)
:::

:::notes
10:45-12:00.

Say: “I am not claiming that every record here is dependently typed. `Vec3` and
`R3Grades` are deliberately plain. The useful type is `MV R3 .full`: the field's
dimension, metric, and allowed grades travel together. The rotor is
`MV R3 .even`, and multiplication determines that the result is full. Then one
explicit adapter produces plain renderer data. The point is to use just enough
type structure to make the next change easier.”

Stop at 12:00 and use the remaining three minutes for questions.
:::
