import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 1000
set_option verso.slides.panel true

#doc (Slides) "Lean's Unfair Advantage" =>

# Lean's unfair advantage

```html
<p class="eyebrow">SF LEAN · ALOK SINGH · JULY 21, 2026</p>
<p class="hero">An ordinary programming language<br><span>with a reason not to become Python</span></p>
<p class="hero-sub">records · functions · errors · Clifford algebra · a typed InfoView boundary</p>
```

:::notes
0:00-0:20. Open with the title, not the Scarf conclusion.

Say: “This is a talk about Lean as a normal programming language. The spicy
version is that Lean may be better positioned than Haskell—not because it is a
better Haskell, but because it has a second job that is much harder to replace.”
:::

# A Haskell story, accurately

```html
<div class="fact-grid">
  <div class="fact"><b>7 years</b><span>Haskell in Scarf production</span></div>
  <div class="fact"><b>held up</b><span>reliability, types, performance</span></div>
  <div class="fact accent"><b>new API work</b><span>now goes into Python</span></div>
  <div class="fact"><b>the tax</b><span>build time, ecosystem, agent feedback</span></div>
</div>
<p class="correction">Not a big-bang rewrite. Existing Haskell still runs while its footprint shrinks.</p>
<p class="source"><a href="https://avi.press/posts/2026-07-10-after-7-years-in-production-scarf-has-reluctantly-moved-away-from-haskell.html">Avi Press, “After 7 years in production, Scarf has reluctantly moved away from Haskell,” July 10, 2026</a></p>
```

:::notes
0:20-1:05. Be exact. Avi Press says Haskell delivered reliable code, caught
real bugs, and performed well. Scarf started putting new API work in a Python
server; the existing Haskell server still runs and is being reduced gradually.
The stated costs were compilation time and ecosystem friction, amplified by
parallel agent workflows.

Do not say “Scarf deleted all its Haskell.” The accurate version makes the
argument stronger.
:::

# My inference, not Scarf's

```html
<p class="hot-take">A language is vulnerable when its distinctive value becomes<br><span>organizationally substitutable.</span></p>
<div class="question">So what does Lean offer that “Python + more tests” does not?</div>
```

:::fragment fadeUp
A continuum from executable model to machine-checked specification and proof.
:::

:::notes
1:05-1:40. Mark the inference clearly as yours.

Say: “The interesting question is not whether Python is bad, or whether Haskell
is bad. It is what remains distinctive when code generation makes an
application cheap to port. My bet is that Lean has a stronger answer.”
:::

# One language, two jobs

```html
<div class="jobs">
  <div class="job">
    <p class="job-kicker">JOB ONE</p>
    <h3>Build the program</h3>
    <p>strict functional code</p>
    <p>arrays, loops, IO, errors</p>
    <p>native compilation and Lake libraries</p>
  </div>
  <div class="plus">+</div>
  <div class="job proof-job">
    <p class="job-kicker">JOB TWO</p>
    <h3>State why it is right</h3>
    <p>dependent types</p>
    <p>propositions and proofs in the language</p>
    <p>a small kernel checks the result</p>
  </div>
</div>
<p class="source"><a href="https://lean-lang.org/">Lean is officially described as both a programming language and proof assistant · lean-lang.org</a></p>
```

:::notes
1:40-2:10.

Say: “Python alone can replace an application. Replacing a Lean application
that also serves as its checked specification changes the product. But Lean
only earns that advantage if job one is real—if it can do boring programming.”
:::

# The boring part is the point

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
2:10-2:35. Click `sampleCount` if you want Verso's code info panel, but do not
linger. This slide is also the fallback if the editor is unavailable.

Say: “A record, a function, an explicit error, and an evaluated result. The
deck itself is compiled by Lean. Now let me do the less toy version live.”
:::

# LIVE — prove job one first

```html
<p class="live">record → function → <code>Except</code> → <code>Array</code> → typed scene props → JSON → SVG</p>
<div class="live-steps">
  <span>3 × 3 → 4 × 3</span>
  <span>success → explicit error</span>
  <span>9 samples → 600 multivectors</span>
</div>
<p class="switch">Switch to Cursor · <code>OrdinaryProgrammingDemo.lean</code></p>
```

:::notes
2:35-9:45. Switch to Cursor.

1. In `OrdinaryProgrammingDemo.lean`, show `tinyGrid`, `swirlField`, and
   `sampleCount`.
2. Put the cursor on the successful `#eval`: `Except.ok 9`.
3. Edit only `xCount := 3` to `xCount := 4`; show `Except.ok 12`.
4. Show the final invalid-grid command and its explicit error.
5. Switch to `MultivectorFieldDemo.lean`, click `#html`, toggle grade 2 off/on,
   play/pause, drag the empty background once, and reset.

Use the plain explanation: number, arrow, oriented plane, oriented volume.
Say once that these are Float computations, not proved real-number facts.

After the visual, return to this deck and advance once.
:::

# One program, three reusable boundaries

```lean
import Grassmann       -- packed Clifford runtime
import GrassmannFields -- functions, grids, sampling, validation
import GrassmannViz    -- typed scene and offline InfoView
```

$$`F_0(p)=v(p)+p\,v(p)+\tau(p)I`

$$`F_\theta(p)=R_\theta F_0(p)\operatorname{reverse}(R_\theta)`

```html
<div class="ownership"><b>Lean owns</b> positions, products, coefficients, 24 frames, validation<br><b>the view owns</b> projection, glyph geometry, interaction, SVG</div>
```

:::notes
9:45-10:45.

Say: “The basic file imports only the renderer-neutral field library. The
visual opts into a separate InfoView library. The JavaScript does not perform a
Clifford product, rotate a coefficient, resample, or interpolate a frame.”

Explain only one algebraic fact: `p*v` contributes scalar and oriented-plane
parts. The vector term gives arrows; the pseudoscalar term gives halos.
:::

# Not “Haskell bad”

```html
<div class="closing">
  <p>Haskell's strengths held up.</p>
  <p>Lean's niche is not “nicer functional syntax.”</p>
  <p class="closing-main">Lean is an ordinary language<br><span>whose second job is not ordinary.</span></p>
</div>
```

:::fragment fadeUp
*program → test → specification → proof → editor tool*<br>
[browser demo](../demo/) · [presenter tutorial](../tutorial/) · [one-screen cue card](../cue-card/)
:::

:::notes
10:45-12:00.

Close: “So my claim is narrower than ‘Lean beats Haskell at everything,’ and I
think more interesting. Lean is better differentiated. You can start with
records, functions, arrays, errors, and a UI; then move selected invariants into
dependent types and proofs without changing languages. That gives Lean a
reason to exist even when Python is easy to generate.”

Repeat the boundary: tonight's visual is numerical runtime evidence, not a
formal proof. Stop at 12:00 and use the remaining three minutes for questions.
:::
