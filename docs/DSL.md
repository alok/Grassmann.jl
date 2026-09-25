# Interactive DSL: spec (draft, 2026-09-25)

Status: **draft, not started.** It is scheduled after feature and performance parity with Julia.
Decisions marked **(open)** are for Alok to confirm; everything else is the default plan.

## 1. Goal

Make using this library interactively as pleasant as `julia> using Grassmann; @basis ℝ^3`, and
better than it where Lean can help. Concretely:

1. You can type Julia-style geometric algebra into Lean and get Julia's answer, printed the way Julia
   prints it.
2. The same text runs at typed-kernel speed: fusion is automatic, so you don't write `fused%`.
3. Results render in the infoview as tables, colors and 3-D views, not just strings.
4. Mistakes (for example a grade mismatch, a wrong space or a non-invertible element) get messages
   that say what to write instead.
5. A terminal REPL (`lake exe ga`) for people who never open an editor.

Non-goals:
- A full Julia parser. The DSL covers the subset the Grassmann/Cartan docs use.
- Replacing the typed API. The DSL elaborates *to* it.

## 2. What exists today (inputs to the design)

| Piece | Where | Use in the DSL |
|---|---|---|
| Operator notation (∧ ∨ ⋅ ⨼ ⨽ × ⊛ ⊘ ⋆ ~ ! ₊ ₋ …) | `Grassmann/Notation.lean` | the typed-term side of `ga!` |
| Space literals `S!"+++"`, `D!"…"`, `V!"…"`, `ℝ^n`, `Λ(V)`, `Λ!"…"` | `DirectSum/Parse.lean`, `DirectSum/Basis.lean` | space expressions |
| `basis!`, `dualbasis!`, `mixedbasis!` (Julia `@basis`) | `Grassmann/Basis.lean` | `@basis` inside a block |
| literals `chain![…]`, `mv![…]`, `spinor![…]`, `op![…]`, … | `Grassmann/Types/Multivector.lean`, `Grassmann/Forms/Literal.lean` | constructor calls |
| `fused% e`, `batch% e`, `batchInto% e` | `Grassmann/Fuse.lean`, `Grassmann/Batch/Elab.lean` | automatic fusion backend |
| Dynamic layer `TA V α` (Julia result kinds and printing) | `Grassmann/Dynamic/**` | untyped/REPL evaluation |
| Julia-subset parser and interpreter (docs corpus) | `Tests/Golden/Docs{Parse,Interp,Ops,Eval}.lean` | seed of the REPL; move into a library |
| `clifford` tactic, `grassmann` grind set | `Grassmann/Tactic*`, `Grassmann/Spec/**` | `ga!`-level equational proofs |
| LeanPlot `#plot`/`#figure` infoview widgets | LeanPlot `widgets/` | field plots from `#ga` |

## 3. Components

### 3.1 `ga!{ … }` term block (Julia grammar, typed result)

- A new syntax category `gaTerm` with **Julia's precedences**. The Lean-level infixes keep Lean's
  precedences because ∧/∨ must still parse as `Prop` connectives outside the block. Julia's
  table: `∨ + - | ⊻` at plus level; `∧ * / \ ⋅ × ⨼ ⨽ ⊛ ⊘ ∘` at times level; `^` binds tighter
  and is right-associative; prefix `~ ! ⋆ -`; postfix `'`, `₊`, `₋`.
- **Juxtaposition of a numeric literal and an identifier or parenthesized expression**
  (`2v1`, `3.5v₁₂`, `2(v1+v2)`) is a scalar multiplication, as in Julia. Juxtaposition of two
  identifiers is an error that suggests `*`.
- Identifiers `v1`, `v12`, `v₁₂`, `e1`, `ϵ1`, `∞`, `∅`, … resolve against the space in scope. The
  space comes from the innermost `@basis`, a `ga! (V := ℝ3) { … }` header, or the expected type.
- Calls: `exp(x)`, `log`, `sqrt`, `inv`, `abs`, `norm`, `unit`, `↑`/`↓`, `grade(x, k)` (Julia's
  `x(k)` is also accepted), `Chain{V,1}(1,2,3)`, `Multivector{V}(…)`, `TensorOperator(…)`.
- `ga!` expands to the **typed** API: each subterm gets its static kind (Chain/Half/Multivector/
  Single/Couple). The result is an ordinary Lean term, so it can appear inside definitions,
  proofs and `#eval`.
- **Auto-fusion.** When the whole block is a typed expression over one space, it elaborates
  through `fused%` (one allocation, straight-line code). Scalar-valued blocks allocate nothing.
  `ga! (fuse := false)` opts out, for debugging.

### 3.2 `#ga` command (evaluate and show)

- `#ga v1 + 2v12` elaborates as in 3.1, evaluates, prints Julia's string (`1v₁ + 2v₁₂`), and
  attaches an infoview widget with:
  - the blade table: blade, grade, coefficient, with grade-colored rows;
  - kind, space and metric;
  - for vectors and bivectors in 2-D/3-D (or conformal points), a 3-D view (arrows, oriented
    planes, circles or spheres for CGA round objects);
  - for fields (Cartan), a LeanPlot figure (streamplot, surface or contour, whichever fits).
- `#ga @basis ℝ^3` declares a basis for the rest of the file (same as `basis!`).

### 3.3 Terminal REPL `lake exe ga`

- Promote the docs interpreter (`Tests/Golden/Docs*.lean`) into a library, `Grassmann.Julia`:
  parser, environment, evaluator on `TA`, and Julia-exact printing.
- The executable is a `ga>` prompt with history, `@basis` and multi-line input. Its output is
  byte-identical to Julia's for every statement the docs corpus covers.
- The golden test: replay all 501 docs statements through the REPL library and require the
  same results as `Tests/Golden/Docs`. That makes the REPL correct by construction for the
  corpus.

### 3.4 Delaborators and hover

- Elements delaborate as `ga!{ 1v₁ + 2v₁₂ }`-style literals (or as Julia strings when the
  expression is closed), not as `{ data := #[…] }` structures.
- Hovering a `ga!` subterm shows its static kind, grade and space.

### 3.5 Friendly errors

In the `ga!` elaborator (where the kinds are known), with a "try this" suggestion where one
exists:
- grade mismatches under `+`, for example `Chain ℝ3 1 + Chain ℝ3 2`: the result is a
  Multivector; suggest the explicit promotion or `mv!`;
- mixing spaces: name both spaces and suggest `↑`/`↓` or an explicit embedding;
- `inv`/`/` of an element that is not invertible (when it is detected statically, for example
  a null vector in CGA);
- unknown identifiers that look like blades (`v4` in ℝ3): list the space's generators.

### 3.6 Proof integration

`ga!` terms are ordinary terms, so `clifford`/`grind` apply. Add a `ga_simp` simp set that
normalizes `ga!`-produced terms to the `Cl g` model, so equalities stated in Julia syntax
(`example : ga!{ (v1 ∧ v2) ⋅ v2 } = ga!{ v1 } := by clifford`) are one-liners.

## 4. Testing and quality gates

- Every docs-corpus statement must evaluate the same through (a) `Tests/Golden/Docs`,
  (b) `ga!` + `toString` where it is typed-expressible, and (c) the REPL library.
- Fusion equivalence: `ga!{e}` equals `ga! (fuse := false) {e}` bit-for-bit on random inputs
  (property tests).
- Precedence tests: a table of Julia expressions with Julia's parse (from `Meta.parse` in the
  oracle), compared against the `gaTerm` parse tree.
- Perf: `ga!` blocks in the bench suite must match `fused%` timings (no DSL overhead).
- Error messages: `#guard_msgs` tests for every friendly error.

## 5. Milestones

1. `gaTerm` grammar, Julia precedences, juxtaposition, identifiers → typed API. `#ga` printing.
2. Auto-fusion through `fused%`; precedence and fusion goldens.
3. Blade-table widget and 3-D view; delaborators; hover.
4. `Grassmann.Julia` library (moved docs interpreter) and `lake exe ga`.
5. Friendly errors; `ga_simp` and proof examples.
6. Cartan field plotting from `#ga`.

## 6. Open questions

- **(open)** Block syntax: `ga!{ … }` vs `ga⟪ … ⟫` vs a `julia` code block (`#julia`).
  Default: `ga!{…}` for terms and `#ga` for commands.
- **(open)** Should `ga!` accept Julia's `x(k)` grade selection? It collides with function
  application of elements used as operators (Julia also overloads it). Default: accept it when
  `k` is a numeric literal.
- **(open)** Unicode subscripts only (`v₁₂`), or also ASCII `v12`? Default: both, printing
  subscripts.
- **(open)** REPL: a standalone executable in the root package, or a separate `repl/` Lake
  package (so the root stays small)? Default: the root package; it has no dependencies.
