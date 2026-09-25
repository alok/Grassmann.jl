import Tests.Golden.DocsInterp

/-!
# The docs evaluator (`grassmann/docs`)

The docs suite (`oracle/golden/docs/*.json`, 58 shards, 501 statements; oracle-schema.md
§8.8) records README and documentation statements evaluated REPL-style in a Julia sandbox.
This evaluator replays each shard's statements, in order, on the dynamic layer
(`Tests.Golden.DocsInterp`: a Julia-subset interpreter whose operators and functions are the
`Grassmann.TA` API) and compares Julia's kind, `T`, `V`, `grade`/`bits`, dense values
(bitwise), `str` and `compact_str` of every value it models; displays of composite values
(tuples, vectors, `typeof`, bases, spaces, function objects) are compared as strings.

A statement the interpreter does not model (matrices, operators and forms, calculus
`∇ ∂ d`, simplicial complexes, projective `↑ ↓`, chain fields, tangent products with
tensor-valued coefficients, closure displays) is unimplemented, and so is every later
statement that uses its result. The composite statements that
`Tests.Golden.CompositeDocs` evaluates (values only) take precedence when that module
registers later.

Known issues (`docsKnownIssues`): Julia defects the docs suite does not tag (the oracle's
`defects.json` tags them only in the composite suite).
-/

namespace Tests.ElementOracle.Docs

open Lean Tests.ElementOracle

/-- Read the statements of a docs shard from the committed golden file. -/
def loadShardInputs (shard : String) : IO (Array String) := do
  let j ← loadJson (goldenRoot / "docs" / s!"{shard}.json")
  let cs ← IO.ofExcept (j.getObjValAs? (Array Json) "cases")
  return cs.map fun c => (c.getObjValAs? String "input").toOption.getD ""

/-- The statements of a docs shard, in order (the file read at preparation time). -/
private unsafe def shardInputsImpl (shard : String) : Array String :=
  match unsafeIO (loadShardInputs shard) with
  | .ok xs => xs
  | .error _ => #[]

/-- The statements of a docs shard, in order (read once per shard). -/
@[implemented_by shardInputsImpl]
opaque shardInputs (shard : String) : Array String

/-- A match table for one docs statement. -/
def docsInput (input : String) : MatchTable :=
  { suite := some (Glob.compile "docs"), input := some (Glob.compile input) }

/-- Julia defects on docs statements that `defects.json` tags only in other suites. -/
def docsKnownIssues : Array KnownIssue := #[
  { id := "docs-couple-inv-hyperbolic",
    note := "Julia defect couple-inv-hyperbolic (inv of a Couple whose blade squares to +1 uses the " ++
      "elliptic formula: inv(2+v1) = 0.4 - 0.2v₁; the inverse is (2-v1)/3). defects.json tags it " ++
      "only in the composite suite; request: add the docs match {suite: docs, input: \"inv(2+v1)\"} " ++
      "to oracle/defects.toml",
    tables := #[docsInput "inv(2+v1)"] },
  { id := "docs-conformal-blade-complement",
    note := "Julia defect conformal-blade-complement (the term-level complements of conformal blades " ++
      "apply Leibniz's null factors 2, ½: !v∞ = 2v∅₁₂, !v∅ = -0.5v∞₁₂ in S\"∞∅++\"; the container " ++
      "level, which defects.json names correct, gives v∅₁₂ and -v∞₁₂). defects.json tags it in the " ++
      "unary/products suites only; request: add docs matches for algebra.md:1354 cases 5, 6, 8",
    tables := #[docsInput "⋆v∞, !v∞, ⋆v∅, !v∅", docsInput "!v∞ * v12 == -2v∅, !v∅ * v12 == v∞/2",
      docsInput "v∞ * !v∞, v∅ * !v∅"] },
  { id := "docs-interop-wedge-sign",
    note := "Julia's cross-space interop (design.md:172) evaluates Λ(ℝ^2).v1+v2 ∧ Λ(ℝ^3).v3 as " ++
      "-v₁₃ - v₂₃ (the operands swapped); (v₁ + v₂) ∧ v₃ = v₁₃ + v₂₃, which the port computes after " ++
      "embedding into the union ℝ^3. Request: a defect entry (interop-operand-swap) in oracle/defects.toml",
    tables := #[{ docsInput "a ∧ b" with block := some (Glob.compile "design.md:172*") }] }
]

/-- The docs registration: each shard is replayed once (`prepare`), each case reads its
statement's result; values are compared bit for bit, except for statements that ran a series
or a dense closed form (`approx`), which `docsApproxRegistration` compares with the
composite tolerance. -/
def docsRegistration : Registration :=
  { name := "grassmann/docs", suite := "docs", op := "docs"
    prepare := fun p =>
      let results := runStatements (sandboxOf p.shard) (shardInputs p.shard)
      ⟨fun ctx _ => match (results[ctx.case.idx]?).join with
        | some (e, false) => some e
        | _ => none⟩
    knownIssues := docsKnownIssues }

/-- The statements that ran a series (`exp`, `log`, `sqrt`, … of a container): Julia's generated
loops sum in another order, so values are compared with `rtol = 1e-12`, `atol = 1e-14` (the
kinds and strings exactly). -/
def docsApproxRegistration : Registration :=
  { name := "grassmann/docs-series", suite := "docs", op := "docs"
    prepare := fun p =>
      let results := runStatements (sandboxOf p.shard) (shardInputs p.shard)
      ⟨fun ctx _ => match (results[ctx.case.idx]?).join with
        | some (e, true) => some e
        | _ => none⟩
    floatTol := some (1e-12, 1e-14)
    knownIssues := docsKnownIssues }

initialize
  register docsRegistration
  register docsApproxRegistration

end Tests.ElementOracle.Docs
