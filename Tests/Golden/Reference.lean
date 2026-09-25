import Tests.Golden.Registry

/-!
# The DirectSum reference evaluator (values only)

The element oracle's `ref` semantics (docs/port-notes/oracle-schema.md §8.2–8.4) are the
linear and bilinear extensions of the blade-level rules: arith is the exact linear
combination of the operands' dense vectors, the products and the linear unary maps act on the
operands converted to `Multivector`. DirectSum's kernel interface (`DirectSum.Ops`:
`terms₁`/`terms₂`, oracle-verified blade by blade) is exactly that blade level, so extending
it over dense vectors gives an independent **value** evaluator for

* arith: `add`, `sub`, `neg`, `mul`/`div`/`rdiv` by a number;
* products: every op except `sandwich`/`tsandwich` (whose reference projects, §8.3);
* unary: `neg`, the involutions, complements, `metric`/`antimetric`, `even`/`odd`,
  `real`/`imag`, and the grade projections `scalar`…`volume`, `grade:k`.

It checks values only (`Aspects.kind/str/compact := false`): Julia's result *kind* comes from
the Grassmann layer, which registers its own evaluators later and then takes precedence.
Values compare as numbers (`ValueMode.componentwise 0 0`: exact, with `-0.0 = 0.0`), because a
dense-vector accumulation does not reproduce which zero coefficients Julia stores negated. A
golden output that is a plain number (`grade(x, k)` of a term, `imag` of a Couple) is compared
as that number times `One` (the schema's convention for numbers, §8.2).

Tables are built once per (shard, op) (`Registration.prepare`); the extensions iterate over
the nonzero operand coefficients only.
-/

namespace Tests.ElementOracle

open DirectSum

/-- The DirectSum unary operation of an oracle op key (schema §12). -/
def unOpOf? : String → Option UnOp
  | "reverse" => some .reverse
  | "involute" => some .involute
  | "clifford" => some .clifford
  | "antireverse" => some .antireverse
  | "complementright" => some .complementright
  | "complementleft" => some .complementleft
  | "hodge" => some .complementrighthodge
  | "complementlefthodge" => some .complementlefthodge
  | "metric" => some .metric
  | "antimetric" => some .antimetric
  | "even" => some .even
  | "odd" => some .odd
  | "real" => some .real
  | "imag" => some .imag
  | _ => none

/-- The DirectSum binary operation of an oracle op key (schema §12). -/
def binOpOf? : String → Option BinOp
  | "mul" => some .mul
  | "wedge" => some .wedge
  | "vee" => some .vee
  | "contraction" => some .contraction
  | "lcontraction" => some .contractionLeft
  | "lshift" => some .contractionRevLeft
  | "rshift" => some .contractionRevRight
  | "revmul" => some .reverseMul
  | "scalarprod" => some .scalarContraction
  | "cross" => some .cross
  | "veedot" => some .veedot
  | "antidot" => some .antidot
  | _ => none

/-- The grade kept by a projection op (`volume` keeps `grade(V)`). -/
def projectionGrade? (V : TensorBundle) : String → Option Nat
  | "scalar" => some 0
  | "vector" => some 1
  | "bivector" => some 2
  | "trivector" => some 3
  | "volume" => some V.grade
  | op => if op.startsWith "grade:" then (op.drop 6).toString.toNat? else none

/-- A real coefficient vector to compute with. -/
inductive NumVec where
  /-- Exact coefficients. -/
  | exact (v : Array Rat)
  /-- Float coefficients. -/
  | float (v : FloatArray)
  deriving Inhabited

/-- A `Rat` as the nearest double (exact for the metric factors that occur). -/
@[inline] def ratToFloat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

namespace NumVec

/-- Length. -/
def size : NumVec → Nat
  | .exact v => v.size
  | .float v => v.size

/-- As doubles. -/
def toFloats : NumVec → FloatArray
  | .exact v => FloatArray.mk (v.map ratToFloat)
  | .float v => v

/-- The positions of the nonzero coefficients (NaN counts as nonzero). -/
def support : NumVec → Array Nat
  | .exact v => (List.range v.size).toArray.filter fun i => v[i]! != 0
  | .float v => (List.range v.size).toArray.filter fun i => !(v[i]! == 0)

/-- As an oracle coefficient vector. -/
def toCoeffs : NumVec → Coeffs
  | .exact v => .exact v
  | .float v => .float v

/-- The operand of an element in an `n`-generator space: its dense vector, or a number
`s` as `s·One`. `none` for complex/display-only coefficients and elements without dense
values (Infinity, Phasor). -/
def ofElem? (N : Nat) (e : GoldenElem) : Option NumVec :=
  let embed := fun (c : Coeffs) => match c with
    | .exact v => some (NumVec.exact ((Array.replicate N (0 : Rat)).set! 0 (v[0]?.getD 0)))
    | .float v => some (NumVec.float ((FloatArray.mk (Array.replicate N 0)).set! 0 (v[0]?.getD 0)))
    | _ => none
  match e.dense, e.value with
  | some (.exact v), _ => if v.size == N then some (.exact v) else none
  | some (.float v), _ => if v.size == N then some (.float v) else none
  | some _, _ => none
  | none, some v => if e.kind == .number || e.kind == .bool then embed v else none
  | none, none => none

/-- Scale by an exact factor. -/
def scale (c : Rat) : NumVec → NumVec
  | .exact v => .exact (v.map (c * ·))
  | .float v => let f := ratToFloat c; .float (FloatArray.mk (v.data.map (f * ·)))

/-- Componentwise `a + s·b` (floats if either is). -/
def axpy (s : Rat) (a b : NumVec) : NumVec :=
  match a, b with
  | .exact x, .exact y => .exact ((x.zip y).map fun (p, q) => p + s * q)
  | _, _ =>
    let x := a.toFloats
    let y := b.toFloats
    let f := ratToFloat s
    .float (FloatArray.mk ((List.range x.size).toArray.map fun i => x[i]! + f * y[i]!))

/-- Keep only the coefficients of grade `g`. -/
def project (n g : Nat) (x : NumVec) : NumVec :=
  let basis := Leibniz.indexBasisAll n
  let keep := fun (i : Nat) => Bits.popcount (basis[i]?.getD 0) == g
  match x with
  | .exact v => .exact ((List.range v.size).toArray.map fun i => if keep i then v[i]! else 0)
  | .float v => .float (FloatArray.mk ((List.range v.size).toArray.map fun i => if keep i then v[i]! else 0))

end NumVec

/-- Per blade (dense position): the terms `(position, coefficient)` of a unary op, or
`none` where DirectSum rejects the blade (or a tangent-nested term occurs). -/
abbrev UnaryTable := Array (Option (Array (Nat × Rat)))

/-- Per blade pair: the terms of a binary op. -/
abbrev BinaryTable := Array (Array (Option (Array (Nat × Rat))))

/-- Position-indexed terms of a blade-level result. -/
def placeTerms (n : Nat) (r : Except String (Array BladeTerm)) : Option (Array (Nat × Rat)) :=
  match r with
  | .ok ts => if ts.any (·.z != 0) then none else some (ts.map fun t => (Leibniz.basisRank n t.bits, t.coef))
  | .error _ => none

/-- The unary table of an op in `V`. -/
def unaryTable (V : TensorBundle) (op : UnOp) : UnaryTable :=
  (Leibniz.indexBasisAll V.n).map fun b => placeTerms V.n (V.terms₁ op b)

/-- The binary table of an op in `V`. -/
def binaryTable (V : TensorBundle) (op : BinOp) : BinaryTable :=
  let basis := Leibniz.indexBasisAll V.n
  basis.map fun a => basis.map fun b => placeTerms V.n (V.terms₂ op a b)

/-- Apply a unary table to an operand (over its nonzero coefficients). -/
def applyUnary (N : Nat) (t : UnaryTable) (x : NumVec) : Option NumVec := do
  match x with
  | .exact v =>
    let mut out := Array.replicate N (0 : Rat)
    for i in x.support do
      for (ic, c) in ← t[i]?.join do out := out.modify ic (· + c * v[i]!)
    return .exact out
  | .float v =>
    let mut out := FloatArray.mk (Array.replicate N 0)
    for i in x.support do
      for (ic, c) in ← t[i]?.join do out := out.set! ic (out[ic]! + ratToFloat c * v[i]!)
    return .float out

/-- Apply a binary table to two operands (over their nonzero coefficient pairs). -/
def applyBinary (N : Nat) (t : BinaryTable) (x y : NumVec) : Option NumVec := do
  let sx := x.support
  let sy := y.support
  match x, y with
  | .exact u, .exact w =>
    let mut out := Array.replicate N (0 : Rat)
    for i in sx do
      for j in sy do
        for (ic, c) in ← (t[i]?.bind (·[j]?)).join do out := out.modify ic (· + c * u[i]! * w[j]!)
    return .exact out
  | _, _ =>
    let u := x.toFloats
    let w := y.toFloats
    let mut out := FloatArray.mk (Array.replicate N 0)
    for i in sx do
      for j in sy do
        for (ic, c) in ← (t[i]?.bind (·[j]?)).join do
          out := out.set! ic (out[ic]! + ratToFloat c * u[i]! * w[j]!)
    return .float out

/-- The evaluator result carrying only values. -/
def valuesOnly (x : NumVec) : GoldenElem := { kind := .multivector, dense := some x.toCoeffs }

/-- The number `s` of a Number operand. -/
def numberOf? (e : GoldenElem) : Option Rat :=
  if e.kind != .number then none else
  match e.value.map (·.get 0) with
  | some (Scalar.exact q) => some q
  | some (Scalar.float f) => floatToRat f
  | _ => none

/-- Arith (schema §8.2): the exact linear combination of the operands (a number `s` is
`s·One`); `mul`/`div`/`rdiv` scale by a number operand. -/
def arithEval (N : Nat) (op : String) : Evaluator := fun _ args => do
  let a ← args[0]?
  match op, args[1]? with
  | "neg", none => return valuesOnly ((← NumVec.ofElem? N a).scale (-1))
  | "add", some b => return valuesOnly (NumVec.axpy 1 (← NumVec.ofElem? N a) (← NumVec.ofElem? N b))
  | "sub", some b => return valuesOnly (NumVec.axpy (-1) (← NumVec.ofElem? N a) (← NumVec.ofElem? N b))
  | "mul", some b =>
    match numberOf? a, numberOf? b with
    | some s, _ => return valuesOnly ((← NumVec.ofElem? N b).scale s)
    | _, some s => return valuesOnly ((← NumVec.ofElem? N a).scale s)
    | none, none => none
  | "div", some b | "rdiv", some b =>
    let s ← numberOf? b
    if s == 0 then none
    return valuesOnly ((← NumVec.ofElem? N a).scale s⁻¹)
  | _, _ => none

/-- `directsum/reference`, prepared for a shard's space and an op: the DirectSum tables are
built here, once per (shard, op). -/
def referencePrepare (p : PrepCtx) : Prepared :=
  let op := p.op
  match p.space with
  | none => ⟨fun _ _ => none⟩
  | some d =>
    let V := d.bundle
    let N := 2 ^ V.n
    if p.suite == "arith" then ⟨arithEval N op⟩
    else if let some u := unOpOf? op then
      let t := unaryTable V u
      ⟨fun _ args => do
        let a ← args[0]?
        if args.size != 1 then none
        return valuesOnly (← applyUnary N t (← NumVec.ofElem? N a))⟩
    else if let some bop := binOpOf? op then
      let t := binaryTable V bop
      ⟨fun _ args => do
        let a ← args[0]?
        let b ← args[1]?
        return valuesOnly (← applyBinary N t (← NumVec.ofElem? N a) (← NumVec.ofElem? N b))⟩
    else if op == "neg" then
      ⟨fun _ args => do
        let a ← args[0]?
        if args.size != 1 then none
        return valuesOnly ((← NumVec.ofElem? N a).scale (-1))⟩
    else if let some g := projectionGrade? V op then
      ⟨fun _ args => do
        let a ← args[0]?
        if args.size != 1 then none
        return valuesOnly (NumVec.project V.n g (← NumVec.ofElem? N a))⟩
    else ⟨fun _ _ => none⟩

/-- Where DirectSum's blade rules keep a documented Julia basis-level defect whose correct
behaviour (the `correct` field of `defects.json`) is the container level. -/
def directSumKnownIssues : Array KnownIssue := #[
  { id := "directsum-conformal-blade-complement",
    note := "DirectSum.TensorBundle.complementright/complementleft/bladeMetric apply Julia's \
      basis-level null factors 2, ½ (and cl∘⋆ for metric) in conformal spaces; the element \
      oracle's container level, which defects.json names correct (conformal-blade-complement), \
      does not. Owner: DirectSum (BladeAlgebra.lean)",
    tables := #[{ suite := some (Glob.compile "unary"), space := some (Glob.compile "CGA*"),
                  op := some (Glob.compile "complementright|complementleft|metric") }] },
  { id := "directsum-projective-blade-metric",
    note := "DirectSum.TensorBundle.bladeMetric/antimetric return 𝟎 for a blade holding a lone \
      ∞ or ∅ in ∞-only/∅-only spaces (Julia's basis-level rule); the container level, which \
      defects.json names correct (projective-blade-metric), scales by v∞² = +1 / v∅² = -1. \
      Owner: DirectSum (BladeAlgebra.lean)",
    tables := #[{ suite := some (Glob.compile "unary"), space := some (Glob.compile "INF*|ORG*"),
                  op := some (Glob.compile "metric|antimetric") }] }
]

/-- The reference registration (values only; see the module docstring). -/
def referenceRegistration : Registration :=
  { name := "directsum/reference", suite := "arith|products|unary", op := "*",
    prepare := referencePrepare,
    aspects := { kind := false, str := false, compact := false },
    floatTol := some (0, 0),
    knownIssues := directSumKnownIssues }

end Tests.ElementOracle
