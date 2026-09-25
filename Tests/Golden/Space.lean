import Tests.Golden.Elem

/-!
# Space descriptors → `DirectSum.TensorBundle`

A per-space shard carries a self-contained descriptor of its space
(docs/port-notes/oracle-schema.md §5). This module decodes it into a
`DirectSum.TensorBundle` in two independent ways and checks Julia's printing against
DirectSum's:

1. from the decoded fields (`n`, `metric`, `hasinf`, `hasorigin`, `dyadmode`, `diffvars`,
   `diffmode`; a dual `DiagonalForm` stores the negation of the effective diagonal);
2. by evaluating the `julia` source of the bundle (`S"∞∅+++"`, `D"1,2,-3"`, `4`,
   `(S"+++")'`, `S"++"⊕(S"++")'`, `tangent(S"++",2,2)`) with DirectSum's own parsers and
   space algebra (`parseSignature`, `parseDiagonal`, `adjoint`, `oplus`, `tangent`).

`checkSpace` then compares: both bundles, `show` against `showHandle` (Julia
`string(Submanifold(bundle))`), `show_bundle` against `toString` (an `Int` manifold shows as
its dimension), `grade`, `options`, `isdiag`, `conformal`, `isdual`, the dense basis order
against `Leibniz.indexBasisAll`, the blade `names` against `bladeLabel`, and `Isq` (the
scalar part of `I·I`) against DirectSum's blade product.
-/

namespace Tests.ElementOracle

open Lean DirectSum

/-- The `metric` object of a descriptor. -/
inductive MetricDesc where
  /-- `{"kind": "signature", "neg": …}` (DirectSum's raw metric word). -/
  | signature (neg : UInt64)
  /-- `{"kind": "diagonal", "diag": […]}` (effective values `e_k²`). -/
  | diagonal (diag : Array Rat)
  /-- `{"kind": "euclidean"}` (Julia's `Int` manifold). -/
  | euclidean
  deriving BEq, Repr, Inhabited

/-- A decoded space descriptor (schema §5), with the `TensorBundle` it denotes. -/
structure SpaceDesc where
  /-- Registry name (= shard name). -/
  name : String
  /-- Julia source of the bundle. -/
  julia : String
  /-- Prose. -/
  description : String
  /-- `string(Submanifold(bundle))`: the space elements print with. -/
  showStr : String
  /-- `show` of the bundle itself. -/
  showBundle : String
  /-- `mdims`. -/
  n : Nat
  /-- `grade(V)`. -/
  grade : Nat
  /-- The metric. -/
  metric : MetricDesc
  /-- Raw DirectSum option word. -/
  options : Nat
  /-- Generator 1 is `∞`. -/
  hasinf : Bool
  /-- The `∅` generator is present. -/
  hasorigin : Bool
  /-- `hasinf ∧ hasorigin`. -/
  conformal : Bool
  /-- Diagonal metric. -/
  isdiag : Bool
  /-- 0 plain, 1 dual, −1 mixed. -/
  dyadmode : Int
  /-- Dual space. -/
  isdual : Bool
  /-- Number of tangent variables. -/
  diffvars : Nat
  /-- Tangent order. -/
  diffmode : Nat
  /-- Scalar part of `I·I` (`none` when Julia could not compute it). -/
  Isq : Option Int
  /-- Every basis blade in dense order (`[]` when `n > 8`). -/
  basis : Array UInt64
  /-- Printed blade names, same order. -/
  names : Array String
  /-- The bundle built from the fields. -/
  bundle : TensorBundle
  deriving Inhabited

/-- The keys of a space descriptor (schema §5). -/
def spaceKeys : List String :=
  ["name", "julia", "description", "show", "show_bundle", "n", "grade", "metric", "options",
   "hasinf", "hasorigin", "conformal", "isdiag", "dyadmode", "isdual", "diffvars", "diffmode",
   "Isq", "basis", "names"]

/-- A required string field of a space descriptor. -/
private def reqStr (j : Json) (k : String) : Except String String :=
  match j.getObjVal? k with
  | .ok (.str s) => .ok s
  | _ => .error s!"space.{k}: string expected"

/-- A required natural-number field of a space descriptor. -/
private def reqNat (j : Json) (k : String) : Except String Nat :=
  match (j.getObjValD k).getNat? with
  | .ok n => .ok n
  | _ => .error s!"space.{k}: natural number expected"

/-- A required integer field of a space descriptor. -/
private def reqInt (j : Json) (k : String) : Except String Int :=
  match (j.getObjValD k).getInt? with
  | .ok n => .ok n
  | _ => .error s!"space.{k}: integer expected"

/-- A required Bool field of a space descriptor. -/
private def reqBool (j : Json) (k : String) : Except String Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => .ok b
  | _ => .error s!"space.{k}: Bool expected"

/-- The bundle a descriptor's fields denote. -/
def bundleOfFields (n : Nat) (m : MetricDesc) (hasinf hasorigin : Bool) (dyadmode : Int)
    (diffvars diffmode : Nat) : TensorBundle :=
  let metric : Metric := match m with
    | .signature neg => .signature neg
    | .euclidean => .euclid
    -- DirectSum stores the primal diagonal; the descriptor has the effective one
    | .diagonal d => .diagonal (if dyadmode > 0 then d.map (- ·) else d)
  { n, metric, hasinf, hasorigin, dyadmode, diffvars, diffmode }

/-- Decode a space descriptor (schema §5). -/
def SpaceDesc.decode (j : Json) : Except String SpaceDesc := do
  let .obj kvs := j | throw "space is not an object"
  let keys := kvs.toList.map (·.1)
  unless keys.length == spaceKeys.length && spaceKeys.all keys.contains do
    throw s!"space keys {keys}"
  let n ← reqNat j "n"
  let mj := j.getObjValD "metric"
  let metric ← match mj.getObjVal? "kind" with
    | .ok (.str "signature") =>
      match (mj.getObjValD "neg").getNat? with
      | .ok neg => pure (MetricDesc.signature neg.toUInt64)
      | _ => throw "metric.neg: natural number expected"
    | .ok (.str "diagonal") =>
      let some d := (mj.getObjValD "diag").getArr?.toOption | throw "metric.diag: array expected"
      let vals ← d.mapM fun x => match x with
        | .str s => match parseInt64? s with
          | some v => pure (v : Rat)
          | none => throw s!"metric.diag entry {s.quote} is not an Int64"
        | _ => throw "metric.diag entry is not a string"
      pure (MetricDesc.diagonal vals)
    | .ok (.str "euclidean") => pure .euclidean
    | _ => throw s!"bad metric {mj.compress}"
  let Isq ← match j.getObjVal? "Isq" with
    | .ok .null => pure none
    | .ok (.str s) => match parseInt64? s with
      | some v => pure (some v)
      | none => throw s!"space.Isq {s.quote} is not an Int64"
    | _ => throw "space.Isq: string or null expected"
  let basis ← match (j.getObjValD "basis").getArr? with
    | .ok a => a.mapM fun x => match x.getNat? with
      | .ok b => pure b.toUInt64
      | _ => throw "space.basis entry is not a natural number"
    | _ => throw "space.basis: array expected"
  let names ← match (j.getObjValD "names").getArr? with
    | .ok a => a.mapM fun x => match x with
      | .str s => pure s
      | _ => throw "space.names entry is not a string"
    | _ => throw "space.names: array expected"
  let hasinf ← reqBool j "hasinf"
  let hasorigin ← reqBool j "hasorigin"
  let dyadmode ← reqInt j "dyadmode"
  let diffvars ← reqNat j "diffvars"
  let diffmode ← reqNat j "diffmode"
  return {
    name := ← reqStr j "name", julia := ← reqStr j "julia", description := ← reqStr j "description",
    showStr := ← reqStr j "show", showBundle := ← reqStr j "show_bundle", n, grade := ← reqNat j "grade",
    metric, options := ← reqNat j "options", hasinf, hasorigin, conformal := ← reqBool j "conformal",
    isdiag := ← reqBool j "isdiag", dyadmode, isdual := ← reqBool j "isdual", diffvars, diffmode,
    Isq, basis, names,
    bundle := bundleOfFields n metric hasinf hasorigin dyadmode diffvars diffmode }

/-! ## Evaluating the Julia source of a bundle -/

/-- A tiny evaluator for the bundle expressions of the registry (schema §5.1): string
macros `S"…"`, `D"…"`, `V"…"`, integer literals (the `Int` manifold), parentheses, pPost
`'` (adjoint), infix `⊕`, and `tangent(X[, μ[, ν]])`, all through DirectSum. -/
partial def evalBundleSrc (src : String) : Except String TensorBundle := do
  let (v, rest) ← pSum src.toList
  unless rest.all (·.isWhitespace) do throw s!"trailing input {String.ofList rest}"
  return v
where
  skipWs (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)
  /-- `pSum := pPost ("⊕" pPost)*` -/
  pSum (cs : List Char) : Except String (TensorBundle × List Char) := do
    let (a, rest) ← pPost cs
    match skipWs rest with
    | '⊕' :: r =>
      let (b, r) ← pSum r
      return (← TensorBundle.oplus a b, r)
    | r => return (a, r)
  /-- `pPost := pAtom "'"*` -/
  pPost (cs : List Char) : Except String (TensorBundle × List Char) := do
    let (a, rest) ← pAtom (skipWs cs)
    let rec primes (v : TensorBundle) : List Char → Except String (TensorBundle × List Char)
      | '\'' :: r => do primes (← v.adjoint) r
      | r => pure (v, r)
    primes a rest
  pStr (cs : List Char) : Except String (String × List Char) :=
    match cs with
    | '"' :: r =>
      let body := r.takeWhile (· != '"')
      match r.dropWhile (· != '"') with
      | '"' :: rest => .ok (String.ofList body, rest)
      | _ => .error "unterminated string macro"
    | _ => .error "string expected"
  pNat (cs : List Char) : Option (Nat × List Char) :=
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty then none else some ((String.ofList ds).toNat!, cs.dropWhile Char.isDigit)
  pAtom (cs : List Char) : Except String (TensorBundle × List Char) := do
    match cs with
    | '(' :: r =>
      let (v, r) ← pSum r
      match skipWs r with
      | ')' :: r => return (v, r)
      | _ => throw "`)` expected"
    | 'S' :: r@('"' :: _) => let (s, r) ← pStr r; return (← TensorBundle.parseSignature s, r)
    | 'D' :: r@('"' :: _) => let (s, r) ← pStr r; return (← TensorBundle.parseDiagonal s, r)
    | 'V' :: r@('"' :: _) => let (s, r) ← pStr r; return (← TensorBundle.parseBundle s, r)
    | 't' :: 'a' :: 'n' :: 'g' :: 'e' :: 'n' :: 't' :: '(' :: r =>
      let (v, r0) ← pSum r
      let mut r := skipWs r0
      let mut args : Array Nat := #[]
      while r.head? == some ',' do
        let some (k, r') := pNat (skipWs r.tail) | throw "tangent: integer argument expected"
        args := args.push k
        r := skipWs r'
      match r with
      | ')' :: rest =>
        let w := match args with
          | #[] => v.tangent
          | #[mu] => v.tangent mu
          | #[mu, nu] => v.tangent mu nu
          | _ => v
        if args.size > 2 then throw "tangent: too many arguments"
        return (w, rest)
      | _ => throw "tangent: `)` expected"
    | _ =>
      match pNat cs with
      | some (n, r) => return (TensorBundle.euclidean n, r)
      | none => throw s!"cannot evaluate {String.ofList (cs.take 20)}"

/-! ## Space displays → (bundle, subspace mask) -/

/-- Whether `c` is a Unicode subscript digit. -/
def isSubDigit (c : Char) : Bool := '₀' ≤ c && c ≤ '₉'

/-- The value of a superscript digit string (`²` ↦ 2, `¹²` ↦ 12). -/
def supValue (cs : List Char) : Nat :=
  let digit := fun (c : Char) => match c with
    | '⁰' => 0 | '¹' => 1 | '²' => 2 | '³' => 3 | '⁴' => 4
    | '⁵' => 5 | '⁶' => 6 | '⁷' => 7 | '⁸' => 8 | _ => 9
  cs.foldl (fun acc c => 10 * acc + digit c) 0

/-- Reconstruct a bundle and a subspace mask from a Julia space display (Julia
`show(::Submanifold)`, the `V` of an element or a docs `Space` value): `T^μ` prefix, `∞`/`∅`,
the metric entries (`+`/`-` for a diagonal `Signature`, `1`/`-1` for a conformal one, `1` for
the `Int` manifold, comma-separated values for a `DiagonalForm`, `_` for a generator outside
the subspace), the tangent-variable subscripts (superscripts after them for a dyadic space),
and the `'`/`*` suffix. The result is one bundle that prints this way: `showSub` of it must
give the string back (checked by the harness), which exercises DirectSum's printing of every
space the goldens mention. `none` if the string is not a space display. -/
def parseHandle? (s : String) : Option (TensorBundle × UInt64) := do
  let cs := s.toList
  let (mu, cs) := match cs with
    | 'T' :: rest => (supValue (rest.takeWhile isScriptDigit), rest.dropWhile isScriptDigit)
    | _ => (0, cs)
  let '⟨' :: rest := cs | none
  let inner := rest.takeWhile (· != '⟩')
  let after := (rest.dropWhile (· != '⟩')).drop 1
  let dyadmode : Int ← match after with
    | [] => some 0
    | ['\''] => some 1
    | ['*'] => some (-1)
    | _ => none
  let scripts := inner.filter isScriptDigit
  let body := inner.filter (!isScriptDigit ·)
  let nu := (scripts.filter isSubDigit).length
  let nu := if nu == 0 then scripts.length else nu   -- a dual tangent space uses superscripts
  let (inf, body) := match body with | '∞' :: r => (true, r) | r => (false, r)
  let (origin, body) := match body with | '∅' :: r => (true, r) | r => (false, r)
  let nulls := (if inf then 1 else 0) + (if origin then 1 else 0)
  -- metric entries: (present, value) with value the effective square (or the sign)
  let (metricKind, entries) : String × List (Bool × Rat) ←
    if body.contains ',' then
      let es ← ((String.ofList body).splitOn ",").mapM fun e =>
        if e == "_" then some (false, (1 : Rat)) else (TensorBundle.parseRat e).toOption.map (true, ·)
      some ("diagonal", es)
    else if inf && origin then
      let rec toks : List Char → Option (List (Bool × Rat))
        | [] => some []
        | '_' :: r => do pure ((false, 1) :: (← toks r))
        | '-' :: '1' :: r => do pure ((true, -1) :: (← toks r))
        | '1' :: r => do pure ((true, 1) :: (← toks r))
        | _ => none
      some ("signature", ← toks body)
    else if !body.isEmpty && body.all (fun c => c == '1' || c == '_') && !inf && !origin then
      some ("euclid", body.map fun c => (c == '1', (1 : Rat)))
    else
      let es ← body.mapM fun c => match c with
        | '+' => some (true, (1 : Rat))
        | '-' => some (true, (-1 : Rat))
        | '_' => some (false, (1 : Rat))
        | _ => none
      some ("signature", es)
  let m := entries.length
  let slots := if dyadmode < 0 then 2 * nu else nu
  let n := nulls + m + slots
  let dual := dyadmode > 0
  let metric : Metric ← match metricKind with
    | "diagonal" => some (.diagonal (entries.toArray.map fun (_, x) => if dual then -x else x))
    | "euclid" => some .euclid
    | _ =>
      -- ∅ carries a `-` bit in Julia's metric word; the ∞/∅ bits do not print
      let base : UInt64 := if origin then Bits.shl 1 (if inf then 1 else 0) else 0
      some (.signature (entries.zipIdx.foldl (fun acc ((_, x), k) =>
        if x < 0 then acc ||| Bits.shl 1 (nulls + k) else acc) base))
  let mask : UInt64 := Id.run do
    let mut mask := Bits.lowMask nulls
    for ((present, _), k) in entries.zipIdx do
      if present then mask := mask ||| Bits.shl 1 (nulls + k)
    return mask ||| Bits.shl (Bits.lowMask slots) (nulls + m)
  let V : TensorBundle := { n, metric, hasinf := inf, hasorigin := origin, dyadmode,
                            diffvars := nu, diffmode := mu }
  return (V, mask)

/-- Whether DirectSum prints a Julia space display back exactly (through `parseHandle?`). -/
def handleRoundTrips (s : String) : Bool :=
  match parseHandle? s with
  | some (V, S) => V.showSub S == s
  | none => false

/-! ## Checks -/

/-- Julia `show` of the bundle itself: an `Int` manifold shows as its dimension. -/
def bundleShow (V : TensorBundle) : String :=
  match V.metric with
  | .euclid => toString V.n
  | _ => V.toString

/-- The scalar part of `I·I` for the top blade `I` of `V`, by DirectSum's blade product;
`none` for a tangent-nested result. -/
def pseudoscalarSquare? (V : TensorBundle) : Option Rat :=
  let I := Bits.lowMask V.n
  match V.mul I I with
  | .nested .. => none
  | r => some ((r.terms.filter (·.1 == 0)).foldl (fun acc (_, c) => acc + c) 0)

/-- One named check. -/
structure Check where
  /-- What was checked. -/
  what : String
  /-- Whether it held. -/
  ok : Bool
  /-- Detail on failure. -/
  detail : String := ""

/-- Every check on one space descriptor (the "space printing" evaluator): the two bundle
constructions agree and DirectSum reproduces Julia's printed forms and tables. -/
def checkSpace (d : SpaceDesc) : Array Check := Id.run do
  let V := d.bundle
  let mut cs : Array Check := #[]
  cs := cs.push { what := "valid", ok := V.valid }
  match evalBundleSrc d.julia with
  | .ok W => cs := cs.push { what := s!"julia source {d.julia}", ok := W == V, detail := s!"{repr W} vs {repr V}" }
  | .error e => cs := cs.push { what := s!"julia source {d.julia}", ok := false, detail := e }
  cs := cs.push { what := "show", ok := V.showHandle == d.showStr, detail := s!"{V.showHandle} vs {d.showStr}" }
  cs := cs.push { what := "show_bundle", ok := bundleShow V == d.showBundle,
                  detail := s!"{bundleShow V} vs {d.showBundle}" }
  cs := cs.push { what := "grade", ok := V.grade == d.grade && d.grade == d.n - V.tangentSlots,
                  detail := s!"{V.grade} vs {d.grade}" }
  let opts := match V.metric with | .euclid => 0 | _ => V.options
  cs := cs.push { what := "options", ok := opts == d.options, detail := s!"{opts} vs {d.options}" }
  cs := cs.push { what := "flags", ok := V.isdiag == d.isdiag && V.hasconformal == d.conformal
                    && V.isdual == d.isdual && (V.dyadmode < 0) == V.isdyadic,
                  detail := s!"isdiag {V.isdiag} conformal {V.hasconformal} isdual {V.isdual}" }
  if d.n ≤ 8 then
    let basis := Leibniz.indexBasisAll d.n
    cs := cs.push { what := "basis (dense order)", ok := basis == d.basis, detail := s!"{basis}" }
    let names := basis.map (V.bladeLabel ·)
    cs := cs.push { what := "names", ok := names == d.names, detail := s!"{names} vs {d.names}" }
  else
    cs := cs.push { what := "basis/names empty for n > 8", ok := d.basis.isEmpty && d.names.isEmpty }
  if let some isq := d.Isq then
    let mine := pseudoscalarSquare? V
    cs := cs.push { what := "Isq", ok := mine == some (isq : Rat), detail := s!"{repr mine} vs {isq}" }
  return cs

/-! ## Self-checks -/

#guard (evalBundleSrc "S\"∞∅+++\"").toOption == some S!"∞∅+++"
#guard (evalBundleSrc "(S\"+++\")'").toOption == some (S!"+++").dual
#guard (evalBundleSrc "tangent(S\"++\",2,2)").toOption == some ((S!"++").tangent 2 2)
#guard ((evalBundleSrc "S\"++\"⊕(S\"++\")'").toOption.map (·.toString)) == some "⟨++--⟩*"
#guard (evalBundleSrc "S\"+x+\"").toOption.isNone
#guard handleRoundTrips "⟨∞∅-1-1-1⟩'" && handleRoundTrips "⟨0,-1,-1,-1⟩'" && handleRoundTrips "T²⟨++₁₂⟩"
#guard handleRoundTrips "⟨__+_+⟩" && handleRoundTrips "⟨1__1⟩" && handleRoundTrips "⟨++--⟩*"
#guard !handleRoundTrips "⟨+x+⟩" && !handleRoundTrips "⟨+++"
#guard pseudoscalarSquare? S!"-+++" == some (-1)
#guard pseudoscalarSquare? D!"0,1,1,1" == some 0

end Tests.ElementOracle
