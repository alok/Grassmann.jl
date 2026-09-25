import Tests.Golden.Scalar
import DirectSum

/-!
# Element objects of the element oracle

`GoldenElem` is a neutral, library-independent decoding of one element object ("E",
docs/port-notes/oracle-schema.md §7): the kind tag, grade/bits, the dense coefficient vector
(exact `Rat` or bit-exact `Float`), `native`, `terms`, a Number's value, nested Phasor
parts, and the printed strings. It is what evaluators consume and produce
(`Tests.Golden.Registry`); a Lean algebra layer converts it to and from its own types.

`encode` is the exact inverse of `decode` on every committed golden (the round trip is one of
the harness's checks), so a `GoldenElem` loses nothing but JSON key order.

The schema invariants of §7/§7.1 (field presence per kind, dense length `2ⁿ`, the storage
support of each kind, `native` = gather of `dense`) are checked by `validate`.
-/

namespace Tests.Golden

open Lean

/-- The `kind` tag of an element object (schema §7). -/
inductive Kind where
  | zero | one | infinity | submanifold | single | chain | spinor | cospinor | multivector
  | couple | pseudoCouple | phasor | number | bool | space | other | error
  deriving BEq, Repr, Inhabited, Hashable, DecidableEq

namespace Kind

/-- Every kind, in schema order. -/
def all : Array Kind :=
  #[.zero, .one, .infinity, .submanifold, .single, .chain, .spinor, .cospinor, .multivector,
    .couple, .pseudoCouple, .phasor, .number, .bool, .space, .other, .error]

/-- The JSON tag. -/
def name : Kind → String
  | .zero => "Zero" | .one => "One" | .infinity => "Infinity" | .submanifold => "Submanifold"
  | .single => "Single" | .chain => "Chain" | .spinor => "Spinor" | .cospinor => "CoSpinor"
  | .multivector => "Multivector" | .couple => "Couple" | .pseudoCouple => "PseudoCouple"
  | .phasor => "Phasor" | .number => "Number" | .bool => "Bool" | .space => "Space"
  | .other => "Other" | .error => "Error"

/-- Decode a JSON tag. -/
def ofName? (s : String) : Option Kind := all.find? (·.name == s)

/-- An algebra element (a Julia `TensorAlgebra` value; has `T`, optional `V`). -/
def isElement : Kind → Bool
  | .number | .bool | .space | .other | .error => false
  | _ => true

/-- Carries `grade` (the storage grade, Julia's type parameter `G`). -/
def isGraded : Kind → Bool
  | .zero | .one | .infinity | .submanifold | .single | .chain => true
  | _ => false

/-- Carries `bits` (one blade `B`). -/
def hasBits : Kind → Bool
  | .one | .submanifold | .single | .couple | .pseudoCouple => true
  | _ => false

/-- Carries `dense` (every element kind except Infinity and Phasor). -/
def hasDense (k : Kind) : Bool := k.isElement && k != .infinity && k != .phasor

/-- A term: Zero, One, Infinity, Submanifold or Single (schema §8.3 sandwich rule). -/
def isTerm : Kind → Bool
  | .zero | .one | .infinity | .submanifold | .single => true
  | _ => false

end Kind

instance : ToString Kind := ⟨Kind.name⟩

/-- A JSON field that may be absent, `null`, or a value. -/
inductive Field (α : Type) where
  | absent
  | null
  | val (x : α)
  deriving BEq, Repr, Inhabited

namespace Field

/-- The value, if present and not null. -/
def get? {α : Type} : Field α → Option α
  | .val x => some x
  | _ => none

/-- Present (possibly null). -/
def isPresent {α : Type} : Field α → Bool
  | .absent => false
  | _ => true

end Field

/-- One element object (schema §7), decoded. Optional JSON fields are `none` when absent. -/
structure GoldenElem where
  /-- The kind tag. -/
  kind : Kind
  /-- `T`: the coefficient type (absent for Error/Space/Other). -/
  T : Option CoeffType := none
  /-- `V`: the element's space `show`, only when it differs from the shard's space. -/
  V : Option String := none
  /-- `grade`: the storage grade (Zero, One, Infinity, Submanifold, Single, Chain). -/
  grade : Option Nat := none
  /-- `bits`: the blade `B` (One, Submanifold, Single, Couple, PseudoCouple). -/
  bits : Option UInt64 := none
  /-- `dense`: the `2ⁿ` coefficients in dense order (§5.2). -/
  dense : Option Coeffs := none
  /-- `terms`: sparse `[[bits, coef], …]` (docs, `n > 10`). -/
  terms : Option (Array UInt64 × Coeffs) := none
  /-- `native`: `value(x)` in the kind's storage order (construct suite). -/
  native : Option Coeffs := none
  /-- `value` of a Number/Bool, as a vector of length 1. -/
  value : Option Coeffs := none
  /-- Phasor amplitude. -/
  amp : Option GoldenElem := none
  /-- Phasor angle. -/
  angle : Option GoldenElem := none
  /-- `str`: `sprint(show, x)`; `null` when `show` threw on a Number/Other/Space. -/
  str : Field String := .absent
  /-- `str_error`: `show` itself threw (a Julia bug). -/
  strError : Bool := false
  /-- `compact_str`: `show` with `:compact => true`. -/
  compactStr : Field String := .absent
  /-- `type`: `string(typeof(x))` (informational). -/
  type : Option String := none
  /-- `error`: the exception type name of an Error. -/
  error : Option String := none
  /-- `msg`: the first line of an Error's message. -/
  msg : Option String := none
  /-- `label` of an input-pool entry. -/
  label : Option String := none
  /-- `src` of an input-pool entry (the Julia source that built it). -/
  src : Option String := none
  deriving Inhabited

namespace GoldenElem

/-- A Julia error with the given exception type and message (the value an evaluator
returns to say "the port rejects this operation"). -/
def rejected (error msg : String) : GoldenElem := { kind := .error, error, msg }

/-- The printed string, if present. -/
def str? (e : GoldenElem) : Option String := e.str.get?

end GoldenElem

/-! ## Spaces of elements: generator count from a `show` string -/

/-- Whether `c` is a Unicode subscript or superscript digit (tangent-variable glyphs). -/
def isScriptDigit (c : Char) : Bool :=
  ('₀' ≤ c && c ≤ '₉') || c == '¹' || c == '²' || c == '³' || ('⁰' ≤ c && c ≤ '⁹')

/-- The number of generators `n` of a space from its `show` (`⟨+++⟩`, `⟨∞∅111⟩`,
`⟨1,2,-3⟩'`, `T²⟨++₁₂⟩`, the subspace `⟨_+++⟩`, the Int space `⟨1111⟩`): the non-`_`
metric entries (a conformal `-1` counts once) plus the tangent-variable glyphs. `none` if
the string is not a space display. This is the `n` against which an element with a `V`
field is laid out (dense length `2ⁿ`). -/
def spaceDims? (s : String) : Option Nat :=
  let cs := s.toList
  -- strip the `T^μ` prefix
  let cs := match cs with
    | 'T' :: rest => rest.dropWhile isScriptDigit
    | _ => cs
  match cs with
  | '⟨' :: rest =>
    let inner := rest.takeWhile (· != '⟩')
    let tail := rest.dropWhile (· != '⟩')
    if tail.isEmpty then none else
    let scripts := (inner.filter isScriptDigit).length
    let body := inner.filter (fun c => !isScriptDigit c)
    if body.contains '[' then
      -- MetricTensor rows `[1.0, 0.5, 0.0]…`
      some ((body.filter (· == '[')).length + scripts)
    else if body.contains ',' then
      let entries := (String.ofList body).splitOn ","
      some ((entries.filter (fun e => e != "_" && e != "")).length + scripts)
    else
      let rec count : List Char → Nat
        | [] => 0
        | '_' :: r => count r
        | '-' :: '1' :: r => 1 + count r
        | _ :: r => 1 + count r
      some (count body + scripts)
  | _ => none

/-! ## Decoding -/

/-- The keys an element object may carry (plus `label`/`src` on inputs). -/
def elemKeys : List String :=
  ["kind", "T", "V", "grade", "bits", "dense", "terms", "native", "value", "amp", "angle",
   "str", "str_error", "compact_str", "type", "error", "msg", "label", "src"]

/-- A string-or-null field. -/
def decodeTextField (j : Json) (key : String) : Except String (Field String) :=
  match j.getObjVal? key with
  | .error _ => .ok .absent
  | .ok .null => .ok .null
  | .ok (.str s) => .ok (.val s)
  | .ok v => .error s!"field {key} is not a string: {v.compress}"

/-- An optional string field. -/
def decodeOptStr (j : Json) (key : String) : Except String (Option String) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok (.str s) => .ok (some s)
  | .ok v => .error s!"field {key} is not a string: {v.compress}"

/-- An optional natural-number field (read exactly, never through `Float`). -/
def decodeOptNat (j : Json) (key : String) : Except String (Option Nat) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok v => match v.getNat? with
    | .ok n => .ok (some n)
    | .error _ => .error s!"field {key} is not a natural number: {v.compress}"

/-- An optional array field. -/
def decodeOptArr (j : Json) (key : String) : Except String (Option (Array Json)) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok (.arr a) => .ok (some a)
  | .ok v => .error s!"field {key} is not an array: {v.compress}"

/-- Decode one element object. Unknown keys are an error (the schema lists every field). -/
partial def GoldenElem.decode (j : Json) : Except String GoldenElem := do
  let .obj kvs := j | throw s!"element is not an object: {j.compress.take 80}"
  for (k, _) in kvs.toList do
    unless elemKeys.contains k do throw s!"unknown element field {k}"
  let kindName ← match j.getObjVal? "kind" with
    | .ok (.str s) => pure s
    | _ => throw "element without kind"
  let some kind := Kind.ofName? kindName | throw s!"unknown kind {kindName}"
  let T := (← decodeOptStr j "T").map CoeffType.ofName
  let coeffs := fun (key : String) => do
    match ← decodeOptArr j key with
    | none => pure none
    | some a => match T with
      | some t => pure (some (← Coeffs.decode t a))
      | none => throw s!"{key} without T"
  let dense ← coeffs "dense"
  let native ← coeffs "native"
  let value ← match j.getObjVal? "value" with
    | .error _ => pure none
    | .ok v => match T with
      | some t => pure (some (Coeffs.ofScalars t #[← decodeScalar t v]))
      | none => throw "value without T"
  let terms ← match ← decodeOptArr j "terms" with
    | none => pure none
    | some ts =>
      let t := T.getD (.other "?")
      let mut bs : Array UInt64 := #[]
      let mut cs : Array Scalar := #[]
      for p in ts do
        match p with
        | .arr #[b, c] =>
          let some bn := b.getNat?.toOption | throw s!"bad terms entry {p.compress}"
          bs := bs.push bn.toUInt64
          cs := cs.push (← decodeScalar t c)
        | _ => throw s!"bad terms entry {p.compress}"
      pure (some (bs, Coeffs.ofScalars t cs))
  let sub := fun (key : String) => do
    match j.getObjVal? key with
    | .error _ => pure none
    | .ok v => pure (some (← GoldenElem.decode v))
  let strError ← match j.getObjVal? "str_error" with
    | .error _ => pure false
    | .ok (.bool b) => pure b
    | .ok v => throw s!"str_error is not a Bool: {v.compress}"
  return {
    kind, T, V := ← decodeOptStr j "V", grade := ← decodeOptNat j "grade",
    bits := (← decodeOptNat j "bits").map (·.toUInt64), dense, terms, native, value,
    amp := ← sub "amp", angle := ← sub "angle",
    str := ← decodeTextField j "str", strError, compactStr := ← decodeTextField j "compact_str",
    type := ← decodeOptStr j "type", error := ← decodeOptStr j "error", msg := ← decodeOptStr j "msg",
    label := ← decodeOptStr j "label", src := ← decodeOptStr j "src" }

/-! ## Encoding -/

/-- Encode back to a JSON element object (the exact inverse of `decode` up to key order). -/
partial def GoldenElem.encode (e : GoldenElem) : Json := Id.run do
  let t := e.T.getD (.other "?")
  let mut kv : Array (String × Json) := #[("kind", .str e.kind.name)]
  if let some T := e.T then kv := kv.push ("T", .str T.name)
  if let some v := e.V then kv := kv.push ("V", .str v)
  if let some g := e.grade then kv := kv.push ("grade", toJson g)
  if let some b := e.bits then kv := kv.push ("bits", toJson b.toNat)
  if let some d := e.dense then kv := kv.push ("dense", .arr (d.encode t))
  if let some (bs, cs) := e.terms then
    kv := kv.push ("terms", .arr ((bs.zip (cs.encode t)).map fun (b, c) => .arr #[toJson b.toNat, c]))
  if let some d := e.native then kv := kv.push ("native", .arr (d.encode t))
  if let some v := e.value then kv := kv.push ("value", encodeScalar t (v.get 0))
  if let some a := e.amp then kv := kv.push ("amp", a.encode)
  if let some a := e.angle then kv := kv.push ("angle", a.encode)
  match e.str with
  | .absent => pure ()
  | .null => kv := kv.push ("str", .null)
  | .val s => kv := kv.push ("str", .str s)
  if e.strError then kv := kv.push ("str_error", .bool true)
  match e.compactStr with
  | .absent => pure ()
  | .null => kv := kv.push ("compact_str", .null)
  | .val s => kv := kv.push ("compact_str", .str s)
  if let some s := e.type then kv := kv.push ("type", .str s)
  if let some s := e.error then kv := kv.push ("error", .str s)
  if let some s := e.msg then kv := kv.push ("msg", .str s)
  if let some s := e.label then kv := kv.push ("label", .str s)
  if let some s := e.src then kv := kv.push ("src", .str s)
  return Json.mkObj kv.toList

/-! ## Storage layouts (schema §7.1) -/

/-- The dense positions (0-based, dense order) where an element of kind `k` in an
`n`-generator space may be nonzero, and the `native` gather order. `none` for kinds
without dense storage. -/
def supportIndices (n : Nat) (k : Kind) (grade : Nat) (bits : UInt64) : Option (Array Nat) :=
  let basis := Leibniz.indexBasisAll n
  let pos := fun (b : UInt64) => Leibniz.basisRank n b
  let top : UInt64 := (1 <<< n.toUInt64) - 1
  let byGrade := fun (p : Nat → Bool) =>
    (basis.zipIdx.filter fun (b, _) => p (DirectSum.Bits.popcount b)).map (·.2)
  match k with
  | .zero => some #[]
  | .one | .submanifold | .single => some #[pos bits]
  | .chain => some (byGrade (· == grade))
  | .spinor => some (byGrade (· % 2 == 0))
  | .cospinor => some (byGrade (· % 2 == 1))
  | .multivector => some (List.range (2 ^ n)).toArray
  | .couple => some #[0, pos bits]
  | .pseudoCouple => some #[pos bits, pos top]
  | _ => none

/-- The `n` an element is laid out in: its own `V`'s when present, else the shard's. -/
def GoldenElem.dims? (e : GoldenElem) (shardN : Option Nat) : Option Nat :=
  match e.V with
  | some v => spaceDims? v
  | none => shardN

/-- Check the schema invariants of one element (§7 field presence, §7.1 storage) in a space
of `n` generators (`none`: unknown, e.g. docs values without a decodable `V`). `strict :=
false` (defect-tagged outputs, which may be Julia's malformed values) checks only the field
grammar. Returns the list of violations. -/
partial def GoldenElem.validate (e : GoldenElem) (n : Option Nat) (strict : Bool := true) :
    Array String := Id.run do
  let mut errs : Array String := #[]
  let k := e.kind
  let need := fun (errs : Array String) (c : Bool) (m : String) => if c then errs else errs.push m
  if k == .error then
    return need errs (e.error.isSome && e.msg.isSome) "Error without error/msg"
  if k == .number || k == .bool then
    errs := need errs (e.T.isSome && e.value.isSome) s!"{k} without T/value"
    return need errs e.str.isPresent s!"{k} without str"
  if k == .space || k == .other then
    return need errs (e.str.isPresent && e.type.isSome) s!"{k} without str/type"
  errs := need errs e.T.isSome s!"{k} without T"
  errs := need errs (e.str.isPresent != e.strError) s!"{k}: needs exactly one of str / str_error"
  if k.isGraded then errs := need errs e.grade.isSome s!"{k} without grade"
  if k.hasBits then errs := need errs e.bits.isSome s!"{k} without bits"
  if strict && (k == .one || k == .submanifold || k == .single) then
    if let (some b, some g) := (e.bits, e.grade) then
      errs := need errs (DirectSum.Bits.popcount b == g) s!"{k}: grade {g} != popcount(bits {b})"
  if k == .one then errs := need errs (e.bits == some 0) "One with bits != 0"
  if (k == .zero || k == .infinity) && strict then
    errs := need errs (e.grade == some 0) s!"{k} with grade != 0"
  if k == .phasor then
    for (nm, sub) in [("amp", e.amp), ("angle", e.angle)] do
      match sub with
      | some x => errs := errs ++ (x.validate (x.dims? n) strict).map (s!"{nm}: " ++ ·)
      | none => errs := errs.push s!"Phasor without {nm}"
    return errs
  if k == .infinity then
    return need errs e.dense.isNone "Infinity with dense"
  let some n := e.dims? n
    | return (if e.V.isSome && e.dense.isSome then errs.push s!"undecodable space {e.V.getD ""}" else errs)
  if let some (bs, cs) := e.terms then
    errs := need errs (n > 10) s!"terms for n = {n} ≤ 10"
    errs := need errs (bs.size == cs.size) "terms length"
    return errs
  let some d := e.dense
    | return need errs (n > 10) s!"{k} without dense"
  errs := need errs (d.size == 2 ^ n) s!"dense length {d.size} != 2^{n}"
  if d.size != 2 ^ n || !strict || !(e.T.getD (.other "")).parseable then return errs
  let bits := e.bits.getD 0
  let some supp := supportIndices n k (e.grade.getD 0) bits | return errs
  -- One/Submanifold: the coefficient on the blade is 1
  if k == .one || k == .submanifold then
    let one := match d.get (supp[0]?.getD 0) with
      | .exact x => x == 1
      | .complex (.exact x) (.exact y) => x == 1 && y == 0
      | _ => false
    errs := need errs one s!"{k}: basis blade coefficient != 1"
  let inSupp := supp.foldl (fun (m : Array Bool) i => m.setIfInBounds i true) (Array.replicate d.size false)
  let bad := (List.range d.size).find? fun i => !(inSupp[i]?.getD false) && !d.isZeroAt i
  if let some i := bad then
    errs := errs.push s!"{k} has a nonzero coefficient on blade {Leibniz.indexBasisAll n |>.getD i 0}"
  if let some nat := e.native then
    let top : UInt64 := (1 <<< n.toUInt64) - 1
    let degenerate := (k == .couple || k == .pseudoCouple) && (bits == 0 || bits == top)
    if !degenerate then
      let g := d.gather supp
      errs := need errs ((compareCoeffs .exact nat g).isNone) "native is not the storage gather of dense"
  return errs

/-! ## Self-checks -/

#guard spaceDims? "⟨+++⟩" == some 3
#guard spaceDims? "⟨∞∅-1-1-1⟩'" == some 5
#guard spaceDims? "⟨0,-1,-1,-1⟩'" == some 4
#guard spaceDims? "T²⟨++₁₂⟩" == some 4
#guard spaceDims? "⟨_+++⟩" == some 3
#guard spaceDims? "⟨1__1⟩" == some 2
#guard spaceDims? "⟨++--⟩*" == some 4
#guard spaceDims? "v₁₂" == none
#guard supportIndices 3 .spinor 0 0 == some #[0, 4, 5, 6]
#guard supportIndices 3 .pseudoCouple 0 3 == some #[4, 7]
#guard supportIndices 4 .chain 2 0 == some #[5, 6, 7, 8, 9, 10]

end Tests.Golden
