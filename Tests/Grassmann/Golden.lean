/-
A direct spot check of the typed layer against the Julia oracle goldens
(`oracle/golden/{products,unary,arith}/*.json`, schema in
docs/port-notes/oracle-schema.md). The full golden consumer is `Tests/Golden`;
this suite only decodes the element inputs into the typed containers, runs the
typed operation and compares the **dense** coefficients (exactly, over `Rat`:
the integer and dyadic `Float64` inputs make every result exact) with

* the case's `ref` when a `ref`-policy defect tags it (Julia's value is wrong
  there and the port follows the documented correction), else
* `out.dense`,

skipping `skip`-policy defects, Julia errors without a reference, and inputs
outside the typed element model (`Infinity`, plain numbers in products). Result
kinds and strings are the dynamic layer's business and are not compared.

Products are sampled (every 7th case of each shard, rotating through the
operations and operand pairs); the unary and arith shards are checked in full
where supported.
-/
import Tests.Grassmann.Common
import Lean.Data.Json

open Lean Grassmann DirectSum StaticVectors

namespace GrassmannTests.Golden

/-! ## Decoding -/

/-- A decimal string (`-2.75`, `1.0e-5`, `3`) as an exact rational. -/
def parseDecimal (s : String) : Option Rat := do
  let (neg, body) := if s.startsWith "-" then (true, s.drop 1) else (false, s.toSlice)
  let body := body.toString
  let (mant, ex) ← match body.splitOn "e" with
    | [m] => some (m, (0 : Int))
    | [m, e] => (fun (x : Int) => (m, x)) <$> e.toInt?
    | _ => none
  let (ip, fp) := match mant.splitOn "." with
    | [i] => (i, "")
    | [i, f] => (i, f)
    | _ => ("", "")
  let digits ← (ip ++ fp).toNat?
  let e : Int := ex - fp.length
  let v : Rat := if e ≥ 0 then (digits * 10 ^ e.toNat : Nat) else (digits : Rat) / ((10 ^ (-e).toNat : Nat) : Rat)
  return if neg then -v else v

/-- A golden coefficient (`Int64`, `Rational{Int64}` `a//b`, finite `Float64`) as a rational. -/
def parseCoef (j : Json) : Option Rat := do
  let s ← j.getStr?.toOption
  match s.splitOn "//" with
  | [a, b] => do
    let a ← a.toInt?
    let b ← b.toNat?
    if b == 0 then none else some ((a : Rat) / (b : Rat))
  | _ => parseDecimal s

/-- A dense golden vector. -/
def parseDense (j : Json) : Option (Array Rat) := do
  let a ← j.getArr?.toOption
  a.mapM parseCoef

/-- A decoded element of the typed layer (over `Rat`). -/
inductive Elem (V : TensorBundle) where
  | chain (g : Nat) (c : Chain V g Rat)
  | half (p : Bool) (h : Half V p Rat)
  | multi (m : Multivector V Rat)
  | single (g : Nat) (s : Single V g Rat)
  | couple (z : Couple V Rat)
  | pseudo (z : PseudoCouple V Rat)

/-- The dense vector of a decoded element. -/
def Elem.dense {V : TensorBundle} : Elem V → Array Rat
  | .chain _ c => (toMultivector c).v.toArray
  | .half _ h => (toMultivector h).v.toArray
  | .multi m => m.v.toArray
  | .single _ s => (toMultivector s).v.toArray
  | .couple z => z.toMultivector.v.toArray
  | .pseudo z => z.toMultivector.v.toArray

/-- Decode a golden element object (`none` for kinds outside the typed model). -/
def decode (V : TensorBundle) (j : Json) : Option (Elem V) := do
  let n := V.n
  let kind ← (j.getObjValAs? String "kind").toOption
  let dense? := (j.getObjVal? "dense").toOption.bind parseDense
  let at_ := fun (d : Array Rat) (b : UInt64) => d[Leibniz.basisRank n b]!
  let bits : UInt64 := ((j.getObjValAs? Nat "bits").toOption.getD 0).toUInt64
  let grade := (j.getObjValAs? Nat "grade").toOption.getD 0
  match kind with
  | "Zero" => some (.chain 0 Chain.zero)
  | "One" => some (.single 0 ⟨0, 1⟩)
  | "Submanifold" => some (.single grade ⟨bits, 1⟩)
  | "Number" => do
    let x ← (j.getObjVal? "value").toOption.bind parseCoef
    some (.single 0 ⟨0, x⟩)
  | "Single" => do let d ← dense?; some (.single grade ⟨bits, at_ d bits⟩)
  | "Chain" => do
    let d ← dense?
    some (.chain grade ⟨convertLayout n .full (.chain grade) (Values.ofFn fun i => d[i.1]!)⟩)
  | "Spinor" => do let d ← dense?; some (.half false (toHalf (⟨Values.ofFn fun i => d[i.1]!⟩ : Multivector V Rat) false))
  | "CoSpinor" => do let d ← dense?; some (.half true (toHalf (⟨Values.ofFn fun i => d[i.1]!⟩ : Multivector V Rat) true))
  | "Multivector" => do let d ← dense?; some (.multi ⟨Values.ofFn fun i => d[i.1]!⟩)
  | "Couple" => do
    let d ← dense?
    some (.couple ⟨bits, d[0]!, if bits == 0 then 0 else at_ d bits⟩)
  | "PseudoCouple" => do
    let d ← dense?
    let top := Bits.lowMask n
    some (.pseudo ⟨bits, at_ d bits, if bits == top then 0 else at_ d top⟩)
  | _ => none

/-! ## Typed dispatch -/

/-- Densify. -/
@[inline] def mv {X : Type} {V : TensorBundle} [DenseLayout X V Rat] (x : X) : Array Rat :=
  (toMultivector x).v.toArray

/-- Apply a typed binary operation to every pair of element kinds (the operator
term is elaborated separately at each of the 36 type pairs). -/
local macro "bin_dispatch " f:term : term =>
  `(fun a b => match a, b with
    | .chain _ x, .chain _ y => mv ($f x y) | .chain _ x, .half _ y => mv ($f x y)
    | .chain _ x, .multi y => mv ($f x y) | .chain _ x, .single _ y => mv ($f x y)
    | .chain _ x, .couple y => mv ($f x y) | .chain _ x, .pseudo y => mv ($f x y)
    | .half _ x, .chain _ y => mv ($f x y) | .half _ x, .half _ y => mv ($f x y)
    | .half _ x, .multi y => mv ($f x y) | .half _ x, .single _ y => mv ($f x y)
    | .half _ x, .couple y => mv ($f x y) | .half _ x, .pseudo y => mv ($f x y)
    | .multi x, .chain _ y => mv ($f x y) | .multi x, .half _ y => mv ($f x y)
    | .multi x, .multi y => mv ($f x y) | .multi x, .single _ y => mv ($f x y)
    | .multi x, .couple y => mv ($f x y) | .multi x, .pseudo y => mv ($f x y)
    | .single _ x, .chain _ y => mv ($f x y) | .single _ x, .half _ y => mv ($f x y)
    | .single _ x, .multi y => mv ($f x y) | .single _ x, .single _ y => mv ($f x y)
    | .single _ x, .couple y => mv ($f x y) | .single _ x, .pseudo y => mv ($f x y)
    | .couple x, .chain _ y => mv ($f x y) | .couple x, .half _ y => mv ($f x y)
    | .couple x, .multi y => mv ($f x y) | .couple x, .single _ y => mv ($f x y)
    | .couple x, .couple y => mv ($f x y) | .couple x, .pseudo y => mv ($f x y)
    | .pseudo x, .chain _ y => mv ($f x y) | .pseudo x, .half _ y => mv ($f x y)
    | .pseudo x, .multi y => mv ($f x y) | .pseudo x, .single _ y => mv ($f x y)
    | .pseudo x, .couple y => mv ($f x y) | .pseudo x, .pseudo y => mv ($f x y))

/-- Apply a typed unary operation to every element kind. -/
local macro "un_dispatch " f:term : term =>
  `(fun a => match a with
    | .chain _ x => mv ($f x) | .half _ x => mv ($f x) | .multi x => mv ($f x)
    | .single _ x => mv ($f x) | .couple x => mv ($f x) | .pseudo x => mv ($f x))

/-- A linear map of the dense containers applied to any element (the single-term
kinds through their `Multivector`). -/
local macro "lin_dispatch " fc:ident fh:ident fm:ident : term =>
  `(fun a => match a with
    | .chain _ x => mv ($fc x) | .half _ x => mv ($fh x) | .multi x => mv ($fm x)
    | .single _ x => mv ($fm (toMultivector x)) | .couple x => mv ($fm (toMultivector x))
    | .pseudo x => mv ($fm (toMultivector x)))

/-- The typed binary operation of an op key. -/
def binary (V : TensorBundle) : String → Option (Elem V → Elem V → Array Rat)
  | "mul" => some (bin_dispatch (fun x y => x * y))
  | "wedge" => some (bin_dispatch (fun x y => wedge x y))
  | "vee" => some (bin_dispatch (fun x y => vee x y))
  | "contraction" => some (bin_dispatch (fun x y => x ⋅ y))
  | "lcontraction" => some (bin_dispatch (fun x y => x ⨼ y))
  | "lshift" => some (bin_dispatch (fun x y => shiftLeftContraction x y))
  | "rshift" => some (bin_dispatch (fun x y => shiftRightContraction x y))
  | "revmul" => some (bin_dispatch (fun x y => x ∗ y))
  | "scalarprod" => some (bin_dispatch (fun x y => x ⊛ y))
  | "cross" => some (bin_dispatch (fun x y => cross x y))
  | "sandwich" => some (bin_dispatch (fun x y => x ⊘ y))
  | "tsandwich" => some (bin_dispatch (fun x y => x >>> y))
  | "veedot" => some (bin_dispatch (fun x y => x ⟇ y))
  | "antidot" => some (bin_dispatch (fun x y => antidot x y))
  | "add" => some (bin_dispatch (fun x y => x + y))
  | "sub" => some (bin_dispatch (fun x y => x - y))
  | "div" => some (bin_dispatch (fun x y => x / y))
  | "rdiv" => some (bin_dispatch (fun x y => x / y))
  | _ => none

/-- The typed unary operation of an op key. -/
def unary (V : TensorBundle) : String → Option (Elem V → Array Rat)
  | "neg" => some (un_dispatch (fun x => -x))
  | "reverse" => some (un_dispatch (fun x => ~x))
  | "involute" => some (un_dispatch (fun x => involute x))
  | "clifford" => some (un_dispatch (fun x => clifford x))
  | "complementright" => some (un_dispatch (fun x => complementRight x))
  | "complementleft" => some (un_dispatch (fun x => complementLeft x))
  | "hodge" => some (un_dispatch (fun x => hodge x))
  | "even" => some (un_dispatch (fun x => even x))
  | "odd" => some (un_dispatch (fun x => odd x))
  | "Multivector" => some (un_dispatch (fun x => toMultivector x))
  | "antireverse" => some (lin_dispatch Chain.antireverse Half.antireverse Multivector.antireverse)
  | "complementlefthodge" =>
    some (lin_dispatch Chain.complementlefthodge Half.complementlefthodge Multivector.complementlefthodge)
  | "metric" => some (lin_dispatch Chain.metric Half.metric Multivector.metric)
  | "antimetric" => some (lin_dispatch Chain.antimetric Half.antimetric Multivector.antimetric)
  | "real" => some (lin_dispatch Chain.realPart Half.realPart Multivector.realPart)
  | "imag" => some (lin_dispatch Chain.imagPart Half.imagPart Multivector.imagPart)
  | "scalar" => some (un_dispatch (fun x => gradePart x 0))
  | "vector" => some (un_dispatch (fun x => gradePart x 1))
  | "bivector" => some (un_dispatch (fun x => gradePart x 2))
  | "trivector" => some (un_dispatch (fun x => gradePart x 3))
  | "volume" => some (un_dispatch (fun x => gradePart x V.n))
  | op =>
    if op.startsWith "grade:" then
      (op.drop 6).toString.toNat?.map fun k => un_dispatch (fun x => gradePart x k)
    else none

/-! ## Running a shard -/

/-- Defect id ↦ policy. -/
def loadPolicies : IO (Std.HashMap String String) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile "oracle/golden/defects.json"))
  let ds ← IO.ofExcept (j.getObjValAs? (Array Json) "defects")
  return ds.foldl (init := {}) fun m d =>
    match d.getObjValAs? String "id", d.getObjValAs? String "policy" with
    | .ok i, .ok p => m.insert i p
    | _, _ => m

/-- The Lean space of a golden shard, by registry name. -/
def spaceOf : String → Option TensorBundle
  | "E2" => some S!"++" | "E3" => some S!"+++" | "E4" => some S!"++++" | "E5" => some S!"+++++"
  | "M4" => some S!"-+++" | "D3" => some D!"1,2,-3" | "PGA3" => some D!"0,1,1,1"
  | "INF3" => some S!"∞+++" | "CGA2" => some S!"∞∅++" | "CGA3" => some S!"∞∅+++"
  | _ => none

/-- Check the sampled cases of one shard (`stride`: every `stride`-th case). -/
def runShard (policies : Std.HashMap String String) (suite shard : String) (stride : Nat) : IO Tally := do
  let some V := spaceOf shard | return ({} : Tally).bad s!"{suite}/{shard}: unknown space"
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile s!"oracle/golden/{suite}/{shard}.json"))
  let mut t : Tally := {}
  -- the golden dense order is Leibniz's
  let basis := ((j.getObjValD "space").getObjValAs? (Array Nat) "basis").toOption.getD #[]
  t := t.check (basis.map (·.toUInt64) == Leibniz.indexBasisAll V.n) s!"{suite}/{shard}: dense order"
  let inputs := (j.getObjValAs? (Array Json) "inputs").toOption.getD #[]
  let elems := inputs.map (decode V)
  let cases := (j.getObjValAs? (Array Json) "cases").toOption.getD #[]
  for c in cases, idx in [0:cases.size] do
    if idx % stride != 0 then continue
    let op := (c.getObjValAs? String "op").toOption.getD ""
    let tags := (c.getObjValAs? (Array String) "defects").toOption.getD #[]
    let pols := tags.filterMap (policies.get? ·)
    if pols.contains "skip" then t := t.skip "skip-policy defect"; continue
    let out := c.getObjValD "out"
    let ref? := (c.getObjVal? "ref").toOption.bind parseDense
    let want? := if pols.contains "ref" && ref?.isSome then ref? else
      if (out.getObjValAs? String "kind").toOption == some "Error" then none
      else (out.getObjVal? "dense").toOption.bind parseDense
    let some want := want? | t := t.skip "Julia error without a reference"; continue
    let a? := (c.getObjValAs? Nat "a").toOption.bind (elems[·]?) |>.join
    let b? := (c.getObjValAs? Nat "b").toOption.bind (elems[·]?) |>.join
    let hasB := (c.getObjVal? "b").toOption.isSome
    let got? : Option (Array Rat) :=
      if hasB then do
        let f ← binary V op
        return f (← a?) (← b?)
      else do
        let f ← unary V op
        return f (← a?)
    match got? with
    | some got => t := t.check (got == want) s!"{suite}/{shard} case {idx} {op}: {got} ≠ {want}"
    | none => t := t.skip "outside the typed element model"
  return t

/-- Run the golden spot check. -/
def run : IO Tally := do
  let policies ← loadPolicies
  let mut t : Tally := {}
  for shard in ["E3", "M4", "PGA3", "CGA3", "D3", "INF3"] do
    t := t.merge (← runShard policies "products" shard 7)
  for shard in ["E3", "M4", "PGA3", "CGA3"] do
    t := t.merge (← runShard policies "unary" shard 1)
  for shard in ["E3", "CGA3"] do
    t := t.merge (← runShard policies "arith" shard 1)
  return t

end GrassmannTests.Golden
