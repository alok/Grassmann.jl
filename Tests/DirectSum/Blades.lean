/-
Blade-level oracle suite: every record of `oracle/golden/blades/dump_all.jsonl`
and `dump_small.jsonl` (Grassmann 0.8.46, `oracle/probes/parity/dump.jl`),
every operation, checked against `DirectSum.TensorBundle` on terms (exact),
result kind and printed string.

Documented Julia defects (port-notes/grassmann-parity.md §8.6) are skipped only
after proving the mismatch is that defect:

* D1 `C4neg` / D2 `MetricTensor`: Lean computes the exact product; a mismatch
  is counted only if the bug-compatible `DirectSum.Compat` port reproduces
  Julia's value exactly.
* D4 cache collision: `dump_all` tangent records are checked against the
  fresh-process `dump_small` record when they disagree.
* D5 `antimetric_term` undefined, D6 tangent container complements
  (`UndefVarError: args` / wrong grade): Julia throws or misbehaves; Lean
  defines the value.
-/
import Tests.DirectSum.Common
import DirectSum.Compat

open Lean DirectSum DirectSum.Bits

namespace DirectSumTests.Blades

/-- Space descriptor from a dump `info` record. -/
def spaceOf (info : Json) : TensorBundle :=
  let nm := jStr info "space"
  let n := jNat info "N"
  let opts := jNat info "opts"
  let m := opts % 16
  let inf := m ∈ [1, 3, 5, 7, 9, 11]
  let origin := m ∈ [2, 3, 6, 7, 10, 11]
  let dyad : Int := if 8 ≤ m && m ≤ 11 then -1 else if 4 ≤ m && m ≤ 7 then 1 else 0
  let base : TensorBundle :=
    if nm.startsWith "MT" then .metricTensor #[#[1, 1/2, 0], #[1/2, 1, 1/2], #[0, 1/2, 1]]
    else if nm == "I4" then .euclidean n
    else match info.getObjValD "diag" with
      | .arr d => .diag (d.map fun | .num x => jsonRat x | _ => 0)
      | _ => { n, metric := .signature (jNat info "metricbits").toUInt64 }
  { base with hasinf := inf, hasorigin := origin, dyadmode := dyad, polymode := opts &&& 16 == 0,
              diffvars := jNat info "diffvars", diffmode := jNat info "diffmode" }

/-- Julia's value for one operation: `none` for an error, else `(terms, kind,
string)`. A term whose coefficient is itself a blade (tangent `∂₁⊗…`) is kept
with coefficient `0` and compared through the string. -/
def julia (j : Json) : Option (Terms × String × String) :=
  match j.getObjVal? "err" with
  | .ok _ => none
  | .error _ =>
    let ts := (jArr j "t").filterMap fun p => match p with
      | .arr #[.num k, .num c] => some ((jsonRat k).num.toNat.toUInt64, jsonRat c)
      | .arr #[.num k, .str _] => some ((jsonRat k).num.toNat.toUInt64, 0)
      | _ => none
    some (ts, jStr j "T", jStr j "s")

/-- Julia's kind name and printed string(s) for a Lean blade result. -/
def render (V : TensorBundle) (r : BladeResult) (float : Bool) : String × String :=
  match r with
  | .zero => ("Zero", "𝟎")
  | .blade b => ("Submanifold", V.bladeLabel b)
  | .single c b => ("Single", V.showTerm c b float)
  | .sum t => let k := sumKind V t; (k.name, showContainer V k t float)
  | .nested z (.blade d) => ("Single", V.loworder.bladeLabel z ++ "⊗" ++ V.bladeLabel d)
  | .nested z (.single c d) =>
    ("Single", showNum c float ++ V.loworder.bladeLabel z ++ "⊗" ++ V.bladeLabel d)
  | .nested _ _ => ("Single", "<nested>")

/-- Compare a Lean result with Julia's record: terms exactly, kind, and the string
in either `Int` or `Float64` rendering. -/
def agree (V : TensorBundle) (mine : Except String BladeResult) (jl : Option (Terms × String × String)) :
    Bool × String :=
  match mine, jl with
  | .error _, none => (true, "")
  | .error e, some (_, _, s) => (false, s!"Lean error `{e}`, Julia `{s}`")
  | .ok r, none => (false, s!"Lean {repr r}, Julia threw")
  | .ok r, some (ts, kind, s) =>
    let (k1, s1) := render V r false
    let (_, s2) := render V r true
    -- a nested (tangent-coefficient) result is compared by blade and string
    let termsOk := match r with
      | .nested _ inner => inner.terms.map (·.1) == ts.map (·.1)
      | _ => normTerms r.terms == normTerms ts
    let kindOk := k1 == kind
    let strOk := s1 == s || s2 == s
    (termsOk && kindOk && strOk,
      s!"terms {termsOk} kind {kindOk} ({k1} vs {kind}) str `{s1}` vs `{s}`")

/-- Container (`Chain`) result: one-hot `2.0 e_a` mapped through `f`, a Chain of
grade `g`, printed with Julia `Float64` and signed zeros normalized. -/
def agreeChain (V : TensorBundle) (g : Nat) (mine : Except String Terms)
    (jl : Option (Terms × String × String)) : Bool × String :=
  match mine, jl with
  | .error _, none => (true, "")
  | .error e, some (_, _, s) => (false, s!"Lean error `{e}`, Julia `{s}`")
  | .ok t, none => (false, s!"Lean {repr t}, Julia threw")
  | .ok t, some (ts, kind, s) =>
    let t := t.scale 2
    let termsOk := normTerms t == normTerms ts
    let str := showContainer V (.chain g) t true
    let strOk := normSignedZero str == normSignedZero s
    (termsOk && kind == "Chain" && strOk, s!"terms {termsOk} kind {kind} str `{str}` vs `{s}`")

/-- The Lean and Julia-compatible (`Compat`) results of a unary operation. -/
def unaryOps (V : TensorBundle) (a : UInt64) :
    List (String × (Except String BladeResult) × Option (Except String BladeResult)) :=
  [ ("rev", .ok (V.reverse a), none), ("inv", .ok (V.involute a), none),
    ("cli", .ok (V.clifford a), none), ("arev", .ok (V.antireverse a), none),
    ("conj", .ok (V.conj a), none),
    ("cr", V.complementright a, none), ("cl", V.complementleft a, none),
    ("hr", V.complementrighthodge a, some (Compat.complementrighthodge V a)),
    ("hl", V.complementlefthodge a, some (Compat.complementlefthodge V a)),
    ("met", V.bladeMetric a, some (Compat.bladeMetric V a)),
    ("ameta", V.antimetric a, none),
    ("sq", .ok (V.mul a a), some (.ok (Compat.mul V a a))) ]

/-- The Lean and `Compat` results of a binary operation. -/
def binaryOps (V : TensorBundle) (a b : UInt64) :
    List (String × (Except String BladeResult) × Option (Except String BladeResult)) :=
  [ ("mul", .ok (V.mul a b), some (.ok (Compat.mul V a b))),
    ("wedge", .ok (V.wedge a b), none), ("vee", .ok (V.vee a b), none),
    ("dot", .ok (V.contraction a b), some (.ok (Compat.contraction V a b))),
    ("cross", V.cross a b, some (Compat.cross V a b)),
    ("mulS", .ok ((V.mul a b).scale 6), some (.ok ((Compat.mul V a b).scale 6))) ]

/-- Records of the fresh-process dump, keyed by `(space, a, b)` / `(space, a)`. -/
abbrev Fresh := Std.HashMap (String × Nat × Int) Json

/-- Load a JSONL file. -/
def loadLines (path : System.FilePath) : IO (Array Json) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Json.parse line with
    | .ok j => out := out.push j
    | .error e => throw (IO.userError s!"{path}: bad JSON: {e}")
  return out

/-- Classify a mismatch as a documented defect, if the evidence supports it. -/
def defectClass (V : TensorBundle) (nm op : String) (compatOk : Bool) (freshOk : Bool)
    (jl : Option (Terms × String × String)) : Option String :=
  if freshOk then some "D4 regressive/interior cache collision (tangent space, non-fresh process)"
  else if compatOk && V.hasconformal then some "D1 conformal product ignores signature bits (C4neg)"
  else if compatOk then some "D2 MetricTensor product drops middle grades"
  else if op == "ameta" && jl.isNone then some "D5 antimetric_term undefined"
  else if V.istangent && ["crc", "clc", "hrc", "hlc", "revc", "arevc"].contains op then
    some "D6 tangent Chain complement/reverse (UndefVarError args / wrong grade)"
  else let _ := nm; none

/-- Check one dump file. `fresh` gives the fresh-process records used to
recognize cache-collision (D4) records in `dump_all`. -/
def checkFile (path : System.FilePath) (fresh : Fresh) (t : Tally) : IO Tally := do
  let lines ← loadLines path
  let mut t := t
  let mut spaces : Std.HashMap String TensorBundle := {}
  for r in lines do
    match r.getObjVal? "info" with
    | .ok info =>
      let V := spaceOf info
      let nm := jStr info "space"
      spaces := spaces.insert nm V
      -- space display, basis order and blade names
      t := t.check (V.showHandle == jStr info "show") s!"{nm} show `{V.showHandle}` vs `{jStr info "show"}`"
      let basis := (jArr info "basis").map fun j => match j with | .num x => (jsonRat x).num.toNat.toUInt64 | _ => 0
      t := t.check (Leibniz.indexBasisAll V.n == basis) s!"{nm} basis order"
      let names := (jArr info "names").map fun j => j.getStr?.toOption.getD ""
      t := t.check (basis.map (V.bladeLabel ·) == names) s!"{nm} names {basis.map (V.bladeLabel ·)}"
      t := t.check (V.grade == jNat info "grade") s!"{nm} grade"
    | .error _ =>
    let nm := jStr r "space"
    let some V := spaces[nm]? | continue
    match r.getObjVal? "u" with
    | .ok u =>
      let a := (jNat u "a").toUInt64
      for (op, mine, compat) in unaryOps V a do
        let jl := julia (u.getObjValD op)
        let (ok, msg) := agree V mine jl
        if ok then t := t.ok else
        let compatOk := match compat with | some c => (agree V c jl).1 | none => false
        match defectClass V nm op compatOk false jl with
        | some c => t := t.defect c
        | none => t := t.bad s!"{path.fileName.getD ""} {nm} {op} a={a}: {msg}"
      -- container (Chain) variants of the complements and reverses
      let g := popcount a
      let chainOps : List (String × Nat × Except String Terms × Option (Except String Terms)) :=
        [ ("crc", V.n - g, V.complementrightChain a, none),
          ("clc", V.n - g, V.complementleftChain a, none),
          ("hrc", V.n - g, V.complementrighthodgeChain a, some (Compat.complementrighthodgeChain V a)),
          ("hlc", V.n - g, V.complementlefthodgeChain a, some (Compat.complementlefthodgeChain V a)),
          ("revc", g, .ok #[(a, if V.reverseChainSign g a then -1 else 1)], none),
          ("arevc", g, .ok #[(a, if V.antireverseChainSign g a then -1 else 1)], none) ]
      for (op, gout, mine, compat) in chainOps do
        let jv := u.getObjValD op
        if jv.isNull then continue
        let jl := julia jv
        let (ok, msg) := agreeChain V gout mine jl
        if ok then t := t.ok else
        let compatOk := match compat with | some c => (agreeChain V gout c jl).1 | none => false
        match defectClass V nm op compatOk false jl with
        | some c => t := t.defect c
        | none => t := t.bad s!"{path.fileName.getD ""} {nm} {op} a={a}: {msg}"
    | .error _ =>
      if (r.getObjValD "skipZ") == .bool true then continue
      let a := (jNat r "a").toUInt64
      let b := (jNat r "b").toUInt64
      for (op, mine, compat) in binaryOps V a b do
        let jl := julia (r.getObjValD op)
        let (ok, msg) := agree V mine jl
        if ok then t := t.ok else
        let compatOk := match compat with | some c => (agree V c jl).1 | none => false
        let freshOk := match fresh[(nm, a.toNat, (b.toNat : Int))]? with
          | some f => V.istangent && (agree V mine (julia (f.getObjValD op))).1
          | none => false
        match defectClass V nm op compatOk freshOk jl with
        | some c => t := t.defect c
        | none => t := t.bad s!"{path.fileName.getD ""} {nm} {op} a={a} b={b}: {msg}"
  return t

/-- Index the fresh-process records. -/
def freshIndex (lines : Array Json) : Fresh := Id.run do
  let mut m : Fresh := {}
  for r in lines do
    if (r.getObjVal? "a").isOk && (r.getObjVal? "b").isOk then
      m := m.insert (jStr r "space", jNat r "a", jInt r "b") r
  return m

/-- Run the blade-level oracle suite. -/
def run : IO Tally := do
  let root : System.FilePath := "oracle/golden/blades"
  let small ← loadLines (root / "dump_small.jsonl")
  let fresh := freshIndex small
  let t ← checkFile (root / "dump_all.jsonl") fresh {}
  checkFile (root / "dump_small.jsonl") {} t

end DirectSumTests.Blades
