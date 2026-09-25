/-
Derived blade-operation oracle suite: every record of
`Tests/DirectSum/golden/derived.jsonl` (`gen_derived.jl`, one fresh Julia
process per space), checked on terms (exact), result kind and printed string:

* P1' the derived operators of grassmann-parity.md §2.3 on every blade pair:
  `<`, `⨼`, `⨽`, `<<`, `>>`, `∗`, `⊛`, `⟇`, `antidot`;
* P4 tangent spaces, blade pairs whose `∂` bits overlap (`*`, `∧`, `∨`, `⋅`
  with the nested `∂₁⊗…` coefficient);
* P5 random blade pairs for `n = 6 … 24` (Euclidean and alternating
  signature): `*`, `∧`, `∨`, `⋅`, `⋆a`, `~a`;
* P6 `signbit(V)`, `signbit(V,G)`, and `iseven`/`isodd`/`even`/`odd`/`real`/`imag`
  of every blade.

Mismatches are counted as documented Julia defects only when the evidence
supports it: D1 (`C4neg`)/D2 (`MetricTensor`) when the same composition over the
bug-compatible `DirectSum.Compat` primitives reproduces Julia exactly.
-/
import Tests.DirectSum.Blades
import DirectSum.Ops

open Lean DirectSum DirectSum.Bits

namespace DirectSumTests.Derived

open Blades (spaceOf julia agree loadLines)

/-- The primitive products a derived operator is composed from. -/
structure Prims where
  /-- Geometric product. -/
  mul : UInt64 → UInt64 → BladeResult
  /-- Grassmann `contraction`. -/
  contraction : UInt64 → UInt64 → BladeResult

/-- A derived operator composed over `p` exactly as `DirectSum.Derived` does
(used with the `Compat` primitives to recognize Julia's product defects). -/
def compose (V : TensorBundle) (p : Prims) (op : String) (a b : UInt64) : Except String BladeResult :=
  let dot := fun x y => Except.ok (p.contraction x y)
  let mul := fun x y => Except.ok (p.mul x y)
  match op with
  | "lt" | "lcontr" => .ok (p.contraction b a)
  | "rcontr" => .ok (p.contraction a b)
  | "lshift" => V.mapBilinear dot (.blade b) (V.reverse a)
  | "rshift" => V.mapBilinear dot (V.reverse a) (.blade b)
  | "star" => V.mapBilinear mul (V.reverse a) (.blade b)
  | "cdast" => .ok (p.contraction a b).scalarPart
  | "veedot" => do
    V.mapLinear V.complementleft (← V.mapBilinear mul (← V.complementright a) (← V.complementright b))
  | "antidot" => do
    V.mapLinear V.complementleft (← V.mapBilinear dot (← V.complementright a) (← V.complementright b))
  | _ => .error s!"unknown op {op}"

/-- The library's value of a derived binary operator (the `DirectSum.Ops` API). -/
def mine (V : TensorBundle) (op : String) (a b : UInt64) : Except String BladeResult :=
  match op with
  | "lt" | "lcontr" => V.apply₂ .contractionLeft a b
  | "rcontr" => V.apply₂ .contraction a b
  | "lshift" => V.apply₂ .contractionRevLeft a b
  | "rshift" => V.apply₂ .contractionRevRight a b
  | "star" => V.apply₂ .reverseMul a b
  | "cdast" => V.apply₂ .scalarContraction a b
  | "veedot" => V.apply₂ .veedot a b
  | "antidot" => V.apply₂ .antidot a b
  | "mul" => V.apply₂ .mul a b
  | "wedge" => V.apply₂ .wedge a b
  | "vee" => V.apply₂ .vee a b
  | "dot" => V.apply₂ .contraction a b
  | _ => .error s!"unknown op {op}"

/-- The derived operators of P1'. -/
def derivedOps : List String := ["lt", "lcontr", "rcontr", "lshift", "rshift", "star", "cdast", "veedot", "antidot"]

/-- The products of P4/P5. -/
def productOps : List String := ["mul", "wedge", "vee", "dot"]

/-- Classify a mismatch as a documented product defect. -/
def defectClass (V : TensorBundle) (compatOk : Bool) : Option String :=
  if compatOk && V.hasconformal then some "D1 conformal product ignores signature bits (C4neg)"
  else if compatOk && !V.isdiag then some "D2 MetricTensor product drops middle grades"
  else none

/-- Check one binary op of a record. -/
def checkBinary (t : Tally) (V : TensorBundle) (nm op : String) (r : Json) (a b : UInt64) : Tally :=
  let jl := julia (r.getObjValD op)
  let (ok, msg) := agree V (mine V op a b) jl
  if ok then t.ok else
  let compat : Prims := { mul := Compat.mul V, contraction := Compat.contraction V }
  let compatOk := (agree V (compose V compat op a b) jl).1 || (match op with
    | "mul" => (agree V (.ok (Compat.mul V a b)) jl).1
    | "dot" => (agree V (.ok (Compat.contraction V a b)) jl).1
    | _ => false)
  match defectClass V compatOk with
  | some c => t.defect c
  | none => t.bad s!"{nm} {op} a={a} b={b}: {msg}"

/-- A JSON Boolean array. -/
def boolArr (j : Json) : Option (Array Bool) :=
  match j with
  | .arr xs => xs.mapM fun | .bool b => some b | _ => none
  | _ => none

/-- Run the derived-operation suite. -/
def run (path : System.FilePath := "Tests/DirectSum/golden/derived.jsonl") : IO Tally := do
  let lines ← loadLines path
  let mut t : Tally := {}
  let mut spaces : Std.HashMap String TensorBundle := {}
  for r in lines do
    match r.getObjVal? "info" with
    | .ok info =>
      let V := spaceOf info
      let nm := jStr info "space"
      spaces := spaces.insert nm V
      t := t.check (V.showHandle == jStr info "show") s!"{nm} show `{V.showHandle}` vs `{jStr info "show"}`"
      t := t.check (V.grade == jNat info "grade") s!"{nm} grade"
      if let some sb := boolArr (info.getObjValD "signbit") then
        t := t.check (V.signbit == sb) s!"{nm} signbit {V.signbit} vs {sb}"
      if let .arr gs := info.getObjValD "signbitG" then
        for g in [0:gs.size] do
          if let some sb := boolArr gs[g]! then
            t := t.check (V.signbitGrade g == sb) s!"{nm} signbit(V,{g})"
    | .error _ =>
    let nm := jStr r "space"
    let some V := spaces[nm]? | t := t.bad s!"record for unknown space {nm}"; continue
    if let .ok u := r.getObjVal? "u" then
      let a := (jNat u "a").toUInt64
      let res : BladeResult := .blade a
      for (op, want) in [("iseven", res.isEvenGrade), ("isodd", res.isOddGrade)] do
        t := t.check (((u.getObjValD op).getObjValD "b") == .bool want) s!"{nm} {op} a={a}"
      for (op, f) in [("even", UnOp.even), ("odd", .odd), ("real", .real), ("imag", .imag)] do
        let (ok, msg) := agree V (V.apply₁ f a) (julia (u.getObjValD op))
        t := t.check ok s!"{nm} {op} a={a}: {msg}"
      continue
    let a := (jNat r "a").toUInt64
    let b := (jNat r "b").toUInt64
    if (r.getObjValD "large") == .bool true then
      for op in productOps do t := checkBinary t V nm op r a b
      let (ok, msg) := agree V (V.apply₁ .complementrighthodge a) (julia (r.getObjValD "hr"))
      t := t.check ok s!"{nm} ⋆ a={a}: {msg}"
      let (ok, msg) := agree V (V.apply₁ .reverse a) (julia (r.getObjValD "rev"))
      t := t.check ok s!"{nm} ~ a={a}: {msg}"
    else if (r.getObjValD "overlap") == .bool true then
      for op in productOps do t := checkBinary t V nm op r a b
    else
      for op in derivedOps do t := checkBinary t V nm op r a b
  return t

/-! Compile-time spot checks (Julia 1.13 / Grassmann 0.8.46 values). -/

/-- `r` is `ok x` with `x == y`. -/
def okIs (r : Except String BladeResult) (y : BladeResult) : Bool :=
  match r with
  | .ok x => x == y
  | .error _ => false

-- E3: v₁ << v₁₂ = v₂, v₁₂ << v₁₂ = -1v, v₁₂ >> v₁ = -1v₂, v₂ ∗ v₁₂ = -1v₁
#guard okIs ((ℝ^3).contractionRevLeft 1 3) (.blade 2)
#guard okIs ((ℝ^3).contractionRevLeft 3 3) (.single (-1) 0)
#guard okIs ((ℝ^3).contractionRevRight 3 1) (.single (-1) 2)
#guard okIs ((ℝ^3).reverseMul 2 3) (.single (-1) 1)
-- E3: v₁ ⟇ v₁₂ = -1v₁₃, antidot(v₁,v₁₂) = 1v₁₃, v₁₂ ⊛ v₁₂ = v
#guard okIs ((ℝ^3).veedot 1 3) (.single (-1) 5)
#guard okIs ((ℝ^3).antidot 1 3) (.single 1 5)
#guard (ℝ^3).scalarContraction 3 3 == .blade 0
-- tangent(ℝ^2) (μ = 1): ∂₁ ⋅ ∂₁ = 𝟎 (Julia's Single order rule); tangent(ℝ^2,2,2): ∂₁ * ∂₁ = ∂₁⊗∂₁
#guard ((ℝ^2).tangent).contraction 4 4 == .zero
#guard ((ℝ^2).tangent 2 2).mul 4 4 == .nested 4 (.blade 4)

end DirectSumTests.Derived
