/-
`dynamic/composite`: the transcendental functions of the dynamic layer
(`Grassmann.Dynamic.Composite`, `Grassmann.Dynamic.Division`) against the composite oracle
(`oracle/golden/composite/*.json`, 1192 cases in `ℝ²`, `ℝ³`, `ℝ⁴`, `S"+---"`, `S"∞∅+++"`).

The element harness compares only values in this suite (kinds are informational there,
oracle-schema.md §11 rule 2); this suite compares Julia's **result kind** (with `grade` and
`bits`) as well as the values, under the shard's tolerance
(`‖Δ‖₂ ≤ atol + rtol·max(‖out‖₂, ‖expect‖₂)`). Where Julia throws (`inv(m) is undefined`,
`log`/`sqrt` of a multivector), the dynamic `?` functions must return `none`. Cases tagged
with a defect are skipped (their reasons are counted), as are Julia's `Phasor` results.

Known differences (counted as skips, not failures): `exp-nilpotent-couple` (Julia's
parabolic `exp`, fixed here; the oracle does not tag it yet).
-/
import Tests.Dynamic.Common
import Tests.Golden.GrassmannDynamic
import Tests.Golden.Space
import Grassmann.Dynamic.Composite

open Grassmann DirectSum StaticVectors AbstractTensors GrassmannTests Tests.ElementOracle
  Tests.ElementOracle.Dyn

namespace DynamicTests

variable {V : TensorBundle} [Kernels V]

/-- The dynamic composite op of an oracle key, `none` for a rejection (Julia throws). -/
def compositeOp (op : String) (k : Option Int) (a : TA V Float) (b? : Option (TA V Float)) :
    Option (Option (TA V Float)) :=
  match op, b? with
  | "exp", _ => some (some (TA.exp a))
  | "log", _ => some (TA.log? a)
  | "sqrt", _ => some (TA.root? 2 a)
  | "cos", _ => some (some (TA.cos a))
  | "sin", _ => some (TA.div? (TA.sinh (TA.mul (TA.pseudoI V) a)) (TA.pseudoI V))
  | "tan", _ => some (TA.tan? a)
  | "cosh", _ => some (some (TA.cosh a))
  | "sinh", _ => some (some (TA.sinh a))
  | "inv", _ => some (TA.inv? a)
  | "div", some b => some (TA.div? a b)
  | "pow", _ => k.map fun k => some (TA.powInt a k)
  | _, _ => none

/-- Whether a result kind is one this layer represents (`Phasor` results are not compared). -/
def comparableKind : Kind → Bool
  | .phasor | .other | .number | .bool | .space => false
  | _ => true

/-- One composite case: kind, grade/bits, values (or the rejection). -/
def compositeCase (t : Tally) (shard : Shard) (V : TensorBundle) [Kernels V] (c : GoldenCase) : Tally :=
  let tag := s!"{shard.name} {c.op} case {c.idx}"
  if !c.defects.isEmpty then c.defects.foldl (fun t d => t.skip s!"defect {d}") t
  else match c.out with
  | none => t.skip "no output"
  | some out =>
    let dec := fun (i : Option Nat) => i.bind fun i => (shard.inputs[i]?).bind (decodeTA (α := Float) V)
    match dec c.a with
    | none => t.skip "operand not decodable"
    | some a =>
      match compositeOp c.op c.k a (dec c.b) with
      | none => t.skip s!"op {c.op} not evaluated"
      | some r =>
        if out.kind == .error then t.check r.isNone s!"{tag}: Julia throws, the port computes {r.map toString}"
        else if !comparableKind out.kind then t.skip s!"result kind {out.kind}"
        else match r with
          | none => t.bad s!"{tag}: the port rejects, Julia returns {out.kind} {out.str?.getD ""}"
          | some x =>
            let e := encodeTA x
            let tol := (shard.tol? c.op).getD { rtol := 1e-12, atol := 1e-14 }
            let kindOk := e.kind == out.kind && (out.grade.isNone || e.grade == out.grade) &&
              (out.bits.isNone || e.bits == out.bits)
            -- equal coefficients agree even when infinite (the norm of their difference is NaN)
            let vals := match e.dense, out.dense with
              | some g, some w =>
                if (compareCoeffs .exact g w).isNone then none else compareCoeffs (.norm2 tol.rtol tol.atol) g w
              | _, _ => none
            -- Julia's parabolic `exp` of a couple (defect `exp-nilpotent-couple`, fixed here)
            let nilpotent := c.op == "exp" && out.kind == .couple &&
              (match a with | .couple b .. => TA.bladeSq V b == 0 | _ => false)
            if nilpotent then (t.check kindOk s!"{tag}: kind {e.kind} vs {out.kind}").skip
              "exp-nilpotent-couple (Julia's value is wrong)" else
            let t := t.check kindOk s!"{tag}: kind {e.kind} g{e.grade} b{e.bits} vs {out.kind} g{out.grade} b{out.bits} (`{x}` vs `{out.str?.getD ""}`)"
            t.check vals.isNone s!"{tag}: values {vals.getD ""} (`{x}` vs `{out.str?.getD ""}`)"

/-- `dynamic/composite`: every case of the composite oracle. -/
def compositeRun : IO Tally := do
  let root := goldenRoot
  let m ← loadManifest root "composite"
  forEachShard root m ({} : Tally) fun t _ loaded => do
    match loaded with
    | .error e => return t.bad e
    | .ok (s, _) =>
      match s.space.map (·.bundle) with
      | none => return t.bad s!"{s.name}: no space"
      | some V => return s.cases.foldl (fun t c => compositeCase t s V c) t

end DynamicTests
