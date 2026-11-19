import Grassmann.Eval.Engine

/-!
# Pure-Lean GAlculator & LeanCalculator (`ALOK-950`) State Engine (`Grassmann.Eval.Calc`)

Unifies Enkimute's `galculator.html` pocket Geometric Algebra calculator (`R, C, D, M/STA,
R3, P2D, P3D, C2D, C3D`, memory registers `x1..x10`, history tape, live 3D graph of stored
elements) with `ALOK-950` LeanCalculator's Spacetime Algebra `Cl(3,1)` (`-+++`) workspace
and exact **R3 rational rotor** verification (`12`-row fixture compatible).

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck
(`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval.Calc

open Grassmann.CABI.Alg Grassmann.Scene Grassmann.Eval

/-- Exact rational 3D vector for `ALOK-950` R3 rational rotor checks. -/
structure RatVec3 where
  x : Rat
  y : Rat
  z : Rat
  deriving DecidableEq, Repr, Inhabited

/-- Exact rational 3D even rotor `R = s + b12·e₁₂ + b13·e₁₃ + b23·e₂₃` in `ℝ3`. -/
structure RatRotor3 where
  s   : Rat
  b12 : Rat
  b13 : Rat
  b23 : Rat
  deriving DecidableEq, Repr, Inhabited

/-- Exact rational sandwich `R * v * ~R / (R * ~R)` in `ℝ3` (zero floating-point drift;
directly preserves `ALOK-950` R3 rational rotor exactness). -/
def r3RationalSandwich (r : RatRotor3) (v : RatVec3) : RatVec3 :=
  let n2 := r.s * r.s + r.b12 * r.b12 + r.b13 * r.b13 + r.b23 * r.b23
  if n2 == 0 then ⟨0, 0, 0⟩
  else
    -- Using quaternion isomorphism q = (s, -b23, b13, -b12)
    let w := r.s; let qx := -r.b23; let qy := r.b13; let qz := -r.b12
    let r00 := w * w + qx * qx - qy * qy - qz * qz
    let r01 := 2 * (qx * qy - w * qz)
    let r02 := 2 * (qx * qz + w * qy)
    let r10 := 2 * (qx * qy + w * qz)
    let r11 := w * w - qx * qx + qy * qy - qz * qz
    let r12 := 2 * (qy * qz - w * qx)
    let r20 := 2 * (qx * qz - w * qy)
    let r21 := 2 * (qy * qz + w * qx)
    let r22 := w * w - qx * qx - qy * qy + qz * qz
    ⟨(r00 * v.x + r01 * v.y + r02 * v.z) / n2,
     (r10 * v.x + r11 * v.y + r12 * v.z) / n2,
     (r20 * v.x + r21 * v.y + r22 * v.z) / n2⟩

/-- Pure-Lean calculator session state (`x1..x10` registers + mode + history + input buffer). -/
structure CalcState where
  mode       : String := "STA"
  inputBuf   : String := ""
  display    : String := "0"
  storeArmed : Bool   := false
  history    : Array String := #[]
  registers  : Array (String × String) := #[] -- `(slot, exprText)`
  lastError  : String := ""
  deriving Repr, Inhabited

def CalcState.init (mode : String := "STA") : CalcState :=
  { mode, display := "0", history := #[s!"Mode: {mode} (Lean GAlculator)"],
    registers := #[("x1", "e1 + 0.5e2"), ("x2", "0.4e1 + 1.2e2 + 0.6e3")] }

private def setRegister (regs : Array (String × String)) (slot val : String) :
    Array (String × String) :=
  match regs.findIdx? fun kv => kv.1 == slot with
  | some idx => regs.set! idx (slot, val)
  | none => regs.push (slot, val)

private def evalToText (mode : String) (regs : Array (String × String)) (exprStr : String) :
    Except String String := do
  let (_, V, _, _, r, _) := resolveAlgebra mode
  let mut env : EvalEnv V := { zeroIndexed := r > 0 }
  for (slot, valStr) in regs do
    if let .ok ast := parseExprString valStr then
      if let .ok (v, env1) := evalGA env ast then
        env := env1.bind slot v
  let ast ← parseExprString exprStr
  let (res, _) ← evalGA env ast
  return res.showString (r > 0)

/-- Apply a GAlculator keypad press (`"STA"`, `"P3D"`, `"C3D"`, `"st"`, `"x1"`, `"="`, `"Cl"`, …). -/
def stepKey (st : CalcState) (key : String) : CalcState :=
  match key with
  | "R" | "C" | "D" | "M" | "STA" | "R3" | "P2D" | "P3D" | "C2D" | "C3D" =>
    { st with mode := key, inputBuf := "", display := "0", storeArmed := false,
              history := st.history.push s!"Mode → {key}", lastError := "" }
  | "Cl" | "CLEAR" =>
    if st.inputBuf.isEmpty then
      { st with history := #[], display := "0", storeArmed := false, lastError := "" }
    else
      { st with inputBuf := "", display := "0", storeArmed := false, lastError := "" }
  | "st" | "ST" =>
    { st with storeArmed := true }
  | "=" | "ENTER" =>
    let expr := if st.inputBuf.isEmpty then st.display else st.inputBuf
    match evalToText st.mode st.registers expr with
    | .ok out =>
      let hist := (st.history.push s!"{expr} = {out}")
      let trimmed := if hist.size > 12 then hist.extract (hist.size - 12) hist.size else hist
      { st with inputBuf := "", display := out, history := trimmed, lastError := "" }
    | .error err =>
      { st with lastError := err, display := "ERR" }
  | "x1" | "x2" | "x3" | "x4" | "x5" | "x6" | "x7" | "x8" | "x9" | "x10" =>
    if st.storeArmed then
      let expr := if st.inputBuf.isEmpty then st.display else st.inputBuf
      match evalToText st.mode st.registers expr with
      | .ok out =>
        { st with storeArmed := false, registers := setRegister st.registers key expr,
                  history := st.history.push s!"{key} := {out}", display := out, lastError := "" }
      | .error err =>
        { st with storeArmed := false, lastError := err }
    else
      let next := st.inputBuf ++ key
      { st with inputBuf := next, display := next }
  | "Exp"  => let n := st.inputBuf ++ ".exp()";      { st with inputBuf := n, display := n }
  | "Dual" => let n := st.inputBuf ++ ".Dual";       { st with inputBuf := n, display := n }
  | "Rev"  => let n := st.inputBuf ++ ".Reverse";    { st with inputBuf := n, display := n }
  | "Conj" => let n := st.inputBuf ++ ".Conjugate";  { st with inputBuf := n, display := n }
  | "Inv"  => let n := st.inputBuf ++ "**-1";        { st with inputBuf := n, display := n }
  | _ =>
    let next := st.inputBuf ++ key
    { st with inputBuf := next, display := next }

/-- Directly evaluate an expression in `mode` and update `CalcState`. -/
def evalDirect (st : CalcState) (mode : String) (expr : String) : CalcState :=
  let st1 := { st with mode, inputBuf := expr }
  stepKey st1 "="

/-- Render `CalcState` (all stored registers `x1..x10` + current expression) to a live 3D `SceneFrame`! -/
def toSceneFrame (st : CalcState) (frameSeq : UInt64 := 0) (simTime : Float := 0.0) : SceneFrame := Id.run do
  let mut scriptLines : Array String := #[]
  for (slot, exprStr) in st.registers do
    scriptLines := scriptLines.push s!"let {slot} = {exprStr}"
  if !st.inputBuf.isEmpty then
    scriptLines := scriptLines.push s!"let ans = {st.inputBuf}"
  else if st.registers.size ≥ 2 && (st.mode == "STA" || st.mode == "R3" || st.mode == "M") then
    scriptLines := scriptLines.push "let wedge_x1_x2 = x1 ^ x2"
  let code := ";\n".intercalate scriptLines.toList
  let f := evalScriptToFrame st.mode code #[] simTime frameSeq
  let regs := st.registers.map fun (slot, exprStr) =>
    let fmt := match evalToText st.mode st.registers exprStr with | .ok s => s | .error _ => exprStr
    { slot, formatted := fmt : CalcRegister }
  let hud : CalcHudState :=
    { mode := st.mode, display := st.display, history := st.history, registers := regs }
  let diags := if st.lastError.isEmpty then f.diagnostics else f.diagnostics.push st.lastError
  return { f with mode := .calculator, title := s!"LeanCalculator ({st.mode})",
                  calcHud := some hud, diagnostics := diags }

end Grassmann.Eval.Calc
