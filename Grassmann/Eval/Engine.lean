import Grassmann.CABI.Alg
import Grassmann.Scene.Types
import Grassmann.Eval.Parser
import Grassmann.Eval.Contour

/-!
# Pure-Lean GA Expression / Script Evaluator & 3D Surface Engine (`Grassmann.Eval.Engine`)

Strictly `Init`-only (ZERO `Lean.*`, `Lake.*`, or `Std.*` imports) so the entire
unified `Grassmann.Studio` compiles into a ~3–5 MB standalone Apple dylib/static
lib AND a tiny Emscripten WASM binary!

Evaluates arbitrary Geometric Algebra expressions and CoffeeShop scripts over ANY
`AlgSpace` (`Cl(p,q,r)`, `STA`, `R3`, `PGA2`, `PGA3`, `CGA2`, `CGA3`,
`Complex`, `Dual`, `Quaternion`) using dense `FloatArray` multivectors `MV V`,
bridges `ganja.js` operator conventions cleanly (metric-free `!`, Dorst `<<`,
regressive `&`, sandwich `>>>`), auto-classifies resulting multivectors into
`SceneIR` 3D/2D primitives, and evaluates `z = f(x, y, t)` surfaces using
forward-mode AD + Grassmann exterior normals!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck
(`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval

open Grassmann.CABI.Alg Grassmann.Scene

/-! ## Arbitrary `Cl(p, q, r)` Signature Construction -/

/-- Construct an `AlgSpace` for arbitrary Clifford signature `Cl(p, q, r)`:
places `r` degenerate zeros (`e₀²=0`) FIRST (matching `ganja.js` `PGA2`/`PGA3` order),
followed by `p` positive `+1` generators and `q` negative `-1` generators. -/
def clAlgSpace (p q r : Nat) : AlgSpace :=
  AlgSpace.cl p q r

/-- Resolve an algebra specifier string (`"PGA3"`, `"STA"`, `"CGA3"`, `"R3"`, `"Cl(3,0,1)"`, …)
into `(canonicalName, AlgSpace, p, q, r, isConformalWitt)`. -/
def resolveAlgebra (spec : String) : String × AlgSpace × UInt8 × UInt8 × UInt8 × Bool :=
  let s := spec.trimAscii.toString.toUpper
  match s with
  | "R" | "REAL" | "CL(0,0,0)" => ("R", AlgSpace.V0, 0, 0, 0, false)
  | "C" | "COMPLEX" | "CL(0,1)" | "CL(0,1,0)" => ("Complex", AlgSpace.sig 1 1, 0, 1, 0, false)
  | "D" | "DUAL" | "CL(0,0,1)" => ("Dual", AlgSpace.cl 0 0 1, 0, 0, 1, false)
  | "H" | "QUAT" | "QUATERNION" | "CL(0,2)" | "CL(0,2,0)" =>
    ("Quaternion", AlgSpace.sig 2 3, 0, 2, 0, false)
  | "R2" | "GA2D" | "VGA2" | "CL(2,0)" | "CL(2,0,0)" => ("R2", AlgSpace.R2, 2, 0, 0, false)
  | "R3" | "GA3D" | "VGA3" | "CL(3,0)" | "CL(3,0,0)" => ("R3", AlgSpace.R3, 3, 0, 0, false)
  | "R4" | "CL(4,0)" | "CL(4,0,0)" => ("R4", AlgSpace.R4, 4, 0, 0, false)
  | "STA" | "M" | "MINKOWSKI" | "CL(1,3)" | "CL(3,1)" | "STA31" =>
    -- ALOK-950 canonical signature: S"-+++" (t² = -1, x²=y²=z² = +1)
    ("STA", AlgSpace.STA, 3, 1, 0, false)
  | "PGA2" | "P2D" | "PGA2D" | "CL(2,0,1)" => ("PGA2", AlgSpace.PGA2, 2, 0, 1, false)
  | "PGA3" | "P3D" | "PGA3D" | "CL(3,0,1)" => ("PGA3", AlgSpace.PGA3, 3, 0, 1, false)
  | "CGA2" | "C2D" | "CGA2D" => ("CGA2", AlgSpace.CGA2, 3, 1, 0, true)
  | "CGA3" | "C3D" | "CGA3D" | "CL(4,1)" | "CL(4,1,0)" => ("CGA3", AlgSpace.CGA3, 4, 1, 0, true)
  | _ =>
    -- Parse `CL(p,q)` or `CL(p,q,r)` or shorthand `"p,q,r"`
    let core :=
      if s.startsWith "CL(" && s.endsWith ")" then
        ((s.drop 3).dropEnd 1).toString
      else s
    let parts := (core.splitOn ",").map (fun x => x.trimAscii.toString.toNat?)
    if parts.length ≥ 2 && parts.all Option.isSome then
      let p := (parts.getD 0 none).getD 3
      let q := (parts.getD 1 none).getD 0
      let r := (parts.getD 2 none).getD 0
      let tot := min 6 (p + q + r)
      let p' := min p tot
      let q' := min q (tot - p')
      let r' := min r (tot - p' - q')
      (s!"Cl({p'},{q'},{r'})", clAlgSpace p' q' r', p'.toUInt8, q'.toUInt8, r'.toUInt8, false)
    else
      ("PGA3", AlgSpace.PGA3, 3, 0, 1, false)

/-- Build `Scene.AlgebraMeta` (basis blade names & metric signs `-1/0/+1`) directly from `V`. -/
def algebraMetaOf (name : String) (V : AlgSpace) (p q r : UInt8) (witt : Bool) : AlgebraMeta :=
  let blades := indexBasisAll V.n
  let names := blades.map fun b =>
    if b == 0 then "1"
    else if r > 0 then
      -- Show ganja-style 0-indexed `e0, e1, ...` for degenerate PGA algebras
      let idxs := (List.range V.n).filter (fun i => testBit b i)
      "e" ++ String.join (idxs.map toString)
    else V.bladeLabel b
  let metrics : Array Int8 := blades.map fun b =>
    if b == 0 then (1 : Int8)
    else bladeMetricSign V b
  { name, p, q, r, conformalWitt := witt, basisNames := names, basisMetric := metrics }

/-! ## Ganja Compatibility Helpers on `MV V` -/

/-- Extract dense `FloatArray` of length `2^V.n` in grade-major basis order from `MV V`. -/
def mvToDenseArray {V : AlgSpace} (x : MV V) : FloatArray :=
  let blades := indexBasisAll V.n
  let rec go (i : Nat) (acc : FloatArray) : FloatArray :=
    if i < blades.size then go (i + 1) (acc.push (x.coeff blades[i]!)) else acc
  go 0 (FloatArray.emptyWithCapacity blades.size)

/-- Reconstruct an `MV V` from a dense `FloatArray` in grade-major basis order. -/
def denseArrayToMV {V : AlgSpace} (xs : FloatArray) : MV V :=
  let blades := indexBasisAll V.n
  let rec go (i : Nat) (acc : MV V) : MV V :=
    if i < min blades.size xs.size then
      let c := xs.get! i
      if Float.abs c < 1e-15 then go (i + 1) acc
      else go (i + 1) (MV.add acc (MV.single blades[i]! c))
    else acc
  go 0 MV.zero

/-- Dorst left contraction `a ⌋ b` (`ganja.js`'s `a << b`) on `MV V`. -/
def dorstLDot {V : AlgSpace} (a b : MV V) : MV V :=
  MV.contractionLeft a b

/-- Symmetric inner product (`ganja.js`'s `a | b`). -/
def symDot {V : AlgSpace} (a b : MV V) : MV V :=
  let blades := indexBasisAll V.n
  let rec goA (i : Nat) (acc : MV V) : MV V :=
    if i < blades.size then
      let ba := blades[i]!
      let ca := a.coeff ba
      if Float.abs ca < 1e-15 then goA (i + 1) acc
      else
        let ga := popcount64 ba
        let rec goB (j : Nat) (acc2 : MV V) : MV V :=
          if j < blades.size then
            let bb := blades[j]!
            let cb := b.coeff bb
            if Float.abs cb < 1e-15 then goB (j + 1) acc2
            else
              let gb := popcount64 bb
              let targetG := if ga ≥ gb then ga - gb else gb - ga
              let prod := MV.mul (MV.single ba ca) (MV.single bb cb)
              let proj := MV.gradeProj targetG prod
              goB (j + 1) (MV.add acc2 proj)
          else acc2
        goA (i + 1) (goB 0 acc)
    else acc
  goA 0 MV.zero

/-- Metric-free regressive product (`ganja.js`'s `a & b` = `complementleft(!a ∧ !b)`). -/
def ganjaVee {V : AlgSpace} (a b : MV V) : MV V :=
  MV.complementleft (MV.wedge (MV.complementright a) (MV.complementright b))

/-- Sandwich product `R >>> x = R * x * ~R`. -/
def ganjaSandwich {V : AlgSpace} (r x : MV V) : MV V :=
  MV.mul (MV.mul r x) (MV.reverse r)

/-- Euclidean-style geometric norm `√|⟨x ~x⟩₀|` (falls back to coefficient norm if null). -/
def ganjaNorm {V : AlgSpace} (x : MV V) : Float :=
  let s := (MV.mul x (MV.reverse x)).coeff 0
  let m := Float.sqrt (Float.abs s)
  if m > 1e-12 then m
  else
    let xs := mvToDenseArray x
    let rec sumSq (i : Nat) (acc : Float) : Float :=
      if i < xs.size then
        let v := xs.get! i
        sumSq (i + 1) (acc + v * v)
      else Float.sqrt acc
    sumSq 0 0.0

/-- Normalize multivector `x` by `ganjaNorm x`. -/
def ganjaNormalize {V : AlgSpace} (x : MV V) : MV V :=
  let n := ganjaNorm x
  if n < 1e-12 then x else MV.mulScalar x (1.0 / n)

/-- Dominant grade of an `MV V` (for `InspectEntry` and auto-rendering). -/
def dominantGrade {V : AlgSpace} (x : MV V) : Nat :=
  let blades := indexBasisAll V.n
  let rec go (i : Nat) (bestG : Nat) (bestMag : Float) : Nat :=
    if i < blades.size then
      let b := blades[i]!
      let mag := Float.abs (x.coeff b)
      if mag > bestMag then go (i + 1) (popcount64 b) mag
      else go (i + 1) bestG bestMag
    else bestG
  go 0 0 0.0

/-- Parse blade subscript (e.g. `"0"`, `"12"`, `"013"`, `"∞"`, `"∅"`) into bitmask for `V`.
When `zeroIndexed` is true (PGA with `r > 0`), digit `0` maps to bit `0`, `1` to bit `1`, etc.
Otherwise (Euclidean/STA/CGA), digit `1` maps to bit `0`, `2` to bit `1`, etc., with `∞ → 0, ∅ → 1`
in Witt conformal spaces. -/
def bladeSubToBits (V : AlgSpace) (zeroIndexed : Bool) (sub : String) : Option UInt64 :=
  let rec go (cs : List Char) (mask : UInt64) : Option UInt64 :=
    match cs with
    | [] => some mask
    | c :: rest =>
      let bit? : Option Nat :=
        if c == '∞' then if V.hasInf then some 0 else none
        else if c == '∅' then if V.hasOrigin then some (if V.hasInf then 1 else 0) else none
        else if c.isDigit then
          let d := c.toNat - 48
          if zeroIndexed then
            if d < V.n then some d else none
          else
            let off := V.nulls
            if d == 0 then
              if V.hasOrigin then some (if V.hasInf then 1 else 0) else some 0
            else if d - 1 + off < V.n then some (d - 1 + off)
            else if d - 1 < V.n then some (d - 1)
            else none
        else none
      match bit? with
      | none => none
      | some b => go rest (mask ||| ((1 : UInt64) <<< b.toUInt64))
  go sub.toList 0

/-! ## GA Script Evaluator -/

/-- Evaluation environment for dynamic GA scripts. -/
structure EvalEnv (V : AlgSpace) where
  zeroIndexed : Bool := false
  timeSec     : Float := 0.0
  handles     : Array (UInt32 × Vec3) := #[]
  vars        : Array (String × MV V) := #[]
  order       : Array String := #[] -- preserves declaration order for visualization/inspector

namespace EvalEnv

def lookup? {V : AlgSpace} (env : EvalEnv V) (name : String) : Option (MV V) :=
  (env.vars.find? fun kv => kv.1 == name).map (·.2)

def bind {V : AlgSpace} (env : EvalEnv V) (name : String) (v : MV V) : EvalEnv V :=
  match env.vars.findIdx? fun kv => kv.1 == name with
  | some idx => { env with vars := env.vars.set! idx (name, v) }
  | none => { env with vars := env.vars.push (name, v), order := env.order.push name }

def handlePos {V : AlgSpace} (env : EvalEnv V) (hid : UInt32) (defPos : Vec3) : Vec3 :=
  ((env.handles.find? fun kv => kv.1 == hid).map (·.2)).getD defPos

end EvalEnv

/-- Construct a PGA2/PGA3/CGA/Euclidean point multivector from `(x, y, z)` in space `V`. -/
def makePointMV (V : AlgSpace) (zeroIndexed : Bool) (x y z : Float) : MV V :=
  if zeroIndexed && V.n == 4 then
    let p := MV.single 14 1.0
    let p := MV.add p (MV.single 13 (-x))
    let p := MV.add p (MV.single 11 y)
    MV.add p (MV.single 7 (-z))
  else if zeroIndexed && V.n == 3 then
    let p := MV.single 6 1.0
    let p := MV.add p (MV.single 3 (-x))
    MV.add p (MV.single 5 y)
  else if V.hasconformal && V.n == 5 then
    let r2 := 0.5 * (x * x + y * y + z * z)
    let p := MV.single 1 r2
    let p := MV.add p (MV.single 2 1.0)
    let p := MV.add p (MV.single 4 x)
    let p := MV.add p (MV.single 8 y)
    MV.add p (MV.single 16 z)
  else if V.hasconformal && V.n == 4 then
    let r2 := 0.5 * (x * x + y * y)
    let p := MV.single 1 r2
    let p := MV.add p (MV.single 2 1.0)
    let p := MV.add p (MV.single 4 x)
    MV.add p (MV.single 8 y)
  else if V.n == 4 && V == AlgSpace.STA then
    let p := MV.single 2 x
    let p := MV.add p (MV.single 4 y)
    MV.add p (MV.single 8 z)
  else
    let p := if V.n ≥ 1 then MV.single 1 x else MV.zero
    let p := if V.n ≥ 2 then MV.add p (MV.single 2 y) else p
    if V.n ≥ 3 then MV.add p (MV.single 4 z) else p

/-- Evaluate an `Expr` over `MV V` with full ganja.js + Grassmann.jl operator support. -/
partial def evalGA {V : AlgSpace} (env : EvalEnv V) (e : Expr) :
    Except String (MV V × EvalEnv V) := do
  match e with
  | .num v => return (if v == 0.0 then MV.zero else MV.single 0 v, env)
  | .str _ => return (MV.zero, env)
  | .blade pfx sub =>
    match bladeSubToBits V env.zeroIndexed sub with
    | some bits =>
      let b : MV V := if bits == 0 then MV.one else MV.blade bits
      if pfx == 'E' then return (MV.complementright b, env)
      else return (b, env)
    | none => throw s!"invalid blade literal '{pfx}{sub}' in {V}"
  | .ident name =>
    match env.lookup? name with
    | some v => return (v, env)
    | none =>
      match name with
      | "pi" | "π" => return (MV.single 0 3.14159265358979323846, env)
      | "e" | "ℯ"  => return (MV.single 0 2.71828182845904523536, env)
      | "t" | "time" => return (MV.single 0 env.timeSec, env)
      | "I" | "pss" => return (MV.blade (lowMask V.n), env)
      | "no" | "ori" | "∅" =>
        if V.hasOrigin then return (MV.blade (if V.hasInf then 2 else 1), env)
        else if V.n == 5 then return (MV.add (MV.single 16 0.5) (MV.single 8 (-0.5)), env)
        else throw "no/ori requires conformal space"
      | "ni" | "inf" | "∞" =>
        if V.hasInf then return (MV.blade 1, env)
        else if V.n == 5 then return (MV.add (MV.single 8 1.0) (MV.single 16 1.0), env)
        else throw "ni/inf requires conformal space"
      | "et" => return (MV.blade 1, env)
      | "ex" => return (MV.blade (if V == AlgSpace.STA then 2 else 1), env)
      | "ey" => return (MV.blade (if V == AlgSpace.STA then 4 else 2), env)
      | "ez" => return (MV.blade (if V == AlgSpace.STA then 8 else 4), env)
      | _ => throw s!"unbound identifier '{name}'"
  | .unary op a =>
    let (va, env1) ← evalGA env a
    match op with
    | "-" => return (MV.neg va, env1)
    | "~" => return (MV.reverse va, env1)
    | "!" => return (MV.complementright va, env1)
    | "⋆" => return (MV.hodge va, env1)
    | _   => throw s!"unknown unary operator '{op}'"
  | .binary op a b =>
    let (va, env1) ← evalGA env a
    let (vb, env2) ← evalGA env1 b
    match op with
    | "+" => return (MV.add va vb, env2)
    | "-" => return (MV.sub va vb, env2)
    | "*" | "·" => return (MV.mul va vb, env2)
    | "/" =>
      let sc := vb.coeff 0
      if dominantGrade vb == 0 && Float.abs sc > 1e-15 then
        return (MV.mulScalar va (1.0 / sc), env2)
      else
        return (MV.mul va (MV.inv vb), env2)
    | "∧" => return (MV.wedge va vb, env2)
    | "^" =>
      if dominantGrade va == 0 && dominantGrade vb == 0 then
        return (MV.single 0 (Float.pow (va.coeff 0) (vb.coeff 0)), env2)
      else
        return (MV.wedge va vb, env2)
    | "&" | "∨" => return (ganjaVee va vb, env2)
    | "<<" | "⨼" => return (dorstLDot va vb, env2)
    | "⋅" | "⨽" => return (MV.contraction va vb, env2)
    | "|" => return (symDot va vb, env2)
    | ">>>" => return (ganjaSandwich va vb, env2)
    | "⊘" => return (ganjaSandwich (MV.reverse vb) va, env2)
    | "**" =>
      let expS := vb.coeff 0
      if Float.abs (expS + 1.0) < 1e-9 then
        return (MV.inv va, env2)
      else if dominantGrade va == 0 && dominantGrade vb == 0 then
        return (MV.single 0 (Float.pow (va.coeff 0) expS), env2)
      else if Float.abs (va.coeff 0 - 2.71828182845904523536) < 1e-6 && dominantGrade va == 0 then
        return (MV.exp vb, env2)
      else
        let n := expS.toUInt32.toNat
        let rec powRec (k : Nat) (acc : MV V) : MV V :=
          match k with | 0 => acc | m + 1 => powRec m (MV.mul acc va)
        return (powRec n MV.one, env2)
    | _ => throw s!"unsupported binary operator '{op}'"
  | .field obj fname =>
    let (vo, env1) ← evalGA env obj
    match fname.toLower with
    | "normalized" | "unit" => return (ganjaNormalize vo, env1)
    | "reverse" | "rev"     => return (MV.reverse vo, env1)
    | "conjugate" | "conj"  => return (MV.clifford vo, env1)
    | "involute"            => return (MV.involute vo, env1)
    | "dual"                => return (MV.complementright vo, env1)
    | "undual"              => return (MV.complementleft vo, env1)
    | "length" | "norm"     => return (MV.single 0 (ganjaNorm vo), env1)
    | "s" | "scalar"        => return (MV.single 0 (vo.coeff 0), env1)
    | "inverse" | "inv"     => return (MV.inv vo, env1)
    | _ => throw s!"unknown field '.{fname}'"
  | .method obj mname args =>
    let (vo, env1) ← evalGA env obj
    match mname.toLower with
    | "grade" =>
      if h : 0 < args.size then
        let (vg, env2) ← evalGA env1 args[0]
        return (MV.gradeProj (coeffZeroNat vg) vo, env2)
      else throw "Grade(k) expects 1 argument"
    | "exp" => return (MV.exp vo, env1)
    | "log" => return (MV.log vo, env1)
    | _ => throw s!"unknown method '.{mname}()'"
  | .call fname args =>
    let mut envCur := env
    let mut vals : Array (MV V) := Array.mkEmpty args.size
    for a in args do
      let (v, envNext) ← evalGA envCur a
      vals := vals.push v
      envCur := envNext
    let f0 (i : Nat) (d : Float := 0.0) : Float := (vals[i]?.map (·.coeff 0)).getD d
    match fname.toLower with
    | "sin"  => return (MV.single 0 (Float.sin (f0 0)), envCur)
    | "cos"  => return (MV.single 0 (Float.cos (f0 0)), envCur)
    | "tan"  => return (MV.single 0 (Float.tan (f0 0)), envCur)
    | "sinh" => return (MV.single 0 (Float.sinh (f0 0)), envCur)
    | "cosh" => return (MV.single 0 (Float.cosh (f0 0)), envCur)
    | "sqrt" => return (MV.single 0 (Float.sqrt (max 0.0 (f0 0))), envCur)
    | "abs"  => return (MV.single 0 (Float.abs (f0 0)), envCur)
    | "atan2" => return (MV.single 0 (Float.atan2 (f0 0) (f0 1)), envCur)
    | "exp"  =>
      if h : 0 < vals.size then return (MV.exp vals[0], envCur)
      else throw "exp() expects 1 argument"
    | "log"  =>
      if h : 0 < vals.size then return (MV.log vals[0], envCur)
      else throw "log() expects 1 argument"
    | "rev" | "reverse" =>
      if h : 0 < vals.size then return (MV.reverse vals[0], envCur)
      else throw "rev() expects 1 argument"
    | "dual" =>
      if h : 0 < vals.size then return (MV.complementright vals[0], envCur)
      else throw "dual() expects 1 argument"
    | "norm" | "length" =>
      if h : 0 < vals.size then return (MV.single 0 (ganjaNorm vals[0]), envCur)
      else throw "norm() expects 1 argument"
    | "unit" | "normalize" =>
      if h : 0 < vals.size then return (ganjaNormalize vals[0], envCur)
      else throw "normalize() expects 1 argument"
    | "grade" =>
      if h : 1 < vals.size then return (MV.gradeProj (coeffZeroNat vals[1]) vals[0], envCur)
      else throw "grade(x, k) expects 2 arguments"
    | "point" =>
      return (makePointMV V envCur.zeroIndexed (f0 0) (f0 1) (f0 2), envCur)
    | "handle" =>
      let hid := (f0 0).toUInt32
      let p := envCur.handlePos hid ⟨f0 1, f0 2, f0 3⟩
      return (makePointMV V envCur.zeroIndexed p.x p.y p.z, envCur)
    | "plane" =>
      if envCur.zeroIndexed && V.n == 4 then
        let pl := MV.add (MV.single 1 (f0 3))
          (MV.add (MV.single 2 (f0 0)) (MV.add (MV.single 4 (f0 1)) (MV.single 8 (f0 2))))
        return (pl, envCur)
      else
        let pl := MV.add (MV.single 1 (f0 0)) (MV.add (MV.single 2 (f0 1)) (MV.single 4 (f0 2)))
        return (pl, envCur)
    | "line" =>
      if envCur.zeroIndexed && V.n == 3 then
        let l := MV.add (MV.single 1 (f0 2)) (MV.add (MV.single 2 (f0 0)) (MV.single 4 (f0 1)))
        return (l, envCur)
      else
        return (MV.add (MV.single 2 (f0 0)) (MV.single 4 (f0 1)), envCur)
    | "up" =>
      if h : 0 < vals.size then
        let v := vals[0]
        if V.hasconformal && V.n == 5 then
          return (makePointMV V false (v.coeff 4) (v.coeff 8) (v.coeff 16), envCur)
        else
          return (makePointMV V envCur.zeroIndexed (v.coeff 1) (v.coeff 2) (v.coeff 4), envCur)
      else throw "up() expects 1 argument"
    | "rotor" =>
      if h : 1 < vals.size then
        let b := ganjaNormalize vals[0]
        let ang := 0.5 * f0 1
        return (MV.add (MV.single 0 (Float.cos ang)) (MV.mulScalar b (Float.sin ang)), envCur)
      else throw "rotor(bivector, angle) expects 2 arguments"
    | _ => throw s!"unknown function '{fname}'"
  | .letBind name rhs =>
    let (v, env1) ← evalGA env rhs
    return (v, env1.bind name v)
  | .eq (.ident name) rhs =>
    let (v, env1) ← evalGA env rhs
    return (v, env1.bind name v)
  | .eq lhs rhs =>
    let (vl, env1) ← evalGA env lhs
    let (vr, env2) ← evalGA env1 rhs
    return (MV.sub vl vr, env2)
  | .list elems =>
    let mut envCur := env
    let mut last : MV V := MV.zero
    for el in elems do
      let (v, envNext) ← evalGA envCur el
      last := v
      envCur := envNext
    return (last, envCur)
  | .seq stmts =>
    let mut envCur := env
    let mut last : MV V := MV.zero
    for s in stmts do
      let (v, envNext) ← evalGA envCur s
      last := v
      envCur := envNext
    return (last, envCur)
where
  coeffZeroNat (x : MV V) : Nat := (max 0.0 (x.coeff 0)).toUInt32.toNat

/-! ## Automatic Multivector → `SceneFrame` Classifier -/

private def scriptPalette (i : Nat) : RGBA :=
  match i % 7 with
  | 0 => RGBA.cyan
  | 1 => RGBA.amber
  | 2 => RGBA.green
  | 3 => RGBA.coral
  | 4 => RGBA.violet
  | 5 => RGBA.blue
  | _ => RGBA.white

/-- Classify a single `MV V` element into `SceneFrame` 3D/2D primitives
(PGA2, PGA3, CGA3 Witt, STA `-+++`, R3, Complex/Dual/Quaternion). -/
def appendClassified {V : AlgSpace} (f : SceneFrame) (name : String) (idx : Nat)
    (zeroIndexed : Bool) (x : MV V) : SceneFrame :=
  let col := scriptPalette idx
  let g := dominantGrade x
  let dense := mvToDenseArray x
  let entry : InspectEntry :=
    { idx := idx.toUInt32, name, grade := g.toUInt32,
      formatted := x.showString zeroIndexed, coeffs := dense, editable := true }
  let f := { f with inspect := f.inspect.push entry }
  -- PGA3: D"0,1,1,1" (bit0=e0, bit1=e1, bit2=e2, bit3=e3)
  if zeroIndexed && V.n == 4 then
    let w := x.coeff 14 -- e123
    if g == 3 && Float.abs w > 1e-6 then
      let px := -x.coeff 13 / w
      let py :=  x.coeff 11 / w
      let pz := -x.coeff 7  / w
      { f with points := f.points.push {
          handleId := idx.toUInt32, pos := ⟨px, py, pz⟩, radius := 0.08,
          color := col, role := { draggable := true }, label := name } }
    else if g == 2 then
      let dir : Vec3 := ⟨x.coeff 12, -x.coeff 10, x.coeff 6⟩
      let dn2 := Vec3.normSq dir
      if dn2 > 1e-8 then
        let mom : Vec3 := ⟨x.coeff 3, x.coeff 5, x.coeff 9⟩
        let orig := Vec3.scale (1.0 / dn2) (Vec3.cross dir mom)
        { f with lines := f.lines.push {
            origin := orig, dir := Vec3.normalize dir, clip := 3.0, width := 2.4,
            color := col, label := name } }
      else f
    else if g == 1 then
      let n : Vec3 := ⟨x.coeff 2, x.coeff 4, x.coeff 8⟩
      let nlen := Vec3.norm n
      if nlen > 1e-6 then
        let un := Vec3.scale (1.0 / nlen) n
        let d := x.coeff 1 / nlen
        let center := Vec3.scale (-d) un
        let (u, v) := Vec3.orthonormalBasis un
        { f with planes := f.planes.push {
            center, u, v, extent := 2.0,
            color := ⟨col.r, col.g, col.b, 0.24⟩, label := name } }
      else f
    else f
  -- PGA2: D"0,1,1" (bit0=e0, bit1=e1, bit2=e2)
  else if zeroIndexed && V.n == 3 then
    let w := x.coeff 6 -- e12
    if g == 2 && Float.abs w > 1e-6 then
      let px := -x.coeff 3 / w
      let py :=  x.coeff 5 / w
      { f with points := f.points.push {
          handleId := idx.toUInt32, pos := ⟨px, py, 0.0⟩, radius := 0.07,
          color := col, role := { draggable := true }, label := name } }
    else if g == 1 then
      let a := x.coeff 2; let b := x.coeff 4; let c := x.coeff 1
      let nlen := Float.sqrt (a * a + b * b)
      if nlen > 1e-6 then
        let orig : Vec3 := ⟨-c * a / (nlen * nlen), -c * b / (nlen * nlen), 0.0⟩
        let dir : Vec3 := ⟨-b / nlen, a / nlen, 0.0⟩
        { f with lines := f.lines.push {
            origin := orig, dir, clip := 3.5, width := 2.2, color := col, label := name } }
      else f
    else f
  -- Witt CGA3: S"∞∅+++" (bit0=∞, bit1=∅, bit2=e1, bit3=e2, bit4=e3)
  else if V.hasconformal && V.n == 5 then
    if g == 1 then
      let w := x.coeff 2
      let cInf := x.coeff 1
      let ex := x.coeff 4; let ey := x.coeff 8; let ez := x.coeff 16
      if Float.abs w > 1e-6 then
        let cx := ex / w; let cy := ey / w; let cz := ez / w
        let r2 := cx * cx + cy * cy + cz * cz - 2.0 * cInf / w
        if Float.abs r2 < 1e-3 then
          { f with points := f.points.push {
              handleId := idx.toUInt32, pos := ⟨cx, cy, cz⟩, radius := 0.08,
              color := col, role := { draggable := true }, label := name } }
        else
          { f with spheres := f.spheres.push {
              center := ⟨cx, cy, cz⟩, radius := Float.sqrt (Float.abs r2),
              color := ⟨col.r, col.g, col.b, 0.28⟩, imaginary := r2 < 0.0, label := name } }
      else
        let n : Vec3 := ⟨ex, ey, ez⟩
        let nlen := Vec3.norm n
        if nlen > 1e-6 then
          let un := Vec3.scale (1.0 / nlen) n
          let center := Vec3.scale (cInf / nlen) un
          let (u, v) := Vec3.orthonormalBasis un
          { f with planes := f.planes.push {
              center, u, v, extent := 2.2,
              color := ⟨col.r, col.g, col.b, 0.24⟩, label := name } }
        else f
    else f
  -- STA S"-+++" or Euclidean R3 / R2 / Complex / Quaternion
  else
    let vx := if V == AlgSpace.STA then x.coeff 2 else x.coeff 1
    let vy := if V == AlgSpace.STA then x.coeff 4 else (if V.n ≥ 2 then x.coeff 2 else 0.0)
    let vz := if V == AlgSpace.STA then x.coeff 8 else (if V.n ≥ 3 then x.coeff 4 else 0.0)
    if g == 1 then
      let tip : Vec3 := ⟨vx, vy, vz⟩
      { f with
        segments := f.segments.push {
          a := Vec3.zero, b := tip, width := 3.0, color := col, role := { arrow := true } },
        points := f.points.push {
          handleId := idx.toUInt32, pos := tip, radius := 0.07,
          color := col, role := { draggable := true }, label := name } }
    else if g == 2 && V.n ≥ 3 then
      let b12 := if V == AlgSpace.STA then x.coeff 6 else x.coeff 3
      let b13 := if V == AlgSpace.STA then x.coeff 10 else x.coeff 5
      let b23 := if V == AlgSpace.STA then x.coeff 12 else x.coeff 6
      let area := Float.sqrt (b12 * b12 + b13 * b13 + b23 * b23)
      if area > 1e-6 then
        let n : Vec3 := ⟨b23, -b13, b12⟩
        let (u, v) := Vec3.orthonormalBasis n
        let rad := Float.sqrt (area / 3.141592653589793)
        { f with bivectorDisks := f.bivectorDisks.push {
            origin := Vec3.zero, u := Vec3.scale rad u, v := Vec3.scale rad v,
            area, color := ⟨col.r, col.g, col.b, 0.35⟩, isDisk := true } }
      else f
    else f

/-- Evaluate a full CoffeeShop script string in `algebraSpec` and emit a `SceneFrame`. -/
def evalScriptToFrame (algebraSpec : String) (code : String)
    (handles : Array (UInt32 × Vec3) := #[]) (timeSec : Float := 0.0)
    (frameSeq : UInt64 := 0) : SceneFrame :=
  let (algName, V, p, q, r, witt) := resolveAlgebra algebraSpec
  let zeroIdx := r > 0
  let meta_ := algebraMetaOf algName V p q r witt
  let is2D := (zeroIdx && V.n == 3) || (!zeroIdx && V.n ≤ 2)
  let base : SceneFrame :=
    { frameSeq, simTime := timeSec, mode := .coffeeShop, is2D,
      algebra := meta_, presetId := "custom_script", title := s!"{algName} Script",
      camera := if is2D then { motor := Motor3.translator 0.0 0.0 (-4.0), isOrtho := true } else {} }
  match parseScript code with
  | .error err => { base with diagnostics := #[s!"Parse error: {err}"] }
  | .ok stmts =>
    let initEnv : EvalEnv V := { zeroIndexed := zeroIdx, timeSec, handles }
    let rec runStmts (i : Nat) (env : EvalEnv V) (last : MV V) :
        Except String (MV V × EvalEnv V) := do
      if i < stmts.size then
        let (v, env1) ← evalGA env stmts[i]!
        runStmts (i + 1) env1 v
      else return (last, env)
    match runStmts 0 initEnv MV.zero with
    | .error err => { base with diagnostics := #[s!"Eval error: {err}"] }
    | .ok (lastVal, finalEnv) => Id.run do
      let mut f := base
      let mut idx := 0
      for name in finalEnv.order do
        if let some v := finalEnv.lookup? name then
          f := appendClassified f name idx zeroIdx v
          idx := idx + 1
      if finalEnv.order.isEmpty then
        f := appendClassified f "ans" 0 zeroIdx lastVal
      return f

/-! ## Forward-Mode AD Scalar & Surface Evaluator (`z = f(x, y, t)`) -/

/-- Dual-number jet `(val, dx, dy)` for exact analytical surface tangents & Grassmann normals. -/
structure Jet2 where
  v  : Float
  dx : Float
  dy : Float
  deriving Repr, Inhabited

namespace Jet2

@[inline] def const (c : Float) : Jet2 := ⟨c, 0.0, 0.0⟩
@[inline] def varX (x : Float) : Jet2 := ⟨x, 1.0, 0.0⟩
@[inline] def varY (y : Float) : Jet2 := ⟨y, 0.0, 1.0⟩
@[inline] def add (a b : Jet2) : Jet2 := ⟨a.v + b.v, a.dx + b.dx, a.dy + b.dy⟩
@[inline] def sub (a b : Jet2) : Jet2 := ⟨a.v - b.v, a.dx - b.dx, a.dy - b.dy⟩
@[inline] def neg (a : Jet2) : Jet2 := ⟨-a.v, -a.dx, -a.dy⟩
@[inline] def mul (a b : Jet2) : Jet2 :=
  ⟨a.v * b.v, a.dx * b.v + a.v * b.dx, a.dy * b.v + a.v * b.dy⟩
@[inline] def div (a b : Jet2) : Jet2 :=
  let inv := if Float.abs b.v < 1e-12 then 0.0 else 1.0 / b.v
  let inv2 := inv * inv
  ⟨a.v * inv, (a.dx * b.v - a.v * b.dx) * inv2, (a.dy * b.v - a.v * b.dy) * inv2⟩
@[inline] def chain (a : Jet2) (fv dfv : Float) : Jet2 :=
  ⟨fv, dfv * a.dx, dfv * a.dy⟩

end Jet2

/-- Evaluate a parsed scalar expression `f(x, y, t)` with exact partial derivatives `(f, ∂f/∂x, ∂f/∂y)`. -/
partial def evalJet2 (e : Expr) (x y t : Float) : Jet2 :=
  match e with
  | .num v => Jet2.const v
  | .ident name =>
    match name.toLower with
    | "x" => Jet2.varX x
    | "y" => Jet2.varY y
    | "t" | "time" => Jet2.const t
    | "pi" | "π" => Jet2.const 3.14159265358979323846
    | "e" | "ℯ"  => Jet2.const 2.71828182845904523536
    | _ => Jet2.const 0.0
  | .unary "-" a => Jet2.neg (evalJet2 a x y t)
  | .unary _ a   => evalJet2 a x y t
  | .eq (.ident "z") rhs => evalJet2 rhs x y t
  | .eq lhs rhs => Jet2.sub (evalJet2 lhs x y t) (evalJet2 rhs x y t)
  | .binary op a b =>
    let ja := evalJet2 a x y t
    let jb := evalJet2 b x y t
    match op with
    | "+" => Jet2.add ja jb
    | "-" => Jet2.sub ja jb
    | "*" | "·" => Jet2.mul ja jb
    | "/" => Jet2.div ja jb
    | "^" | "**" =>
      if Float.abs jb.dx < 1e-15 && Float.abs jb.dy < 1e-15 then
        let p := jb.v
        let fv := Float.pow ja.v p
        let df := if Float.abs p < 1e-15 then 0.0 else p * Float.pow ja.v (p - 1.0)
        Jet2.chain ja fv df
      else
        let safeA := max 1e-12 ja.v
        let fv := Float.pow safeA jb.v
        let lnA := Float.log safeA
        ⟨fv, fv * (jb.dx * lnA + jb.v * ja.dx / safeA),
             fv * (jb.dy * lnA + jb.v * ja.dy / safeA)⟩
    | _ => ja
  | .call fname args =>
    let ja := if h : 0 < args.size then evalJet2 args[0] x y t else Jet2.const 0.0
    match fname.toLower with
    | "sin"  => Jet2.chain ja (Float.sin ja.v) (Float.cos ja.v)
    | "cos"  => Jet2.chain ja (Float.cos ja.v) (-Float.sin ja.v)
    | "tan"  =>
      let c := Float.cos ja.v
      Jet2.chain ja (Float.tan ja.v) (if Float.abs c < 1e-9 then 0.0 else 1.0 / (c * c))
    | "exp"  => let ev := Float.exp ja.v; Jet2.chain ja ev ev
    | "sqrt" =>
      let sv := Float.sqrt (max 1e-12 ja.v)
      Jet2.chain ja sv (0.5 / sv)
    | "log" | "ln" =>
      let sa := max 1e-12 ja.v
      Jet2.chain ja (Float.log sa) (1.0 / sa)
    | "abs" => Jet2.chain ja (Float.abs ja.v) (if ja.v < 0.0 then -1.0 else 1.0)
    | "sinh" => Jet2.chain ja (Float.sinh ja.v) (Float.cosh ja.v)
    | "cosh" => Jet2.chain ja (Float.cosh ja.v) (Float.sinh ja.v)
    | _ => ja
  | _ => Jet2.const 0.0

/-- Smooth studio colormap (deep indigo → cyan → emerald → warm gold) for 3D surfaces. -/
def heightColor (u : Float) : RGBA :=
  let t := max 0.0 (min 1.0 u)
  if t < 0.33 then
    let s := t / 0.33
    ⟨0.12 + 0.08 * s, 0.18 + 0.56 * s, 0.52 + 0.42 * s, 1.0⟩
  else if t < 0.66 then
    let s := (t - 0.33) / 0.33
    ⟨0.20 + 0.25 * s, 0.74 + 0.18 * s, 0.94 - 0.44 * s, 1.0⟩
  else
    let s := (t - 0.66) / 0.34
    ⟨0.45 + 0.53 * s, 0.92 - 0.20 * s, 0.50 - 0.32 * s, 1.0⟩

/-- Sample `z = f(x, y, t)` into a smooth CCW `MeshAsset` with analytical tangent-bivector
normals (`⋆(T_x ∧ T_y)`) and vertex colors computed purely in Lean. -/
def evalSurfaceMesh (expr : String) (t : Float)
    (minX maxX minY maxY : Float) (gridN : Nat := 44) (meshId : UInt64 := 9001) :
    Except String MeshAsset := do
  let ast ← parseExprString expr
  let n := max 6 (min 96 gridN)
  let stride := n + 1
  let vCount := stride * stride
  let dx := (maxX - minX) / n.toFloat
  let dy := (maxY - minY) / n.toFloat
  let mut pos := FloatArray.emptyWithCapacity (vCount * 3)
  let mut nrm := FloatArray.emptyWithCapacity (vCount * 3)
  let mut zMin := 1e9
  let mut zMax := -1e9
  for iy in [:stride] do
    let y := minY + iy.toFloat * dy
    for ix in [:stride] do
      let x := minX + ix.toFloat * dx
      let j := evalJet2 ast x y t
      let z := if j.v.isFinite && !j.v.isNaN then max (-6.0) (min 6.0 j.v) else 0.0
      if z < zMin then zMin := z
      if z > zMax then zMax := z
      -- Map math (x, y, z_up) → right-handed 3D scene (x, z_up, -y) so +Y is up!
      -- Tangent vectors T_x = (1, j.dx, 0), T_y = (0, j.dy, -1)
      -- Exterior normal ⋆(T_x ∧ T_y) = (-j.dx, 1, j.dy) normalized
      let nn := Vec3.normalize ⟨-j.dx, 1.0, j.dy⟩
      pos := pos.push x |>.push z |>.push (-y)
      nrm := nrm.push nn.x |>.push nn.y |>.push nn.z
  let span := max 1e-4 (zMax - zMin)
  let mut cols := FloatArray.emptyWithCapacity (vCount * 4)
  for k in [:vCount] do
    let z := pos.get! (k * 3 + 1)
    let c := heightColor ((z - zMin) / span)
    cols := cols.push c.r |>.push c.g |>.push c.b |>.push c.a
  let mut idxs : Array UInt32 := Array.mkEmpty (n * n * 6)
  for iy in [:n] do
    for ix in [:n] do
      let i00 := (iy * stride + ix).toUInt32
      let i10 := i00 + 1
      let i01 := ((iy + 1) * stride + ix).toUInt32
      let i11 := i01 + 1
      -- CCW front-face winding in right-handed (x, y_up, -y_math) space
      idxs := idxs.push i00 |>.push i10 |>.push i11
      idxs := idxs.push i00 |>.push i11 |>.push i01
  let dirtyHash := computeMeshHash meshId pos idxs
  return { meshId, dirtyHash, positions := pos, normals := nrm, colors := cols, indices := idxs }

/-- Parse and solve an array of implicit 2D equations `["x^2+y^2-1", "y-x"]` purely in Lean. -/
def evalEquationsToOverlay (equations : Array String)
    (minX maxX minY maxY : Float) (gridN : Nat := 48) : Except String ContourOverlay := do
  let mut fns : Array (Float → Float → Float) := Array.mkEmpty equations.size
  for eqStr in equations do
    let ast ← parseExprString eqStr
    fns := fns.push fun x y => (evalJet2 ast x y 0.0).v
  return Contour.solveEquationSystem fns minX maxX minY maxY gridN

end Grassmann.Eval
