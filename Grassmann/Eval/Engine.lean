import Grassmann.CABI.Alg
import Grassmann.Scene.Types
import Grassmann.Eval.Parser
import Grassmann.Eval.Contour
import Grassmann.Eval.Implicit3D
import Grassmann.Eval.ImplicitExpr
import Grassmann.CoffeeShop.Mesh
import Grassmann.Codegen.GPUInit

/-!
# Pure-Lean LiveScript v2 GA Script Evaluator & 3D Surface Engine (`Grassmann.Eval.Engine`)

Strictly `Init`-only (ZERO `Lean.*`, `Lake.*`, or `Std.*` imports) so the entire
unified `Grassmann.Studio` compiles into a tiny standalone Apple dylib/static lib
AND Emscripten WASM binary!

Capabilities:
- **Full Multi-Statement CoffeeShop `LiveScript` v2**:
  - `@basis PGA3 | CGA3 | PGA2 | CGA2 | STA | R3 | Complex | Dual | Quaternion | Cl(p,q,r)`
    and `Algebra(p, q, r)` headers
  - Variables (`let x = ...` / `x = ...`), user helper functions (`fn f(x) = ...` & `(x) => ...`),
    bounded loops (`for i in 0..N { ... }`, max 512 iters), list comprehensions
    (`[f(i) for i in 0..N]`), conditionals (`if/else`, `cond ? a : b`), recursion guard (depth 32)
  - Full GA operators over ANY `AlgSpace`: `*`, `^`/`∧`, `&`/`∨`, `<<`/`⨼`, `|`, `~`, `conj`,
    `!`, `⋆`, `>>>`, `⊘`, `exp`, `log`, `norm`, `normalized`, `grade(x, k)`, `inv`
  - Rich geometry constructors: `point`, `draggable`, `handle`, `plane`, `line`, `motor`,
    `translator`, `rotor`, `boost`, `sphere`, `circle`, `seg`, `poly`, `curve`, `closedCurve`,
    `mesh`, `transform`, `slice`, `implicit`, `surface`, `opns`, `color`, `rgb`, `graph([...])`
  - **Reactive Draggable Script Handles** (`point`/`draggable`/`handle`) + **Live `EditCoeff`**
    overrides on named script multivectors so dragging handles or Inspect Stash sliders
    re-executes derived geometry at 60 FPS!
  - Full PGA2, PGA3, CGA2, CGA3 (both OPNS `A^B`/`A^B^C`/`A^B^C^D` AND IPNS `S1^S2`/`S1^S2^S3`!),
    STA `-+++`, R3, Complex, Dual, and Quaternion auto-classification into `SceneFrame` (`GSIR` v1).
- **Forward-Mode AD 3D Surface Mesher** (`evalSurfaceMesh`) and **2D Contour Solver**
  (`evalEquationsToOverlay`).

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) and Steven De Keninck
(`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval

open Grassmann.CABI.Alg Grassmann.Scene Grassmann.CoffeeShop.Mesh
open Grassmann.Eval.Implicit3D Grassmann.Eval.ImplicitExpr Grassmann.Codegen.GPUInit

private def piF : Float := 3.14159265358979323846
private def twoPiF : Float := 6.28318530717958647692

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
    let core :=
      if s.startsWith "CL(" && s.endsWith ")" then
        ((s.drop 3).dropEnd 1).toString
      else s
    let parts := (core.splitOn ",").map (fun x => x.trimAscii.toString.toNat?)
    if parts.length ≥ 2 && parts.all Option.isSome then
      let p := (parts.getD 0 none).getD 3
      let q := (parts.getD 1 none).getD 0
      let r := (parts.getD 2 none).getD 0
      if p == 4 && q == 1 && r == 0 then ("CGA3", AlgSpace.CGA3, 4, 1, 0, true)
      else if p == 3 && q == 0 && r == 1 then ("PGA3", AlgSpace.PGA3, 3, 0, 1, false)
      else if p == 2 && q == 0 && r == 1 then ("PGA2", AlgSpace.PGA2, 2, 0, 1, false)
      else if p == 3 && q == 1 && r == 0 then ("STA", AlgSpace.STA, 3, 1, 0, false)
      else
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

/-- Parse blade subscript (e.g. `"0"`, `"12"`, `"013"`, `"∞"`, `"∅"`) into bitmask for `V`. -/
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

/-- Construct a PGA2/PGA3/CGA/STA/Euclidean point multivector from `(x, y, z)` in space `V`. -/
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

/-- Extract a 3D `Vec3` position from a point multivector in `V` (if point-like). -/
def extractPointVec3 {V : AlgSpace} (zeroIndexed : Bool) (x : MV V) : Option Vec3 :=
  if zeroIndexed && V.n == 4 then
    let w := x.coeff 14
    if Float.abs w > 1e-6 then some ⟨-x.coeff 13 / w, x.coeff 11 / w, -x.coeff 7 / w⟩ else none
  else if zeroIndexed && V.n == 3 then
    let w := x.coeff 6
    if Float.abs w > 1e-6 then some ⟨-x.coeff 3 / w, x.coeff 5 / w, 0.0⟩ else none
  else if V.hasconformal && V.n == 5 then
    let w := x.coeff 2
    if Float.abs w > 1e-6 then some ⟨x.coeff 4 / w, x.coeff 8 / w, x.coeff 16 / w⟩ else none
  else if V.hasconformal && V.n == 4 then
    let w := x.coeff 2
    if Float.abs w > 1e-6 then some ⟨x.coeff 4 / w, x.coeff 8 / w, 0.0⟩ else none
  else if V.n == 4 && V == AlgSpace.STA then
    some ⟨x.coeff 2, x.coeff 4, x.coeff 8⟩
  else
    let px := if V.n ≥ 1 then x.coeff 1 else x.coeff 0
    let py := if V.n ≥ 2 then x.coeff 2 else 0.0
    let pz := if V.n ≥ 3 then x.coeff 4 else 0.0
    some ⟨px, py, pz⟩

/-- Extract a PGA3 `Motor3` from an even multivector `M ∈ PGA3`. -/
def extractMotor3 {V : AlgSpace} (x : MV V) : Motor3 :=
  if V.n == 4 then
    Motor3.normalize
      { s := x.coeff 0, e01 := x.coeff 3, e02 := x.coeff 5, e03 := x.coeff 9,
        e12 := x.coeff 6, e13 := x.coeff 10, e23 := x.coeff 12, e0123 := x.coeff 15 }
  else Motor3.identity

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
    | "pi" | "π" => Jet2.const piF
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

/-! ## Backwards-Compatible Pure-MV Environment (`EvalEnv`, `evalGA`) -/

/-- Evaluation environment for dynamic GA expressions (used by `Calc.lean` & direct callers). -/
structure EvalEnv (V : AlgSpace) where
  zeroIndexed : Bool := false
  timeSec     : Float := 0.0
  handles     : Array (UInt32 × Vec3) := #[]
  vars        : Array (String × MV V) := #[]
  order       : Array String := #[]

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

/-! ## LiveScript v2 Rich Value Runtime (`ScriptVal`, `ScriptEnv`, `evalScriptVal`) -/

/-- Rich runtime value for LiveScript v2 CoffeeShop scripts. -/
inductive ScriptVal (V : AlgSpace) where
  | mv      (x : MV V) (isDraggable : Bool := false) (handleId : Option UInt32 := none) (isDualRound : Bool := false)
  | color   (rgba : RGBA) (hex : UInt32 := 0x44AAFF)
  | str     (s : String)
  | list    (items : Array (ScriptVal V))
  | seg     (a b : Vec3)
  | poly    (verts : Array Vec3)
  | curve   (pts : Array Vec3) (closed : Bool := false)
  | mesh    (asset : MeshAsset) (motor : Motor3 := Motor3.identity)
  | sliced  (res : SliceResult) (center u v : Vec3)
  | opns    (shader : OpnsShaderSource) (uniform : OpnsUniformPrim)
  | circle3 (c : CirclePrim)
  | sphere3 (s : SpherePrim)
  | pair3   (p : PointPairPrim)
  | disk3   (d : BivectorDiskPrim)
  | fnVal   (params : Array String) (body : Expr)
  deriving Inhabited

/-- Execution state for LiveScript v2 (handles, functions, `graph(...)`, loop/recursion guards). -/
structure ScriptEnv (V : AlgSpace) where
  zeroIndexed    : Bool := false
  algName        : String := "PGA3"
  p              : Nat := 3
  q              : Nat := 0
  r              : Nat := 1
  conformalWitt  : Bool := false
  timeSec        : Float := 0.0
  handles        : Array (UInt32 × Vec3) := #[]
  coeffOverrides : Array (UInt32 × UInt32 × Float) := #[]
  paramOverrides : Array (String × Float) := #[]
  emittedParams  : Array ParamSpec := #[]
  vars           : Array (String × ScriptVal V) := #[]
  order          : Array String := #[]
  varColors      : Array (String × Option RGBA) := #[]
  graphItems     : Array (ScriptVal V) := #[]
  hasGraph       : Bool := false
  activeColor    : Option RGBA := none
  nextHandleId   : UInt32 := 0
  nextMeshId     : UInt64 := 7100
  consumedMeshIds : Array UInt64 := #[]
  topBindIdx     : UInt32 := 0
  loopDepth      : Nat := 0
  callDepth      : Nat := 0

private def maxLoopIters : Nat := 512
private def maxCallDepth : Nat := 32

namespace ScriptEnv

def lookup? {V : AlgSpace} (env : ScriptEnv V) (name : String) : Option (ScriptVal V) :=
  (env.vars.find? fun kv => kv.1 == name).map (·.2)

def bindLocal {V : AlgSpace} (env : ScriptEnv V) (name : String) (v : ScriptVal V) : ScriptEnv V :=
  match env.vars.findIdx? fun kv => kv.1 == name with
  | some idx => { env with vars := env.vars.set! idx (name, v) }
  | none     => { env with vars := env.vars.push (name, v) }

/-- Apply any `EditCoeff` overrides for `entryIdx` onto a multivector value. -/
def applyCoeffOverrides {V : AlgSpace} (env : ScriptEnv V) (entryIdx : UInt32) (v : ScriptVal V) :
    ScriptVal V :=
  match v with
  | .mv x drag hid isDual =>
    let matching := env.coeffOverrides.filter (fun o => o.1 == entryIdx)
    if matching.isEmpty then v
    else Id.run do
      let mut arr := mvToDenseArray x
      for (_, bladeIdx, newVal) in matching do
        let bi := bladeIdx.toNat
        if bi < arr.size then arr := arr.set! bi newVal
      return .mv (denseArrayToMV arr) drag hid isDual
  | other => other

def bindTop {V : AlgSpace} (env : ScriptEnv V) (name : String) (v : ScriptVal V) : ScriptEnv V :=
  match env.vars.findIdx? fun kv => kv.1 == name with
  | some idx =>
    let v' := env.applyCoeffOverrides idx.toUInt32 v
    { env with vars := env.vars.set! idx (name, v') }
  | none =>
    let eIdx := env.topBindIdx
    let v' := env.applyCoeffOverrides eIdx v
    { env with
      vars := env.vars.push (name, v'),
      order := env.order.push name,
      varColors := env.varColors.push (name, env.activeColor),
      topBindIdx := eIdx + 1 }

def handlePos {V : AlgSpace} (env : ScriptEnv V) (hid : UInt32) (defPos : Vec3) : Vec3 :=
  ((env.handles.find? fun kv => kv.1 == hid).map (·.2)).getD defPos

/-- Register or update an interactive `@param` / `slider(...)` specification and return its live value. -/
def registerParam {V : AlgSpace} (env : ScriptEnv V) (name label : String)
    (defVal minV maxV stepV : Float) : Float × ScriptEnv V :=
  let lo := min minV maxV
  let hi := max minV maxV
  let rawVal := ((env.paramOverrides.find? fun kv => kv.1 == name).map (·.2)).getD defVal
  let curVal := max lo (min hi rawVal)
  let stp := if stepV > 0.0 then stepV else max 0.001 ((hi - lo) / 100.0)
  let spec : ParamSpec := {
    name,
    label := if label.isEmpty then name else label,
    value := curVal,
    min := lo,
    max := hi,
    step := stp
  }
  let nextParams :=
    match env.emittedParams.findIdx? fun p => p.name == name with
    | some idx => env.emittedParams.set! idx spec
    | none     => env.emittedParams.push spec
  (curVal, { env with emittedParams := nextParams })

end ScriptEnv

private def valAsMV {V : AlgSpace} : ScriptVal V → Except String (MV V × Bool)
  | .mv x _ _ isDual => .ok (x, isDual)
  | .color _ hex     => .ok (MV.single 0 hex.toNat.toFloat, false)
  | .str s           => .error s!"expected multivector or number, got string \"{s}\""
  | .fnVal ..        => .error "expected multivector or number, got function"
  | _                => .error "expected multivector or number"

private def valAsFloat {V : AlgSpace} (v : ScriptVal V) : Except String Float := do
  let (m, _) ← valAsMV v
  return m.coeff 0

private def valAsVec3 {V : AlgSpace} (zeroIdx : Bool) (v : ScriptVal V) : Except String Vec3 :=
  match v with
  | .mv x .. =>
    match extractPointVec3 zeroIdx x with
    | some p => .ok p
    | none => .error "expected point multivector for 3D position"
  | .list xs =>
    if xs.size ≥ 2 then do
      let x ← valAsFloat xs[0]!
      let y ← valAsFloat xs[1]!
      let z ← if xs.size ≥ 3 then valAsFloat xs[2]! else pure 0.0
      return ⟨x, y, z⟩
    else .error "coordinate list must have at least 2 elements"
  | _ => .error "expected point multivector or [x, y, z] list"

private def hexToRGBA (hex : UInt32) : RGBA :=
  RGBA.ofHex (if hex > 0xFFFFFF then hex >>> 8 else hex)
    (if hex > 0xFFFFFF then (hex &&& 0xFF).toNat.toFloat / 255.0 else 1.0)

/-- Build an icosahedron CCW `MeshAsset` for `mesh("icosahedron")`. -/
private def buildIcoScriptMesh (r : Float) (meshId : UInt64) : MeshAsset := Id.run do
  let phi := (1.0 + Float.sqrt 5.0) * 0.5
  let s := r / Float.sqrt (1.0 + phi * phi)
  let raw : Array Vec3 := #[
    ⟨-s, phi*s, 0⟩, ⟨s, phi*s, 0⟩, ⟨-s, -phi*s, 0⟩, ⟨s, -phi*s, 0⟩,
    ⟨0, -s, phi*s⟩, ⟨0, s, phi*s⟩, ⟨0, -s, -phi*s⟩, ⟨0, s, -phi*s⟩,
    ⟨phi*s, 0, -s⟩, ⟨phi*s, 0, s⟩, ⟨-phi*s, 0, -s⟩, ⟨-phi*s, 0, s⟩
  ]
  let faces : Array (Nat × Nat × Nat) := #[
    (0,11,5),(0,5,1),(0,1,7),(0,7,10),(0,10,11),
    (1,5,9),(5,11,4),(11,10,2),(10,7,6),(7,1,8),
    (3,9,4),(3,4,2),(3,2,6),(3,6,8),(3,8,9),
    (4,9,5),(2,4,11),(6,2,10),(8,6,7),(9,8,1)
  ]
  let mut mb : MeshBuilder := {}
  for (a, b, c) in faces do
    let (m1, i0) := mb.addVertex raw[a]! RGBA.cyan
    let (m2, i1) := m1.addVertex raw[b]! RGBA.cyan
    let (m3, i2) := m2.addVertex raw[c]! RGBA.cyan
    mb := m3.addTri i0 i1 i2
  return mb.finalize meshId

/-- Construct a named built-in procedural CCW `MeshAsset` for `mesh("bunny" | ...)`. -/
private def buildNamedScriptMesh (kind : String) (meshId : UInt64) : Except String MeshAsset :=
  match kind.toLower with
  | "bunny" | "bunny_hq" => .ok (buildBunnyMesh meshId)
  | "torus"              => .ok (buildTorusMesh 0.72 0.24 28 16 RGBA.cyan meshId)
  | "cube" | "box"       => .ok (buildBoxMesh 1.0 1.0 1.0 RGBA.violet meshId)
  | "cone"               => .ok (buildConeMesh 0.60 1.25 24 RGBA.amber meshId)
  | "cylinder" | "cyl"   => .ok (buildCylinderMesh 0.45 1.15 24 RGBA.green meshId)
  | "sphere"             =>
    .ok ((MeshBuilder.addEllipsoid {} Vec3.zero ⟨0.75, 0.75, 0.75⟩ 0.0 14 22 RGBA.coral).finalize meshId)
  | "icosahedron" | "ico" => .ok (buildIcoScriptMesh 0.85 meshId)
  | other => .error s!"unknown mesh '{other}' (expected bunny, torus, cube, box, cone, cylinder, sphere, icosahedron)"

/-- Construct a PGA3 screw motor `exp(-angle/2 * L - shift/2 * e0 * L)` from axis `(ax, ay, az)`, `angle`, `shift`. -/
private def makeScrewMotorMV {V : AlgSpace} (zeroIdx : Bool) (ax ay az angle shift : Float) : MV V :=
  let u := Vec3.normalize ⟨ax, ay, az⟩
  if zeroIdx && V.n == 4 then
    let c := Float.cos (0.5 * angle); let s := Float.sin (0.5 * angle)
    let d := -0.5 * shift
    -- Rotor R = cos(θ/2) - sin(θ/2)(uz e12 - uy e13 + ux e23); Translator T = 1 + d (ux e01 + uy e02 + uz e03)
    let rMV := MV.add (MV.single 0 c)
      (MV.add (MV.single 6 (-s * u.z)) (MV.add (MV.single 10 (s * u.y)) (MV.single 12 (-s * u.x))))
    let tMV := MV.add MV.one
      (MV.add (MV.single 3 (d * u.x)) (MV.add (MV.single 5 (d * u.y)) (MV.single 9 (d * u.z))))
    MV.mul tMV rMV
  else if V.n == 3 && !zeroIdx then
    let c := Float.cos (0.5 * angle); let s := Float.sin (0.5 * angle)
    MV.add (MV.single 0 c)
      (MV.add (MV.single 3 (-s * u.z)) (MV.add (MV.single 5 (s * u.y)) (MV.single 6 (-s * u.x))))
  else MV.one

/-- Construct a CGA3 dual sphere `no + c + 0.5*(c² - r²) ni` in Witt CGA3 (`S"∞∅+++"`). -/
private def makeDualSphereMV {V : AlgSpace} (cx cy cz r : Float) : MV V :=
  let c2 := cx * cx + cy * cy + cz * cz
  let p := MV.single 1 (0.5 * (c2 - r * r))
  let p := MV.add p (MV.single 2 1.0)
  let p := MV.add p (MV.single 4 cx)
  let p := MV.add p (MV.single 8 cy)
  MV.add p (MV.single 16 cz)

/-- Extract a 3D plane `(unitNormal, d)` with `n·p + d = 0` from a PGA3 plane or point multivector. -/
private def extractPlaneND {V : AlgSpace} (zeroIdx : Bool) (x : MV V) : Option (Vec3 × Float) :=
  if zeroIdx && V.n == 4 then
    let n : Vec3 := ⟨x.coeff 2, x.coeff 4, x.coeff 8⟩
    let nLen := Vec3.norm n
    if nLen > 1e-6 then
      some (Vec3.scale (1.0 / nLen) n, x.coeff 1 / nLen)
    else
      -- Allow passing a PGA3 point handle directly: horizontal plane through that point!
      match extractPointVec3 true x with
      | some p => some (⟨0.0, 1.0, 0.0⟩, -p.y)
      | none => none
  else
    let n : Vec3 := ⟨x.coeff 1, if V.n ≥ 2 then x.coeff 2 else 0.0, if V.n ≥ 3 then x.coeff 4 else 0.0⟩
    let nLen := Vec3.norm n
    if nLen > 1e-6 then some (Vec3.scale (1.0 / nLen) n, 0.0) else none

/-- Core LiveScript v2 evaluator producing rich `ScriptVal V`s with bounded loops & recursion safety. -/
partial def evalScriptVal {V : AlgSpace} (env : ScriptEnv V) (e : Expr) :
    Except String (ScriptVal V × ScriptEnv V) := do
  match e with
  | .setAlgebra _ => return (.mv MV.zero, env)
  | .num v        => return (.mv (if v == 0.0 then MV.zero else MV.single 0 v), env)
  | .color hex    =>
    let rgba := hexToRGBA hex
    return (.color rgba hex, { env with activeColor := some rgba })
  | .str s        => return (.str s, env)
  | .blade pfx sub =>
    -- If user explicitly shadowed e.g. `let v1 = ...`, honor local variable binding first!
    match env.lookup? s!"{pfx}{sub}" with
    | some v => return (v, env)
    | none =>
      match bladeSubToBits V env.zeroIndexed sub with
      | some bits =>
        let b : MV V := if bits == 0 then MV.one else MV.blade bits
        if pfx == 'E' then return (.mv (MV.complementright b), env)
        else return (.mv b, env)
      | none => throw s!"invalid blade literal '{pfx}{sub}' in {V}"
  | .ident name =>
    match env.lookup? name with
    | some v => return (v, env)
    | none =>
      match name with
      | "pi" | "π"   => return (.mv (MV.single 0 piF), env)
      | "tau"        => return (.mv (MV.single 0 twoPiF), env)
      | "e" | "ℯ"    => return (.mv (MV.single 0 2.71828182845904523536), env)
      | "phi"        => return (.mv (MV.single 0 1.61803398874989484820), env)
      | "t" | "time" => return (.mv (MV.single 0 env.timeSec), env)
      | "I" | "pss"  => return (.mv (MV.blade (lowMask V.n)), env)
      | "no" | "ori" | "∅" =>
        if V.hasOrigin then return (.mv (MV.blade (if V.hasInf then 2 else 1)), env)
        else if V.n == 5 then return (.mv (MV.add (MV.single 16 0.5) (MV.single 8 (-0.5))), env)
        else throw "no/ori requires conformal space (e.g. @basis CGA3)"
      | "ni" | "inf" | "∞" =>
        if V.hasInf then return (.mv (MV.blade 1), env)
        else if V.n == 5 then return (.mv (MV.add (MV.single 8 1.0) (MV.single 16 1.0)), env)
        else throw "ni/inf requires conformal space (e.g. @basis CGA3)"
      | "et" => return (.mv (MV.blade 1), env)
      | "ex" => return (.mv (MV.blade (if V == AlgSpace.STA then 2 else 1)), env)
      | "ey" => return (.mv (MV.blade (if V == AlgSpace.STA then 4 else 2)), env)
      | "ez" => return (.mv (MV.blade (if V == AlgSpace.STA then 8 else 4)), env)
      | _ => throw s!"unbound identifier '{name}'"
  | .unary op a =>
    let (va, env1) ← evalScriptVal env a
    let (ma, dualA) ← valAsMV va
    match op with
    | "-" => return (.mv (MV.neg ma) false none dualA, env1)
    | "~" => return (.mv (MV.reverse ma) false none dualA, env1)
    | "!" => return (.mv (MV.complementright ma) false none (!dualA), env1)
    | "⋆" => return (.mv (MV.hodge ma) false none (!dualA), env1)
    | _   => throw s!"unknown unary operator '{op}'"
  | .binary op a b =>
    let (va, env1) ← evalScriptVal env a
    let (vb, env2) ← evalScriptVal env1 b
    -- Support `M >>> meshVal` rigid motor transform on meshes directly!
    if op == ">>>" then
      match va, vb with
      | .mv m .., .mesh asset m0 =>
        let mNew := Motor3.mul (extractMotor3 m) m0
        return (.mesh asset mNew, env2)
      | _, _ =>
        let (ma, _) ← valAsMV va
        let (mb, dualB) ← valAsMV vb
        return (.mv (ganjaSandwich ma mb) false none dualB, env2)
    else
      let (ma, dualA) ← valAsMV va
      let (mb, dualB) ← valAsMV vb
      match op with
      | "+" => return (.mv (MV.add ma mb) false none (dualA && dualB), env2)
      | "-" => return (.mv (MV.sub ma mb) false none (dualA && dualB), env2)
      | "*" | "·" => return (.mv (MV.mul ma mb), env2)
      | "/" =>
        let sc := mb.coeff 0
        if dominantGrade mb == 0 && Float.abs sc > 1e-15 then
          return (.mv (MV.mulScalar ma (1.0 / sc)) false none dualA, env2)
        else
          return (.mv (MV.mul ma (MV.inv mb)), env2)
      | "∧" => return (.mv (MV.wedge ma mb) false none (dualA && dualB), env2)
      | "^" =>
        if dominantGrade ma == 0 && dominantGrade mb == 0 then
          return (.mv (MV.single 0 (Float.pow (ma.coeff 0) (mb.coeff 0))), env2)
        else
          return (.mv (MV.wedge ma mb) false none (dualA && dualB), env2)
      | "&" | "∨" => return (.mv (ganjaVee ma mb), env2)
      | "<<" | "⨼" => return (.mv (dorstLDot ma mb), env2)
      | "⋅" | "⨽" => return (.mv (MV.contraction ma mb), env2)
      | "|" => return (.mv (symDot ma mb), env2)
      | "⊘" => return (.mv (ganjaSandwich (MV.reverse mb) ma) false none dualA, env2)
      | "**" =>
        let expS := mb.coeff 0
        if Float.abs (expS + 1.0) < 1e-9 then
          return (.mv (MV.inv ma), env2)
        else if dominantGrade ma == 0 && dominantGrade mb == 0 then
          return (.mv (MV.single 0 (Float.pow (ma.coeff 0) expS)), env2)
        else if Float.abs (ma.coeff 0 - 2.71828182845904523536) < 1e-6 && dominantGrade ma == 0 then
          return (.mv (MV.exp mb), env2)
        else
          let n := min 32 expS.toUInt32.toNat
          let rec powRec (k : Nat) (acc : MV V) : MV V :=
            match k with | 0 => acc | m + 1 => powRec m (MV.mul acc ma)
          return (.mv (powRec n MV.one), env2)
      | "==" => return (.mv (MV.single 0 (if Float.abs (ma.coeff 0 - mb.coeff 0) < 1e-9 then 1.0 else 0.0)), env2)
      | "!=" => return (.mv (MV.single 0 (if Float.abs (ma.coeff 0 - mb.coeff 0) ≥ 1e-9 then 1.0 else 0.0)), env2)
      | "<"  => return (.mv (MV.single 0 (if ma.coeff 0 < mb.coeff 0 then 1.0 else 0.0)), env2)
      | ">"  => return (.mv (MV.single 0 (if ma.coeff 0 > mb.coeff 0 then 1.0 else 0.0)), env2)
      | "<=" => return (.mv (MV.single 0 (if ma.coeff 0 ≤ mb.coeff 0 then 1.0 else 0.0)), env2)
      | ">=" => return (.mv (MV.single 0 (if ma.coeff 0 ≥ mb.coeff 0 then 1.0 else 0.0)), env2)
      | "&&" => return (.mv (MV.single 0 (if ma.coeff 0 != 0.0 && mb.coeff 0 != 0.0 then 1.0 else 0.0)), env2)
      | "||" => return (.mv (MV.single 0 (if ma.coeff 0 != 0.0 || mb.coeff 0 != 0.0 then 1.0 else 0.0)), env2)
      | _ => throw s!"unsupported binary operator '{op}'"
  | .field obj fname =>
    let (vo, env1) ← evalScriptVal env obj
    match vo with
    | .list xs =>
      if fname.toLower == "length" || fname.toLower == "size" then
        return (.mv (MV.single 0 xs.size.toFloat), env1)
      else throw s!"unknown list field '.{fname}'"
    | _ =>
      let (mo, dualO) ← valAsMV vo
      match fname.toLower with
      | "normalized" | "unit" => return (.mv (ganjaNormalize mo) false none dualO, env1)
      | "reverse" | "rev"     => return (.mv (MV.reverse mo) false none dualO, env1)
      | "conjugate" | "conj"  => return (.mv (MV.clifford mo) false none dualO, env1)
      | "involute"            => return (.mv (MV.involute mo) false none dualO, env1)
      | "dual"                => return (.mv (MV.complementright mo) false none (!dualO), env1)
      | "undual"              => return (.mv (MV.complementleft mo) false none (!dualO), env1)
      | "length" | "norm"     => return (.mv (MV.single 0 (ganjaNorm mo)), env1)
      | "s" | "scalar"        => return (.mv (MV.single 0 (mo.coeff 0)), env1)
      | "inverse" | "inv"     => return (.mv (MV.inv mo), env1)
      | "x" => return (.mv (MV.single 0 (((extractPointVec3 env1.zeroIndexed mo).map (·.x)).getD 0.0)), env1)
      | "y" => return (.mv (MV.single 0 (((extractPointVec3 env1.zeroIndexed mo).map (·.y)).getD 0.0)), env1)
      | "z" => return (.mv (MV.single 0 (((extractPointVec3 env1.zeroIndexed mo).map (·.z)).getD 0.0)), env1)
      | _ => throw s!"unknown field '.{fname}'"
  | .method obj mname args =>
    let (vo, env1) ← evalScriptVal env obj
    let (mo, dualO) ← valAsMV vo
    match mname.toLower with
    | "grade" =>
      if h : 0 < args.size then
        let (vg, env2) ← evalScriptVal env1 args[0]
        let g ← valAsFloat vg
        return (.mv (MV.gradeProj (max 0.0 g).toUInt32.toNat mo) false none dualO, env2)
      else throw "Grade(k) expects 1 argument"
    | "exp" => return (.mv (MV.exp mo), env1)
    | "log" => return (.mv (MV.log mo), env1)
    | _ => throw s!"unknown method '.{mname}()'"
  | .index obj idxExpr =>
    let (vo, env1) ← evalScriptVal env obj
    let (vi, env2) ← evalScriptVal env1 idxExpr
    let idxF ← valAsFloat vi
    let idx := (max 0.0 idxF).toUInt32.toNat
    match vo with
    | .list xs =>
      if h : idx < xs.size then return (xs[idx], env2)
      else throw s!"list index {idx} out of bounds (length {xs.size})"
    | _ => throw "indexing '[i]' requires a list value"
  | .fnDef name params body =>
    let fnV : ScriptVal V := .fnVal params body
    let env1 := if env.loopDepth == 0 && env.callDepth == 0 then env.bindTop name fnV else env.bindLocal name fnV
    return (fnV, env1)
  | .lambda params body =>
    return (.fnVal params body, env)
  | .ifExpr cond tB fB =>
    let (vc, env1) ← evalScriptVal env cond
    let cf ← valAsFloat vc
    if cf != 0.0 then evalScriptVal env1 tB else evalScriptVal env1 fB
  | .forLoop varName loE hiE body =>
    let (vLo, env1) ← evalScriptVal env loE
    let (vHi, env2) ← evalScriptVal env1 hiE
    let loI := (max 0.0 (← valAsFloat vLo)).toUInt32.toNat
    let hiI := (max 0.0 (← valAsFloat vHi)).toUInt32.toNat
    let count := if hiI ≥ loI then hiI - loI else 0
    if count > maxLoopIters then
      throw s!"loop iteration count {count} exceeds safety limit ({maxLoopIters})"
    let mut envCur : ScriptEnv V := { env2 with loopDepth := env2.loopDepth + 1 }
    let mut last : ScriptVal V := .mv MV.zero
    for k in [:count] do
      let idxVal := Float.ofNat (loI + k)
      envCur := envCur.bindLocal varName (.mv (MV.single 0 idxVal))
      for s in body do
        let (v, envNext) ← evalScriptVal envCur s
        last := v
        envCur := envNext
    return (last, { envCur with loopDepth := env2.loopDepth })
  | .listComp elemE varName loE hiE =>
    let (vLo, env1) ← evalScriptVal env loE
    let (vHi, env2) ← evalScriptVal env1 hiE
    let loI := (max 0.0 (← valAsFloat vLo)).toUInt32.toNat
    let hiI := (max 0.0 (← valAsFloat vHi)).toUInt32.toNat
    let count := if hiI ≥ loI then hiI - loI else 0
    if count > maxLoopIters then
      throw s!"list comprehension length {count} exceeds safety limit ({maxLoopIters})"
    let mut envCur : ScriptEnv V := { env2 with loopDepth := env2.loopDepth + 1 }
    let mut items : Array (ScriptVal V) := Array.mkEmpty count
    for k in [:count] do
      let idxVal := Float.ofNat (loI + k)
      envCur := envCur.bindLocal varName (.mv (MV.single 0 idxVal))
      let (v, envNext) ← evalScriptVal envCur elemE
      items := items.push v
      envCur := envNext
    return (.list items, { envCur with loopDepth := env2.loopDepth })
  | .list elems =>
    let mut envCur := env
    let mut out : Array (ScriptVal V) := Array.mkEmpty elems.size
    for el in elems do
      let (v, envNext) ← evalScriptVal envCur el
      out := out.push v
      envCur := envNext
    return (.list out, envCur)
  | .call fname args =>
    -- Evaluate arguments first
    let mut envCur := env
    let mut vals : Array (ScriptVal V) := Array.mkEmpty args.size
    for a in args do
      let (v, envNext) ← evalScriptVal envCur a
      vals := vals.push v
      envCur := envNext
    -- 1. Check user-defined function in scope first!
    match envCur.lookup? fname with
    | some (.fnVal params body) =>
      if envCur.callDepth ≥ maxCallDepth then
        throw s!"recursion depth limit ({maxCallDepth}) exceeded calling '{fname}'"
      let mut fnEnv : ScriptEnv V := { envCur with callDepth := envCur.callDepth + 1 }
      for i in [:params.size] do
        let argVal := vals.getD i (.mv MV.zero)
        fnEnv := fnEnv.bindLocal params[i]! argVal
      let (res, _) ← evalScriptVal fnEnv body
      return (res, envCur)
    | _ =>
      let f0 (i : Nat) (d : Float := 0.0) : Float :=
        match vals[i]? with
        | some v => (valAsFloat v).toOption.getD d
        | none => d
      let mv0 (i : Nat) : Except String (MV V × Bool) :=
        match vals[i]? with
        | some v => valAsMV v
        | none => .error s!"'{fname}' missing argument {i + 1}"
      match fname.toLower with
      -- Scalar math functions
      | "sin"   => return (.mv (MV.single 0 (Float.sin (f0 0))), envCur)
      | "cos"   => return (.mv (MV.single 0 (Float.cos (f0 0))), envCur)
      | "tan"   => return (.mv (MV.single 0 (Float.tan (f0 0))), envCur)
      | "asin"  => return (.mv (MV.single 0 (Float.asin (max (-1.0) (min 1.0 (f0 0))))), envCur)
      | "acos"  => return (.mv (MV.single 0 (Float.acos (max (-1.0) (min 1.0 (f0 0))))), envCur)
      | "atan"  => return (.mv (MV.single 0 (Float.atan (f0 0))), envCur)
      | "atan2" => return (.mv (MV.single 0 (Float.atan2 (f0 0) (f0 1))), envCur)
      | "sinh"  => return (.mv (MV.single 0 (Float.sinh (f0 0))), envCur)
      | "cosh"  => return (.mv (MV.single 0 (Float.cosh (f0 0))), envCur)
      | "tanh"  => return (.mv (MV.single 0 (Float.tanh (f0 0))), envCur)
      | "sqrt"  => return (.mv (MV.single 0 (Float.sqrt (max 0.0 (f0 0)))), envCur)
      | "abs"   => return (.mv (MV.single 0 (Float.abs (f0 0))), envCur)
      | "floor" => return (.mv (MV.single 0 (Float.floor (f0 0))), envCur)
      | "ceil"  => return (.mv (MV.single 0 (Float.ceil (f0 0))), envCur)
      | "min"   => return (.mv (MV.single 0 (min (f0 0) (f0 1))), envCur)
      | "max"   => return (.mv (MV.single 0 (max (f0 0) (f0 1))), envCur)
      | "clamp" => return (.mv (MV.single 0 (max (f0 1) (min (f0 2) (f0 0)))), envCur)
      | "pow"   => return (.mv (MV.single 0 (Float.pow (f0 0) (f0 1))), envCur)
      | "lerp" | "mix" =>
        let (ma, _) ← mv0 0; let (mb, _) ← mv0 1; let u := f0 2 0.5
        return (.mv (MV.add (MV.mulScalar ma (1.0 - u)) (MV.mulScalar mb u)), envCur)
      -- GA multivector functions
      | "exp" =>
        let (m, _) ← mv0 0
        return (.mv (MV.exp m), envCur)
      | "log" =>
        let (m, _) ← mv0 0
        return (.mv (MV.log m), envCur)
      | "rev" | "reverse" =>
        let (m, d) ← mv0 0
        return (.mv (MV.reverse m) false none d, envCur)
      | "conj" | "conjugate" =>
        let (m, d) ← mv0 0
        return (.mv (MV.clifford m) false none d, envCur)
      | "inv" | "inverse" =>
        let (m, _) ← mv0 0
        return (.mv (MV.inv m), envCur)
      | "dual" =>
        let (m, d) ← mv0 0
        return (.mv (MV.complementright m) false none (!d), envCur)
      | "undual" =>
        let (m, d) ← mv0 0
        return (.mv (MV.complementleft m) false none (!d), envCur)
      | "norm" | "length" =>
        let (m, _) ← mv0 0
        return (.mv (MV.single 0 (ganjaNorm m)), envCur)
      | "unit" | "normalize" | "normalized" =>
        let (m, d) ← mv0 0
        return (.mv (ganjaNormalize m) false none d, envCur)
      | "grade" =>
        let (m, d) ← mv0 0
        let k := (max 0.0 (f0 1)).toUInt32.toNat
        return (.mv (MV.gradeProj k m) false none d, envCur)
      -- Reactive draggable points & handles!
      | "point" | "draggable" =>
        let defP : Vec3 := ⟨f0 0, f0 1, f0 2⟩
        let isTopLevel := envCur.loopDepth == 0 && envCur.callDepth == 0
        if isTopLevel || fname.toLower == "draggable" then
          let hid := envCur.nextHandleId
          let p := envCur.handlePos hid defP
          let envNext := { envCur with nextHandleId := hid + 1 }
          return (.mv (makePointMV V envNext.zeroIndexed p.x p.y p.z) true (some hid), envNext)
        else
          return (.mv (makePointMV V envCur.zeroIndexed defP.x defP.y defP.z) false none, envCur)
      | "handle" =>
        let hid := (max 0.0 (f0 0)).toUInt32
        let p := envCur.handlePos hid ⟨f0 1, f0 2, f0 3⟩
        let envNext := { envCur with nextHandleId := max envCur.nextHandleId (hid + 1) }
        return (.mv (makePointMV V envNext.zeroIndexed p.x p.y p.z) true (some hid), envNext)
      -- Interactive `@param` slider (`slider("name", default, min, max[, step[, label]])`)
      | "slider" | "param" =>
        match (vals[0]? : Option (ScriptVal V)) with
        | some (.str pName) =>
          let defV := f0 1 0.5
          let minV := f0 2 0.0
          let maxV := f0 3 1.0
          let stepV := if vals.size ≥ 5 then f0 4 0.0 else 0.0
          let lbl :=
            match (vals[5]? : Option (ScriptVal V)) with
            | some (.str s) => s
            | _ => pName
          let (curV, envNext) := envCur.registerParam pName lbl defV minV maxV stepV
          return (.mv (MV.single 0 curV), envNext)
        | _ => throw "slider(\"name\", default, min, max[, step[, label]]) expects a parameter name string"
      -- Planes, lines, motors, rotors, boosts
      | "plane" =>
        -- Either `plane(A, B, C)` from 3 points (`A & B & C`), or `plane(a, b, c, d)` coefficients!
        let threePts : Bool :=
          vals.size == 3 &&
          (match vals[0]!, vals[1]!, vals[2]! with
           | .mv a .., .mv b .., .mv c .. =>
             dominantGrade a ≥ 2 && dominantGrade b ≥ 2 && dominantGrade c ≥ 2
           | _, _, _ => false)
        if threePts then
          let (ma, _) ← mv0 0; let (mb, _) ← mv0 1; let (mc, _) ← mv0 2
          return (.mv (ganjaVee (ganjaVee ma mb) mc) false none true, envCur)
        else if envCur.zeroIndexed && V.n == 4 then
          let pl := MV.add (MV.single 1 (f0 3))
            (MV.add (MV.single 2 (f0 0)) (MV.add (MV.single 4 (f0 1)) (MV.single 8 (f0 2))))
          return (.mv pl false none true, envCur)
        else if V.hasconformal && V.n == 5 then
          -- Dual plane in CGA3 Witt: nx e1 + ny e2 + nz e3 + d e∞
          let pl := MV.add (MV.single 1 (f0 3))
            (MV.add (MV.single 4 (f0 0)) (MV.add (MV.single 8 (f0 1)) (MV.single 16 (f0 2))))
          return (.mv pl false none true, envCur)
        else
          let pl := MV.add (MV.single 1 (f0 0)) (MV.add (MV.single 2 (f0 1)) (MV.single 4 (f0 2)))
          return (.mv pl false none true, envCur)
      | "line" =>
        -- `line(A, B)` joins two points, or `line(a, b, c)` builds a 2D line!
        if vals.size == 2 then
          let (ma, _) ← mv0 0; let (mb, _) ← mv0 1
          if dominantGrade ma ≥ 1 && dominantGrade mb ≥ 1 then
            if V.hasconformal then
              let ni : MV V := MV.blade 1
              return (.mv (MV.wedge (MV.wedge ma mb) ni), envCur)
            else
              return (.mv (ganjaVee ma mb), envCur)
          else
            return (.mv (MV.add (MV.single 2 (f0 0)) (MV.single 4 (f0 1))), envCur)
        else if envCur.zeroIndexed && V.n == 3 then
          let l := MV.add (MV.single 1 (f0 2)) (MV.add (MV.single 2 (f0 0)) (MV.single 4 (f0 1)))
          return (.mv l, envCur)
        else
          return (.mv (MV.add (MV.single 2 (f0 0)) (MV.single 4 (f0 1))), envCur)
      | "translator" =>
        let tx := f0 0; let ty := f0 1; let tz := f0 2
        if envCur.zeroIndexed && V.n == 4 then
          let tr := MV.add MV.one
            (MV.add (MV.single 3 (-0.5 * tx)) (MV.add (MV.single 5 (-0.5 * ty)) (MV.single 9 (-0.5 * tz))))
          return (.mv tr, envCur)
        else if envCur.zeroIndexed && V.n == 3 then
          let tr := MV.add MV.one (MV.add (MV.single 3 (-0.5 * tx)) (MV.single 5 (-0.5 * ty)))
          return (.mv tr, envCur)
        else
          return (.mv MV.one, envCur)
      | "motor" =>
        -- `motor(ax, ay, az, angle[, shift])` OR `motor(lineMV, angle[, shift])`
        if vals.size ≥ 4 then
          let m := makeScrewMotorMV envCur.zeroIndexed (f0 0) (f0 1) (f0 2) (f0 3) (f0 4 0.0)
          return (.mv m, envCur)
        else if vals.size ≥ 2 then
          let (lMV, _) ← mv0 0
          let ang := f0 1; let sh := f0 2 0.0
          let uL := ganjaNormalize lMV
          let gen := MV.mulScalar uL (-0.5 * ang)
          let gen2 := if envCur.zeroIndexed && Float.abs sh > 1e-9 then
            MV.add gen (MV.mulScalar (MV.mul (MV.blade 1) uL) (-0.5 * sh))
            else gen
          return (.mv (MV.exp gen2), envCur)
        else throw "motor() expects (axisLine, angle[, shift]) or (ax, ay, az, angle[, shift])"
      | "rotor" =>
        if vals.size ≥ 2 then
          let (bMV, _) ← mv0 0
          let b := ganjaNormalize bMV
          let ang := 0.5 * f0 1
          return (.mv (MV.add (MV.single 0 (Float.cos ang)) (MV.mulScalar b (Float.sin ang))), envCur)
        else throw "rotor(bivector, angle) expects 2 arguments"
      | "boost" =>
        -- STA `-+++` Lorentz boost `cosh(η/2) + sinh(η/2) * (et ∧ dir)`!
        let (dx, dy, dz, eta) :=
          if vals.size ≥ 4 then (f0 0, f0 1, f0 2, f0 3)
          else if vals.size == 2 then
            match vals[0]! with
            | .mv d .. =>
              let p := (extractPointVec3 envCur.zeroIndexed d).getD ⟨1.0, 0.0, 0.0⟩
              (p.x, p.y, p.z, f0 1)
            | _ => (1.0, 0.0, 0.0, f0 1)
          else (1.0, 0.0, 0.0, f0 0)
        let u := Vec3.normalize ⟨dx, dy, dz⟩
        let c := Float.cosh (0.5 * eta); let s := Float.sinh (0.5 * eta)
        if V == AlgSpace.STA then
          -- In STA `-+++`: et=bit0(1), ex=bit1(2), ey=bit2(4), ez=bit3(8) => et∧ex=3, et∧ey=5, et∧ez=9
          let b := MV.add (MV.single 0 c)
            (MV.add (MV.single 3 (s * u.x)) (MV.add (MV.single 5 (s * u.y)) (MV.single 9 (s * u.z))))
          return (.mv b, envCur)
        else
          let b := MV.add (MV.single 0 c) (MV.single 3 s)
          return (.mv b, envCur)
      | "up" =>
        let (v, _) ← mv0 0
        if V.hasconformal && V.n == 5 then
          return (.mv (makePointMV V false (v.coeff 4) (v.coeff 8) (v.coeff 16)), envCur)
        else
          return (.mv (makePointMV V envCur.zeroIndexed (v.coeff 1) (v.coeff 2) (v.coeff 4)), envCur)
      -- Spheres & circles (exact GA multivectors in CGA, visual primitives elsewhere!)
      | "sphere" =>
        if vals.size == 4 && V.hasconformal && V.n == 5 then
          return (.mv (makeDualSphereMV (f0 0) (f0 1) (f0 2) (f0 3)) false none true, envCur)
        else if vals.size == 4 then
          let col := envCur.activeColor.getD ⟨0.28, 0.68, 1.0, 0.28⟩
          return (.sphere3 { center := ⟨f0 0, f0 1, f0 2⟩, radius := Float.abs (f0 3), color := col }, envCur)
        else if vals.size == 2 then
          let ctr ← valAsVec3 envCur.zeroIndexed vals[0]!
          let r := Float.abs (f0 1)
          if V.hasconformal && V.n == 5 then
            return (.mv (makeDualSphereMV ctr.x ctr.y ctr.z r) false none true, envCur)
          else
            let col := envCur.activeColor.getD ⟨0.28, 0.68, 1.0, 0.28⟩
            return (.sphere3 { center := ctr, radius := r, color := col }, envCur)
        else throw "sphere() expects (x, y, z, r) or (centerPt, r)"
      | "circle" =>
        if vals.size == 3 then
          if V.hasconformal then
            let (ma, _) ← mv0 0; let (mb, _) ← mv0 1; let (mc, _) ← mv0 2
            return (.mv (MV.wedge (MV.wedge ma mb) mc), envCur)
          else
            -- 3D circumcircle of 3 points in any algebra!
            let pA ← valAsVec3 envCur.zeroIndexed vals[0]!
            let pB ← valAsVec3 envCur.zeroIndexed vals[1]!
            let pC ← valAsVec3 envCur.zeroIndexed vals[2]!
            let ab := Vec3.sub pB pA; let ac := Vec3.sub pC pA
            let n := Vec3.normalize (Vec3.cross ab ac)
            let u := Vec3.normalize ab; let v := Vec3.cross n u
            let bx := Vec3.dot ab u; let cx := Vec3.dot ac u; let cy := Vec3.dot ac v
            let ux := 0.5 * bx
            let uy := if Float.abs cy > 1e-5 then (cx * cx + cy * cy - bx * cx) / (2.0 * cy) else 0.0
            let ctr := Vec3.add pA (Vec3.add (Vec3.scale ux u) (Vec3.scale uy v))
            let rad := Vec3.norm (Vec3.sub pA ctr)
            let col := envCur.activeColor.getD RGBA.cyan
            return (.circle3 { center := ctr, u, v, radius := rad, width := 2.6, color := col }, envCur)
        else if vals.size ≥ 4 then
          let col := envCur.activeColor.getD RGBA.cyan
          return (.circle3 { center := ⟨f0 0, f0 1, f0 2⟩, u := ⟨1,0,0⟩, v := ⟨0,1,0⟩,
                             radius := Float.abs (f0 3), width := 2.6, color := col }, envCur)
        else throw "circle() expects (A, B, C) or (x, y, z, r)"
      -- Segments, polygons, curves
      | "seg" | "segment" =>
        if vals.size ≥ 2 then
          let pA ← valAsVec3 envCur.zeroIndexed vals[0]!
          let pB ← valAsVec3 envCur.zeroIndexed vals[1]!
          return (.seg pA pB, envCur)
        else throw "seg(A, B) expects 2 points"
      | "poly" | "polygon" =>
        let srcVals := match vals.toList with | [.list xs] => xs | _ => vals
        let mut pts : Array Vec3 := Array.mkEmpty srcVals.size
        for sv in srcVals do
          pts := pts.push (← valAsVec3 envCur.zeroIndexed sv)
        if pts.size < 3 then throw "poly() requires at least 3 points"
        return (.poly pts, envCur)
      | "curve" | "closedcurve" =>
        let srcVals := match vals.toList with | [.list xs] => xs | _ => vals
        let mut pts : Array Vec3 := Array.mkEmpty srcVals.size
        for sv in srcVals do
          pts := pts.push (← valAsVec3 envCur.zeroIndexed sv)
        return (.curve pts (fname.toLower == "closedcurve"), envCur)
      -- Procedural meshes, motor transforms & live plane slicing!
      | "mesh" =>
        match (vals[0]? : Option (ScriptVal V)) with
        | some (.str kind) =>
          let mid := envCur.nextMeshId
          let asset ← buildNamedScriptMesh kind mid
          return (.mesh asset Motor3.identity, { envCur with nextMeshId := mid + 1 })
        | _ => throw "mesh() expects a string name (\"bunny\", \"torus\", \"cube\", \"icosahedron\", ...)"
      | "transform" =>
        if vals.size ≥ 2 then
          match vals[0]!, vals[1]! with
          | .mesh asset m0, .mv mMV .. =>
            let newId := envCur.nextMeshId
            let envNext := { envCur with nextMeshId := newId + 1,
                                         consumedMeshIds := envCur.consumedMeshIds.push asset.meshId }
            return (.mesh { asset with meshId := newId } (Motor3.mul (extractMotor3 mMV) m0), envNext)
          | .mv mMV .., .mesh asset m0 =>
            let newId := envCur.nextMeshId
            let envNext := { envCur with nextMeshId := newId + 1,
                                         consumedMeshIds := envCur.consumedMeshIds.push asset.meshId }
            return (.mesh { asset with meshId := newId } (Motor3.mul (extractMotor3 mMV) m0), envNext)
          | _, _ => throw "transform(mesh, motor) expects a mesh and a motor"
        else throw "transform(mesh, motor) expects 2 arguments"
      | "slice" =>
        if vals.size ≥ 2 then
          match vals[0]!, vals[1]! with
          | .mesh asset _, .mv plMV .. =>
            match extractPlaneND envCur.zeroIndexed plMV with
            | some (nrm, d) =>
              let idLo := envCur.nextMeshId
              let idHi := idLo + 1
              let res := sliceMeshByPlane asset nrm d idLo idHi
              let ctr := Vec3.scale (-d) nrm
              let (pu, pv) := Vec3.orthonormalBasis nrm
              let envNext :=
                { envCur with nextMeshId := idLo + 2,
                              consumedMeshIds := envCur.consumedMeshIds.push asset.meshId }
              return (.sliced res ctr pu pv, envNext)
            | none => throw "slice(mesh, plane): second argument is not a valid plane"
          | _, _ => throw "slice(mesh, plane) expects a mesh and a plane multivector"
        else throw "slice(mesh, plane) expects 2 arguments"
      -- Live 3D implicit isosurfaces, surfaces & GPU OPNS shaders!
      | "implicit" =>
        match (vals[0]? : Option (ScriptVal V)) with
        | some (.str exprStr) =>
          let gridN := if vals.size ≥ 2 then max 8 (min 28 (f0 1 16.0).toUInt32.toNat) else 16
          let b := if vals.size ≥ 3 then max 0.5 (min 6.0 (f0 2 1.5)) else 1.5
          let mid := envCur.nextMeshId
          let m ← evalImplicitExprMesh exprStr envCur.timeSec ⟨-b,-b,-b⟩ ⟨b,b,b⟩ gridN mid true
          return (.mesh m Motor3.identity, { envCur with nextMeshId := mid + 1 })
        | _ => throw "implicit(\"expr\"[, gridN, bound]) expects an equation string"
      | "surface" =>
        match (vals[0]? : Option (ScriptVal V)) with
        | some (.str exprStr) =>
          let b := if vals.size ≥ 2 then max 0.5 (min 8.0 (f0 1 2.0)) else 2.0
          let gridN := if vals.size ≥ 3 then max 8 (min 64 (f0 2 32.0).toUInt32.toNat) else 32
          let mid := envCur.nextMeshId
          let m ← evalSurfaceMesh exprStr envCur.timeSec (-b) b (-b) b gridN mid
          return (.mesh m Motor3.identity, { envCur with nextMeshId := mid + 1 })
        | _ => throw "surface(\"expr\"[, bound, gridN]) expects a z = f(x, y, t) string"
      | "opns" =>
        match (vals[0]? : Option (ScriptVal V)) with
        | some (.str exprStr) =>
          let sh ← compileImplicitExprToGpu exprStr "script_implicit_gpu"
          let col := envCur.activeColor.getD RGBA.cyan
          let u : OpnsUniformPrim :=
            { shaderIdx := 0, grade := 0, coeffs := FloatArray.empty,
              thresh := 0.015, maxSteps := 96, stepSize := 0.01, color := col, isIPNS := false }
          return (.opns sh u, envCur)
        | some (.mv x ..) =>
          let g := dominantGrade x
          let spec : AlgSpec :=
            { name := envCur.algName, p := envCur.p, q := envCur.q, r := envCur.r,
              conformalWitt := envCur.conformalWitt }
          let isIpns := g == 1 && envCur.conformalWitt
          let sh ← compileGaOpnsBundle s!"script_{envCur.algName}_g{g}" spec g isIpns
          let blades := indexBasisGrade V.n g
          let mut coeffs := FloatArray.emptyWithCapacity blades.size
          for b in blades do coeffs := coeffs.push (x.coeff b)
          let col := envCur.activeColor.getD RGBA.violet
          let u : OpnsUniformPrim :=
            { shaderIdx := 0, grade := g.toUInt32, coeffs, thresh := 0.02, maxSteps := 96,
              stepSize := 0.01, color := col, isIPNS := isIpns }
          return (.opns sh u, envCur)
        | _ => throw "opns() expects a multivector or implicit equation string"
      -- Color & explicit graph() scene builder!
      | "color" =>
        match (vals[0]? : Option (ScriptVal V)) with
        | some (.color rgba hex) => return (.color rgba hex, { envCur with activeColor := some rgba })
        | _ =>
          let hex := (max 0.0 (f0 0)).toUInt32
          let rgba := hexToRGBA hex
          return (.color rgba hex, { envCur with activeColor := some rgba })
      | "rgb" | "rgba" =>
        let rgba : RGBA := ⟨max 0.0 (min 1.0 (f0 0 1.0)), max 0.0 (min 1.0 (f0 1 1.0)),
                            max 0.0 (min 1.0 (f0 2 1.0)), max 0.0 (min 1.0 (f0 3 1.0))⟩
        return (.color rgba 0xFFFFFF, { envCur with activeColor := some rgba })
      | "graph" =>
        let items := match vals.toList with | [.list xs] => xs | _ => vals
        let envNext := { envCur with graphItems := envCur.graphItems ++ items, hasGraph := true }
        return (.list items, envNext)
      | _ => throw s!"unknown function '{fname}'"
  | .letBind name rhs =>
    let (v, env1) ← evalScriptVal env rhs
    let env2 := if env1.loopDepth == 0 && env1.callDepth == 0 then env1.bindTop name v else env1.bindLocal name v
    return (v, env2)
  | .eq (.ident name) rhs =>
    let (v, env1) ← evalScriptVal env rhs
    let env2 := if env1.loopDepth == 0 && env1.callDepth == 0 then env1.bindTop name v else env1.bindLocal name v
    return (v, env2)
  | .eq lhs rhs =>
    let (vl, env1) ← evalScriptVal env lhs
    let (vr, env2) ← evalScriptVal env1 rhs
    let (ml, _) ← valAsMV vl
    let (mr, _) ← valAsMV vr
    return (.mv (MV.sub ml mr), env2)
  | .seq stmts =>
    let mut envCur := env
    let mut last : ScriptVal V := .mv MV.zero
    for s in stmts do
      let (v, envNext) ← evalScriptVal envCur s
      last := v
      envCur := envNext
    return (last, envCur)

/-- Backwards-compatible pure-MV evaluator `evalGA` (delegates directly to `evalScriptVal`!). -/
partial def evalGA {V : AlgSpace} (env : EvalEnv V) (e : Expr) :
    Except String (MV V × EvalEnv V) := do
  let sEnv : ScriptEnv V :=
    { zeroIndexed := env.zeroIndexed, timeSec := env.timeSec, handles := env.handles,
      vars := env.vars.map (fun (k, v) => (k, .mv v)), order := env.order }
  let (v, sEnv1) ← evalScriptVal sEnv e
  let (m, _) ← valAsMV v
  let mut newVars : Array (String × MV V) := #[]
  for (k, sv) in sEnv1.vars do
    match sv with
    | .mv x .. => newVars := newVars.push (k, x)
    | _ => pure ()
  return (m, { env with vars := newVars, order := sEnv1.order })

/-! ## Automatic Multivector & Rich Value → `SceneFrame` Classifier -/

private def scriptPalette (i : Nat) : RGBA :=
  match i % 7 with
  | 0 => RGBA.cyan
  | 1 => RGBA.amber
  | 2 => RGBA.green
  | 3 => RGBA.coral
  | 4 => RGBA.violet
  | 5 => RGBA.blue
  | _ => RGBA.white

/-- Classify a single `MV V` element into `SceneFrame` 3D/2D primitives across ALL algebras:
PGA3, PGA2, CGA3 (grades 1–4, both OPNS & IPNS!), CGA2, STA `-+++`, R3, R2, Complex, Dual, Quaternion! -/
def appendClassifiedWith {V : AlgSpace} (f : SceneFrame) (name : String) (idx : Nat)
    (zeroIndexed : Bool) (x : MV V) (colorOpt : Option RGBA := none)
    (draggable : Bool := true) (handleIdOpt : Option UInt32 := none)
    (isDualRound : Bool := false) (addInspect : Bool := true) : SceneFrame :=
  let col := colorOpt.getD (scriptPalette idx)
  let hid := handleIdOpt.getD idx.toUInt32
  let g := dominantGrade x
  let f :=
    if addInspect then
      let dense := mvToDenseArray x
      let entry : InspectEntry :=
        { idx := idx.toUInt32, name, grade := g.toUInt32,
          formatted := x.showString zeroIndexed, coeffs := dense, editable := true }
      { f with inspect := f.inspect.push entry }
    else f
  -- 1. PGA3: D"0,1,1,1" (bit0=e0, bit1=e1, bit2=e2, bit3=e3)
  if zeroIndexed && V.n == 4 then
    let w := x.coeff 14 -- e123
    if g == 3 && Float.abs w > 1e-6 then
      let px := -x.coeff 13 / w
      let py :=  x.coeff 11 / w
      let pz := -x.coeff 7  / w
      { f with points := f.points.push {
          handleId := hid, pos := ⟨px, py, pz⟩, radius := 0.085,
          color := col, role := { draggable }, label := name } }
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
  -- 2. PGA2: D"0,1,1" (bit0=e0, bit1=e1, bit2=e2)
  else if zeroIndexed && V.n == 3 then
    let w := x.coeff 6 -- e12
    if g == 2 && Float.abs w > 1e-6 then
      let px := -x.coeff 3 / w
      let py :=  x.coeff 5 / w
      { f with points := f.points.push {
          handleId := hid, pos := ⟨px, py, 0.0⟩, radius := 0.075,
          color := col, role := { draggable }, label := name } }
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
  -- 3. Witt CGA3: S"∞∅+++" (bit0=∞, bit1=∅, bit2=e1, bit3=e2, bit4=e3) — ALL GRADES 1..4!
  else if V.hasconformal && V.n == 5 then
    let ni : MV V := MV.blade 1
    let classifyDual1 (s : MV V) : SceneFrame :=
      let w := s.coeff 2
      let cInf := s.coeff 1
      let ex := s.coeff 4; let ey := s.coeff 8; let ez := s.coeff 16
      if Float.abs w > 1e-6 then
        let cx := ex / w; let cy := ey / w; let cz := ez / w
        let r2 := cx * cx + cy * cy + cz * cz - 2.0 * cInf / w
        if Float.abs r2 < 1e-3 then
          { f with points := f.points.push {
              handleId := hid, pos := ⟨cx, cy, cz⟩, radius := 0.085,
              color := col, role := { draggable }, label := name } }
        else
          { f with spheres := f.spheres.push {
              center := ⟨cx, cy, cz⟩, radius := Float.sqrt (Float.abs r2),
              color := ⟨col.r, col.g, col.b, 0.26⟩, imaginary := r2 < 0.0, label := name } }
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
    let classifyPairOrCircle (b : MV V) (asCircle : Bool) : SceneFrame :=
      -- Exact Witt center `C = b * ni * b` and direction `d = ni ⌋ b`!
      let cPt := MV.mul (MV.mul b ni) b
      let dVec := MV.contractionLeft ni b
      let dEuc : Vec3 := ⟨dVec.coeff 4, dVec.coeff 8, dVec.coeff 16⟩
      let dNorm2 := Vec3.normSq dEuc
      let w := cPt.coeff 2
      if dNorm2 > 1e-8 && Float.abs w > 1e-8 then
        let ctr : Vec3 := ⟨cPt.coeff 4 / w, cPt.coeff 8 / w, cPt.coeff 16 / w⟩
        let num := (MV.mul b (MV.reverse b)).coeff 0
        let den := (MV.mul dVec (MV.reverse dVec)).coeff 0
        let r2 := if Float.abs den > 1e-10 then num / den else 0.0
        let rad := Float.sqrt (Float.abs r2)
        let dir := Vec3.scale (1.0 / Float.sqrt dNorm2) dEuc
        if asCircle then
          let (u, v) := Vec3.orthonormalBasis dir
          { f with circles := f.circles.push {
              center := ctr, u, v, radius := rad, width := 2.8,
              color := col, imaginary := r2 < 0.0, label := name } }
        else
          let p1 := Vec3.add ctr (Vec3.scale rad dir)
          let p2 := Vec3.sub ctr (Vec3.scale rad dir)
          { f with pointPairs := f.pointPairs.push {
              p1, p2, radius := 0.075, color := col, imaginary := r2 < 0.0,
              showLink := true, label := name } }
      else if dNorm2 > 1e-8 then
        -- Flat line (dual or primal)
        let dir := Vec3.scale (1.0 / Float.sqrt dNorm2) dEuc
        { f with lines := f.lines.push {
            origin := Vec3.zero, dir, clip := 3.0, width := 2.4, color := col, label := name } }
      else f
    if g == 1 then
      classifyDual1 x
    else if g == 4 then
      classifyDual1 (MV.complementright x)
    else if g == 2 then
      classifyPairOrCircle x isDualRound
    else if g == 3 then
      -- Grade-3 OPNS circle `A^B^C` (or line `A^B^ni` if flat)
      let dualB := MV.complementright x
      let flat := MV.wedge x ni
      if ganjaNorm flat < 1e-4 then
        -- Flat 3D line `A ^ B ^ ni`: direction is `e∞ ⌋ (e∅ ⌋ x)` or dual normal
        let lDir : Vec3 := ⟨x.coeff 12, -x.coeff 20, x.coeff 24⟩
        let d2 := Vec3.normSq lDir
        if d2 > 1e-8 then
          { f with lines := f.lines.push {
              origin := Vec3.zero, dir := Vec3.normalize lDir, clip := 3.2, width := 2.4,
              color := col, label := name } }
        else classifyPairOrCircle dualB true
      else
        classifyPairOrCircle dualB true
    else f
  -- 4. Witt CGA2: S"∞∅++" (bit0=∞, bit1=∅, bit2=e1, bit3=e2)
  else if V.hasconformal && V.n == 4 then
    if g == 1 || g == 3 then
      let s := if g == 3 then MV.complementright x else x
      let w := s.coeff 2; let cInf := s.coeff 1
      let ex := s.coeff 4; let ey := s.coeff 8
      if Float.abs w > 1e-6 then
        let cx := ex / w; let cy := ey / w
        let r2 := cx * cx + cy * cy - 2.0 * cInf / w
        if Float.abs r2 < 1e-3 then
          { f with points := f.points.push {
              handleId := hid, pos := ⟨cx, cy, 0.0⟩, radius := 0.075,
              color := col, role := { draggable }, label := name } }
        else
          { f with circles := f.circles.push {
              center := ⟨cx, cy, 0.0⟩, u := ⟨1,0,0⟩, v := ⟨0,1,0⟩,
              radius := Float.sqrt (Float.abs r2), width := 2.6,
              color := col, imaginary := r2 < 0.0, label := name } }
      else
        let nlen := Float.sqrt (ex * ex + ey * ey)
        if nlen > 1e-6 then
          { f with lines := f.lines.push {
              origin := ⟨cInf * ex / (nlen * nlen), cInf * ey / (nlen * nlen), 0.0⟩,
              dir := ⟨-ey / nlen, ex / nlen, 0.0⟩, clip := 3.5, width := 2.2,
              color := col, label := name } }
        else f
    else f
  -- 5. STA S"-+++" (`et=1, ex=2, ey=4, ez=8`)
  else if V == AlgSpace.STA then
    if g == 1 then
      -- Map spacetime 4-vector (ct, x, y, z) -> 3D (x, ct, z) or (x, y, z) if ct == 0
      let ct := x.coeff 1; let vx := x.coeff 2; let vy := x.coeff 4; let vz := x.coeff 8
      let tip : Vec3 := if Float.abs ct > 1e-6 && Float.abs vy < 1e-6 then ⟨vx, ct, vz⟩ else ⟨vx, vy, vz⟩
      { f with
        segments := f.segments.push { a := Vec3.zero, b := tip, width := 3.0, color := col, role := { arrow := true } },
        points := f.points.push { handleId := hid, pos := tip, radius := 0.075, color := col,
                                  role := { draggable }, label := name } }
    else if g == 2 then
      -- Spatial magnetic bivector (e12=6, e13=10, e23=12) + boost electric bivector (e01=3, e02=5, e03=9)
      let b12 := x.coeff 6; let b13 := x.coeff 10; let b23 := x.coeff 12
      let area := Float.sqrt (b12 * b12 + b13 * b13 + b23 * b23)
      let f1 :=
        if area > 1e-6 then
          let n : Vec3 := ⟨b23, -b13, b12⟩
          let (u, v) := Vec3.orthonormalBasis n
          let rad := Float.sqrt (area / piF)
          { f with bivectorDisks := f.bivectorDisks.push {
              origin := Vec3.zero, u := Vec3.scale rad u, v := Vec3.scale rad v,
              area, color := ⟨col.r, col.g, col.b, 0.35⟩, isDisk := true } }
        else f
      let eVec : Vec3 := ⟨x.coeff 3, x.coeff 5, x.coeff 9⟩
      if Vec3.norm eVec > 1e-6 then
        { f1 with segments := f1.segments.push {
            a := Vec3.zero, b := eVec, width := 3.2, color := RGBA.coral, role := { arrow := true } } }
      else f1
    else f
  -- 6. Euclidean R3 / R2 / Complex / Dual / Quaternion
  else
    let vx := if V.n == 1 then x.coeff 0 else if V.n ≥ 1 then x.coeff 1 else x.coeff 0
    let vy := if V.n == 1 then x.coeff 1 else if V.n ≥ 2 then x.coeff 2 else 0.0
    let vz := if V.n ≥ 3 then x.coeff 4 else 0.0
    if V.n == 1 then
      -- Complex / Dual number `a + b*i` plotted in 2D plane!
      let tip : Vec3 := ⟨vx, vy, 0.0⟩
      { f with
        segments := f.segments.push { a := Vec3.zero, b := tip, width := 2.6, color := col, role := { arrow := true } },
        points := f.points.push { handleId := hid, pos := tip, radius := 0.07, color := col,
                                  role := { draggable }, label := name } }
    else if g == 1 then
      let tip : Vec3 := ⟨vx, vy, vz⟩
      { f with
        segments := f.segments.push {
          a := Vec3.zero, b := tip, width := 3.0, color := col, role := { arrow := true } },
        points := f.points.push {
          handleId := hid, pos := tip, radius := 0.075,
          color := col, role := { draggable }, label := name } }
    else if g == 2 && V.n ≥ 3 then
      let b12 := x.coeff 3; let b13 := x.coeff 5; let b23 := x.coeff 6
      let area := Float.sqrt (b12 * b12 + b13 * b13 + b23 * b23)
      if area > 1e-6 then
        let n : Vec3 := ⟨b23, -b13, b12⟩
        let (u, v) := Vec3.orthonormalBasis n
        let rad := Float.sqrt (area / piF)
        { f with bivectorDisks := f.bivectorDisks.push {
            origin := Vec3.zero, u := Vec3.scale rad u, v := Vec3.scale rad v,
            area, color := ⟨col.r, col.g, col.b, 0.35⟩, isDisk := true } }
      else f
    else f

/-- Backwards-compatible classifier wrapper. -/
def appendClassified {V : AlgSpace} (f : SceneFrame) (name : String) (idx : Nat)
    (zeroIndexed : Bool) (x : MV V) : SceneFrame :=
  appendClassifiedWith f name idx zeroIndexed x

/-- Append a rich `ScriptVal V` (segments, polygons, curves, meshes, slices, OPNS shaders,
circles, spheres, lists, or multivectors) into a `SceneFrame`. -/
private partial def appendScriptVal {V : AlgSpace} (f : SceneFrame) (name : String) (idx : Nat)
    (zeroIdx : Bool) (colOpt : Option RGBA) (addInspect : Bool) (v : ScriptVal V) : SceneFrame :=
  let col := colOpt.getD (scriptPalette idx)
  match v with
  | .mv x drag hid isDual =>
    appendClassifiedWith f name idx zeroIdx x colOpt drag hid isDual addInspect
  | .color _ _ | .str _ | .fnVal .. => f
  | .seg a b =>
    { f with segments := f.segments.push { a, b, width := 2.8, color := col } }
  | .poly verts =>
    if verts.size < 3 then f
    else Id.run do
      let mut mb : MeshBuilder := {}
      let fillCol : RGBA := ⟨col.r, col.g, col.b, 0.32⟩
      let (mb0, i0) := mb.addVertex verts[0]! fillCol
      mb := mb0
      for k in [1:verts.size - 1] do
        let (mb1, i1) := mb.addVertex verts[k]! fillCol
        let (mb2, i2) := mb1.addVertex verts[k + 1]! fillCol
        mb := mb2.addTri i0 i1 i2
      let m := mb.finalize (8200 + idx.toUInt64)
      let mut fa := FloatArray.emptyWithCapacity (verts.size * 3)
      for p in verts do fa := fa.push p.x |>.push p.y |>.push p.z
      return { f with
        meshAssets := f.meshAssets.push m,
        meshRefs := f.meshRefs.push { meshId := m.meshId, dirtyHash := m.dirtyHash,
                                      color := fillCol, doubleSided := true, useVertexColors := true },
        curves := f.curves.push { points := fa, width := 2.4, color := col, closed := true } }
  | .curve pts closed =>
    if pts.size < 2 then f
    else Id.run do
      let mut fa := FloatArray.emptyWithCapacity (pts.size * 3)
      for p in pts do fa := fa.push p.x |>.push p.y |>.push p.z
      return { f with curves := f.curves.push { points := fa, width := 2.6, color := col, closed } }
  | .mesh asset motor =>
    { f with
      meshAssets := f.meshAssets.push asset,
      meshRefs := f.meshRefs.push { meshId := asset.meshId, dirtyHash := asset.dirtyHash,
                                    motor, color := RGBA.white, useVertexColors := true, doubleSided := true } }
  | .sliced res ctr pu pv =>
    { f with
      meshAssets := f.meshAssets.push res.lowerMesh |>.push res.upperMesh,
      meshRefs := f.meshRefs.push { meshId := res.lowerMesh.meshId, dirtyHash := res.lowerMesh.dirtyHash,
                                    color := RGBA.white, useVertexColors := true, doubleSided := true }
                            |>.push { meshId := res.upperMesh.meshId, dirtyHash := res.upperMesh.dirtyHash,
                                      color := ⟨0.78, 0.85, 1.0, 0.22⟩, useVertexColors := false, doubleSided := true },
      planes := f.planes.push { center := ctr, u := pu, v := pv, extent := 1.45,
                                color := ⟨0.22, 0.88, 0.95, 0.24⟩, label := if name.isEmpty then "Cut Plane" else name },
      segments := f.segments ++ res.contour3D,
      contourOverlay := some res.contour2D }
  | .opns sh u =>
    let shIdx := f.opnsShaders.size.toUInt32
    { f with
      opnsShaders := f.opnsShaders.push sh,
      opnsUniforms := f.opnsUniforms.push { u with shaderIdx := shIdx } }
  | .circle3 c =>
    { f with circles := f.circles.push { c with color := col, label := if name.isEmpty then c.label else name } }
  | .sphere3 s =>
    { f with spheres := f.spheres.push { s with color := ⟨col.r, col.g, col.b, 0.26⟩, label := if name.isEmpty then s.label else name } }
  | .pair3 p =>
    { f with pointPairs := f.pointPairs.push { p with color := col, label := if name.isEmpty then p.label else name } }
  | .disk3 d =>
    { f with bivectorDisks := f.bivectorDisks.push { d with color := ⟨col.r, col.g, col.b, 0.35⟩ } }
  | .list items => Id.run do
    -- Ganja.js list rendering: inline color tokens switch color, strings label the next/prev item!
    let mut fCur := f
    let mut curCol := colOpt
    let mut pendingLbl := name
    let mut subIdx := idx
    for k in [:items.size] do
      let it := items[k]!
      match it with
      | .color rgba _ => curCol := some rgba
      | .str s => pendingLbl := s
      | _ =>
        -- Look ahead: if next item is a string label (ganja.js style `[A & B, "L"]`), attach it!
        let lbl :=
          match items[k + 1]? with
          | some (.str nextS) => nextS
          | _ => pendingLbl
        fCur := appendScriptVal fCur lbl subIdx zeroIdx curCol false it
        pendingLbl := ""
        subIdx := subIdx + 1
    return fCur

/-- Inspect parsed statements for a leading `@basis <ALG>` or `Algebra(p, q, r)` directive. -/
private def extractAlgebraHeader (stmts : Array Expr) : Option String :=
  (stmts.find? fun s => match s with | .setAlgebra _ => true | _ => false).bind fun s =>
    match s with | .setAlgebra spec => some spec | _ => none

/-- Default KaTeX `formula` & 1-sentence `summary` for LiveScript v2 custom scripts by algebra. -/
private def scriptMathMeta (algName : String) (p q r : UInt8) : String × String :=
  match algName with
  | "PGA3" =>
    ("M X \\widetilde{M},\\quad A \\vee B,\\quad \\Pi_1 \\wedge \\Pi_2 \\in \\mathrm{Cl}_{3,0,1}",
     "Live 3D Projective Geometric Algebra script compiled and evaluated purely in Lean 4.")
  | "PGA2" =>
    ("A \\vee B,\\quad \\ell_1 \\wedge \\ell_2,\\quad \\ell \\rfloor P \\in \\mathrm{Cl}_{2,0,1}",
     "Live 2D Projective Geometric Algebra script evaluated purely in Lean 4.")
  | "CGA3" =>
    ("S_1 \\wedge S_2,\\quad A \\wedge B \\wedge C \\wedge D \\in \\mathrm{Cl}_{4,1}",
     "Live 3D Conformal Geometric Algebra script computing rounds, intersections, and versors in Lean 4.")
  | "CGA2" =>
    ("C = A \\wedge B \\wedge C,\\quad X' = V X \\widetilde{V} \\in \\mathrm{Cl}_{3,1}",
     "Live 2D Conformal Geometric Algebra script evaluated purely in Lean 4.")
  | "STA" =>
    ("B = \\exp\\!\\left(\\tfrac{\\eta}{2}\\,\\gamma_0\\gamma_1\\right),\\quad F = \\mathbf{E} + I\\mathbf{B} \\in \\mathrm{Cl}_{3,1}",
     "Live Spacetime Algebra Cl(3,1) (-+++) script computing Lorentz boosts and bivectors in Lean 4.")
  | "R3" =>
    ("a b = a \\cdot b + a \\wedge b,\\quad R \\mathbf{v} \\widetilde{R} \\in \\mathrm{Cl}_{3,0}",
     "Live 3D Euclidean Geometric Algebra script with exact rotors, bivectors, and 3D surfaces in Lean 4.")
  | _ =>
    ("a b = a \\cdot b + a \\wedge b \\in \\mathrm{Cl}_{" ++ toString p.toNat ++ "," ++ toString q.toNat ++ "," ++ toString r.toNat ++ "}",
     s!"Live {algName} Geometric Algebra script evaluated in real time inside Lean 4.")

/-- Evaluate a full LiveScript v2 CoffeeShop script string in `algebraSpec` and emit a `SceneFrame`
(with reactive draggable handles, live `@param`/`slider(...)` overrides, `EditCoeff`, Inspect Stash,
and exact `Line:Col` diagnostics). -/
def evalScriptToFrame (algebraSpec : String) (code : String)
    (handles : Array (UInt32 × Vec3) := #[]) (timeSec : Float := 0.0)
    (frameSeq : UInt64 := 0) (coeffOverrides : Array (UInt32 × UInt32 × Float) := #[])
    (paramOverrides : Array (String × Float) := #[]) :
    SceneFrame :=
  match parseScript code with
  | .error err =>
    let (algName, V, p, q, r, witt) := resolveAlgebra algebraSpec
    let zeroIdx := r > 0
    let meta_ := algebraMetaOf algName V p q r witt
    let is2D := (zeroIdx && V.n == 3) || (!zeroIdx && V.n ≤ 2)
    let (fml, smry) := scriptMathMeta algName p q r
    { frameSeq, simTime := timeSec, mode := .coffeeShop, is2D,
      algebra := meta_, presetId := "custom_script", title := s!"{algName} Script",
      script := code, formula := fml, summary := smry,
      camera := if is2D then { motor := Motor3.translator 0.0 0.0 (-4.0), isOrtho := true } else {},
      diagnostics := #[s!"Parse error — {err}"] }
  | .ok stmts =>
    let effectiveSpec := (extractAlgebraHeader stmts).getD algebraSpec
    let (algName, V, p, q, r, witt) := resolveAlgebra effectiveSpec
    let zeroIdx := r > 0
    let meta_ := algebraMetaOf algName V p q r witt
    let is2D := (zeroIdx && V.n == 3) || (witt && V.n == 4) || (!zeroIdx && V.n ≤ 2)
    let (fml, smry) := scriptMathMeta algName p q r
    let base : SceneFrame :=
      { frameSeq, simTime := timeSec, mode := .coffeeShop, is2D,
        algebra := meta_, presetId := "custom_script", title := s!"{algName} Script",
        script := code, formula := fml, summary := smry,
        camera := if is2D then { motor := Motor3.translator 0.0 0.0 (-4.0), isOrtho := true } else {} }
    let initEnv : ScriptEnv V :=
      { zeroIndexed := zeroIdx, algName, p := p.toNat, q := q.toNat, r := r.toNat,
        conformalWitt := witt, timeSec, handles, coeffOverrides, paramOverrides }
    let rec runStmts (i : Nat) (env : ScriptEnv V) (last : ScriptVal V) :
        Except String (ScriptVal V × ScriptEnv V) := do
      if i < stmts.size then
        let (v, env1) ← evalScriptVal env stmts[i]!
        runStmts (i + 1) env1 v
      else return (last, env)
    match runStmts 0 initEnv (.mv MV.zero) with
    | .error err => { base with diagnostics := #[s!"Eval error: {err}"] }
    | .ok (lastVal, finalEnv) => Id.run do
      let mut f := { base with params := finalEnv.emittedParams }
      if finalEnv.hasGraph then
        -- 1. Populate Inspect Stash for ALL top-level named multivector variables!
        let mut iIdx := 0
        for name in finalEnv.order do
          if let some (.mv x ..) := finalEnv.lookup? name then
            let g := dominantGrade x
            f := { f with inspect := f.inspect.push {
              idx := iIdx.toUInt32, name, grade := g.toUInt32,
              formatted := x.showString zeroIdx, coeffs := mvToDenseArray x, editable := true } }
            iIdx := iIdx + 1
        -- 2. Render explicit `graph([...])` items with exact inline colors & labels!
        f := appendScriptVal f "" 0 zeroIdx none false (.list finalEnv.graphItems)
      else
        -- Auto-render all top-level named variables (preserving declaration order & active color!)
        let mut idx := 0
        for name in finalEnv.order do
          if let some v := finalEnv.lookup? name then
            let skipConsumed :=
              match v with
              | .mesh asset _ => finalEnv.consumedMeshIds.contains asset.meshId
              | _ => false
            if !skipConsumed then
              let cOpt := ((finalEnv.varColors.find? fun kv => kv.1 == name).bind (·.2))
              f := appendScriptVal f name idx zeroIdx cOpt true v
            idx := idx + 1
        if finalEnv.order.isEmpty then
          f := appendScriptVal f "ans" 0 zeroIdx finalEnv.activeColor true lastVal
      return f

end Grassmann.Eval
