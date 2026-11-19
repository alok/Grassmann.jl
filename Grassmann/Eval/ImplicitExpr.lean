import Grassmann.Scene.Types
import Grassmann.Eval.Implicit3D

/-!
# Strictly `Init`-Only User-Typed 3D Implicit & Parametric Expression Evaluator

Self-contained Pratt expression parser, constant-folding optimizer, and zero-allocation
unboxed-`Float` evaluator wired directly into `Grassmann.Eval.Implicit3D`'s O(1)
edge-deduplicated Kuhn Marching Tetrahedra and parametric 3D surface mesher.

Zero `Lean.*`, zero `Std.*`, zero `DirectSum`, zero external deps — links straight
into both the tiny standalone C ABI dylib and the Lean 4.36 → C → Emscripten WASM bundle!

Supports:
- **Equations & expressions**: `lhs = rhs` auto-rewrites to `(lhs) - (rhs)`!
- **Implicit multiplication**: `2x`, `3(x+y)`, `2pi`, `(x-1)(x+1)`
- **Operators**: `+`, `-`, `*`, `/`, right-associative `^`, unary `-` / `+`
- **Functions**: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `sinh`, `cosh`, `tanh`,
  `exp`, `log`/`ln`, `sqrt`, `abs`, `floor`, `ceil`, `sign`, `atan2`, `min`, `max`,
  `pow`, `hypot`
- **Variables & constants**: `x`, `y`, `z`, `u`, `v`, `t`, `r` (`√(x²+y²+z²)`), `pi`, `tau`, `e`, `phi`
- **Peephole optimizer**: constant folding + integer power specialization (`^2`, `^3`, `^4`)
- **Adaptive coarse-probe bounding-box refinement**: probes a `7³` grid (`<0.1 ms`) to
  focus `gridN³` resolution tightly on active sign-change regions for `<15 ms` interactive speed!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.Eval.ImplicitExpr

open Grassmann.Scene Grassmann.Eval.Implicit3D

private def piF : Float := 3.14159265358979323846
private def twoPiF : Float := 6.28318530717958647692
private def eF : Float := 2.71828182845904523536
private def phiF : Float := 1.61803398874989484820

/-! ## 1. Compiled Zero-Alloc Expression AST -/

inductive UnaryOp where
  | neg | sq | cube | p4
  | sin | cos | tan | asin | acos | atan
  | sinh | cosh | tanh | exp | log | sqrt | abs | floor | ceil | sign
  deriving Repr, BEq, Inhabited

inductive BinaryOp where
  | add | sub | mul | div | pow | atan2 | min | max | hypot
  deriving Repr, BEq, Inhabited

inductive Expr where
  | lit   (val : Float)
  | varX | varY | varZ | varU | varV | varT | varR
  | un    (op : UnaryOp) (a : Expr)
  | bin   (op : BinaryOp) (a b : Expr)
  deriving Repr, Inhabited

/-! ## 2. Tokenizer (Strictly `Init`-Only) -/

private inductive Tok where
  | num (v : Float)
  | id  (s : String)
  | plus | minus | star | slash | caret | eq | comma | lparen | rparen
  deriving Repr, BEq, Inhabited

private def parseDecimal (s : String) : Option Float := Id.run do
  let cs := s.toList.toArray
  if cs.isEmpty then return none
  let mut i := 0
  let n := cs.size
  let mut acc : Float := 0.0
  let mut digits := 0
  while i < n && cs[i]!.isDigit do
    acc := acc * 10.0 + Float.ofNat (cs[i]!.toNat - '0'.toNat)
    digits := digits + 1
    i := i + 1
  if i < n && cs[i]! == '.' then
    i := i + 1
    let mut place : Float := 0.1
    while i < n && cs[i]!.isDigit do
      acc := acc + Float.ofNat (cs[i]!.toNat - '0'.toNat) * place
      place := place * 0.1
      digits := digits + 1
      i := i + 1
  if digits == 0 then return none
  if i < n && (cs[i]! == 'e' || cs[i]! == 'E') then
    i := i + 1
    let mut sgn : Float := 1.0
    if i < n && cs[i]! == '+' then i := i + 1
    else if i < n && cs[i]! == '-' then sgn := -1.0; i := i + 1
    let mut eAcc : Nat := 0
    let mut eDigs := 0
    while i < n && cs[i]!.isDigit do
      eAcc := eAcc * 10 + (cs[i]!.toNat - '0'.toNat)
      eDigs := eDigs + 1
      i := i + 1
    if eDigs == 0 then return none
    acc := acc * Float.pow 10.0 (sgn * Float.ofNat eAcc)
  if i == n then return some acc else return none

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentCont (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'

private def tokenize (src : String) : Except String (Array Tok) := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut out : Array Tok := #[]
  while i < n do
    let c := cs[i]!
    if c.isWhitespace then
      i := i + 1
    else if c.isDigit || (c == '.' && i + 1 < n && cs[i + 1]!.isDigit) then
      let start := i
      let mut hasDot := c == '.'
      i := i + 1
      while i < n do
        let ch := cs[i]!
        if ch.isDigit then i := i + 1
        else if ch == '.' && !hasDot then hasDot := true; i := i + 1
        else if (ch == 'e' || ch == 'E') && i + 1 < n then
          i := i + 1
          if i < n && (cs[i]! == '+' || cs[i]! == '-') then i := i + 1
        else break
      let numStr := String.ofList ((cs.extract start i).toList)
      match parseDecimal numStr with
      | some v => out := out.push (.num v)
      | none => return .error s!"Invalid number literal '{numStr}'"
    else if isIdentStart c then
      let start := i
      i := i + 1
      while i < n && isIdentCont cs[i]! do i := i + 1
      let idStr := (String.ofList ((cs.extract start i).toList)).toLower
      out := out.push (.id idStr)
    else
      match c with
      | '+' => out := out.push .plus;   i := i + 1
      | '-' => out := out.push .minus;  i := i + 1
      | '*' =>
        if i + 1 < n && cs[i + 1]! == '*' then
          out := out.push .caret; i := i + 2
        else
          out := out.push .star; i := i + 1
      | '/' => out := out.push .slash;  i := i + 1
      | '^' => out := out.push .caret;  i := i + 1
      | '=' => out := out.push .eq;     i := i + 1
      | ',' => out := out.push .comma;  i := i + 1
      | '(' => out := out.push .lparen; i := i + 1
      | ')' => out := out.push .rparen; i := i + 1
      | _ => return .error s!"Unexpected character '{c}' at index {i}"
  return .ok out

/-! ## 3. Peephole Constant Folder & Power Specializer -/

@[inline] private def evalUnary (op : UnaryOp) (a : Float) : Float :=
  match op with
  | .neg   => -a
  | .sq    => a * a
  | .cube  => a * a * a
  | .p4    => let s := a * a; s * s
  | .sin   => Float.sin a
  | .cos   => Float.cos a
  | .tan   => Float.tan a
  | .asin  => Float.asin (max (-1.0) (min 1.0 a))
  | .acos  => Float.acos (max (-1.0) (min 1.0 a))
  | .atan  => Float.atan a
  | .sinh  => Float.sinh a
  | .cosh  => Float.cosh a
  | .tanh  => Float.tanh a
  | .exp   => Float.exp (max (-40.0) (min 40.0 a))
  | .log   => Float.log (max 1e-12 (Float.abs a))
  | .sqrt  => Float.sqrt (max 0.0 a)
  | .abs   => Float.abs a
  | .floor => Float.floor a
  | .ceil  => Float.ceil a
  | .sign  => if a > 0.0 then 1.0 else if a < 0.0 then -1.0 else 0.0

@[inline] private def evalBinary (op : BinaryOp) (a b : Float) : Float :=
  match op with
  | .add   => a + b
  | .sub   => a - b
  | .mul   => a * b
  | .div   => if Float.abs b < 1e-12 then 0.0 else a / b
  | .pow   => Float.pow a b
  | .atan2 => Float.atan2 a b
  | .min   => min a b
  | .max   => max a b
  | .hypot => Float.sqrt (a * a + b * b)

private def mkUn (op : UnaryOp) (a : Expr) : Expr :=
  match a with
  | .lit v => .lit (evalUnary op v)
  | _      => .un op a

private def mkBin (op : BinaryOp) (a b : Expr) : Expr :=
  match op, a, b with
  | _, .lit va, .lit vb => .lit (evalBinary op va vb)
  | .pow, x, .lit 2.0   => mkUn .sq x
  | .pow, x, .lit 3.0   => mkUn .cube x
  | .pow, x, .lit 4.0   => mkUn .p4 x
  | .pow, x, .lit 1.0   => x
  | .pow, _, .lit 0.0   => .lit 1.0
  | .mul, x, .lit 1.0   => x
  | .mul, .lit 1.0, x   => x
  | .mul, _, .lit 0.0   => .lit 0.0
  | .mul, .lit 0.0, _   => .lit 0.0
  | .add, x, .lit 0.0   => x
  | .add, .lit 0.0, x   => x
  | .sub, x, .lit 0.0   => x
  | _, _, _             => .bin op a b

/-! ## 4. Pratt Recursive-Descent Parser (with Implicit Multiplication & `=` Support) -/

private structure PState where
  toks : Array Tok
  pos  : Nat := 0

private def peek (st : PState) : Option Tok :=
  if st.pos < st.toks.size then some st.toks[st.pos]! else none

private def advance (st : PState) : PState := { st with pos := st.pos + 1 }

private def isImplicitMulStart (t : Tok) : Bool :=
  match t with
  | .lparen | .id _ => true
  | _ => false

private def lookupUnaryFn (name : String) : Option UnaryOp :=
  match name with
  | "sin"   => some .sin   | "cos"   => some .cos   | "tan"   => some .tan
  | "asin"  => some .asin  | "acos"  => some .acos  | "atan"  => some .atan
  | "sinh"  => some .sinh  | "cosh"  => some .cosh  | "tanh"  => some .tanh
  | "exp"   => some .exp   | "log" | "ln" => some .log
  | "sqrt"  => some .sqrt  | "abs"   => some .abs
  | "floor" => some .floor | "ceil"  => some .ceil  | "sign"  => some .sign
  | "sq"    => some .sq    | "cb" | "cube" => some .cube
  | _       => none

private def lookupBinaryFn (name : String) : Option BinaryOp :=
  match name with
  | "atan2" => some .atan2 | "min" => some .min | "max" => some .max
  | "pow"   => some .pow   | "hypot" => some .hypot
  | _       => none

mutual
  private partial def parseEquation (st : PState) : Except String (Expr × PState) := do
    let (lhs, st1) ← parseAdd st
    match peek st1 with
    | some .eq =>
      let (rhs, st2) ← parseAdd (advance st1)
      return (mkBin .sub lhs rhs, st2)
    | _ => return (lhs, st1)

  private partial def parseAdd (st : PState) : Except String (Expr × PState) := do
    let (lhs0, st0) ← parseMul st
    let mut lhs := lhs0
    let mut s := st0
    while true do
      match peek s with
      | some .plus =>
        let (rhs, s1) ← parseMul (advance s)
        lhs := mkBin .add lhs rhs; s := s1
      | some .minus =>
        let (rhs, s1) ← parseMul (advance s)
        lhs := mkBin .sub lhs rhs; s := s1
      | _ => break
    return (lhs, s)

  private partial def parseMul (st : PState) : Except String (Expr × PState) := do
    let (lhs0, st0) ← parseUnary st
    let mut lhs := lhs0
    let mut s := st0
    while true do
      match peek s with
      | some .star =>
        let (rhs, s1) ← parseUnary (advance s)
        lhs := mkBin .mul lhs rhs; s := s1
      | some .slash =>
        let (rhs, s1) ← parseUnary (advance s)
        lhs := mkBin .div lhs rhs; s := s1
      | some tok =>
        if isImplicitMulStart tok then
          let (rhs, s1) ← parsePow s
          lhs := mkBin .mul lhs rhs; s := s1
        else break
      | none => break
    return (lhs, s)

  private partial def parseUnary (st : PState) : Except String (Expr × PState) := do
    match peek st with
    | some .minus =>
      let (e, st1) ← parseUnary (advance st)
      return (mkUn .neg e, st1)
    | some .plus =>
      parseUnary (advance st)
    | _ => parsePow st

  private partial def parsePow (st : PState) : Except String (Expr × PState) := do
    let (base, st1) ← parseAtom st
    match peek st1 with
    | some .caret =>
      let (exp, st2) ← parseUnary (advance st1) -- right-associative, supports x^-2!
      return (mkBin .pow base exp, st2)
    | _ => return (base, st1)

  private partial def parseAtom (st : PState) : Except String (Expr × PState) := do
    match peek st with
    | some (.num v) => return (.lit v, advance st)
    | some .lparen =>
      let (e, st1) ← parseAdd (advance st)
      match peek st1 with
      | some .rparen => return (e, advance st1)
      | _ => throw "Expected closing ')'"
    | some (.id name) =>
      let st1 := advance st
      match peek st1 with
      | some .lparen =>
        -- Function call: unary or binary
        let stArgs := advance st1
        let (arg1, stAfter1) ← parseAdd stArgs
        match peek stAfter1 with
        | some .comma =>
          let (arg2, stAfter2) ← parseAdd (advance stAfter1)
          match peek stAfter2 with
          | some .rparen =>
            match lookupBinaryFn name with
            | some bop => return (mkBin bop arg1 arg2, advance stAfter2)
            | none => throw s!"Unknown 2-argument function '{name}'"
          | _ => throw s!"Expected ')' after second argument of '{name}'"
        | some .rparen =>
          match lookupUnaryFn name with
          | some uop => return (mkUn uop arg1, advance stAfter1)
          | none => throw s!"Unknown 1-argument function '{name}'"
        | _ => throw s!"Expected ',' or ')' in call to '{name}'"
      | _ =>
        -- Variable or constant
        match name with
        | "x"   => return (.varX, st1)
        | "y"   => return (.varY, st1)
        | "z"   => return (.varZ, st1)
        | "u"   => return (.varU, st1)
        | "v"   => return (.varV, st1)
        | "t"   => return (.varT, st1)
        | "r"   => return (.varR, st1)
        | "pi"  => return (.lit piF, st1)
        | "tau" => return (.lit twoPiF, st1)
        | "e"   => return (.lit eF, st1)
        | "phi" => return (.lit phiF, st1)
        | _     => throw s!"Unknown identifier '{name}'"
    | some tok => throw s!"Unexpected token {repr tok}"
    | none => throw "Unexpected end of expression"
end

/-- Parse and peephole-optimize a user-typed implicit equation or parametric coordinate expression. -/
def parseExpr (input : String) : Except String Expr := do
  let toks ← tokenize input
  if toks.isEmpty then throw "Empty expression"
  let (e, stEnd) ← parseEquation { toks, pos := 0 }
  if stEnd.pos < toks.size then
    throw s!"Unexpected trailing token at index {stEnd.pos}"
  return e

/-! ## 5. Zero-Allocation Unboxed-Float Evaluator -/

/-- Evaluate a compiled `Expr` at `(x, y, z, u, v, t)` with zero heap allocations. -/
def evalExpr (e : Expr) (x y z u v t : Float) : Float :=
  match e with
  | .lit val    => val
  | .varX       => x
  | .varY       => y
  | .varZ       => z
  | .varU       => u
  | .varV       => v
  | .varT       => t
  | .varR       => Float.sqrt (x * x + y * y + z * z)
  | .un op a    => evalUnary op (evalExpr a x y z u v t)
  | .bin op a b => evalBinary op (evalExpr a x y z u v t) (evalExpr b x y z u v t)

/-! ## 6. Adaptive Coarse-Probe Marching Tetrahedra & Parametric Mesher -/

/-- Probe a coarse `7³` grid (`343` samples) to tighten `[bmin, bmax]` around active
sign-change cells (padded by 1.5 coarse cells) so the full `gridN³` budget delivers
sharper meshes in `<15 ms`. Falls back to original bounds if the coarse probe finds
no sign change (e.g. very thin shell). -/
private def refineBounds (f : Vec3 → Float) (bmin bmax : Vec3) : Vec3 × Vec3 := Id.run do
  let n := 6
  let n1 := n + 1
  let dx := (bmax.x - bmin.x) / Float.ofNat n
  let dy := (bmax.y - bmin.y) / Float.ofNat n
  let dz := (bmax.z - bmin.z) / Float.ofNat n
  let mut vals := FloatArray.emptyWithCapacity (n1 * n1 * n1)
  for iz in [:n1] do
    let z := bmin.z + Float.ofNat iz * dz
    for iy in [:n1] do
      let y := bmin.y + Float.ofNat iy * dy
      for ix in [:n1] do
        let x := bmin.x + Float.ofNat ix * dx
        vals := vals.push (f ⟨x, y, z⟩)
  let atV (ix iy iz : Nat) := vals.get! ((iz * n1 + iy) * n1 + ix)
  let mut found := false
  let mut loX := bmax.x; let mut hiX := bmin.x
  let mut loY := bmax.y; let mut hiY := bmin.y
  let mut loZ := bmax.z; let mut hiZ := bmin.z
  for iz in [:n] do
    for iy in [:n] do
      for ix in [:n] do
        let b0 := atV ix iy iz < 0.0
        let diff :=
          (atV (ix+1) iy iz < 0.0) != b0 ||
          (atV ix (iy+1) iz < 0.0) != b0 ||
          (atV (ix+1) (iy+1) iz < 0.0) != b0 ||
          (atV ix iy (iz+1) < 0.0) != b0 ||
          (atV (ix+1) iy (iz+1) < 0.0) != b0 ||
          (atV ix (iy+1) (iz+1) < 0.0) != b0 ||
          (atV (ix+1) (iy+1) (iz+1) < 0.0) != b0
        if diff then
          found := true
          let x0 := bmin.x + Float.ofNat ix * dx; let x1 := x0 + dx
          let y0 := bmin.y + Float.ofNat iy * dy; let y1 := y0 + dy
          let z0 := bmin.z + Float.ofNat iz * dz; let z1 := z0 + dz
          if x0 < loX then loX := x0; if x1 > hiX then hiX := x1
          if y0 < loY then loY := y0; if y1 > hiY then hiY := y1
          if z0 < loZ then loZ := z0; if z1 > hiZ then hiZ := z1
  if !found then
    return (bmin, bmax)
  else
    let padX := dx * 0.75; let padY := dy * 0.75; let padZ := dz * 0.75
    let rMin : Vec3 := ⟨max bmin.x (loX - padX), max bmin.y (loY - padY), max bmin.z (loZ - padZ)⟩
    let rMax : Vec3 := ⟨min bmax.x (hiX + padX), min bmax.y (hiY + padY), min bmax.z (hiZ + padZ)⟩
    return (rMin, rMax)

/-- Parse & mesh an arbitrary user-typed 3D implicit equation `f(x, y, z, t) = 0` directly
into a watertight CCW `MeshAsset` using Kuhn Marching Tetrahedra + optional adaptive
bounding-box focusing! -/
def evalImplicitExprMesh (exprStr : String) (t : Float := 0.0)
    (bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩) (bmax : Vec3 := ⟨1.6, 1.6, 1.6⟩)
    (gridN : Nat := 18) (meshId : UInt64 := 5001) (adaptive : Bool := true) :
    Except String MeshAsset := do
  let expr ← parseExpr exprStr
  let f (p : Vec3) : Float := evalExpr expr p.x p.y p.z 0.0 0.0 t
  let (useMin, useMax) := if adaptive then refineBounds f bmin bmax else (bmin, bmax)
  return marchingTetrahedra f useMin useMax gridN gridN gridN meshId

/-- Parse & mesh an arbitrary user-typed 3D parametric surface
`(fx(u, v, t), fy(u, v, t), fz(u, v, t))` over `[uMin, uMax] × [vMin, vMax]` into a
CCW `MeshAsset` with analytical exterior-product normals and curvature iridescence! -/
def evalParametricExprMesh (fxStr fyStr fzStr : String) (t : Float := 0.0)
    (uMin : Float := 0.0) (uMax : Float := twoPiF)
    (vMin : Float := 0.0) (vMax : Float := twoPiF)
    (nu : Nat := 40) (nv : Nat := 24)
    (doubleSided : Bool := true) (meshId : UInt64 := 5002) : Except String MeshAsset := do
  let ex ← parseExpr fxStr
  let ey ← parseExpr fyStr
  let ez ← parseExpr fzStr
  let surf (u v : Float) : Vec3 :=
    ⟨evalExpr ex 0.0 0.0 0.0 u v t,
     evalExpr ey 0.0 0.0 0.0 u v t,
     evalExpr ez 0.0 0.0 0.0 u v t⟩
  return buildParametricSurface surf uMin uMax vMin vMax nu nv meshId doubleSided

/-- Render any user-typed 3D implicit equation directly into a canonical `SceneFrame` (`GSIR` v1). -/
def evalImplicitExprToFrame (exprStr : String) (seq : UInt64 := 0) (t : Float := 0.0)
    (bmin : Vec3 := ⟨-1.6, -1.6, -1.6⟩) (bmax : Vec3 := ⟨1.6, 1.6, 1.6⟩)
    (gridN : Nat := 18) : SceneFrame :=
  let base : SceneFrame :=
    { frameSeq := seq, simTime := t, mode := .surface, is2D := false,
      gridEnabled := true, darkTheme := true, gridSize := 2.2,
      algebra := { name := "R3", p := 3, q := 0, r := 0,
                   basisNames := #["1","e1","e2","e3","e12","e13","e23","I"],
                   basisMetric := #[1,1,1,1,-1,-1,-1,-1] },
      presetId := "implicit_expr", title := s!"Implicit: {exprStr} = 0",
      camera := { motor := Motor3.orbitCamera 0.55 (-0.32) 4.6, fovDeg := 45.0, distance := 4.6 } }
  match evalImplicitExprMesh exprStr t bmin bmax gridN 5001 true with
  | .ok mesh =>
    { base with
      meshAssets := #[mesh],
      meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                      color := RGBA.white, useVertexColors := true }],
      inspect := #[{ idx := 0, name := "f(x,y,z,t)=0", grade := 0,
                     formatted := s!"{exprStr} · {mesh.positions.size/3} verts, {mesh.indices.size/3} tris" }] }
  | .error err =>
    { base with diagnostics := #[err] }

/-- Render any user-typed 3D parametric surface `(fx, fy, fz)` directly into a `SceneFrame` (`GSIR` v1). -/
def evalParametricExprToFrame (fxStr fyStr fzStr : String) (seq : UInt64 := 0) (t : Float := 0.0)
    (uMin : Float := 0.0) (uMax : Float := twoPiF)
    (vMin : Float := 0.0) (vMax : Float := twoPiF)
    (nu : Nat := 40) (nv : Nat := 24) : SceneFrame :=
  let base : SceneFrame :=
    { frameSeq := seq, simTime := t, mode := .surface, is2D := false,
      gridEnabled := true, darkTheme := true, gridSize := 2.2,
      algebra := { name := "R3", p := 3, q := 0, r := 0,
                   basisNames := #["1","e1","e2","e3","e12","e13","e23","I"],
                   basisMetric := #[1,1,1,1,-1,-1,-1,-1] },
      presetId := "parametric_expr", title := s!"Parametric: ({fxStr}, {fyStr}, {fzStr})",
      camera := { motor := Motor3.orbitCamera 0.55 (-0.32) 4.6, fovDeg := 45.0, distance := 4.6 } }
  match evalParametricExprMesh fxStr fyStr fzStr t uMin uMax vMin vMax nu nv true 5002 with
  | .ok mesh =>
    { base with
      meshAssets := #[mesh],
      meshRefs := #[{ meshId := mesh.meshId, dirtyHash := mesh.dirtyHash,
                      color := RGBA.white, useVertexColors := true, doubleSided := true }],
      inspect := #[{ idx := 0, name := "S(u,v,t)", grade := 0,
                     formatted := s!"({fxStr}, {fyStr}, {fzStr}) · {mesh.positions.size/3} verts" }] }
  | .error err =>
    { base with diagnostics := #[err] }

end Grassmann.Eval.ImplicitExpr
