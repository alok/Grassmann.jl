import Tests.Golden.DocsEval

/-!
# Displays and operators of the docs interpreter

Julia's displays of composite values (tuples, vectors with their element-type prefix,
`typeof`, bases, function objects), the oracle encoding of every value, and the binary
operators between elements and numbers, each mapped onto the dynamic layer (`Grassmann.TA`)
after Julia's coefficient promotion.
-/

namespace Tests.ElementOracle.Docs

open Grassmann DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase
  Tests.ElementOracle Tests.ElementOracle.Dyn

/-! ## Displays -/

/-- Julia's name of a coefficient type. -/
def typeName (t : CoeffType) : String :=
  match t with
  | .int64 => "Int64" | .rational => "Rational{Int64}" | .float64 => "Float64" | .bool => "Bool"
  | .complex r => "Complex{" ++ (match r with
      | .int64 => "Int64" | .rational => "Rational{Int64}" | .float64 => "Float64" | _ => "?") ++ "}"
  | .other s => s

/-- Julia's display of a chain of the subspace `mask` (only the subspace's blades, with the
parent's labels: `V(2,3,4)(x)` of `S"∞+++"` prints `1.40532v₁ + …` without `v∞`). -/
def subChainStr {V : TensorBundle} (mask : UInt64) (compact : Bool) (x : AnyTA V) : Option String :=
  let go := fun {α : Type} [Coeff α] [JuliaShow α] (t : TA V α) => match t with
    | .chain g c =>
      some (TA.showTerms V compact ((layoutTerms V (.chain g) c.v).filter fun (b, _) => b &&& ~~~mask == 0))
    | _ => none
  match x with
  | .int t => go t | .rat t => go t | .float t => go t | .bool t => go t
  | .cint t => go t | .crat t => go t | .cfloat t => go t

/-- The encoded element (kind, grade, bits, dense, strings) of an element value, with its
space display and, for an element of a subspace, the subspace's own layout and display. -/
def encodeElem (V : TensorBundle) (hdl : String) (mask : UInt64) (x : AnyTA V) : GoldenElem :=
  let e := x.encode
  let e := { e with V := some hdl }
  if mask == lowMask V.n then e else
    -- compress to the subspace spanned by `mask`
    let k := popcount mask
    let gens := (List.range V.n).filter fun i => testBit mask i
    let up := fun (b : UInt64) => (List.range k).foldl (fun acc j =>
      if testBit b j then acc ||| ((1 : UInt64) <<< (gens.getD j 0).toUInt64) else acc) (0 : UInt64)
    let down := fun (b : UInt64) => (List.range k).foldl (fun acc j =>
      if testBit b (gens.getD j 0) then acc ||| ((1 : UInt64) <<< j.toUInt64) else acc) (0 : UInt64)
    let idx := (Leibniz.indexBasisAll k).map fun b => Leibniz.basisRank V.n (up b)
    let pick := fun (v : FloatArray) => idx.foldl (fun acc i => acc.push (v.get! i)) FloatArray.empty
    let dense := e.dense.map fun d =>
      match d with
      | .exact v => .exact (idx.map fun i => v[i]!)
      | .float v => .float (pick v)
      | .complexExact re im => .complexExact (idx.map fun i => re[i]!) (idx.map fun i => im[i]!)
      | .complexFloat re im => .complexFloat (pick re) (pick im)
      | .raw v => .raw v
    let e := { e with dense, bits := e.bits.map down }
    match subChainStr mask false x, subChainStr mask true x with
    | some s, some c => { e with str := .val s, compactStr := .val c }
    | _, _ => e

/-- The encoding of a term of a large space (`n > 10`): the oracle records no dense vector
there (schema §7: sparse `terms`), so kind, `T`, `grade`, `bits` and the strings are
compared; containers of large spaces are not modelled. -/
def encodeBig {V : TensorBundle} (hdl : String) (x : AnyTA V) : Option GoldenElem :=
  let lite := fun {α : Type} [Coeff α] [JuliaShow α] [OracleScalar α] (t : TA V α) =>
    match t with
    | .zero | .one | .blade _ | .single .. =>
      some {
        kind := kindOf t.kind, T := some (resultT t.kind (OracleScalar.T α)), V := some hdl
        grade := t.grade?, bits := t.bits?, str := .val t.showString, compactStr := .val t.showCompact }
    | _ => none
  match x with
  | .int t => lite t | .rat t => lite t | .float t => lite t | .bool t => lite t
  | .cint t => lite t | .crat t => lite t | .cfloat t => lite t

/-- Spaces up to this many generators have dense encodings. -/
def denseLimit : Nat := 10

/-- The Julia type name of an element (`typeof(x)`), where the docs print it. -/
def elemTypeName {V : TensorBundle} (hdl : String) (x : AnyTA V) : Option String :=
  let e := x.encode
  let T := typeName x.T
  let g := e.grade.getD 0
  match e.kind with
  | .chain => some ("Chain{" ++ hdl ++ ", " ++ toString g ++ ", " ++ T ++ ", " ++
      toString (Leibniz.binomial V.n g) ++ "}")
  | .multivector => some ("Multivector{" ++ hdl ++ ", " ++ T ++ ", " ++ toString (2 ^ V.n) ++ "}")
  | .spinor =>
    if halfDim V.n false == 4 then some ("Quaternion{" ++ hdl ++ ", " ++ T ++ "}")
    else some ("Spinor{" ++ hdl ++ ", " ++ T ++ ", " ++ toString (halfDim V.n false) ++ "}")
  | .couple =>
    let b := V.bladeLabel (e.bits.getD 0)
    some ((if x.T == .int64 then "GaussianInteger{" else "Couple{") ++ hdl ++ ", " ++ b ++ ", " ++ T ++ "}")
  | .pseudoCouple => some ("PseudoCouple{" ++ hdl ++ ", " ++ V.bladeLabel (e.bits.getD 0) ++ ", " ++ T ++ "}")
  | _ => none

/-- The element-type prefix Julia prints before a `Vector` (empty for `Int64`/`Float64`
vectors; `Submanifold{V}`, `Single{V, G, B, T} where B`, … for algebra elements). -/
def vecPrefix (xs : Array Val) : Option String := do
  if xs.all (fun | .num (.int _) => true | _ => false) then return ""
  if xs.all (fun | .num (.float _) => true | _ => false) then return ""
  let es ← xs.mapM fun
    | .elem V hdl _ x => if V.n > denseLimit then none else some (hdl, x.encode, x.T)
    | _ => none
  let some (hdl, _, T) := es[0]? | none
  let kinds := es.map (·.2.1.kind)
  let T := typeName T
  if kinds.all (fun k => k == .submanifold || k == .one) then return "Submanifold{" ++ hdl ++ "}"
  if kinds.all (· == .single) then
    let gs := es.map (·.2.1.grade.getD 0)
    if gs.all (· == gs.getD 0 0) then
      return "Single{" ++ hdl ++ ", " ++ toString (gs.getD 0 0) ++ ", B, " ++ T ++ "} where B"
    else return "Single{" ++ hdl ++ ", _A, _B, " ++ T ++ "} where {_A, _B}"
  if kinds.all (fun k => k == .single || k == .one) && es.all (·.2.1.grade == some 0) then
    return "TensorTerm{" ++ hdl ++ ", 0, " ++ T ++ "}"
  none

/-- Julia `show(x)` of a value (`none` where the display is not modelled). -/
partial def showVal (sandbox : Nat) : Val → Option String
  | .num n => some (n.showJ false)
  | .elem V hdl _ x => if V.n > denseLimit then (encodeBig hdl x).bind (·.str?) else x.encode.str?
  | .space V m sub => some (if sub then V.showSub m else toString V)
  | .basis V m =>
    if m == lowMask V.n then some V.showBasis
    else
      let bs := (Leibniz.indexBasisAll V.n).filter fun b => b &&& ~~~m == 0
      some ("DirectSum.Basis{" ++ V.showSub m ++ "," ++ toString bs.size ++ "}("
        ++ ", ".intercalate (bs.map (V.bladeLabel ·)).toList ++ ")")
  | .tuple xs => do
    let ss ← xs.mapM (showVal sandbox)
    return "(" ++ ", ".intercalate ss.toList ++ (if ss.size == 1 then ",)" else ")")
  | .vec xs => do
    let ss ← xs.mapM (showVal sandbox)
    return (← vecPrefix xs) ++ "[" ++ ", ".intercalate ss.toList ++ "]"
  | .values xs => some ("[" ++ ", ".intercalate (xs.map (·.showJ false)).toList ++ "]")
  | .user f _ _ => some ("Main.DocSandbox" ++ toString sandbox ++ ".var\"#" ++ f ++ "\"()")
  | .nothing => some "nothing"
  | .opaque d => some d
  | _ => none

/-- A number as an oracle element. -/
def encodeNum (n : Num) : Option GoldenElem :=
  let one := fun (x : Float) => (FloatArray.emptyWithCapacity 1).push x
  let mk := fun (k : Kind) (t : CoeffType) (v : Coeffs) =>
    let e : GoldenElem := { kind := k, T := some t, value := some v }
    some { e with str := Field.val (n.showJ false), compactStr := Field.val (n.showJ true) }
  match n with
  | .int k => mk .number .int64 (.exact #[(k : Rat)])
  | .rat q => mk .number .rational (.exact #[q])
  | .float x => mk .number .float64 (.float (one x))
  | .cint a b => mk .number (.complex .int64) (.complexExact #[(a : Rat)] #[(b : Rat)])
  | .cfloat a b => mk .number (.complex .float64) (.complexFloat (one a) (one b))
  | .bool b => mk .bool .bool (.exact #[if b then 1 else 0])
  | .pi => none

/-- A value as an oracle element (`none` where it is not modelled). -/
def encodeVal (sandbox : Nat) (v : Val) : Option GoldenElem :=
  match v with
  | .num n => encodeNum n
  | .elem V hdl m x => if V.n > denseLimit then encodeBig hdl x else some (encodeElem V hdl m x)
  | .space V m true => some { kind := .space, str := .val (V.showSub m), compactStr := .val (V.showSub m) }
  | _ => (showVal sandbox v).map fun s => { kind := .other, str := .val s }

/-! ## Elements across spaces -/

/-- Two elements in one space (Julia requires it; across spaces see `embedInto`). -/
def sameSpace {V W : TensorBundle} (x : AnyTA V) (y : AnyTA W) : Option (AnyTA V × AnyTA V) :=
  if h : W = V then some (x, h ▸ y) else none

/-- The element of `W` with the coefficients of `x : AnyTA V` (same blade masks), keeping the
kind: Julia's `interop` into the union of two plain signatures, one a prefix of the other
(`Λ(ℝ^2).v1 ∧ Λ(ℝ^3).v3`, docs `design.md:172`). -/
def embedInto {V : TensorBundle} (W : TensorBundle) (x : AnyTA V) : Option (AnyTA W) :=
  let go := fun {α : Type} [Coeff α] (t : TA V α) => (match t with
    | .zero => some .zero | .one => some .one | .infinity => some .infinity
    | .blade b => some (.blade b) | .single b v => some (.single b v)
    | .couple b re im => if popcount b == V.n && V.n != W.n then none else some (.couple b re im)
    | .chain g _ => some (.chain g (TA.chainOf W g t.coeff))
    | .spinor _ => some (.spinor (TA.halfOf W false t.coeff))
    | .cospinor _ => some (.cospinor (TA.halfOf W true t.coeff))
    | .multi _ => some (.multi (TA.multiOf W t.coeff))
    | _ => none : Option (TA W α))
  match x with
  | .int t => .int <$> go t | .rat t => .rat <$> go t | .float t => .float <$> go t
  | .bool t => .bool <$> go t | .cint t => .cint <$> go t | .crat t => .crat <$> go t
  | .cfloat t => .cfloat <$> go t

/-- Whether `V` is a plain signature whose generators are the first ones of `W` (the union
`V ∪ W` is then `W`). -/
def prefixOf (V W : TensorBundle) : Bool :=
  V.n ≤ W.n && V.dyadmode == 0 && W.dyadmode == 0 && !V.istangent && !W.istangent &&
    !V.hasconformal && !W.hasconformal &&
    (match V.metric, W.metric with
     | .signature s, .signature t => s == t &&& lowMask V.n
     | _, _ => false)

/-! ## Binary operators -/

/-- Whether the geometric product of two terms of a tangent space has a tensor-valued
coefficient (a repeated `∂`, DirectSum's `BladeResult.nested`), which a scalar `TA` cannot
hold. -/
def nestedProduct {V : TensorBundle} (a b : AnyTA V) : Bool :=
  match a.blade?, b.blade? with
  | some x, some y => match V.apply₂ .mul x y with
    | .ok (.nested ..) => true
    | _ => false
  | _, _ => true

/-- Julia's binary operator `op` between two elements of one space, after promotion. -/
def elemBin (op : String) {V : TensorBundle} (a b : AnyTA V) : Option Val :=
  -- dyadic spaces (Julia's results live in sub-bundles) and tangent products with
  -- tensor-valued coefficients (`∂₁⊗∂₁v₁`) are not modelled
  if V.isdyadic || (V.istangent && nestedProduct a b) then none else
  let rev := fun (x : AnyTA V) => x.un fun y => TA.reverse y
  let el := fun (r : Option (AnyTA V)) => r.map (mkElem V)
  -- Julia reverses the divisor in its own coefficient type before `/` promotes it
  let divide := fun (ldiv : Bool) => do
    let (num, den) := if ldiv then (b, a) else (a, b)
    let rden := rev den
    let num ← forDiv num
    let den' ← forDiv den
    let rden ← forDiv rden
    let T ← CoeffType.promote num.T den'.T
    match ← num.promoteTo T, ← den'.promoteTo T, ← rden.promoteTo T with
    | .float x, .float y, .float ry =>
      el ((if ldiv then (TA.invWith? y ry).map (TA.mul · x) else TA.divWith? x y ry).map AnyTA.float)
    | .rat x, .rat y, .rat ry =>
      el ((if ldiv then (TA.invWith? y ry).map (TA.mul · x) else TA.divWith? x y ry).map AnyTA.rat)
    | _, _, _ => none
  match op with
  | "+" => el (bin2 a b fun x y => TA.add x y)
  | "-" => el (elemSub a b)
  | "*" | "⟑" | "⊖" => el (bin2 a b fun x y => TA.mul x y)
  | "∧" => el (bin2 a b fun x y => TA.wedge x y)
  | "∨" => el (bin2 a b fun x y => TA.vee x y)
  | "⋅" | "|" | "⨽" | ">" => el (bin2 a b fun x y => TA.contraction x y)
  | "⨼" | "<" => el (bin2 b a fun x y => TA.contraction x y)
  | "×" => el (bin2 a b fun x y => TA.cross x y)
  | "<<" => el (bin2 b (rev a) fun x y => TA.contraction x y)
  | ">>" => el (bin2 (rev a) b fun x y => TA.contraction x y)
  | "∗" => el (bin2 (rev a) b fun x y => TA.mul x y)
  | "⊛" => el (bin2 a b fun x y => TA.scalarprod x y)
  | "⊘" => do
    let T ← CoeffType.promote a.T b.T
    el (AnyTA.nary T (fun xs => TA.sandwichWith xs[0]! xs[1]! xs[2]! xs[3]! xs[4]!)
      #[a, b, rev b, b.un fun y => TA.involute y, b.un fun y => TA.clifford y])
  | ">>>" => do
    let T ← CoeffType.promote a.T b.T
    el (AnyTA.nary T (fun xs => TA.tsandwichWith xs[0]! xs[1]! xs[2]!) #[a, a.un fun y => TA.clifford y, b])
  | "==" => do
    let T ← CoeffType.promote a.T b.T
    match ← a.promoteTo T, ← b.promoteTo T with
    | .int x, .int y => some (.num (.bool (TA.equal x y)))
    | .rat x, .rat y => some (.num (.bool (TA.equal x y)))
    | .float x, .float y => some (.num (.bool (TA.equal x y)))
    | _, _ => none
  | "≈" => do
    let x ← toF a
    let y ← toF b
    some (.num (.bool (TA.isapprox x y)))
  | "∥" => do
    let r ← bin2 a b fun x y => TA.wedge x y
    let w ← toF r
    some (.num (.bool (TA.iszero w)))
  | "/" => divide false
  | "\\" => divide true
  | _ => none

/-- Julia `x op n` for an element and a number (`numFirst`: `n op x`). -/
def elemNum (op : String) {V : TensorBundle} (x : AnyTA V) (n : Num) (numFirst : Bool) : Option Val :=
  let el := fun (r : Option (AnyTA V)) => r.map (mkElem V)
  -- `π*v₁` keeps an `Irrational` coefficient in Julia; dyadic spaces are not modelled
  if (n matches .pi) && (op == "*" || op == "+" || op == "-") then none else
  if V.isdyadic then none else
  match op, numFirst with
  | "+", false => el (withNumber x n none fun t s => TA.addNum t s)
  | "+", true => el (withNumber x n none fun t s => TA.numAdd s t)
  | "-", false => el (withNumber x n none fun t s => TA.subNum t s)
  | "-", true => el (withNumber x n none fun t s => TA.numSub s t)
  | "*", false => el (withNumber x n none fun t s => TA.mulScalar t s)
  | "*", true => el (withNumber x n none fun t s => TA.smul s t)
  | "/", false => do
    -- Julia `/`: `Int64` coefficients divide as `Float64`
    let x ← forDiv x
    let T ← CoeffType.promote x.T n.T
    let T := if T == .int64 then .float64 else T
    match ← x.promoteTo T, ← n.lift T with
    | .float t, .float s => el (some (.float (TA.divScalar t s)))
    | .rat t, .rat s => el (some (.rat (TA.divScalar t s)))
    | _, _ => none
  | "//", false => do
    match ← x.promoteTo .rational, ← n.lift .rational with
    | .rat t, .rat s => el (some (.rat (TA.divScalar t s)))
    | _, _ => none
  | "/", true => do
    -- `n / x = n ⟑ inv(x)`
    let t ← toF x
    let i ← TA.inv? t
    el (withNumber (.float i) n none fun t s => TA.smul s t)
  | "^", false => do
    let k ← n.toInt?
    if k ≥ 0 then el (some (x.un fun t => TA.powNat t k.toNat))
    else
      let t ← toF x
      el (some (.float (TA.powInt t k)))
  | "^", true => do
    -- `b ^ t = exp(t ⟑ log(b))`
    let t ← toF x
    el (some (.float (TA.rpow n.toFloat t)))
  | _, _ => none

/-- Julia `a op b` for two numbers. -/
def numBin (op : String) (a b : Num) : Option Val :=
  match op with
  | "+" | "-" | "*" => (Num.arith op a b).map .num
  | "/" => (Num.fdiv a b).map .num
  | "//" => do
    match ← a.toInt?, ← b.toInt? with
    | x, y => some (.num (.rat (mkRat x y.toNat * (if y < 0 then -1 else 1))))
  | "^" => do
    match a, b with
    | .int x, .int y => if y ≥ 0 then some (.num (.int (x ^ y.toNat))) else none
    | _, _ => some (.num (.float (F64.pow a.toFloat b.toFloat)))
  | "==" => some (.num (.bool (a.toFloat == b.toFloat)))
  | "<" => some (.num (.bool (a.toFloat < b.toFloat)))
  | ">" => some (.num (.bool (a.toFloat > b.toFloat)))
  | _ => none

end Tests.ElementOracle.Docs
