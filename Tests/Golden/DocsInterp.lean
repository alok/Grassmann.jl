import Tests.Golden.DocsOps
import Grassmann.Basis

/-!
# The docs interpreter

`evalExpr` evaluates a parsed docs statement in the sandbox environment; `runStatements`
replays a shard's statements in order (Julia's REPL session) and encodes each value for the
oracle comparison. Built-in functions (`exp`, `inv`, `grade`, `typeof`, `Chain{V,1}(…)`,
`Λ(V)`, `@basis`, …) are dispatched by name in `callBuiltin`.
-/

namespace Tests.ElementOracle.Docs

open Grassmann DirectSum DirectSum.Bits StaticVectors AbstractTensors JuliaBase
  Tests.ElementOracle Tests.ElementOracle.Dyn

/-- Lift an `Option` into the evaluator (`none` is unsupported). -/
def need {β : Type} (what : String) : Option β → EvalM β
  | some x => pure x
  | none => unsupported what

/-- Lift an `Except String` into the evaluator. -/
def liftE {β : Type} : Except String β → EvalM β
  | .ok x => pure x
  | .error e => throw e

/-- A numeric literal. -/
def parseNum (s : String) : EvalM Num :=
  if s.any (fun c => c == '.' || c == 'e') then
    match F64.parse? s with
    | some x => pure (.float x)
    | none => unsupported s!"literal {s}"
  else match s.toNat? with
    | some k => pure (.int k)
    | none => unsupported s!"literal {s}"

/-- The element value of an `AnyTA` in the space of another element value (its display and
subspace are kept). -/
def likeElem (V : TensorBundle) (hdl : String) (m : UInt64) (x : AnyTA V) : Val := .elem V hdl m x

/-- Julia `f(x)` for an element and a dynamic unary map. -/
def mapElem (v : Val) (f : {V : TensorBundle} → AnyTA V → Option (AnyTA V)) : EvalM Val := do
  match v with
  | .elem V hdl m x => return .elem V hdl m (← need "map" (f x))
  | _ => unsupported "element expected"

/-- Julia's `Float64` composite functions on an element. -/
def floatFn (v : Val) (f : {V : TensorBundle} → [Kernels V] → TA V Float → Option (TA V Float)) : EvalM Val :=
  mapElem v fun x => viaFloat x f

/-- The elements a collection value iterates over (a tuple, a vector, the blades of a
basis). -/
def iterate : Val → EvalM (Array Val)
  | .tuple xs | .vec xs => pure xs
  | .values xs => pure (xs.map .num)
  | _ => unsupported "not iterable"

/-- The blades of the subspace `m` of `V`, as element values (Julia `Λ(V).b`). -/
def basisBlades (V : TensorBundle) (m : UInt64) : Array Val :=
  let hdl := if m == lowMask V.n then V.showHandle else V.showSub m
  ((Leibniz.indexBasisAll V.n).filter fun b => b &&& ~~~m == 0).map (bladeVal V hdl m ·)

/-- Numbers of a constructor's arguments (`Chain{V,1}(4,5,6)`, or one `Values`). -/
def numArgs (args : Array Val) : EvalM (Array Num) := do
  match args with
  | #[.values xs] => pure xs
  | _ => args.mapM fun
    | .num n => pure (if n matches .pi then .float F64.pi else n)
    | _ => unsupported "number expected"

/-- The common coefficient type of a list of numbers (Julia's `promote`). -/
def commonT (xs : Array Num) : EvalM CoeffType := do
  let some t0 := xs[0]? | unsupported "empty"
  xs.foldlM (fun t x => need "promote" (CoeffType.promote t x.T)) t0.T

/-- A container of layout `l` of `V` from its coefficients in storage order. -/
def containerOf {α : Type} [Coeff α] (V : TensorBundle) (l : Layout) (zs : Array α) : TA V α :=
  TA.ofLayout (V := V) l (Values.ofFn fun i => zs[i.1]!)

/-- A container (`layout`) of `V` from its numbers in storage order. -/
def mkContainer (V : TensorBundle) (layout : Layout) (xs : Array Num) : EvalM (AnyTA V) := do
  if xs.size != layout.size V.n then unsupported "length"
  let t ← commonT xs
  let ys ← need "promote" (xs.mapM (·.lift t))
  need "container" <| match t with
    | .int64 => .int <$> (containerOf V layout <$> ys.mapM fun | .int k => some k | _ => none)
    | .rational => .rat <$> (containerOf V layout <$> ys.mapM fun | .rat q => some q | _ => none)
    | .float64 => .float <$> (containerOf V layout <$> ys.mapM fun | .float x => some x | _ => none)
    | .complex .int64 =>
      .cint <$> (containerOf V layout <$> ys.mapM fun | .cint a b => some ⟨a, b⟩ | _ => none)
    | .complex .float64 =>
      .cfloat <$> (containerOf V layout <$> ys.mapM fun | .cfloat a b => some ⟨a, b⟩ | _ => none)
    | _ => none

/-- The numbers of an element in its storage order (Julia `value(t)`). -/
def storage {V : TensorBundle} (x : AnyTA V) : Option (Array Num) :=
  let e := x.encode
  let supp? := supportIndices V.n e.kind (e.grade.getD 0) (e.bits.getD 0)
  match supp?, e.dense with
  | some supp, some (.exact v) =>
    some (supp.map fun i => let q := v[i]!; if x.T == .rational then .rat q else .int q.num)
  | some supp, some (.float v) => some (supp.map fun i => .float (v.get! i))
  | _, _ => none

/-- An `Int64` number from a value. -/
def intArg : Val → EvalM Int
  | .num n => need "integer" n.toInt?
  | _ => unsupported "integer expected"

/-- Whether a value is an element of a large space (only looked up and displayed). -/
def isBig : Val → Bool
  | .elem V .. => V.n > denseLimit
  | _ => false

/-- The sandbox number of a shard name (`31-algebra-of-space.md-7` ↦ 31). -/
def sandboxOf (shard : String) : Nat :=
  (String.ofList (shard.toList.takeWhile Char.isDigit)).toNat?.getD 0

mutual

/-- Evaluate an expression. -/
partial def evalExpr (e : Expr) : EvalM Val := do
  match e with
  | .num s => return .num (← parseNum s)
  | .ident x => evalIdent x
  | .str pfx body =>
    match pfx with
    | "S" | "D" | "V" => return bare (← spaceMacro pfx body)
    | "basis" => doBasis (← liftE (TensorBundle.parseBundle body))
    | _ => unsupported s!"string macro {pfx}"
  | .mac m args => evalMacro m args
  | .call f args => do
    let args ← args.mapM evalExpr
    match f with
    | .ident x =>
      match (← get).vars.get? x with
      | some fv => callVal fv args
      | none => callBuiltin x #[] args
    | .curly (.ident c) ps => callBuiltin c (← ps.mapM evalExpr) args
    | .field (.ident "DirectSum") "Basis" => callBuiltin "DirectSum.Basis" #[] args
    | _ => callVal (← evalExpr f) args
  | .curly (.ident c) ps => return .ctor c (← ps.mapM evalExpr)
  | .curly .. => unsupported "type"
  | .index a args => indexVal (← evalExpr a) (← args.mapM evalExpr)
  | .field (.ident "DirectSum") f => return .fn ("DirectSum." ++ f)
  | .field a name => fieldVal (← evalExpr a) name
  | .bin op a b => do
    let x ← evalExpr a
    let y ← evalExpr b
    binVal op x y
  | .un op a => unVal op (← evalExpr a)
  | .adj a => do
    match ← evalExpr a with
    | .space V _ false => return bare (← liftE V.adjoint)
    | .space V m true => return .space (← liftE V.adjoint) m true
    | .basis V m => return .basis (← liftE V.adjoint) m
    | _ => unsupported "adjoint"
  | .tuple xs => return .tuple (← xs.mapM evalExpr)
  | .vect xs => do
    let vs ← xs.mapM evalExpr
    if vs.all (fun | .num _ => true | _ => false) then
      return .values (vs.filterMap fun | .num n => some n | _ => none)
    return .vec vs
  | .compr body x src => do
    let items ← iterate (← evalExpr src)
    let saved := (← get).vars
    let mut out : Array Val := #[]
    for it in items do
      setVar x it
      out := out.push (← evalExpr body)
    modify fun env => { env with vars := saved }
    return .vec out
  | .cmp ops xs => do
    let vs ← xs.mapM evalExpr
    let mut result : Option Val := none
    for i in [0:ops.size] do
      let r ← binVal ops[i]! vs[i]! vs[i + 1]!
      match r with
      | .num (.bool b) =>
        if !b then return .num (.bool false)
        result := some r
      | other =>
        -- `<`/`>` between elements are contractions (a single comparison only)
        if ops.size == 1 then return other else unsupported "chained non-Boolean comparison"
    return result.getD (.num (.bool true))
  | .assign lhs rhs => do
    let v ← evalExpr rhs
    bindPattern lhs v
    return v
  | .lam ps body => return .closure ps body (← get).vars.toList
  | .block xs => do
    let mut v : Val := .nothing
    for x in xs do v ← evalExpr x
    return v
  | .fdef f ps body => do
    let v := Val.user f ps body
    setVar f v
    return v
  | .ret x => evalExpr x

/-- Bind the value of an assignment. -/
partial def bindPattern (lhs : Expr) (v : Val) : EvalM Unit := do
  match lhs with
  | .ident x => setVar x v
  | .tuple xs => do
    let items ← iterate v
    if items.size < xs.size then unsupported "destructuring"
    for i in [0:xs.size] do bindPattern xs[i]! items[i]!
  | _ => unsupported "assignment target"

/-- An identifier: a variable, a constant, or a built-in function. -/
partial def evalIdent (x : String) : EvalM Val := do
  match (← get).vars.get? x with
  | some v => return v
  | none =>
    match x with
    | "π" => return .num .pi
    | "im" => return .num (.cint 0 1)
    | "true" => return .num (.bool true)
    | "false" => return .num (.bool false)
    | "nothing" => return .nothing
    | "Inf" => return .num (.float F64.inf)
    | "NaN" => return .num (.float F64.nan)
    | "ℝ" => return bare (TensorBundle.sig 1)
    | "ℝ0" | "ℝ1" | "ℝ2" | "ℝ3" | "ℝ4" | "ℝ5" | "ℝ6" | "ℝ7" | "ℝ8" | "ℝ9" =>
      return subOf (TensorBundle.euclidean ((x.drop 1).toString.toNat!))
    | "𝕚" => return mkElem ℝ3 (.int (.single 6 1))
    | "𝕛" => return mkElem ℝ3 (.int (.single 5 (-1)))
    | "𝕜" => return mkElem ℝ3 (.int (.single 3 1))
    | _ => return .fn x

/-- A macro call (`@basis V`, `@basis V E e`, `@dualbasis V`, `@mixedbasis V`). -/
partial def evalMacro (m : String) (args : Array Expr) : EvalM Val := do
  match m, args with
  | "basis", #[v] => let (V, _) ← asSpace (← evalExpr v); doBasis V
  | "basis", #[v, .ident e1, .ident e2] =>
    let (V, _) ← asSpace (← evalExpr v)
    doBasis V e1 (some e2)
  | "dualbasis", #[v] => let (V, _) ← asSpace (← evalExpr v); doBasis V.dual
  | "mixedbasis", #[v] =>
    let (V, _) ← asSpace (← evalExpr v)
    doBasis (← liftE (TensorBundle.oplus V V.dual))
  | _, _ => unsupported s!"macro @{m}"

/-- Call a value (a user function, a closure, an element's grade selection `A(g)`, a
built-in). -/
partial def callVal (f : Val) (args : Array Val) : EvalM Val := do
  match f with
  | .user _ ps body => withLocals ps args (← get).vars body
  | .closure ps body env => withLocals ps args (Std.HashMap.ofList env) body
  | .fn name => callBuiltin name #[] args
  | .ctor name ps => callBuiltin name ps args
  | .elem V hdl m x =>
    -- Julia `A(g)`: the grade-`g` part
    match args with
    | #[.num (.int g)] => return .elem V hdl m (x.un fun y => TA.gradeProj g.toNat y)
    | _ => unsupported "element call"
  | .space V m _ =>
    match args with
    | #[.fn "∇"] =>
      -- Julia `V(∇)` of a plain space: `v₁ + v₂ + ⋯` (tangent spaces: calculus, not modelled)
      if V.istangent || V.isdyadic then unsupported "∇ of a tangent space"
      let V' := V
      return mkElem V' (← mkContainer V' (.chain 1) (Array.replicate V'.n (.int 1)))
    | _ =>
      -- Julia `V(i, j, …)`: the subspace spanned by generators `i, j, …`
      let ks ← args.mapM intArg
      let mask := ks.foldl (fun acc k => acc ||| ((1 : UInt64) <<< (k.toNat - 1).toUInt64)) (0 : UInt64)
      if mask &&& ~~~m != 0 then unsupported "subspace"
      return .space V mask true
  | _ => unsupported "not callable"

/-- Run `body` with `params` bound to `args` on top of `scope`, restoring the variables
afterwards (Julia's local scope). -/
partial def withLocals (ps : Array String) (args : Array Val) (scope : Std.HashMap String Val)
    (body : Expr) : EvalM Val := do
  if ps.size != args.size then unsupported "arity"
  let env ← get
  if env.fuel == 0 then unsupported "recursion"
  let saved := env.vars
  let base := saved.fold (fun acc k v => if acc.contains k then acc else acc.insert k v) scope
  set { env with vars := (ps.zip args).foldl (fun acc (p, a) => acc.insert p a) base, fuel := env.fuel - 1 }
  let r ← evalExpr body
  modify fun e => { e with vars := saved, fuel := env.fuel }
  return r

/-- Indexing (`Λ(3)[3]`, `A[1]`, `t[i]`). -/
partial def indexVal (a : Val) (args : Array Val) : EvalM Val := do
  match a, args with
  | .basis V m, #[.num (.int i)] =>
    let bs := basisBlades V m
    need "index" bs[i.toNat - 1]?
  | .tuple xs, #[.num (.int i)] | .vec xs, #[.num (.int i)] => need "index" xs[i.toNat - 1]?
  | .values xs, #[.num (.int i)] => .num <$> need "index" xs[i.toNat - 1]?
  | .elem _ _ _ x, #[.num (.int g)] =>
    -- Julia `m[g]`: the grade-`g` values of a multivector
    match x.encode.kind with
    | .multivector =>
      let y := x.un fun t => TA.gradeProj g.toNat t
      return .values (← need "values" (storage y))
    | _ => unsupported "element index"
  | _, _ => unsupported "index"

/-- Field access (`Λ(3).v21`, `Λ(3).b`, `G4.v12`). -/
partial def fieldVal (a : Val) (name : String) : EvalM Val := do
  match a with
  | .basis V m | .space V m true =>
    if name == "b" then return .vec (basisBlades V m)
    let hdl := if m == lowMask V.n then V.showHandle else V.showSub m
    let r ← need s!"blade {name}" (V.lookup name)
    return ofBladeResult V hdl m r
  | _ => unsupported s!"field {name}"

/-- A binary operator on two values. -/
partial def binVal (op : String) (a b : Val) : EvalM Val := do
  if isBig a || isBig b then unsupported "large space"
  match a, b with
  | .num x, .num y => need s!"number {op}" (numBin op x y)
  | .elem V hdl m x, .elem W _ _ y =>
    match sameSpace x y with
    | some (x, y) =>
      let r ← need s!"element {op}" (elemBin op x y)
      return keepSpace hdl m r
    | none =>
      if prefixOf V W then
        let x' ← need "interop" (embedInto W x)
        need s!"element {op}" (elemBin op x' y)
      else if prefixOf W V then
        let y' ← need "interop" (embedInto V y)
        need s!"element {op}" (elemBin op x y')
      else unsupported "different spaces"
  | .elem _ hdl m x, .num n => keepSpace hdl m <$> need s!"element {op} number" (elemNum op x n false)
  | .num n, .elem _ hdl m x => keepSpace hdl m <$> need s!"number {op} element" (elemNum op x n true)
  | .space V _ _, .num (.int k) =>
    match op with
    | "^" => return bare (← liftE (V.pow k.toNat))
    | "==" => return .num (.bool (spaceEq V (TensorBundle.euclidean k.toNat)))
    | _ => unsupported "space op"
  | .basis V m, .basis W m' =>
    if op == "⊕" && m == lowMask V.n && m' == lowMask W.n then
      let U ← liftE (TensorBundle.oplus V W)
      return .basis U (lowMask U.n)
    else unsupported "basis op"
  | .space V _ _, .space W _ _ =>
    match op with
    | "⊕" | "+" => return bare (← liftE (TensorBundle.oplus V W))
    | "==" => return .num (.bool (spaceEq V W))
    | _ => unsupported "space op"
  | .values xs, .values ys =>
    if op == "+" && xs.size == ys.size then
      return .values (← need "values" ((xs.zip ys).mapM fun (x, y) => Num.arith "+" x y))
    else unsupported "values op"
  | _, _ => unsupported s!"operator {op}"
where
  /-- Keep the display/subspace of the left operand's space. -/
  keepSpace (hdl : String) (m : UInt64) : Val → Val
    | .elem V _ _ x => .elem V hdl m x
    | v => v

/-- A prefix operator. -/
partial def unVal (op : String) (a : Val) : EvalM Val := do
  if isBig a then unsupported "large space"
  match op, a with
  | "-", .num n => .num <$> need "neg" n.neg
  | "+", v => return v
  | "-", .elem V hdl m x => return .elem V hdl m (x.un fun y => TA.neg y)
  | "~", .elem V hdl m x => return .elem V hdl m (x.un fun y => TA.reverse y)
  | "!", .elem V hdl m x => return .elem V hdl m (x.complement fun y => TA.complementright y)
  | "⋆", .elem V hdl m x => return .elem V hdl m (x.un fun y => TA.hodge y)
  | "√", v => callBuiltin "sqrt" #[] #[v]
  | _, _ => unsupported s!"prefix {op}"

/-- Built-in functions and constructors (`params`: `Chain{V,1}`'s type parameters). -/
partial def callBuiltin (name : String) (params : Array Val) (args : Array Val) : EvalM Val := do
  if args.any isBig then unsupported "large space"
  let elem1 := fun (f : {V : TensorBundle} → AnyTA V → AnyTA V) => do
    match args with
    | #[.elem V hdl m x] => return Val.elem V hdl m (f x)
    | _ => unsupported s!"{name}: one element expected"
  let ffn := fun (f : {V : TensorBundle} → [Kernels V] → TA V Float → Option (TA V Float)) => do
    match args with
    | #[v@(.elem ..)] => floatFn v f
    | _ => unsupported s!"{name}: one element expected"
  let bin := fun (op : String) => do
    match args with
    | #[a, b] => binVal op a b
    | _ => unsupported s!"{name}: two arguments expected"
  match name with
  -- spaces
  | "Submanifold" =>
    match args with
    | #[.num (.int n)] => return subOf (TensorBundle.euclidean n.toNat)
    | #[.space V m _] => return .space V m true
    | _ => unsupported "Submanifold"
  | "Manifold" =>
    match args with
    | #[.num (.int n)] => return subOf (TensorBundle.euclidean n.toNat)
    | #[v] => let (V, m) ← asSpace v; return .space V m true
    | _ => unsupported "Manifold"
  | "Λ" | "DirectSum.Basis" =>
    match args with
    | #[.num (.int n)] => return .basis (TensorBundle.euclidean n.toNat) (lowMask n.toNat)
    | #[v] => let (V, m) ← asSpace v; return .basis V m
    | _ => unsupported "Λ"
  | "collect" =>
    match args with
    | #[.space V m true] => return .basis V m
    | #[.space V _ false] => return .opaque V.showCollect
    | _ => unsupported "collect"
  | "tangent" =>
    match args with
    | #[s] => let (V, _) ← asSpace s; return bare (V.tangent)
    | #[s, .num (.int μ)] => let (V, _) ← asSpace s; return bare (V.tangent μ.toNat)
    | #[s, .num (.int μ), .num (.int ν)] => let (V, _) ← asSpace s; return bare (V.tangent μ.toNat ν.toNat)
    | _ => unsupported "tangent"
  | "mdims" =>
    match args with
    | #[v] => let (V, m) ← asSpace v; return .num (.int (if m == lowMask V.n then V.n else popcount m))
    | _ => unsupported "mdims"
  | "Values" => return .values (← numArgs args)
  -- constructors
  | "Chain" | "Multivector" | "Spinor" | "CoSpinor" =>
    let xs ← numArgs args
    let V ← match params with
      | #[] =>
        -- no space: Julia infers `Submanifold(n)` from the length
        if name == "Chain" then pure (TensorBundle.euclidean xs.size)
        else if name == "Multivector" then
          pure (TensorBundle.euclidean ((List.range 12).find? (2 ^ · == xs.size)).get!)
        else pure (TensorBundle.euclidean (((List.range 12).find? (2 ^ · == 2 * xs.size)).getD 1))
      | ps => (·.1) <$> asSpace ps[0]!
    let layout : Layout ← match name, params with
      | "Chain", #[_, .num (.int g)] => pure (.chain g.toNat)
      | "Chain", _ => pure (.chain 1)
      | "Multivector", _ => pure .full
      | "Spinor", _ => pure .even
      | _, _ => pure .odd
    return mkElem V (← mkContainer V layout xs)
  | "Couple" =>
    let xs ← numArgs args
    let V := TensorBundle.euclidean 2
    match xs with
    | #[.int a, .int b] => return mkElem V (.int (.couple 3 a b))
    | #[.float a, .float b] => return mkElem V (.float (.couple 3 a b))
    | _ => unsupported "Couple"
  | "Single" =>
    match params, args with
    | #[s], #[.num n] =>
      let (V, _) ← asSpace s
      return mkElem V (← need "Single" (numTA V n))
    | _, _ => unsupported "Single"
  | "Zero" => let (V, _) ← asSpace (← need "Zero" args[0]?); return mkElem V (.int .zero)
  | "One" => let (V, _) ← asSpace (← need "One" args[0]?); return mkElem V (.int .one)
  | "quaternion" =>
    match ← numArgs args with
    | #[.int s, .int i, .int j, .int k] =>
      return mkElem ℝ3 (.int (.spinor (Spinor.quaternion s i j k)))
    | _ => unsupported "quaternion"
  | "quatvalues" | "quatvalue" =>
    match args with
    | #[.elem _ _ _ x] =>
      let xs ← need "quatvalues" (storage x)
      match xs with
      | #[a, b, c, d] => return .values #[a, b, ← need "neg" c.neg, d]
      | _ => unsupported "quatvalues"
    | _ => unsupported "quatvalues"
  | "complexify" =>
    match args with
    | #[.num n] => return .num n
    | #[.elem V _ _ x] =>
      match x.encode.kind, storage x with
      | .chain, some #[.int a, .int b] => return mkElem V (.int (.couple (lowMask V.n) a b))
      | .chain, some #[.float a, .float b] => return mkElem V (.float (.couple (lowMask V.n) a b))
      | .couple, _ => return args[0]!
      | _, _ => unsupported "complexify"
    | _ => unsupported "complexify"
  | "vectorize" =>
    match args with
    | #[.num (.cint a b)] =>
      let V := TensorBundle.euclidean 2
      return mkElem V (← mkContainer V (.chain 1) #[.int a, .int b])
    | #[.elem V _ _ x] =>
      match x with
      | .int (.couple b re im) => if b == lowMask V.n && V.n == 2 then
          return mkElem V (← mkContainer V (.chain 1) #[.int re, .int im]) else unsupported "vectorize"
      | _ => unsupported "vectorize"
    | _ => unsupported "vectorize"
  -- predicates and accessors
  | "typeof" =>
    match args with
    | #[.elem _ hdl _ x] => return .opaque (← need "typeof" (elemTypeName hdl x))
    | _ => unsupported "typeof"
  | "dump" => return .nothing
  | "value" =>
    match args with
    | #[.elem _ _ _ x] => return .values (← need "value" (storage x))
    | _ => unsupported "value"
  | "grade" =>
    match args with
    | #[.elem _ _ _ x] => return .num (.int (← need "grade" (x.encode.grade)))
    | #[.elem V hdl m x, .num (.int g)] => return .elem V hdl m (x.un fun y => TA.gradeProj g.toNat y)
    | _ => unsupported "grade"
  | "indices" =>
    match args with
    | #[.elem V _ _ x] =>
      let b ← need "indices" x.encode.bits
      let ids : Array Nat := ((List.range V.n).filter fun i => testBit b i).toArray
      return .values (ids.map fun (i : Nat) => Num.int (Int.ofNat (i + 1)))
    | _ => unsupported "indices"
  | "hyperplanes" =>
    match args with
    | #[s] =>
      let (V, _) ← asSpace s
      return .vec ((Grassmann.hyperplanes V).map fun h => mkElem V (.int (.single h.bits h.val)))
    | _ => unsupported "hyperplanes"
  | "norm" =>
    match args with
    | #[.elem _ _ _ x] => return .num (.float (← need "norm" x.norm))
    | #[.num n] => return .num (.float n.toFloat.abs)
    | _ => unsupported "norm"
  | "abs2" =>
    match args with
    | #[.elem V hdl m x] => return .elem V hdl m (← need "abs2" x.abs2)
    | _ => unsupported "abs2"
  | "isscalar" | "isvector" | "isbivector" | "istrivector" | "isvolume" | "iszero" | "isone"
  | "istensor" | "isgraded" | "isterm" =>
    match args with
    | #[.elem _ _ _ x] =>
      let t ← need name (toF x)
      return .num (.bool (match name with
        | "isscalar" => TA.isscalar t | "isvector" => TA.isvector t | "isbivector" => TA.isbivector t
        | "istrivector" => TA.istrivector t | "isvolume" => TA.isvolume t | "iszero" => TA.iszero t
        | "isone" => TA.isone t | "istensor" => TA.istensor t | "isgraded" => TA.isgraded t
        | _ => TA.isterm t))
    | _ => unsupported name
  -- unary maps
  | "reverse" => elem1 fun x => x.un fun y => TA.reverse y
  | "involute" => elem1 fun x => x.un fun y => TA.involute y
  | "clifford" => elem1 fun x => x.un fun y => TA.clifford y
  | "conj" => elem1 fun x => x.un fun y => TA.reverse y
  | "even" => elem1 fun x => x.un fun y => TA.even y
  | "odd" => elem1 fun x => x.un fun y => TA.odd y
  | "real" => elem1 fun x => x.un fun y => TA.realPart y
  | "imag" => elem1 fun x => x.un fun y => TA.imagPart y
  | "metric" => elem1 fun x => x.un fun y => TA.metric y
  | "antimetric" | "cometric" | "pseudometric" => elem1 fun x => x.un fun y => TA.antimetric y
  | "scalar" => elem1 fun x => x.un fun y => TA.scalar y
  | "vector" => elem1 fun x => x.un fun y => TA.vector y
  | "bivector" => elem1 fun x => x.un fun y => TA.bivector y
  | "trivector" => elem1 fun x => x.un fun y => TA.trivector y
  | "pseudoscalar" | "volume" => elem1 fun x => x.un fun y => TA.volume y
  | "complementright" => elem1 fun x => x.complement fun y => TA.complementright y
  | "complementleft" => elem1 fun x => x.complement fun y => TA.complementleft y
  | "complementrighthodge" | "hodge" => elem1 fun x => x.un fun y => TA.hodge y
  | "complementlefthodge" => elem1 fun x => x.un fun y => TA.complementlefthodge y
  -- products
  | "wedge" => bin "∧"
  | "vee" => bin "∨"
  | "contraction" => bin "⋅"
  | "sandwich" => bin "⊘"
  | "cross" => bin "×"
  | "wedgedot" => bin "*"
  -- composite functions (Julia's `Float64` results)
  | "exp" =>
    match args with
    | #[.num n] => return .num (.float (F64.exp n.toFloat))
    | _ => ffn fun t => some (TA.exp t)
  | "log" => ffn fun t => TA.log? t
  | "sqrt" =>
    match args with
    | #[.num n] => return .num (.float (Float.sqrt n.toFloat))
    | _ => ffn fun t => TA.root? 2 t
  | "cbrt" => ffn fun t => TA.root? 3 t
  | "inv" =>
    match args with
    | #[.elem V hdl m x] =>
      let rx := x.un fun y => TA.reverse y
      match ← need "inv" (forDiv x), ← need "inv" (forDiv rx) with
      | .float t, .float rt => return .elem V hdl m (.float (← need "inv" (TA.invWith? t rt)))
      | .rat t, .rat rt => return .elem V hdl m (.rat (← need "inv" (TA.invWith? t rt)))
      | _, _ => unsupported "inv"
    | _ => unsupported "inv"
  | "tdims" =>
    match args with
    | #[v] => let (V, _) ← asSpace v; return .num (.int (2 ^ V.n))
    | _ => unsupported "tdims"
  | "gdims" =>
    match args with
    | #[.num (.int n), .num (.int k)] => return .num (.int (Leibniz.binomial n.toNat k.toNat))
    | _ => unsupported "gdims"
  | "∠" =>
    match args with
    | #[.num (.float a), .elem V hdl m θ] =>
      let θ ← need "angle" (toF θ)
      return .elem V hdl m (.float (.phasor a θ))
    | _ => unsupported "∠"
  | "abs" => ffn fun t => TA.abs? t
  | "unit" => ffn fun t => (TA.abs? t).bind (TA.div? t)
  | "cos" =>
    match args with
    | #[.num n] => return .num (.float (F64.cos n.toFloat))
    | _ => ffn fun t => some (TA.cos t)
  | "sin" =>
    match args with
    | #[.num n] => return .num (.float (F64.sin n.toFloat))
    | _ => ffn fun t => TA.div? (TA.sinh (TA.mul (TA.pseudoI _) t)) (TA.pseudoI _)
  | "tan" => ffn fun t => TA.tan? t
  | "cosh" => ffn fun t => some (TA.cosh t)
  | "sinh" => ffn fun t => some (TA.sinh t)
  | "tanh" => ffn fun t => TA.tanh? t
  | "expm1" => ffn fun t => some (TA.expm1 t)
  | "log1p" => ffn fun t => TA.log1p? t
  | _ => unsupported s!"function {name}"

end

/-- Evaluate one statement: its value (Julia's `ans`) or an error. -/
def evalStatement (input : String) : EvalM Val := do
  let e ← liftE (parse input)
  let v ← evalExpr e
  match v with
  | .nothing => pure ()
  | _ => setVar "ans" v
  return v

/-- Replay a shard's statements in order; the result of each is its oracle encoding
(`none` when the statement is not modelled). -/
def runStatements (sandbox : Nat) (inputs : Array String) : Array (Option GoldenElem) := Id.run do
  let mut env : Env := { sandbox }
  let mut out : Array (Option GoldenElem) := #[]
  for inp in inputs do
    match (evalStatement inp).run env with
    | .ok (v, env') =>
      env := env'
      out := out.push (encodeVal sandbox v)
    | .error _ => out := out.push none
  return out

end Tests.ElementOracle.Docs
