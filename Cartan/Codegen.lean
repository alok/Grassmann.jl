import Grassmann

/-!
# Generated field kernels (elaboration-time code generation)

`cartan_field_kernels 2 3` emits, for the Euclidean spaces `ℝ2`, `ℝ3`, straight-line field
kernels for the Grassmann products and linear maps between dense layouts, and dispatchers
`Cartan.Generated.bin?`/`un?` that the field operations consult before interpreting a plan
(`Cartan.Kernel`).

Each kernel is the Grassmann plan of its key (`Grassmann.Kernel.build`, evaluated while
elaborating) written out as one loop over the points: the operand coefficients a point needs are
read once, and every output is the plan's row accumulated in the plan's order from `0`
(`o + v`, `o - v`, or `o + c * v` with the coefficient's exact bits), so a generated kernel is
bit-identical to the interpreted plan and to the pointwise Grassmann product (DESIGN.md §5.2
applied to whole fields; the property tests compare them).

Keys: every pair of chain grades for `*`, `∧`, `∨`, `⋅`; and, for spaces of at most 3
generators, spinors, co-spinors and multivectors with each other and with vectors. Unary maps
(the complements, reverse, involute, Clifford conjugation) for every chain grade, both halves and
the full algebra.
-/

namespace Cartan.Codegen

open Lean Elab Command
open DirectSum Grassmann Grassmann.Kernel AbstractTensors

/-- Lean source of a layout. -/
def layoutSrc : Layout → String
  | .chain g => s!"(.chain {g})"
  | .even => ".even"
  | .odd => ".odd"
  | .full => ".full"

/-- Lean source of a binary operation. -/
def binSrc : BinOp → String
  | .mul => ".mul" | .wedge => ".wedge" | .vee => ".vee" | .contraction => ".contraction"
  | .contractionLeft => ".contractionLeft" | .contractionRevLeft => ".contractionRevLeft"
  | .contractionRevRight => ".contractionRevRight" | .reverseMul => ".reverseMul"
  | .scalarContraction => ".scalarContraction" | .cross => ".cross" | .veedot => ".veedot"
  | .antidot => ".antidot"

/-- Lean source of a unary operation. -/
def unSrc : UnOp → String
  | .reverse => ".reverse" | .involute => ".involute" | .clifford => ".clifford" | .conj => ".conj"
  | .antireverse => ".antireverse" | .antiinvolute => ".antiinvolute" | .anticlifford => ".anticlifford"
  | .complementright => ".complementright" | .complementleft => ".complementleft"
  | .complementrighthodge => ".complementrighthodge" | .complementlefthodge => ".complementlefthodge"
  | .metric => ".metric" | .antimetric => ".antimetric"
  | .complementrightanti => ".complementrightanti" | .complementleftanti => ".complementleftanti"
  | op => s!".{(reprStr op).drop 21}"

/-- The binary keys generated for `n` generators: `(op, la, lb, lc)`. -/
def binKeys (n : Nat) : Array (BinOp × Layout × Layout × Layout) := Id.run do
  let mut out := #[]
  for g in [0:n+1] do
    for h in [0:n+1] do
      out := out.push (.mul, .chain g, .chain h, halfLayout ((g + h) % 2 == 1))
      if g + h ≤ n then out := out.push (.wedge, .chain g, .chain h, .chain (g + h))
      if g + h ≥ n then out := out.push (.vee, .chain g, .chain h, .chain (g + h - n))
      if h ≤ g then out := out.push (.contraction, .chain g, .chain h, .chain (g - h))
  if n ≤ 3 then
    for p in [false, true] do
      for q in [false, true] do
        out := out.push (.mul, halfLayout p, halfLayout q, halfLayout (p ^^ q))
      out := out.push (.mul, .chain 1, halfLayout p, halfLayout (!p))
      out := out.push (.mul, halfLayout p, .chain 1, halfLayout (!p))
      out := out.push (.wedge, .chain 1, halfLayout p, halfLayout (!p))
      out := out.push (.contraction, halfLayout p, .chain 1, halfLayout (!p))
    out := out.push (.mul, .full, .full, .full)
    out := out.push (.mul, .full, .chain 1, .full)
    out := out.push (.mul, .chain 1, .full, .full)
  return out

/-- The unary keys generated for `n` generators: `(op, la, lc)`. -/
def unKeys (n : Nat) : Array (UnOp × Layout × Layout) := Id.run do
  let mut out := #[]
  for g in [0:n+1] do
    for op in [UnOp.reverse, .involute, .clifford] do
      out := out.push (op, .chain g, .chain g)
    for op in [UnOp.complementrighthodge, .complementright, .complementleft] do
      out := out.push (op, .chain g, .chain (n - g))
  for p in [false, true] do
    for op in [UnOp.reverse, .involute, .clifford] do
      out := out.push (op, halfLayout p, halfLayout p)
    for op in [UnOp.complementrighthodge, .complementright, .complementleft] do
      out := out.push (op, halfLayout p, halfLayout (p ^^ (n % 2 == 1)))
  for op in [UnOp.reverse, .involute, .clifford, .complementrighthodge, .complementright, .complementleft] do
    out := out.push (op, .full, .full)
  return out

/-- The Lean source of a float coefficient (its exact bits). -/
def floatSrc (x : Float) : String := s!"(Float.ofBits {x.toBits.toNat})"

/-- The accumulation of one plan row: `((0 + v₀) - v₁) + c * v₂ …` (Grassmann `Plan.acc`). -/
def rowSrc (p : Plan) (c : Nat) (term : Nat → String) : String := Id.run do
  let s := p.rowStart[c]!.toNat
  let e := p.rowStart[c + 1]!.toNat
  let mut acc := "(0 : Float)"
  for t in [s:e] do
    let code := p.code.get! t
    let v := term t
    acc :=
      if code == 0 then s!"({acc} + {v})"
      else if code == 1 then s!"({acc} - {v})"
      else s!"({acc} + {floatSrc (Coeff.ofRat (p.coef[t]!) : Float)} * {v})"
  return acc

/-- Source of a binary field kernel `name a b n i out` over `k` points. -/
def binKernelSrc (name doc : String) (p : Plan) (wa wb : Nat) : String := Id.run do
  let as := (p.ia.map (·.toNat)).toList.eraseDups
  let bs := (p.ib.map (·.toNat)).toList.eraseDups
  let mut body := s!"    let oa := i * {wa}\n    let ob := i * {wb}\n"
  for j in as do body := body ++ s!"    let x{j} := a.get! (oa + {j})\n"
  for j in bs do body := body ++ s!"    let y{j} := b.get! (ob + {j})\n"
  let mut pushes := "out"
  for c in [0:p.outputs] do
    let r := rowSrc p c fun t => s!"x{p.ia[t]!.toNat} * y{p.ib[t]!.toNat}"
    body := body ++ s!"    let r{c} := {r}\n"
    pushes := s!"({pushes}.push r{c})"
  s!"/-- {doc} -/\ndef {name} (a b : FloatArray) : (k i : Nat) → FloatArray → FloatArray\n" ++
    s!"  | 0, _, out => out\n  | k + 1, i, out =>\n{body}    {name} a b k (i + 1) {pushes}"

/-- Source of a unary field kernel. -/
def unKernelSrc (name doc : String) (p : Plan) (wa : Nat) : String := Id.run do
  let as := (p.ia.map (·.toNat)).toList.eraseDups
  let mut body := s!"    let oa := i * {wa}\n"
  for j in as do body := body ++ s!"    let x{j} := a.get! (oa + {j})\n"
  let mut pushes := "out"
  for c in [0:p.outputs] do
    let r := rowSrc p c fun t => s!"x{p.ia[t]!.toNat}"
    body := body ++ s!"    let r{c} := {r}\n"
    pushes := s!"({pushes}.push r{c})"
  s!"/-- {doc} -/\ndef {name} (a : FloatArray) : (k i : Nat) → FloatArray → FloatArray\n" ++
    s!"  | 0, _, out => out\n  | k + 1, i, out =>\n{body}    {name} a k (i + 1) {pushes}"

/-- Elaborate one command given as source text. -/
def elabSrc (src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src "<cartan_field_kernels>" with
  | .ok stx => elabCommand stx
  | .error e => throwError "cartan_field_kernels: {e}\n{src}"

/-- `cartan_field_kernels n₁ n₂ …`: generated field kernels for the Euclidean spaces with
`n₁, n₂, …` generators, and the dispatchers `Cartan.Generated.bin?`, `Cartan.Generated.un?`. -/
syntax (name := cartanFieldKernels) "cartan_field_kernels " (num)+ : command

@[command_elab cartanFieldKernels] def elabCartanFieldKernels : CommandElab := fun stx => do
  let ns := stx[1].getArgs.map (·.isNatLit?.getD 0)
  let mut binArms : Array String := #[]
  let mut unArms : Array String := #[]
  let mut idx := 0
  for n in ns do
    let V := TensorBundle.euclidean n
    let mut bArms : Array String := #[]
    let mut uArms : Array String := #[]
    for (op, la, lb, lc) in binKeys n do
      match build { V, op := .bin op, la, lb, lc } with
      | .error _ => pure ()
      | .ok p =>
        if p.outputs == 0 || p.nested != 0 then continue
        let name := s!"Cartan.Generated.bin{idx}"
        idx := idx + 1
        let doc := s!"Generated field kernel: `{reprStr op}` of `{reprStr la}` × `{reprStr lb}` into `{reprStr lc}` in ℝ^{n}."
        elabSrc (binKernelSrc name doc p (la.size n) (lb.size n))
        bArms := bArms.push
          s!"    | {binSrc op}, {layoutSrc la}, {layoutSrc lb}, {layoutSrc lc} => some fun a b k => {name} a b k 0 (FloatArray.emptyWithCapacity (k * {lc.size n}))"
    for (op, la, lc) in unKeys n do
      match build { V, op := .un op, la, lb := la, lc } with
      | .error _ => pure ()
      | .ok p =>
        if p.outputs == 0 || p.nested != 0 then continue
        let name := s!"Cartan.Generated.un{idx}"
        idx := idx + 1
        let doc := s!"Generated field kernel: `{reprStr op}` of `{reprStr la}` into `{reprStr lc}` in ℝ^{n}."
        elabSrc (unKernelSrc name doc p (la.size n))
        uArms := uArms.push
          s!"    | {unSrc op}, {layoutSrc la}, {layoutSrc lc} => some fun a k => {name} a k 0 (FloatArray.emptyWithCapacity (k * {lc.size n}))"
    binArms := binArms.push
      (s!"  if V == TensorBundle.euclidean {n} then\n    match op, la, lb, lc with\n" ++
        "\n".intercalate bArms.toList ++ "\n    | _, _, _, _ => none\n  else")
    unArms := unArms.push
      (s!"  if V == TensorBundle.euclidean {n} then\n    match op, la, lc with\n" ++
        "\n".intercalate uArms.toList ++ "\n    | _, _, _ => none\n  else")
  elabSrc ("/-- The generated binary field kernel of `(V, op, la, lb, lc)`, if any: " ++
    "`k a b n` evaluates the plan at `n` points. -/\n" ++
    "def Cartan.Generated.bin? (V : DirectSum.TensorBundle) (op : DirectSum.BinOp)\n" ++
    "    (la lb lc : DirectSum.Layout) : Option (FloatArray → FloatArray → Nat → FloatArray) :=\n" ++
    "\n".intercalate binArms.toList ++ " none")
  elabSrc ("/-- The generated unary field kernel of `(V, op, la, lc)`, if any. -/\n" ++
    "def Cartan.Generated.un? (V : DirectSum.TensorBundle) (op : DirectSum.UnOp)\n" ++
    "    (la lc : DirectSum.Layout) : Option (FloatArray → Nat → FloatArray) :=\n" ++
    "\n".intercalate unArms.toList ++ " none")

end Cartan.Codegen
