import Tests.Golden.Reference

/-!
# Built-in evaluators

Evaluators that need nothing beyond the libraries below the Grassmann element layer
(JuliaBase, Leibniz, DirectSum). The Grassmann dynamic layer registers the algebra later
(`Tests.Golden.Registry`).

| name | suite / op | computes | checks |
|---|---|---|---|
| `juliabase/show` | floats / `show` | `JuliaBase.JuliaShow.showString`/`showCompact` of every scalar type | `str`, `compact_str` |
| `leibniz/storage` | construct | the dense vector from `(kind, grade, bits, T, native)` through the Leibniz storage orders (schema §7.1, incl. degenerate Couples), and the display of `Zero`, `One`, basis blades (`DirectSum.TensorBundle.bladeLabel`) and `Single`s (`JuliaBase.JuliaShow.showValue`, i.e. Leibniz `showvalue`, then the label) | kind, values, strings |
| `identity/Multivector` | unary / `Multivector` | `Multivector(a)`: the dense vector is unchanged | kind, values |

The space-printing checks (`show`, `show_bundle`, names, basis order, `Isq`) run per shard in
`Tests.ElementOracle.checkSpace` (module `Tests.Golden.Space`); the encode/decode round trips run on every element while
loading (`Tests.Golden.Shard`).
-/

namespace Tests.ElementOracle

open JuliaBase

/-! ## Scalars (floats suite) -/

/-- Julia `show` of one scalar of type `T` through `JuliaBase.JuliaShow`. -/
def showScalar (T : CoeffType) (x : Scalar) (compact : Bool) : Option String :=
  let sh := fun {α : Type} [JuliaShow α] (v : α) => some (JuliaShow.showIO compact v)
  match T, x with
  | .float64, .float f => sh f
  | .int64, .exact q => sh q.num
  | .bool, .exact q => sh (q != 0)
  | .rational, .exact q => sh q
  | .complex .float64, .complex (.float a) (.float b) => sh (Complex.mk a b)
  | .complex .int64, .complex (.exact a) (.exact b) => sh (Complex.mk a.num b.num)
  | .complex .bool, .complex (.exact a) (.exact b) => sh (Complex.mk (a != 0) (b != 0))
  | .complex .rational, .complex (.exact a) (.exact b) => sh (Complex.mk a b)
  | _, _ => none

/-- Leibniz `showvalue` of a coefficient of type `T` (everything before the blade label:
`3`, `-0.5`, `(1//3)`, `(1 + 2im)`, `true*`, `NaN*`) through `JuliaBase.JuliaShow.showValue`. -/
def showValueScalar (T : CoeffType) (x : Scalar) (compact : Bool) : Option String :=
  let sv := fun {α : Type} [JuliaShow α] (v : α) => some (JuliaShow.showValue compact v)
  match T, x with
  | .float64, .float f => sv f
  | .int64, .exact q => sv q.num
  | .bool, .exact q => sv (q != 0)
  | .rational, .exact q => sv q
  | .complex .float64, .complex (.float a) (.float b) => sv (Complex.mk a b)
  | .complex .int64, .complex (.exact a) (.exact b) => sv (Complex.mk a.num b.num)
  | .complex .bool, .complex (.exact a) (.exact b) => sv (Complex.mk (a != 0) (b != 0))
  | .complex .rational, .complex (.exact a) (.exact b) => sv (Complex.mk a b)
  | _, _ => none

/-- `juliabase/show`: the printed forms of a floats-suite scalar. -/
def floatsShow : Evaluator := fun _ args => do
  let x ← args[0]?
  let T ← x.T
  let v ← x.value
  let s ← showScalar T (v.get 0) false
  let c ← showScalar T (v.get 0) true
  return { x with str := .val s, compactStr := .val c }

/-! ## Storage layouts (construct suite) -/

/-- Exact or float sum of two scalars of one representation (the degenerate Couple:
both parts on one blade). -/
def Scalar.add : Scalar → Scalar → Option Scalar
  | .exact a, .exact b => some (.exact (a + b))
  | .float a, .float b => some (.float (a + b))
  | .complex a b, .complex c d => do pure (.complex (← a.add c) (← b.add d))
  | _, _ => none

/-- The unit coefficient of type `T` (One and basis blades). -/
def unitScalar (T : CoeffType) : Scalar :=
  match T with
  | .float64 => .float 1
  | .complex .float64 => .complex (.float 1) (.float 0)
  | .complex _ => .complex (.exact 1) (.exact 0)
  | _ => .exact 1

/-- `leibniz/storage`: rebuild the dense vector of a constructed element from its
constructor data (schema §8.1), scattering `native` through the kind's storage order
(`Tests.ElementOracle.supportIndices`, i.e. `Leibniz.indexBasis`/`indexEven`/`indexOdd`), and print
`Zero`, `One` and basis blades with `DirectSum.TensorBundle.bladeLabel`, and `Single`s as
`showValueScalar` followed by the label. -/
def constructDense : Evaluator := fun ctx args => do
  let x ← args[0]?
  let T ← x.T
  let n ← x.dims? (ctx.space.map (·.n))
  let N := 2 ^ n
  let zeros := Coeffs.zeros T N
  let label := fun (b : UInt64) => show Option String from do
    -- elements of the shard space print with its labels; others (a `V` field) are not ours
    if x.V.isSome then none else
    let V ← ctx.bundle?
    pure (V.bladeLabel b)
  let withStr := fun (e : GoldenElem) (s : Option String) =>
    match s with
    | some t => { e with str := .val t, compactStr := .val t }
    | none => e
  let base : GoldenElem := { kind := x.kind, T, V := x.V, grade := x.grade, bits := x.bits }
  match x.kind with
  | .zero => return withStr { base with dense := some zeros } (some "𝟎")
  | .one | .submanifold =>
    let b ← x.bits
    let supp ← supportIndices n x.kind 0 b
    return withStr { base with dense := some (zeros.set (supp[0]?.getD 0) (unitScalar T)) } (label b)
  | .single | .chain | .spinor | .cospinor | .multivector | .couple | .pseudoCouple =>
    let nat ← x.native
    let b := x.bits.getD 0
    -- a Single prints as Leibniz `showvalue` followed by the blade label
    let singleStr := fun (e : GoldenElem) => match x.kind, label b with
      | .single, some l =>
        match showValueScalar T (nat.get 0) false, showValueScalar T (nat.get 0) true with
        | some s, some c => { e with str := .val (s ++ l), compactStr := .val (c ++ l) }
        | _, _ => e
      | _, _ => e
    let supp ← supportIndices n x.kind (x.grade.getD 0) b
    if nat.size != supp.size then none
    let top : UInt64 := (1 <<< n.toUInt64) - 1
    let degenerate := (x.kind == .couple && b == 0) || (x.kind == .pseudoCouple && b == top)
    if degenerate then
      let s ← (nat.get 0).add (nat.get 1)
      return { base with dense := some (zeros.set (supp[0]?.getD 0) s) }
    let d := (List.range supp.size).foldl (fun acc i => acc.set (supp[i]?.getD 0) (nat.get i)) zeros
    return singleStr { base with dense := some d }
  | _ => none

/-! ## Identities -/

/-- `identity/Multivector`: `Multivector(a)` keeps the dense vector and the coefficient
type, and lives in the same space. -/
def multivectorIdentity : Evaluator := fun _ args => do
  let x ← args[0]?
  if !x.kind.hasDense then none
  let d ← x.dense
  return { kind := .multivector, T := x.T, V := x.V, dense := some d }

/-- The built-in registrations (lowest precedence). -/
def builtinRegistrations : Array Registration := #[
  { name := "juliabase/show", suite := "floats", op := "show", eval := floatsShow },
  { name := "leibniz/storage", suite := "construct", op := "construct", eval := constructDense },
  { name := "identity/Multivector", suite := "unary", op := "Multivector", eval := multivectorIdentity },
  referenceRegistration
]

end Tests.ElementOracle
