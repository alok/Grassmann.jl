module

public meta import Lean.Elab.Term

/-!
# Float literals as module-level constants: `f64! x`, `f32! x`

Lean elaborates the `Float` literal `0.9394130628134757` to
`Float.ofScientific 9394130628134757 true 16`. The code generator usually hoists that call into a
constant computed once, but not always: once the literal is inlined into a branch where its `Bool`
argument is already held in a variable, the call stays in the hot path, and `Float.ofScientific`
takes its bignum model path for mantissas of 17 digits or exponents beyond `10^22`, microseconds per
call. Even when it is hoisted, a constant inside a function body becomes a *closed term*, read
through a once-cell whose state is an `_Atomic(int)`: every use is a sequentially consistent load
(`ldar` on aarch64) and a branch. A top-level `def` of type `Float`, in contrast, is initialized
with its module and read as a plain global.

`f64! x` and `f32! x` therefore decode the literal while elaborating (with the same
`Float.ofScientific`/`Float32.ofScientific`, so the value is identical) and elaborate to a
module-level constant `JuliaBase.FloatLit.lit.M.f64.x<bits>` (`M` the current module, so that two
modules never declare the same name), declared on first use and holding
`Float.ofBits <bits>` (resp. `Float32.ofBits`). They also accept natural-number literals
(`f64! 2` is `2.0`) and a leading minus sign (`f64! -0.5`; write that rather than `-f64! 0.5`,
whose negation would again be a closed term). Julia's kernels (`JuliaBase.Math`,
`JuliaBase.Trig`, `JuliaBase.Hyperbolic`) and every hot path of the port write their constants
this way; see `docs/PERF.md` for the measured effect. This is the port's one literal macro
(Geophysics' former `f64%` is gone).
-/

public section

namespace JuliaBase

/-- `f64! 0.25` (or `f64! 2`): a `Float` literal decoded at elaboration time into a module-level
constant `Float.ofBits n` (a plain global load in compiled code). -/
syntax:max (name := f64Lit) "f64! " "-"? (scientific <|> num) : term

/-- `f32! 0.25` (or `f32! 2`): a `Float32` literal decoded at elaboration time into a module-level
constant `Float32.ofBits n`. -/
syntax:max (name := f32Lit) "f32! " "-"? (scientific <|> num) : term

/-- `f64bits! 0x7FF0000000000000`: the `Float` with these IEEE bits, as a module-level constant
(the same constant as the `f64!` literal of that value). For values without a short decimal
form, and for `Inf`/`NaN`; `Float.ofBits n` in a function body is a closed term read through an
atomic once-cell. -/
syntax:max (name := f64BitsLit) "f64bits! " num : term

/-- `f32bits! 0x3fc90fdb`: the `Float32` with these IEEE bits, as a module-level constant. -/
syntax:max (name := f32BitsLit) "f32bits! " num : term

/-- `i64! 8` (or `i64! -53`): an `Int64` literal as a module-level constant (a plain global
load in compiled code). An `Int64`/`Int32` literal inside a function body is otherwise a closed
term, `Int64.ofNat 8` computed once and read through a once-cell (an atomic load and a branch on
every use); `UInt64` literals are C immediates and need nothing. -/
syntax:max (name := i64Lit) "i64! " "-"? num : term

/-- `i32! 20` (or `i32! -60`): an `Int32` literal as a module-level constant (see `i64!`). -/
syntax:max (name := i32Lit) "i32! " "-"? num : term

end JuliaBase
end

public meta section

open Lean Elab Term Meta

namespace JuliaBase

namespace FloatLit

/-- The value of a literal node as `(mantissa, negative exponent?, exponent)`. -/
def literal? (x : Syntax) : Option (Nat × Bool × Nat) :=
  match x.isScientificLit? with
  | some v => some v
  | none => x.isNatLit?.map fun n => (n, false, 0)

/-- Hexadecimal digits of a natural number (lowercase, at least one digit). -/
def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The module-level constant `JuliaBase.FloatLit.lit.<module>.<tag>.x<bits>` holding
`ofBits bits`, declared and compiled on first use in the current module (outside every namespace
of the module itself, which may be a structure's). -/
def litConst (tag : String) (ty ofBits : Name) (bits : Expr) (bitsNat : Nat) : TermElabM Expr := do
  let name := `JuliaBase.FloatLit.lit ++ (← getMainModule) ++ Name.mkSimple tag ++
    Name.mkSimple ("x" ++ hex bitsNat)
  unless (← getEnv).contains name do
    let decl := Declaration.defnDecl {
      name, levelParams := [], type := mkConst ty, value := mkApp (mkConst ofBits) bits,
      hints := .abbrev, safety := .safe }
    addAndCompile decl
  return mkConst name

/-- Elaborate `f64! x` / `f64! -x` (the minus flips the sign bit, so `f64! -0.0` is `-0.0`). -/
@[term_elab f64Lit] def elabF64 : TermElab := fun stx _ => do
  match literal? stx[2] with
  | some (m, s, e) =>
    let bits := (Float.ofScientific m s e).toBits
    let bits := if stx[1].isNone then bits else bits ^^^ 0x8000000000000000
    litConst "f64" ``Float ``Float.ofBits (toExpr bits) bits.toNat
  | none => throwErrorAt stx[2] "f64!: expected a numeric literal"

/-- Elaborate `f32! x` / `f32! -x`. -/
@[term_elab f32Lit] def elabF32 : TermElab := fun stx _ => do
  match literal? stx[2] with
  | some (m, s, e) =>
    let bits := (Float32.ofScientific m s e).toBits
    let bits := if stx[1].isNone then bits else bits ^^^ 0x80000000
    litConst "f32" ``Float32 ``Float32.ofBits (toExpr bits) bits.toNat
  | none => throwErrorAt stx[2] "f32!: expected a numeric literal"

/-- Elaborate `f64bits! n`. -/
@[term_elab f64BitsLit] def elabF64Bits : TermElab := fun stx _ => do
  match stx[1].isNatLit? with
  | some n =>
    unless n < 2 ^ 64 do throwErrorAt stx[1] "f64bits!: more than 64 bits"
    let bits : UInt64 := n.toUInt64
    litConst "f64" ``Float ``Float.ofBits (toExpr bits) bits.toNat
  | none => throwErrorAt stx[1] "f64bits!: expected a natural-number literal"

/-- Elaborate `f32bits! n`. -/
@[term_elab f32BitsLit] def elabF32Bits : TermElab := fun stx _ => do
  match stx[1].isNatLit? with
  | some n =>
    unless n < 2 ^ 32 do throwErrorAt stx[1] "f32bits!: more than 32 bits"
    let bits : UInt32 := n.toUInt32
    litConst "f32" ``Float32 ``Float32.ofBits (toExpr bits) bits.toNat
  | none => throwErrorAt stx[1] "f32bits!: expected a natural-number literal"

/-- Elaborate `i64! n` / `i64! -n` (two's complement, wrapping as Julia's `Int64`). -/
@[term_elab i64Lit] def elabI64 : TermElab := fun stx _ => do
  match stx[2].isNatLit? with
  | some n =>
    let v : Int := if stx[1].isNone then n else -n
    let bits := (Int64.ofInt v).toUInt64
    litConst "i64" ``Int64 ``UInt64.toInt64 (toExpr bits) bits.toNat
  | none => throwErrorAt stx[2] "i64!: expected a natural-number literal"

/-- Elaborate `i32! n` / `i32! -n`. -/
@[term_elab i32Lit] def elabI32 : TermElab := fun stx _ => do
  match stx[2].isNatLit? with
  | some n =>
    let v : Int := if stx[1].isNone then n else -n
    let bits := (Int32.ofInt v).toUInt32
    litConst "i32" ``Int32 ``UInt32.toInt32 (toExpr bits) bits.toNat
  | none => throwErrorAt stx[2] "i32!: expected a natural-number literal"

end FloatLit

end JuliaBase
