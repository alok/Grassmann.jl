/-!
# Float literals decoded at elaboration time: `f64! x`, `f32! x`

Lean elaborates the `Float` literal `0.9394130628134757` to
`Float.ofScientific 9394130628134757 true 16`. The code generator usually hoists that call into a
constant computed once, but not always: once the literal is inlined into a branch where its `Bool`
argument is already held in a variable, the call stays in the hot path, and `Float.ofScientific`
takes its bignum model path for mantissas of 17 digits or exponents beyond `10^22`, microseconds per
call. `f64! x` and `f32! x` decode the literal while elaborating (with the same `Float.ofScientific`,
so the value is identical) and leave `Float.ofBits n` / `Float32.ofBits n`, a free bit cast, in the
compiled code. They also accept natural-number literals (`f64! 2` is `2.0`). Julia's kernels
(`JuliaBase.Math`, `JuliaBase.Trig`, `JuliaBase.Hyperbolic`) and every hot path of the port write
their constants this way; see `docs/PERF.md` for the measured effect.

This is the port's one literal macro (Geophysics' former `f64%` is gone).
-/

namespace JuliaBase

/-- `f64! 0.25` (or `f64! 2`): a `Float` literal decoded at elaboration time into `Float.ofBits n`. -/
syntax:max "f64! " (scientific <|> num) : term

/-- `f32! 0.25` (or `f32! 2`): a `Float32` literal decoded at elaboration time into
`Float32.ofBits n`. -/
syntax:max "f32! " (scientific <|> num) : term

macro_rules
  | `(f64! $x:scientific) =>
    match x.raw.isScientificLit? with
    | some (m, s, e) => `(Float.ofBits $(Lean.quote (Float.ofScientific m s e).toBits.toNat))
    | none => Lean.Macro.throwError "f64!: expected a scientific literal"
  | `(f64! $x:num) => `(Float.ofBits $(Lean.quote (Float.ofNat x.getNat).toBits.toNat))
  | `(f32! $x:scientific) =>
    match x.raw.isScientificLit? with
    | some (m, s, e) => `(Float32.ofBits $(Lean.quote (Float32.ofScientific m s e).toBits.toNat))
    | none => Lean.Macro.throwError "f32!: expected a scientific literal"
  | `(f32! $x:num) => `(Float32.ofBits $(Lean.quote (Float32.ofNat x.getNat).toBits.toNat))

end JuliaBase
