/-!
# Float literals as IEEE bits

A decimal `Float` literal elaborates to `OfScientific.ofScientific m b e`. The
compiler normally hoists it into a once-initialized constant, but when the
literal sits in a branch where a runtime `Bool` is known to equal `b`, it may
substitute that variable for `b`, and the literal is then converted from its
decimal digits (with `Nat` arithmetic) *every time the code runs* — about
50 ns per literal, measured in `JMath.pow` and `Column.domainError`.

`f64% 1.5e-3` expands, at macro-expansion time, to `Float.ofBits <bits>` with the
bits computed by the same `Float.ofScientific`, so the value is identical and the
compiled code only reinterprets a 64-bit constant.
-/

namespace Geophysics

/-- `f64% x`: the `Float` literal `x` as a bit-pattern constant (same value as `x`). -/
syntax "f64% " scientific : term
/-- `f64% n`: the `Float` value of the natural literal `n` as a bit-pattern constant. -/
syntax "f64% " num : term

macro_rules
  | `(f64% $x:scientific) => do
    let some (m, s, e) := x.raw.isScientificLit? | Lean.Macro.throwError "f64%: not a literal"
    let bits := (Float.ofScientific m s e).toBits
    `(Float.ofBits $(Lean.Syntax.mkNumLit (toString bits.toNat)))
  | `(f64% $x:num) => do
    let bits := (Float.ofNat x.getNat).toBits
    `(Float.ofBits $(Lean.Syntax.mkNumLit (toString bits.toNat)))

end Geophysics
