import JuliaBase

/-!
# Type parameters: Julia's `Int`-or-`Float64` numbers

FlowGeometry.jl keeps every shape parameter of a profile or an airfoil in the *type*
(`ClarkY{12, 0.21, 150}`, `Modified{8.25, 63.5, 0.2, 150}`, `Joukowski{1.1, 0.1, 0, 1, 5}`), and the
`NACA"…"` macro fills them with `Meta.parse` of the digit groups, so a parameter is an `Int` or a
`Float64` depending on how it was written (`"12"` is `12`, `"12.5"` is `12.5`). The arithmetic is
the same either way (`t/100` converts), but Julia *prints* them differently, and the port reproduces
Julia's type strings. `Num` keeps the distinction.
-/

namespace FlowGeometry

open JuliaBase

/-- A Julia type parameter that is an `Int` or a `Float64` (FlowGeometry.jl passes both). -/
inductive Num where
  /-- A Julia `Int` parameter (printed `12`). -/
  | int (n : Int)
  /-- A Julia `Float64` parameter (printed with Julia's shortest round-trip digits, `0.21`). -/
  | float (x : Float)
  deriving Inhabited, Repr

namespace Num

/-- The value as a `Float64` (Julia's promotion `Float64(n)`, exact for the sizes used). -/
@[inline] def toFloat : Num → Float
  | int n => Float.ofInt n
  | float x => x

/-- Julia `show` of the parameter inside a type (`12`, `0.21`, `-3`, `1.0e-5`). -/
def jshow : Num → String
  | int n => toString n
  | float x => F64.showString x

instance : ToString Num := ⟨jshow⟩

/-- `12` is `Num.int 12`. -/
instance {n : Nat} : OfNat Num n := ⟨int n⟩

/-- `0.21` is `Num.float 0.21`. -/
instance : OfScientific Num := ⟨fun m s e => float (OfScientific.ofScientific m s e)⟩

/-- `-x`. -/
instance : Neg Num := ⟨fun | int n => int (-n) | float x => float (-x)⟩

/-- Julia `==` of two parameters (as numbers: `12 == 12.0`). -/
instance : BEq Num := ⟨fun a b => a.toFloat == b.toFloat⟩

/-- Julia `Meta.parse` of a NACA digit group (`\d+(\.\d+)?`): an `Int` without a decimal point
(leading zeros allowed, `"010"` is `10`), a correctly rounded `Float64` with one. -/
def parse (s : String) : Num :=
  if s.contains '.' then float (F64.parse s) else int (s.toNat?.getD 0)

/-- Julia `m ÷ 10` for the parameter (`div` on `Int`, `div(m, 10.0)` on `Float64`). -/
def div10 : Num → Num
  | int n => int (n.tdiv 10)
  | float x => float (F64.div x 10)

/-- Julia `m % 10` (`rem`: truncated remainder with the sign of `m`). -/
def rem10 : Num → Num
  | int n => int (n.tmod 10)
  | float x => float (F64.rem x 10)

end Num

/-- `f 0, …, f (n-1)` packed (tail-recursive fill). -/
@[specialize] def floatsOfFn (n : Nat) (f : Nat → Float) : FloatArray :=
  go n 0 (FloatArray.emptyWithCapacity n)
where
  /-- the fill loop -/
  go : Nat → Nat → FloatArray → FloatArray
    | 0, _, acc => acc
    | k + 1, i, acc => go k (i + 1) (acc.push (f i))

end FlowGeometry
