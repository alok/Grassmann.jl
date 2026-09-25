import Similitude.Quantity

/-!
# Logarithmic quantities: `log(q)`, `neper`, `bel`, `decibel`

Julia's `log(x::Quantity{U}) = Quantity{U}(log(x.v), log(dimensions(x)))`
(`dimension.jl:315-321`, `Similitude.jl:57`) makes a quantity whose dimension is
a `LogGroup`: the formal logarithm, in some base, of a USQ dimension. The units
`neper`, `bel` and `decibel` (`derived.jl:390-392`) are `U(𝟏, log(𝟙))`,
`U(𝟏, log10(𝟙))` and `U(𝟏, dB(𝟙))`.

`LogQuantity U b d α` is that quantity with the system, the base `b` and the
dimension `d` in its type. It prints as Julia does: the value, then the base's
function applied to the dimension's image in the system's base units (never the
registered unit name: `log(kg⋅m²s⁻²)`, not `log(J)`), then the system:
`0.6931471805599453 [log(kg⋅m²s⁻²)] Metric`, `𝟏 = 1.0 [dB(𝟙)] English`.

Arithmetic follows Julia: logarithms of one dimension add and subtract (Julia
keeps the left operand's dimension), numbers scale them (`l / k` is
`l * inv(k)`), and `exp`/`exp2`/`exp10`/`expdb` of the matching base give back
a quantity of the original dimension.

Julia defects: converting a logarithmic quantity to another system raises an
ambiguity error (`log(::Irrational{:ℯ}, ::Group)`), so there is no `to`;
`exp` of a `neper` (a formal `exp(𝟙)` value) is not modelled.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- Julia's display prefix of a logarithm base (`FieldAlgebra.jl:494-498`):
`log(`, `log2(`, `log10(`, `dB(` or `log(b,`. -/
def logPrefix (b : LogBase) : String := (⟨b, (1 : USQGroup)⟩ : LogGroup usqBasis).showFun

/-- A quantity of dimension `log_b(d)` in system `U` (Julia `Quantity{U,T,LogGroup{b}}`).
Only the value exists at run time. -/
@[ext] structure LogQuantity (U : Sys) (b : LogBase) (d : Dim) (α : Type) where
  /-- the value -/
  val : α

namespace LogQuantity

variable {U : Sys} {b : LogBase} {d : Dim} {α : Type} [QScalar α]

/-- Julia `show(io, q)` (`dimension.jl:309-313` with FieldAlgebra's `showgroup` of a
`LogGroup`): `value [log(image in base units)] System`. -/
def display (q : LogQuantity U b d α) : String :=
  let (names, chars, _) := dimText U.name
  let g : USQGroup := Group.mk' (U.image d.toGroup.v) (.int 1)
  s!"{QScalar.jprint q.val} [{logPrefix b}{g.showWith names chars "𝟙"})] {U.name}"

instance : ToString (LogQuantity U b d α) := ⟨display⟩

/-- Julia `a + b` of two logarithms of one dimension (`dimension.jl:433-436`). -/
instance : Add (LogQuantity U b d α) := ⟨fun x y => ⟨x.val + y.val⟩⟩
/-- Julia `a - b` of two logarithms of one dimension. -/
instance : Sub (LogQuantity U b d α) := ⟨fun x y => ⟨x.val - y.val⟩⟩
/-- Julia `-a`. -/
instance : Neg (LogQuantity U b d α) := ⟨fun x => ⟨-x.val⟩⟩
/-- Julia `a * k` for a number (`dimension.jl:333`). -/
instance : HMul (LogQuantity U b d α) α (LogQuantity U b d α) := ⟨fun x k => ⟨x.val * k⟩⟩
/-- Julia `k * a` for a number. -/
instance : HMul α (LogQuantity U b d α) (LogQuantity U b d α) := ⟨fun k x => ⟨k * x.val⟩⟩
/-- Julia `a / k = a * inv(k)` (`dimension.jl:344`). -/
instance : HDiv (LogQuantity U b d α) α (LogQuantity U b d α) := ⟨fun x k => ⟨x.val * k⁻¹⟩⟩

/-- Julia `exp(q)` of a natural logarithm: the quantity of dimension `d`. -/
def exp (q : LogQuantity U .e d Float) : Quantity U d Float := ⟨JuliaBase.F64.exp q.val⟩
/-- Julia `exp2(q)` of a base-2 logarithm. -/
def exp2 (q : LogQuantity U .two d Float) : Quantity U d Float := ⟨JuliaBase.F64.exp2 q.val⟩
/-- Julia `exp10(q)` of a base-10 logarithm. -/
def exp10 (q : LogQuantity U .ten d Float) : Quantity U d Float := ⟨JuliaBase.F64.exp10 q.val⟩
/-- Julia `expdb(q)` of a decibel quantity (`FieldConstants.expdb`). -/
def expdb (q : LogQuantity U .dB d Float) : Quantity U d Float :=
  ⟨(FieldConstants.expdb (.float q.val)).toFloat⟩

end LogQuantity

namespace Quantity

variable {U : Sys} {d : Dim}

/-- Julia `log(q)` (`dimension.jl:315`). -/
def log (q : Quantity U d Float) : LogQuantity U .e d Float := ⟨JuliaBase.F64.log q.val⟩
/-- Julia `log2(q)`. -/
def log2 (q : Quantity U d Float) : LogQuantity U .two d Float := ⟨JuliaBase.F64.log2 q.val⟩
/-- Julia `log10(q)`. -/
def log10 (q : Quantity U d Float) : LogQuantity U .ten d Float := ⟨JuliaBase.F64.log10 q.val⟩
/-- Julia `logdb(q) = 10log10(q)` in decibels (`Similitude.jl:57`). -/
def logdb (q : Quantity U d Float) : LogQuantity U .dB d Float :=
  ⟨(FieldConstants.logdb (.float q.val)).toFloat⟩
/-- Julia `log(k, q) = log(q)/log(k)` for a numeric base `k` (`dimension.jl:318`). -/
def logb (k : JNum) (q : Quantity U d Float) : LogQuantity U (.num k) d Float :=
  ⟨JuliaBase.F64.log q.val / JuliaBase.F64.log k.toFloat⟩

end Quantity

/-- Julia `neper(U) = U(𝟏, log(𝟙))` (`derived.jl:390`). -/
def neper (U : Sys) : LogQuantity U .e Dim.one Scalar := ⟨.grp Consts.one⟩
/-- Julia `bel(U) = U(𝟏, log10(𝟙))` (`derived.jl:391`). -/
def bel (U : Sys) : LogQuantity U .ten Dim.one Scalar := ⟨.grp Consts.one⟩
/-- Julia `decibel(U) = U(𝟏, dB(𝟙))` (`derived.jl:392`). -/
def decibel (U : Sys) : LogQuantity U .dB Dim.one Scalar := ⟨.grp Consts.one⟩

end Similitude
