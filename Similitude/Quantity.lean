import Similitude.Ratio

/-!
# Dimensioned quantities

`Quantity U d α` is Similitude's `Quantity{U,T,D}` (`dimension.jl:270-313`) with
both the unit system `U` and the USQ dimension `d` in the **type**. At runtime a
quantity is just its value (a single-field structure is represented as the
field itself), so the type-level bookkeeping is free:

* `+`/`-` require equal systems and dimensions: adding a length to a time, or a
  Metric length to an English one, is a type error (Julia's `+` fails at
  runtime, `dimension.jl:405-429`);
* `*`, `/`, `inv`, `npow`, `sqrt` compute the result's dimension during
  elaboration (`Dim` arithmetic reduces in the unifier);
* `q.to S` converts to another system by the exact ratio (`Similitude.jl:95-102`);
  a `ConvertUnit U S d` only multiplies quantities of system `U` and dimension `d`;
* `q.recast d₂` reinterprets a quantity at a dimension with the same image in
  `U` (Julia's `==` compares images, so `Metric(1, action) == Metric(1,
  angularmomentum)`); the side condition is decided by the kernel.

The value type is any `QScalar`: `Scalar` reproduces Similitude exactly (values
become exact constant groups after a conversion, `2² = 4.0 [s] English`),
`Float` gives plain floating-point quantities with the same types.
-/

namespace Similitude

open FieldConstants FieldAlgebra UnitSystems

/-- Values a quantity can hold: Julia's arithmetic, a conversion factor and
Julia's `print`. -/
class QScalar (α : Type) extends Add α, Sub α, Mul α, Div α, Neg α, Inv α where
  /-- a literal power `x^n` -/
  npow : α → Nat → α
  /-- Julia `sqrt` -/
  sqrt : α → α
  /-- Julia `cbrt` -/
  cbrt : α → α
  /-- an exact conversion factor as a value -/
  ofRatio : Scalar → α
  /-- Julia `print` -/
  jprint : α → String

instance : QScalar Scalar where
  npow x n := x ^ (n : Int)
  sqrt := Scalar.sqrt
  cbrt := Scalar.cbrt
  ofRatio := id
  jprint := Scalar.toString

instance : QScalar Float where
  inv x := 1.0 / x
  npow x n := JNum.toFloat (FieldConstants.Num.plainLpow (.float x) n)
  sqrt := Float.sqrt
  cbrt := JuliaBase.F64.cbrt
  ofRatio := Scalar.toFloat
  jprint := JuliaBase.F64.showString

/-- A quantity of USQ dimension `d` in unit system `U` with value type `α`
(Julia `Quantity{U,T,D}`). Only the value exists at runtime. -/
@[ext] structure Quantity (U : Sys) (d : Dim) (α : Type) where
  /-- the value, in the units of `U` -/
  val : α

/-- Quantities with Similitude's exact values. -/
abbrev Q (U : Sys) (d : Dim) := Quantity U d Scalar

/-- Julia `U(v, d)`: the quantity `v` of dimension `d` in system `U`. -/
@[inline] def _root_.UnitSystems.Sys.qty {α : Type} (U : Sys) (d : Dim) (v : α) : Quantity U d α := ⟨v⟩

namespace Quantity

variable {U S : Sys} {d d₁ d₂ : Dim} {α : Type} [QScalar α]

instance : Add (Quantity U d α) := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub (Quantity U d α) := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Neg (Quantity U d α) := ⟨fun a => ⟨-a.val⟩⟩
instance : HMul (Quantity U d₁ α) (Quantity U d₂ α) (Quantity U (d₁ * d₂) α) :=
  ⟨fun a b => ⟨a.val * b.val⟩⟩
instance : HDiv (Quantity U d₁ α) (Quantity U d₂ α) (Quantity U (d₁ / d₂) α) :=
  ⟨fun a b => ⟨a.val / b.val⟩⟩
instance : HMul α (Quantity U d α) (Quantity U d α) := ⟨fun k a => ⟨k * a.val⟩⟩
instance : HMul (Quantity U d α) α (Quantity U d α) := ⟨fun a k => ⟨a.val * k⟩⟩
instance : HDiv (Quantity U d α) α (Quantity U d α) := ⟨fun a k => ⟨a.val / k⟩⟩

/-- Julia `inv(q)`: the dimension inverts. -/
@[inline] def inv (a : Quantity U d α) : Quantity U d⁻¹ α := ⟨a.val⁻¹⟩

/-- Julia `q^n` for a literal `n`: the dimension is raised to `n`. -/
@[inline] def npow (a : Quantity U d α) (n : Nat) : Quantity U (d ^ n) α := ⟨QScalar.npow a.val n⟩

/-- Julia `sqrt(q)`: the dimension is halved; exponents are twelfths, so this is
exact for any integral (or even-twelfths) dimension, checked by `decide`. -/
@[inline] def sqrt (a : Quantity U d α) (_h : d.IsSquare := by decide) : Quantity U d.half α :=
  ⟨QScalar.sqrt a.val⟩

/-- Julia `cbrt(q)`: the dimension's cube root. -/
@[inline] def cbrt (a : Quantity U d α) (_h : d.HasRoot 3 := by decide) : Quantity U (d.root 3) α :=
  ⟨QScalar.cbrt a.val⟩

/-- The exact factor converting dimension `d` from `U` to `S`. Deliberately not
inlined: with literal systems and dimension the call is a closed term, which the
compiler hoists, so a typed `Float` conversion compiles to one multiplication by
a precomputed constant. -/
def factor (U S : Sys) (d : Dim) : Scalar := ratio d.toGroup.v U S

/-- Julia `q(S)` / `S(q)`: the same quantity in system `S`, `q.v * ratio(d, U, S)`
(`Similitude.jl:95-102`). With literal systems and dimension the factor is a
closed term, computed once. -/
@[inline] def to (S : Sys) (q : Quantity U d α) : Quantity S d α :=
  ⟨q.val * QScalar.ofRatio (factor U S d)⟩

/-- Reinterpret a quantity at another dimension with the same image in `U`: a
kernel-checked version of Julia's image-based `==` (`dimension.jl:393`). -/
@[inline] def recast (d₂ : Dim) (q : Quantity U d₁ α)
    (_h : U.hom.halfDim d₁ = U.hom.halfDim d₂ := by decide) : Quantity U d₂ α := ⟨q.val⟩

/-- Julia `==` on quantities of one system: equal images and equal values. -/
def beq [BEq α] (a : Quantity U d₁ α) (b : Quantity U d₂ α) : Bool :=
  U.hom.halfDim d₁ == U.hom.halfDim d₂ && a.val == b.val

/-- Julia `show(io, q)` (`dimension.jl:309-313`): `value [unit] System`. -/
def display (q : Quantity U d α) : String :=
  s!"{QScalar.jprint q.val} [{U.showDim d.toGroup.v}] {U.name}"

instance : ToString (Quantity U d α) := ⟨display⟩

/-- The value in `α` (Julia `normal(q)`). -/
@[inline] def normal (q : Quantity U d α) : α := q.val

/-- Julia `quantity(q)` (`dimension.jl:301-302`): the value. Identical to
`normal`; Julia keeps both names because `quantity(q) = q` is also defined for
non-quantities (`:300`), a fallback Lean does not need. -/
@[inline] def quantity (q : Quantity U d α) : α := q.val

/-- Julia `dimensions(q)` (`dimension.jl:303`): the quantity's USQ dimension as a
group. In Julia the dimension is the runtime field `q.d`; here it is the type
index `d`, so this recovers the group from the type and the quantity argument is
erased. -/
@[inline] def dimensions (_ : Quantity U d α) : USQGroup := d.toGroup

/-- Julia `Dimension(q)` (`dimension.jl:304`): the same as `dimensions`, exported
from `derived.jl:15`. Julia's companion fallback `Dimension(q) = q` (`:305`)
has no Lean counterpart — it exists so untyped code can pass either a quantity
or a bare dimension, and Lean dispatches on the type instead. -/
@[inline] def Dimension (q : Quantity U d α) : USQGroup := q.dimensions

/-- Julia `unitsystem2(q)` (`dimension.jl:307`): the quantity's unit system. -/
@[inline] def unitsystem2 (_ : Quantity U d α) : Sys := U

/-- Julia `unitsystem(q) = dimension(U)` (`dimension.jl:306`). Julia's `dimension`
unwraps a `Constant{D}` and is the identity otherwise (`dimension.jl:20-21`), and
a unit system is never a `Constant`, so this agrees with `unitsystem2`. -/
@[inline] def unitsystem (_ : Quantity U d α) : Sys := U

end Quantity

/-- A `ConvertUnit` applies to quantities of its own source system and dimension
(`dimension.jl:362-365`). -/
instance {U S : Sys} {d : Dim} {α : Type} [QScalar α] :
    HMul (ConvertUnit U S d) (Quantity U d α) (Quantity S d α) :=
  ⟨fun _ q => q.to S⟩

/-- The natural unit of dimension `d` expressed in `U` (Julia `d(U)`,
`dimension.jl:248`): `U(ratio(d, Natural, U), d)`. -/
def naturalUnit (U : Sys) (d : Dim) : Q U d := ⟨ratio d.toGroup.v .Natural U⟩

end Similitude
