/-
Norms, scalar parts and inverses (AbstractTensors.jl `AT:435-480`, Grassmann.jl
`src/algebra.jl:473-555`; port-notes/grassmann-algebra.md §4.8, §4.10,
grassmann-products.md §4.13).

* `norm x` is Julia `norm(t) = norm(value(t))`: the Euclidean norm of the
  stored coefficients (metric-blind), a `Float`.
* `abs2` is Julia's: `contraction(t, t)` for homogeneous elements (a grade-0
  chain), `(~t) ⟑ t` for halves and multivectors (Julia returns its scalar part
  when that is all there is; the typed result keeps the container).
* `inv`: for a chain `~a / ⟨~a a⟩₀` (`src/algebra.jl:482-485`, valid for blades
  and versors, unchecked as in Julia); for halves and multivectors Julia's
  algorithm (`src/algebra.jl:486-532`): with `d = (~m) ⟑ m`, return `~m / d₀` when
  `d` is (numerically) a scalar, `~m ⟑ inv(d_k)` when it is a single grade `k`, and
  fail otherwise (`inv?` returns `none`; the `Inv` instance panics with Julia's
  message). The composite functions (`exp`, `log`, ...) are a later stage.

Julia's graded `abs2`/contraction conjugate complex coefficients (`dot`); the
plan kernels use plain products (grassmann-products.md §4.12), so for complex
coefficients `abs2` here is the bilinear, not the Hermitian, square.
-/
import Grassmann.Algebra.Products

namespace Grassmann

open DirectSum StaticVectors AbstractTensors JuliaBase

variable {V : TensorBundle} {G : Nat} {p : Bool} {α : Type} [Coeff α] {X : Type}

/-- Julia `norm(t) = norm(value(t))`: the Euclidean norm of the coefficients. -/
@[inline] def norm [JNorm α] [DenseLayout X V α] (x : X) : Float := (DenseLayout.values x).norm

/-- Julia `norm_sqr(value(t))`: the sum of the squared coefficient magnitudes. -/
@[inline] def normSqr [JNorm α] [DenseLayout X V α] (x : X) : Float := (DenseLayout.values x).normSqr

/-- The scalar coefficient of any element (Julia `value(scalar(t))`). -/
@[inline] def scalarValue [DenseLayout X V α] (x : X) : α := getD (gradePart x 0).v 0

variable [Kernels V]

namespace Chain

/-- Julia `abs2(t) = contraction(t, t)` for a chain: the grade-0 chain `⟨~t t⟩₀`. -/
@[inline] def abs2 (c : Chain V G α) : Chain V 0 α :=
  (contraction c c : Chain V (G - G) α).cast (Nat.sub_self G)

/-- Julia `inv(t) = ~t / value(scalar(abs2(t)))` (`src/algebra.jl:482-485`). -/
@[inline] def inv [Div α] (c : Chain V G α) : Chain V G α := c.reverse / getD c.abs2.v 0

instance [Div α] : Inv (Chain V G α) := ⟨Chain.inv⟩

end Chain

namespace Single

/-- Julia `abs2(t) = contraction(t, t)` for a single term: a scalar. -/
def abs2 {G : Nat} (s : Single V G α) : α :=
  scaleBy ((V.terms₂ .contraction s.bits s.bits).toOption.bind
    (fun ts => (ts.find? (·.bits == 0)).map (·.coef)) |>.getD 0) (s.val * s.val)

/-- Julia `inv(t)` for a single term: `~t / abs2(t)` (`src/algebra.jl:536-546`). -/
@[inline] def inv [Div α] {G : Nat} (s : Single V G α) : Single V G α := (~s) / s.abs2

instance [Div α] {G : Nat} : Inv (Single V G α) := ⟨Single.inv⟩

end Single

namespace Half

/-- Julia `abs2(t) = (~t) ⟑ t` for a half: a spinor. -/
@[inline] def abs2 (h : Half V p α) : Half V false α := ((~h) * h : Half V (p ^^ p) α).cast (by simp)

/-- Julia `inv(m)` for a spinor or co-spinor (`src/algebra.jl:486-532`), or
`none` where Julia throws `inv(m) is undefined`. -/
def inv? [Div α] [JNorm α] (h : Half V p α) : Option (Half V p α) :=
  let rm := ~h
  let d := h.abs2
  let fd := d.v.norm
  if F64.isapprox (JNorm.norm (getD d.v 0)) fd then
    some (rm / getD d.v 0)
  else
    (List.range (V.n + 1)).findSome? fun k =>
      if k == 0 || k % 2 == 1 then none else
      let dk := d.grade k
      if F64.isapprox dk.v.norm fd then
        some ⟨Kernels.binProj .mul (halfLayout p) (.chain k) (halfLayout p) rm.v dk.inv.v⟩
      else none

instance [Div α] [JNorm α] : Inv (Half V p α) :=
  ⟨fun h => match h.inv? with
    | some x => x
    | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"⟩

end Half

namespace Multivector

/-- Julia `abs2(t) = (~t) ⟑ t` for a multivector. -/
@[inline] def abs2 (m : Multivector V α) : Multivector V α := (~m) * m

/-- Julia `inv(m)` for a multivector (`src/algebra.jl:486-532`), or `none` where
Julia throws `inv(m) is undefined`. -/
def inv? [Div α] [JNorm α] (m : Multivector V α) : Option (Multivector V α) :=
  let rm := ~m
  let d := rm * m
  let fd := d.v.norm
  if F64.isapprox (JNorm.norm d.scalarValue) fd then
    some (rm / d.scalarValue)
  else
    (List.range (V.n + 1)).findSome? fun k =>
      if k == 0 then none else
      let dk := d.grade k
      if F64.isapprox dk.v.norm fd then
        some ⟨Kernels.bin .mul .full (.chain k) .full rm.v dk.inv.v⟩
      else none

instance [Div α] [JNorm α] : Inv (Multivector V α) :=
  ⟨fun m => match m.inv? with
    | some x => x
    | none => panic! "inv(m) is undefined (Grassmann.jl src/algebra.jl:486-532)"⟩

end Multivector

/-- Julia `a / b = a ⟑ inv(b)` (**right** division, `AbstractTensors.jl:320`)
between elements. -/
instance (priority := low) {Y Z : Type} [DenseLayout X V α] [DenseLayout Y V α] [Inv Y]
    [HMul X Y Z] : HDiv X Y Z := ⟨fun a b => a * b⁻¹⟩

end Grassmann
