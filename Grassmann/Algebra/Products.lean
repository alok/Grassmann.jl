/-
Products of typed elements with static result types (DESIGN.md §4.2;
port-notes/grassmann-products.md §4.4-4.6, grassmann-algebra.md §4.2-4.3,
§4.12).

Every product is the bilinear extension of the blade rules, evaluated by the
space's `Kernels` directly between the operands' storage layouts (no
densification). Operands are grouped by their static shape: a homogeneous
element of grade `G` (`AsChain`: `Chain`, `Single`, `Submanifold`), a half of
parity `p` (`Half`), or anything else (`DenseLayout`, e.g. `Multivector`,
`Couple`, `PseudoCouple`), and the result type is the smallest static container
that always holds the product:

| op | graded `G` × graded `H` | graded `G` × `Half q` | `Half p` × `Half q` | otherwise |
|---|---|---|---|---|
| `*`, `⟑` (geometric) | `Half ((G+H) odd)` | `Half (q ^^ G odd)` | `Half (p ^^ q)` | `Multivector` |
| `∧` (exterior) | `Chain (G+H)` | `Half (q ^^ G odd)` | `Half (p ^^ q)` | `Multivector` |
| `∨` (regressive) | `Chain (G+H-n)` | `Half (q ^^ G odd ^^ n odd)` | `Half (p ^^ q ^^ n odd)` | `Multivector` |
| `⋅`, `⨽` (contraction) | `Chain (G-H)` | `Half (q ^^ G odd)` | `Half (p ^^ q)` | `Multivector` |
| `x ⊘ R` (sandwich) | `Chain G` | `Chain G` | `Half p` (of `x`) | `Multivector` |
| `R >>> x` | `Chain G` (of `x`) | `Chain G` | `Half` of `x` | `Multivector` |

(the graded/half columns are symmetric: `Half p × graded G` has the same
parity rule). `Submanifold V 1 * Submanifold V 1` is a `Couple V Int`
(`eᵢeⱼ = g(eᵢ,eⱼ) + eᵢ∧eⱼ`). `G + H > n` gives the empty chain (zero), and the
truncated subtractions `G + H - n`, `G - H` give a zero grade-0 chain when the
product vanishes, as in Julia (which returns `Zero`). Julia's value-dependent
narrowings (a scalar or pseudoscalar factor, `v₁⋅M` giving a `Couple`, ...) are
not static and are left to the dynamic layer; the coefficients agree.

Derived products come from the generic definitions of AbstractTensors:
`⨼` (`leftContraction`), `∗` (`reverseProduct`), `⊛` (`scalarProduct`),
`<<`/`>>` (`shiftLeftContraction`/`shiftRightContraction`) and `×`
(`hodge (a ∧ b)`); `⟇` (`veedot`) and `antidot` are defined here from the
container complements, as Julia's `complementleft(!a ⟑ !b)` and
`complementleft(contraction(!a, !b))` (`src/algebra.jl:391-396`).

Sandwiches (`src/algebra.jl:313-385`, grassmann-products.md §4.6):
`x ⊘ R = (~R) ⟑ x ⟑ involute(R)` and `R >>> x = R ⟑ x ⟑ clifford(R)`; when `x` is
homogeneous and `R` is homogeneous or a half, only the grade of `x` is kept
(Julia's generated `product_sandwich`), otherwise the full product is returned.
Julia leaves term ⊘ term unprojected and projects even-blade `Couple` versors;
for versors the projection drops nothing, so the values agree there.

`⊗` is not provided: for graded operands Julia builds a `Dyadic` operator, which
is outside the element model (oracle-schema.md §12).
-/
import Grassmann.Algebra.Unary

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

variable {V : TensorBundle} {G H : Nat} {p q : Bool} {α : Type} [Coeff α] [Kernels V] {X Y : Type}

/-! ## Geometric product -/

instance [AsChain X V G α] [AsChain Y V H α] : HMul X Y (Half V ((G + H) % 2 == 1) α) :=
  ⟨fun a b => ⟨Kernels.bin .mul (.chain G) (.chain H) (halfLayout ((G + H) % 2 == 1))
    (AsChain.toChain a).v (AsChain.toChain b).v⟩⟩

instance [AsChain X V G α] : HMul X (Half V q α) (Half V (q ^^ (G % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .mul (.chain G) (halfLayout q) (halfLayout (q ^^ (G % 2 == 1)))
    (AsChain.toChain a).v b.v⟩⟩

instance [AsChain Y V H α] : HMul (Half V p α) Y (Half V (p ^^ (H % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .mul (halfLayout p) (.chain H) (halfLayout (p ^^ (H % 2 == 1)))
    a.v (AsChain.toChain b).v⟩⟩

instance : HMul (Half V p α) (Half V q α) (Half V (p ^^ q) α) :=
  ⟨fun a b => ⟨Kernels.bin .mul (halfLayout p) (halfLayout q) (halfLayout (p ^^ q)) a.v b.v⟩⟩

instance (priority := low) [DenseLayout X V α] [DenseLayout Y V α] : HMul X Y (Multivector V α) :=
  ⟨fun a b => ⟨Kernels.bin .mul (layoutOf X) (layoutOf Y) .full
    (DenseLayout.values a) (DenseLayout.values b)⟩⟩

instance : Mul (Multivector V α) :=
  ⟨fun a b => ⟨Kernels.bin .mul .full .full .full a.v b.v⟩⟩

/-- `eᵢ eⱼ = g(eᵢ, eⱼ) + eᵢ ∧ eⱼ` as a `Couple` on the blade `eᵢ ∨ eⱼ` (DESIGN.md §4.2;
valid for every symmetric metric, the conformal null pair included). -/
instance (priority := high) : HMul (Submanifold V 1) (Submanifold V 1) (Couple V Int) :=
  ⟨fun a b =>
    let ts := ((V.terms₂ .mul a.bits b.bits).toOption.getD #[]).filter (·.z == 0)
    let c := fun (k : UInt64) => (ts.find? (·.bits == k)).map (·.coef) |>.getD 0
    let bb := a.bits ||| b.bits
    ⟨bb, Coeff.ofRat (c 0), if bb == 0 then 0 else Coeff.ofRat (c bb)⟩⟩

/-- Julia `⟑` = `*` (`AbstractTensors.jl:296`) on every element type. -/
instance {Z : Type} [DenseLayout X V α] [HMul X Y Z] : WedgeDot X Y Z := ⟨(· * ·)⟩

/-! ## Exterior product -/

instance [AsChain X V G α] [AsChain Y V H α] : Wedge X Y (Chain V (G + H) α) :=
  ⟨fun a b => ⟨Kernels.bin .wedge (.chain G) (.chain H) (.chain (G + H))
    (AsChain.toChain a).v (AsChain.toChain b).v⟩⟩

instance [AsChain X V G α] : Wedge X (Half V q α) (Half V (q ^^ (G % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .wedge (.chain G) (halfLayout q) (halfLayout (q ^^ (G % 2 == 1)))
    (AsChain.toChain a).v b.v⟩⟩

instance [AsChain Y V H α] : Wedge (Half V p α) Y (Half V (p ^^ (H % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .wedge (halfLayout p) (.chain H) (halfLayout (p ^^ (H % 2 == 1)))
    a.v (AsChain.toChain b).v⟩⟩

instance : Wedge (Half V p α) (Half V q α) (Half V (p ^^ q) α) :=
  ⟨fun a b => ⟨Kernels.bin .wedge (halfLayout p) (halfLayout q) (halfLayout (p ^^ q)) a.v b.v⟩⟩

instance (priority := low) [DenseLayout X V α] [DenseLayout Y V α] : Wedge X Y (Multivector V α) :=
  ⟨fun a b => ⟨Kernels.bin .wedge (layoutOf X) (layoutOf Y) .full
    (DenseLayout.values a) (DenseLayout.values b)⟩⟩

/-! ## Regressive product -/

instance [AsChain X V G α] [AsChain Y V H α] : Vee X Y (Chain V (G + H - V.n) α) :=
  ⟨fun a b => ⟨Kernels.bin .vee (.chain G) (.chain H) (.chain (G + H - V.n))
    (AsChain.toChain a).v (AsChain.toChain b).v⟩⟩

instance [AsChain X V G α] :
    Vee X (Half V q α) (Half V (q ^^ (G % 2 == 1) ^^ (V.n % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .vee (.chain G) (halfLayout q)
    (halfLayout (q ^^ (G % 2 == 1) ^^ (V.n % 2 == 1))) (AsChain.toChain a).v b.v⟩⟩

instance [AsChain Y V H α] :
    Vee (Half V p α) Y (Half V (p ^^ (H % 2 == 1) ^^ (V.n % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .vee (halfLayout p) (.chain H)
    (halfLayout (p ^^ (H % 2 == 1) ^^ (V.n % 2 == 1))) a.v (AsChain.toChain b).v⟩⟩

instance : Vee (Half V p α) (Half V q α) (Half V (p ^^ q ^^ (V.n % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .vee (halfLayout p) (halfLayout q)
    (halfLayout (p ^^ q ^^ (V.n % 2 == 1))) a.v b.v⟩⟩

instance (priority := low) [DenseLayout X V α] [DenseLayout Y V α] : Vee X Y (Multivector V α) :=
  ⟨fun a b => ⟨Kernels.bin .vee (layoutOf X) (layoutOf Y) .full
    (DenseLayout.values a) (DenseLayout.values b)⟩⟩

/-! ## Contraction (`a ⋅ b = a ⨽ b = contraction(a, b)`, grade `G - H`) -/

instance [AsChain X V G α] [AsChain Y V H α] : Contraction X Y (Chain V (G - H) α) :=
  ⟨fun a b => ⟨Kernels.bin .contraction (.chain G) (.chain H) (.chain (G - H))
    (AsChain.toChain a).v (AsChain.toChain b).v⟩⟩

instance [AsChain X V G α] : Contraction X (Half V q α) (Half V (q ^^ (G % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .contraction (.chain G) (halfLayout q) (halfLayout (q ^^ (G % 2 == 1)))
    (AsChain.toChain a).v b.v⟩⟩

instance [AsChain Y V H α] : Contraction (Half V p α) Y (Half V (p ^^ (H % 2 == 1)) α) :=
  ⟨fun a b => ⟨Kernels.bin .contraction (halfLayout p) (.chain H) (halfLayout (p ^^ (H % 2 == 1)))
    a.v (AsChain.toChain b).v⟩⟩

instance : Contraction (Half V p α) (Half V q α) (Half V (p ^^ q) α) :=
  ⟨fun a b => ⟨Kernels.bin .contraction (halfLayout p) (halfLayout q) (halfLayout (p ^^ q)) a.v b.v⟩⟩

instance (priority := low) [DenseLayout X V α] [DenseLayout Y V α] :
    Contraction X Y (Multivector V α) :=
  ⟨fun a b => ⟨Kernels.bin .contraction (layoutOf X) (layoutOf Y) .full
    (DenseLayout.values a) (DenseLayout.values b)⟩⟩

/-! ## Products through the complements (`⟇`, `antidot`) -/

/-- Julia `veedot(a, b) = a ⟇ b = complementleft(!a ⟑ !b)` (`src/algebra.jl:391`),
on the container complements. -/
instance (priority := low) {X' Y' Z' Z : Type} [DenseLayout X V α] [ComplementRight X X']
    [ComplementRight Y Y'] [HMul X' Y' Z'] [ComplementLeft Z' Z] : VeeDot X Y Z :=
  ⟨fun a b => complementLeft (complementRight a * complementRight b)⟩

/-- Julia `antidot(a, b) = complementleft(contraction(!a, !b))` (`src/algebra.jl:396`;
aliases `codot`, `pseudodot`, `expansion`, `∘`). -/
instance (priority := low) {X' Y' Z' Z : Type} [DenseLayout X V α] [ComplementRight X X']
    [ComplementRight Y Y'] [Contraction X' Y' Z'] [ComplementLeft Z' Z] : Expansion X Y Z :=
  ⟨fun a b => complementLeft (contraction (complementRight a) (complementRight b))⟩

/-- Julia `antidot(a, b)`. -/
@[inline] def antidot {Z : Type} [Expansion X Y Z] (a : X) (b : Y) : Z := expansion a b

/-! ## Sandwich products -/

section Sandwich

/-- `x ⊘ R = (~R) ⟑ x ⟑ involute(R)` projected onto the grade of `x`. -/
instance [AsChain X V G α] [AsChain Y V H α] : Sandwich X Y (Chain V G α) :=
  ⟨fun x R =>
    let r := (AsChain.toChain R).v
    let lt := halfLayout ((H + G) % 2 == 1)
    let t := Kernels.bin .mul (.chain H) (.chain G) lt (Kernels.un .reverse (.chain H) (.chain H) r)
      (AsChain.toChain x).v
    ⟨Kernels.binProj .mul lt (.chain H) (.chain G) t (Kernels.un .involute (.chain H) (.chain H) r)⟩⟩

instance [AsChain X V G α] : Sandwich X (Half V q α) (Chain V G α) :=
  ⟨fun x R =>
    let lq := halfLayout q
    let lt := halfLayout (q ^^ (G % 2 == 1))
    let t := Kernels.bin .mul lq (.chain G) lt (Kernels.un .reverse lq lq R.v) (AsChain.toChain x).v
    ⟨Kernels.binProj .mul lt lq (.chain G) t (Kernels.un .involute lq lq R.v)⟩⟩

instance [AsChain Y V H α] : Sandwich (Half V p α) Y (Half V p α) :=
  ⟨fun x R =>
    let r := (AsChain.toChain R).v
    let lt := halfLayout (p ^^ (H % 2 == 1))
    let t := Kernels.bin .mul (.chain H) (halfLayout p) lt (Kernels.un .reverse (.chain H) (.chain H) r) x.v
    ⟨Kernels.binProj .mul lt (.chain H) (halfLayout p) t
      (Kernels.un .involute (.chain H) (.chain H) r)⟩⟩

instance : Sandwich (Half V p α) (Half V q α) (Half V p α) :=
  ⟨fun x R =>
    let lq := halfLayout q
    let lt := halfLayout (q ^^ p)
    let t := Kernels.bin .mul lq (halfLayout p) lt (Kernels.un .reverse lq lq R.v) x.v
    ⟨Kernels.binProj .mul lt lq (halfLayout p) t (Kernels.un .involute lq lq R.v)⟩⟩

instance (priority := low) [DenseLayout X V α] [DenseLayout Y V α] : Sandwich X Y (Multivector V α) :=
  ⟨fun x R =>
    let ly := layoutOf Y
    let r := DenseLayout.values R
    let t := Kernels.bin .mul ly (layoutOf X) .full (Kernels.un .reverse ly ly r) (DenseLayout.values x)
    ⟨Kernels.bin .mul .full ly .full t (Kernels.un .involute ly ly r)⟩⟩

/-- `R >>> x = R ⟑ x ⟑ clifford(R)` projected onto the grade of `x`
(Julia `>>>`, `src/algebra.jl:351-385`). -/
instance [AsChain X V G α] [AsChain Y V H α] : HShiftRight Y X (Chain V G α) :=
  ⟨fun R x =>
    let r := (AsChain.toChain R).v
    let lt := halfLayout ((H + G) % 2 == 1)
    let t := Kernels.bin .mul (.chain H) (.chain G) lt r (AsChain.toChain x).v
    ⟨Kernels.binProj .mul lt (.chain H) (.chain G) t (Kernels.un .clifford (.chain H) (.chain H) r)⟩⟩

instance [AsChain X V G α] : HShiftRight (Half V q α) X (Chain V G α) :=
  ⟨fun R x =>
    let lq := halfLayout q
    let lt := halfLayout (q ^^ (G % 2 == 1))
    let t := Kernels.bin .mul lq (.chain G) lt R.v (AsChain.toChain x).v
    ⟨Kernels.binProj .mul lt lq (.chain G) t (Kernels.un .clifford lq lq R.v)⟩⟩

instance [AsChain Y V H α] : HShiftRight Y (Half V p α) (Half V p α) :=
  ⟨fun R x =>
    let r := (AsChain.toChain R).v
    let lt := halfLayout (p ^^ (H % 2 == 1))
    let t := Kernels.bin .mul (.chain H) (halfLayout p) lt r x.v
    ⟨Kernels.binProj .mul lt (.chain H) (halfLayout p) t (Kernels.un .clifford (.chain H) (.chain H) r)⟩⟩

instance : HShiftRight (Half V q α) (Half V p α) (Half V p α) :=
  ⟨fun R x =>
    let lq := halfLayout q
    let lt := halfLayout (q ^^ p)
    let t := Kernels.bin .mul lq (halfLayout p) lt R.v x.v
    ⟨Kernels.binProj .mul lt lq (halfLayout p) t (Kernels.un .clifford lq lq R.v)⟩⟩

instance (priority := low) [DenseLayout X V α] [DenseLayout Y V α] :
    HShiftRight Y X (Multivector V α) :=
  ⟨fun R x =>
    let ly := layoutOf Y
    let r := DenseLayout.values R
    let t := Kernels.bin .mul ly (layoutOf X) .full r (DenseLayout.values x)
    ⟨Kernels.bin .mul .full ly .full t (Kernels.un .clifford ly ly r)⟩⟩

/-- Julia `R >>> x` as a named function (the versor on the left). -/
@[inline] def tsandwich {Z : Type} [HShiftRight Y X Z] (R : Y) (x : X) : Z := R >>> x

end Sandwich

end Grassmann
