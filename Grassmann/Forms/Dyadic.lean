/-
Unmaterialised rank-one forms: `Dyadic` (`x ⊗ y`), `Projector` (`λ v̂ ⊗ v̂`)
and `SpectralOperator` (`Σₖ λₖ vₖ ⊗ vₖ`, the result of `eigen`) (Grassmann.jl
`src/forms.jl:374-472, 894-991`; port-notes/grassmann-forms.md §2.4-2.5, §4.6).

Their action on an element uses Grassmann's **contraction** of the element
with the stored vectors (`P ⋅ x = v ⊗ (λ (v ⋅ x))`, metric-aware, as Julia),
while their materialisation `Chain(P) = outer(λ v, v)` (`M[i,j] = λ vᵢ conj(vⱼ)`,
`forms.jl:885`) is metric-free: the two agree on Euclidean spaces, exactly as
in Julia. A `SpectralOperator` acts through the coefficient dot
`Σₖ vₖ λₖ conj(vₖ)·x` (Julia's contraction of complex chains conjugates the
left factor, `forms.jl:983`).

Fixed Julia defects (port-notes §8.4): `P[i,j]` includes `λ` and the conjugate
(Julia's ignores both, item 10), `det(::SpectralOperator)` is `Π λₖ` (Julia
returns the eigenvalue chain itself, item 9). Julia's `+` on projectors and
dyadics (broken there, item 8) is not provided; a sum of rank-one terms is a
`SpectralOperator`.
-/
import Grassmann.Forms.Diagonal

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms JuliaBase

namespace Forms

variable {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] [Kernels V]

/-- The scalar `x ⋅ y` of two grade-`G` chains (Grassmann's contraction, the
grade-0 result as a coefficient). -/
@[inline] def cdot (x y : Chain V G α) : α := getD (contraction x y : Chain V (G - G) α).v 0

/-- The coefficient dot `Σᵢ conj(xᵢ) yᵢ` (Julia `value(x) ⋅ value(y)`, a left fold). -/
@[inline] def vdot {n : Nat} [Conj α] (x y : Values α n) : α := Mat.sdot0 conj x.data y.data 1 1 n 0 0

/-- Julia `outer(a, b)` (`forms.jl:885`): the matrix with columns `a · conj(bⱼ)`. -/
@[inline] def outer {W : TensorBundle} {H : Nat} [Conj α] (a : Chain W H α) (b : Chain V G α) :
    TensorOperator V (.chain G) W (.chain H) α :=
  TensorOperator.ofFn fun i j => a.v.get i * conj (b.v.get j)

end Forms

/-! ## Dyadic -/

/-- Julia `Dyadic{V,X,Y}` (`forms.jl:440-445`): the rank-one map `x ⊗ y`,
`z ↦ x (y ⋅ z)`, from grade `G` of `V` (the side of `y`) to grade `H` of `W`. -/
structure Dyadic (V : TensorBundle) (G : Nat) (W : TensorBundle) (H : Nat) (α : Type) [Coeff α] where
  /-- The image direction (Julia `D.x`). -/
  x : Chain W H α
  /-- The covector side (Julia `D.y`). -/
  y : Chain V G α

namespace Dyadic

variable {V W U : TensorBundle} {G H K : Nat} {α : Type} [Coeff α]

/-- Julia `D ⋅ z = x ⊗ (y ⋅ z)` (`forms.jl:922`). -/
@[inline] def apply [Kernels V] (D : Dyadic V G W H α) (z : Chain V G α) : Chain W H α :=
  D.x * Forms.cdot D.y z

/-- Julia `z ⋅ D = (z ⋅ x) ⊗ y` (`forms.jl:923`). -/
@[inline] def rowApply [Kernels W] (z : Chain W H α) (D : Dyadic V G W H α) : Chain V G α :=
  Forms.cdot z D.x * D.y

/-- Julia `D ⋅ D' = (x (y ⋅ x')) ⊗ y'` (`forms.jl:925`). -/
@[inline] def comp [Kernels W] (A : Dyadic W H U K α) (B : Dyadic V G W H α) : Dyadic V G U K α :=
  ⟨A.x * Forms.cdot A.y B.x, B.y⟩

/-- Julia `tr(D) = value(x) ⋅ value(y)` (`forms.jl:459`), the coefficient dot. -/
@[inline] def tr [Conj α] (D : Dyadic V G V G α) : α := Forms.vdot D.x.v D.y.v

/-- Julia `D[i+1, j+1] = x[i+1] y[j+1]` (`forms.jl:461`). -/
@[inline] def entry (D : Dyadic V G W H α) (i j : Nat) : α := getD D.x.v i * getD D.y.v j

/-- Julia `transpose(D) = Dyadic(y, x)` (`forms.jl:462`). -/
@[inline] def transpose (D : Dyadic V G W H α) : Dyadic W H V G α := ⟨D.y, D.x⟩

/-- Julia `Chain(D) = outer(x, y)` (`forms.jl:466`): the materialised operator. -/
@[inline] def toOperator [Conj α] (D : Dyadic V G W H α) : TensorOperator V (.chain G) W (.chain H) α :=
  Forms.outer D.x D.y

instance : HMul α (Dyadic V G W H α) (Dyadic V G W H α) := ⟨fun s D => ⟨s * D.x, D.y⟩⟩
instance : HMul (Dyadic V G W H α) α (Dyadic V G W H α) := ⟨fun D s => ⟨D.x * s, D.y⟩⟩
instance [Kernels V] : HMul (Dyadic V G W H α) (Chain V G α) (Chain W H α) := ⟨apply⟩
instance [Kernels V] : Contraction (Dyadic V G W H α) (Chain V G α) (Chain W H α) := ⟨apply⟩
instance [Kernels W] : Contraction (Chain W H α) (Dyadic V G W H α) (Chain V G α) := ⟨rowApply⟩
instance [Kernels W] : Contraction (Dyadic W H U K α) (Dyadic V G W H α) (Dyadic V G U K α) := ⟨comp⟩
instance [Kernels W] : HMul (Dyadic W H U K α) (Dyadic V G W H α) (Dyadic V G U K α) := ⟨comp⟩

end Dyadic

/-- Julia `x ⊗ y` of two graded elements (`algebra.jl:150-152`): the dyadic. -/
instance {V W : TensorBundle} {G H : Nat} {α : Type} [Coeff α] :
    TensorProd (Chain W H α) (Chain V G α) (Dyadic V G W H α) := ⟨fun x y => ⟨x, y⟩⟩

/-- Julia `x ⊗ y` with a term on either side (`algebra.jl:150-152`, `Single`/`Submanifold`
operands): the dyadic of the chains. -/
instance {V W : TensorBundle} {G H : Nat} {α : Type} [Coeff α] :
    TensorProd (Single W H α) (Chain V G α) (Dyadic V G W H α) := ⟨fun x y => ⟨Chain.ofSingle x, y⟩⟩
instance {V W : TensorBundle} {G H : Nat} {α : Type} [Coeff α] :
    TensorProd (Chain W H α) (Single V G α) (Dyadic V G W H α) := ⟨fun x y => ⟨x, Chain.ofSingle y⟩⟩
instance {V W : TensorBundle} {G H : Nat} {α : Type} [Coeff α] :
    TensorProd (Single W H α) (Single V G α) (Dyadic V G W H α) :=
  ⟨fun x y => ⟨Chain.ofSingle x, Chain.ofSingle y⟩⟩

/-- Julia `a ⊗ t = a * t` for a scalar `a` (`AT:333`, `⊗` of numbers is multiplication). -/
instance {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] : TensorProd α (Chain V G α) (Chain V G α) :=
  ⟨fun a t => a * t⟩
instance {V : TensorBundle} {G : Nat} {α : Type} [Coeff α] : TensorProd (Chain V G α) α (Chain V G α) :=
  ⟨fun t a => t * a⟩

/-! ## Projector -/

/-- Julia `Projector{V,T,Λ}` (`forms.jl:374-380`): `λ v ⊗ v`, `x ↦ v (λ (v ⋅ x))`
(`forms.jl:921`). The constructor `Projector.ofVector` normalises `v`. -/
structure Projector (V : TensorBundle) (G : Nat) (α : Type) [Coeff α] where
  /-- The (unit) direction. -/
  v : Chain V G α
  /-- The eigenvalue (Julia `P.λ`, default `1`). -/
  lam : α

/-- Julia `const Proj = Projector` (`forms.jl:382`); `Proj(v, λ)` is `Projector.ofVector`. -/
abbrev Proj (V : TensorBundle) (G : Nat) (α : Type) [Coeff α] := Projector V G α

namespace Projector

variable {V W : TensorBundle} {G H : Nat} {α : Type} [Coeff α]

/-- Julia `Proj(v, λ=1) = Projector(v/abs(v), λ)` (`forms.jl:386`), with the
metric norm `abs(v) = √(v ⋅ v)`. -/
@[inline] def ofVector [Kernels V] [Div α] [Analytic α] (v : Chain V G α) (lam : α := Coeff.one) :
    Projector V G α :=
  ⟨v / Analytic.sqrt (Forms.cdot v v), lam⟩

/-- Julia `P ⋅ x = v ⊗ (λ (v ⋅ x))` (`forms.jl:921`). -/
@[inline] def apply [Kernels V] (P : Projector V G α) (x : Chain V G α) : Chain V G α :=
  P.v * (P.lam * Forms.cdot P.v x)

/-- Julia `x ⋅ P = ((x ⋅ v) λ) ⊗ v` (`forms.jl:924`). -/
@[inline] def rowApply [Kernels V] (x : Chain V G α) (P : Projector V G α) : Chain V G α :=
  (Forms.cdot x P.v * P.lam) * P.v

/-- Julia `P ⋅ P' = (v ((λ lam) (v ⋅ v'))) ⊗ v'` (`forms.jl:928`): a dyadic. -/
@[inline] def comp [Kernels V] (A B : Projector V G α) : Dyadic V G V G α :=
  ⟨A.v * ((A.lam * B.lam) * Forms.cdot A.v B.v), B.v⟩

/-- Julia `Dyadic(P) = Dyadic(v λ, v)` (`forms.jl:448`). -/
@[inline] def toDyadic (P : Projector V G α) : Dyadic V G V G α := ⟨P.v * P.lam, P.v⟩

/-- Julia `Chain(P) = outer(v λ, v)` (`forms.jl:432`): `M[i,j] = vᵢ λ conj(vⱼ)`. -/
@[inline] def toOperator [Conj α] (P : Projector V G α) : Endomorphism V (.chain G) α :=
  Forms.outer (P.v * P.lam) P.v

/-- `P[i+1, j+1] = λ vᵢ conj(vⱼ)`, the entry of `Chain(P)` (Julia's
`P.v[i]*P.v[j]`, `forms.jl:419`, drops `λ` and the conjugate). -/
@[inline] def entry [Conj α] (P : Projector V G α) (i j : Nat) : α :=
  getD P.v.v i * P.lam * conj (getD P.v.v j)

/-- Julia `tr(P) = λ` (`forms.jl:415`). -/
@[inline] def tr (P : Projector V G α) : α := P.lam

/-- Julia `det(P)` (`forms.jl:409`): `λ` in one dimension, else `0`. -/
@[inline] def det (P : Projector V G α) : α := if Leibniz.binomial V.n G = 1 then P.lam else Coeff.zero

instance : HMul α (Projector V G α) (Projector V G α) := ⟨fun s P => ⟨P.v, s * P.lam⟩⟩
instance : HMul (Projector V G α) α (Projector V G α) := ⟨fun P s => ⟨P.v, P.lam * s⟩⟩
instance [Kernels V] : HMul (Projector V G α) (Chain V G α) (Chain V G α) := ⟨apply⟩
instance [Kernels V] : Contraction (Projector V G α) (Chain V G α) (Chain V G α) := ⟨apply⟩
instance [Kernels V] : Contraction (Chain V G α) (Projector V G α) (Chain V G α) := ⟨rowApply⟩
instance [Kernels V] : Contraction (Projector V G α) (Projector V G α) (Dyadic V G V G α) := ⟨comp⟩

/-- Julia `D ⋅ P = (x ((y ⋅ v) λ)) ⊗ v` (`forms.jl:926`). -/
instance [Kernels V] : Contraction (Dyadic V G W H α) (Projector V G α) (Dyadic V G W H α) :=
  ⟨fun D P => ⟨D.x * (Forms.cdot D.y P.v * P.lam), P.v⟩⟩

/-- Julia `P ⋅ D = (v (λ (v ⋅ x))) ⊗ y` (`forms.jl:927`). -/
instance [Kernels V] : Contraction (Projector V G α) (Dyadic W H V G α) (Dyadic W H V G α) :=
  ⟨fun P D => ⟨P.v * (P.lam * Forms.cdot P.v D.x), D.y⟩⟩

end Projector

/-! ## SpectralOperator -/

/-- Julia `SpectralOperator{V} = Projector{V,<:Chain{W,1,<:Chain{V,1}}}`
(`forms.jl:383`): `Σₖ λₖ vₖ ⊗ vₖ`, the result of `eigen`: the eigenvectors are
the columns of `vecs`, the eigenvalues `vals`. -/
structure SpectralOperator (V : TensorBundle) (α : Type) [Coeff α] where
  /-- The vectors `vₖ` as columns (Julia `P.v`). -/
  vecs : Endomorphism V (.chain 1) α
  /-- The eigenvalues `λₖ` (Julia `P.λ`). -/
  vals : Values α ((Layout.chain 1).size V.n)

namespace SpectralOperator

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `Proj(v::Chain{W,1,<:Chain{V}}, λ)` (`forms.jl:387`): the vectors normalised by
their metric norms `vₖ/|vₖ|` (the columns of `vecs`), with eigenvalues `vals`. -/
@[specialize] def ofVectors [Kernels V] [Div α] [Analytic α] (vecs : Endomorphism V (.chain 1) α)
    (vals : Values α ((Layout.chain 1).size V.n)) : SpectralOperator V α :=
  ⟨TensorOperator.ofColumns fun j =>
    let v : Chain V 1 α := vecs.column j
    (v / Analytic.sqrt (Forms.cdot v v) : Chain V 1 α), vals⟩

/-- The number of rank-one terms. -/
@[inline] def size (_ : SpectralOperator V α) : Nat := (Layout.chain 1).size V.n

/-- Julia `S ⋅ b = Σₖ vₖ (λₖ (vₖ ⋅ b))` (`forms.jl:983`), with the conjugating
coefficient dot; the terms are added left to right. -/
@[specialize] def apply [Conj α] (S : SpectralOperator V α) (b : Chain V 1 α) : Chain V 1 α :=
  let term := fun (k : Nat) =>
    let vk : Values α ((Layout.chain 1).size V.n) := Values.ofFn fun i => S.vecs.entry i.1 k
    let s := getD S.vals k * Forms.vdot vk b.v
    (⟨vk.map (· * s)⟩ : Chain V 1 α)
  match S.size with
  | 0 => Chain.zero
  | n + 1 => (List.range n).foldl (fun acc k => acc + term (k + 1)) (term 0)

/-- Julia `Chain(S) = Σₖ outer(vₖ λₖ, vₖ)` (`forms.jl:431`): the materialised
endomorphism, `M[i,j] = Σₖ vₖ[i] λₖ conj(vₖ[j])` (a left fold over `k`). -/
@[specialize] def toOperator [Conj α] (S : SpectralOperator V α) : Endomorphism V (.chain 1) α :=
  let n := S.size
  TensorOperator.ofFn fun i j =>
    let t := fun (k : Nat) => S.vecs.entry i.1 k * getD S.vals k * conj (S.vecs.entry j.1 k)
    match n with
    | 0 => Coeff.zero
    | n + 1 => (List.range n).foldl (fun acc k => acc + t (k + 1)) (t 0)

/-- Julia `tr(S) = sum(λ)` (`forms.jl:415`). -/
@[inline] def tr (S : SpectralOperator V α) : α := S.vals.reduce (· + ·) Coeff.zero

/-- `det(S) = Π λₖ` (Julia's `prod(P.λ)` of a chain returns the chain itself,
`forms.jl:416`). -/
@[inline] def det (S : SpectralOperator V α) : α := S.vals.reduce (· * ·) Coeff.one

/-- Julia `S[k+1] = Proj(vₖ, λₖ)` (`forms.jl:420`). -/
@[inline] def term (S : SpectralOperator V α) (k : Fin ((Layout.chain 1).size V.n)) : Projector V 1 α :=
  ⟨Chain.mk (S.vecs.mat.col k), S.vals.get k⟩

/-- `S[i+1, j+1]`: the entry of `Chain(S)` (Julia's `Σₖ vₖ[i] vₖ[j]` ignores `λ`
and the conjugate, `forms.jl:421`). -/
@[inline] def entry [Conj α] (S : SpectralOperator V α) (i j : Nat) : α := S.toOperator.entry i j

/-- Functional calculus: the same vectors, `f(λₖ)` (Julia `exp`, `log`, `inv`
of a `SpectralOperator`, `forms.jl:411-413`). -/
@[inline] def mapVals (f : α → α) (S : SpectralOperator V α) : SpectralOperator V α :=
  ⟨S.vecs, S.vals.map f⟩

/-- Julia `exp(S)`. -/
@[inline] def exp [Analytic α] (S : SpectralOperator V α) : SpectralOperator V α := S.mapVals Analytic.exp
/-- Julia `log(S)`. -/
@[inline] def log [Analytic α] (S : SpectralOperator V α) : SpectralOperator V α := S.mapVals Analytic.log
/-- Julia `inv(S)`. -/
@[inline] def inv [Div α] (S : SpectralOperator V α) : SpectralOperator V α := S.mapVals (Coeff.one / ·)
/-- Julia `invdet(S) = (inv(S), det(S))`. -/
@[inline] def invdet [Div α] (S : SpectralOperator V α) : SpectralOperator V α × α := (S.inv, S.det)

instance : HMul α (SpectralOperator V α) (SpectralOperator V α) := ⟨fun s S => ⟨S.vecs, S.vals.map (s * ·)⟩⟩
instance : HMul (SpectralOperator V α) α (SpectralOperator V α) := ⟨fun S s => ⟨S.vecs, S.vals.map (· * s)⟩⟩
instance [Conj α] : HMul (SpectralOperator V α) (Chain V 1 α) (Chain V 1 α) := ⟨apply⟩
instance [Conj α] : Contraction (SpectralOperator V α) (Chain V 1 α) (Chain V 1 α) := ⟨apply⟩

end SpectralOperator

end Grassmann
