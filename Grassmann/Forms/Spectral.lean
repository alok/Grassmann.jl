/-
Spectral tools of operators (Grassmann.jl `src/forms.jl:1217-1543`;
port-notes/grassmann-forms.md §2.10, §4.9-4.10): characteristic polynomials,
normalised elementary symmetric polynomials (`eigpolys`), Sylvester products,
multiplicities, eigenvalues, eigen-decompositions, Vandermonde matrices and
discriminants.

* `characteristic(X)` returns `(c₀, …, c_{n-1})` with
  `det(zI − X) = zⁿ + c_{n-1}zⁿ⁻¹ + … + c₀`: Julia's closed forms for `n ≤ 4`
  (traces and the determinant, `forms.jl:1445-1462`) and the traces of the
  compounds (`characteristic_exact`, `forms.jl:1500-1517`) beyond. The closed
  forms divide by `2` and `-6`: use a field coefficient type (Julia turns `Int`
  input into `Float64` there).
* `eigvals(X)`: `n = 1` the entry, `n < 5` the closed-form roots of the
  characteristic polynomial (`Forms.Roots`), `n ≥ 5` the dense eigensolver
  (`Forms.Eigen`, Julia: LAPACK), as `Forms.Spectrum` (real- or complex-typed
  exactly when Julia's result is).
* `eigen(X)`: always the dense eigensolver (Julia: LAPACK `eigen(Matrix(X))`),
  as a `SpectralOperator`.
-/
import Grassmann.Forms.Dyadic
import Grassmann.Forms.Eigen

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms JuliaBase

namespace Forms

variable {α : Type} [Coeff α]

/-- Julia's `x^k` for a literal non-negative exponent: `1`, `x`, `x*x`, `x*x*x`
(`Base.literal_pow`), then binary powering (Julia `power_by_squaring`). -/
@[specialize] def literalPow (x : α) : Nat → α
  | 0 => Coeff.one
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x
  | k + 4 =>
    let rec go (b : α) (e : Nat) (acc : α) (fuel : Nat) : α :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
        if e == 0 then acc
        else go (b * b) (e / 2) (if e % 2 == 1 then acc * b else acc) fuel
    go x (k + 4) Coeff.one 64

/-- Julia `nozero(x) = iszero(x) ? one(x) : x` (`forms.jl:1221`). -/
@[inline] def nozero (x : α) : α := if Coeff.isZero x then Coeff.one else x

/-- Julia `sylvester(x)` of a vector (`forms.jl:1225-1227`):
`(Π_{j≠i} nozero(xⱼ - xᵢ))ᵢ`, `j` ascending, a left fold from the first factor. -/
@[specialize] def sylvesterValues {n : Nat} (x : Values α n) : Values α n :=
  Values.ofFn fun i =>
    let fs := (List.range n).filter (· != i.1) |>.map fun j => nozero (getD x j - x.get i)
    match fs with
    | [] => Coeff.one
    | f :: rest => rest.foldl (· * ·) f

/-- Julia `eigmults(x)` (`forms.jl:1228-1231`): `1 + #{j ≠ i : xⱼ = xᵢ}` (exact equality). -/
def eigmultsValues {n : Nat} [BEq α] (x : Values α n) : Values Int n :=
  Values.ofFn fun i => 1 + ((List.range n).filter fun j => j != i.1 && getD x j == x.get i).length

/-- Julia `vandermonde(x)` (`composite.jl:872-876`, `forms.jl:1528`): the matrix
`V[i,j] = xᵢ^(j-1)` on `ℝⁿ`. -/
@[specialize] def vandermonde {n : Nat} (x : Values α n) : Endomorphism (TensorBundle.euclidean n) (.chain 1) α :=
  TensorOperator.ofFn fun i j =>
    literalPow (getD x i.1) j.1

/-- Julia `discriminant(x) = det(vandermonde(x))²` (`forms.jl:1533`):
`Π_{i<j}(xⱼ - xᵢ)²`. -/
@[inline] def discriminantValues {n : Nat} (x : Values α n) : α :=
  let d := (vandermonde x).det
  d * d

end Forms

namespace TensorOperator

variable {V : TensorBundle} {α : Type} [Coeff α]

open Forms

/-- The row-major `Float` buffer of an operator (Julia `Matrix(X)`). -/
def rowMajor {W : TensorBundle} {ld lc : Layout} (X : TensorOperator V ld W lc Float) : FloatArray :=
  let r := lc.size W.n
  let c := ld.size V.n
  ⟨(Array.range (r * c)).map fun t => X.entry (t / c) (t % c)⟩

/-- Julia `characteristic_exact(X)` (`forms.jl:1500-1517`): `cₖ₋₁ = ±tr(Λ^{n-k+1} X)`
(sign `+` iff `n − k` is odd), exact over `Int`. -/
@[specialize] def characteristicExact (X : Endomorphism V (.chain 1) α) : Chain V 1 α :=
  let n := V.n
  let out := fun (g : Nat) => (X.compound g).tr
  ⟨Values.ofFn fun k =>
    let t := out (n - k.1)
    if (n - (k.1 + 1)) % 2 == 1 then t else -t⟩

/-- Julia `characteristic(X)` (`forms.jl:1445-1462`): the monic characteristic
polynomial's lower coefficients `(c₀, …, c_{n-1})`, by Julia's closed forms for
`n ≤ 4` and `characteristicExact` beyond. -/
@[specialize] def characteristicGeneric [Div α] (X : Endomorphism V (.chain 1) α) : Chain V 1 α :=
  let n := V.n
  let c := fun (l : List α) => (⟨Values.ofFn fun i => l[i.1]?.getD Coeff.zero⟩ : Chain V 1 α)
  if n = 1 then c [-X.entry 0 0]
  else if n = 2 then c [X.det, -X.tr]
  else if n = 3 then
    let a0 := -X.det
    let a2 := X.tr
    c [a0, (a2 * a2 - (X.comp X).tr) / Coeff.ofInt 2, -a2]
  else if n = 4 then
    let a3 := X.tr
    let a0 := X.det
    let X2 := X.comp X
    let a32 := a3 * a3
    let trX2 := X2.tr
    let a2 := (a32 - trX2) / Coeff.ofInt 2
    let a1 := (a3 * (a32 - Coeff.ofInt 3 * trX2) + Coeff.ofInt 2 * (X2.comp X).tr) / Coeff.ofInt (-6)
    c [a0, a1, a2, -a3]
  else X.characteristicExact

/-- Julia `characteristic(X)`: the generated straight-line forms for `3 ≤ n ≤ 6`
(`Grassmann.Forms.Unrolled`, bit-identical to `characteristicGeneric`: the closed forms for
`n ≤ 4`, the traces of the compounds beyond), `characteristicGeneric` otherwise. -/
@[specialize] def characteristic [Div α] (X : Endomorphism V (.chain 1) α) : Chain V 1 α :=
  let a := X.mat.v.data
  if V.n = 3 then ⟨Mat.finish (Unrolled.characteristic3 a)⟩
  else if V.n = 4 then ⟨Mat.finish (Unrolled.characteristic4 a)⟩
  else if V.n = 5 then ⟨Mat.finish (Unrolled.characteristic5 a)⟩
  else if V.n = 6 then ⟨Mat.finish (Unrolled.characteristic6 a)⟩
  else X.characteristicGeneric

/-- Julia `characteristic(X, m)` (`forms.jl:1464-1498`): the coefficient
`c_{m-1}` (1-based `m`). -/
@[inline] def characteristicAt [Div α] (X : Endomorphism V (.chain 1) α) (m : Nat) : α :=
  getD X.characteristic.v (m - 1)

/-- Julia `eigpolys(X, G)` (`forms.jl:1249-1257`): the normalised elementary
symmetric polynomial `e_G(λ)/C(n,G)` of the eigenvalues, `(-1)^G c_{n-G}/C(n,G)`
(`det X` for `G = n`, `1` for `G = 0`). -/
@[specialize] def eigpolysAt [Div α] (X : Endomorphism V (.chain 1) α) (G : Nat) : α :=
  let n := V.n
  if G = 0 then Coeff.one
  else if n = G then X.det
  else if n = 2 ∧ G = 1 then X.scalar
  else
    let c := X.characteristicAt (n - G + 1) / Coeff.ofInt (Leibniz.binomial n G)
    if G % 2 == 1 then -c else c

/-- Julia `eigpolys(X)` (`forms.jl:1233-1240`): `(E₁, …, Eₙ)`, `Eₖ = eₖ(λ)/C(n,k)`
computed from the characteristic polynomial (`n = 2`: from `scalar(X)` and `det X`). -/
@[specialize] def eigpolys [Div α] (X : Endomorphism V (.chain 1) α) : Chain V 1 α :=
  let n := V.n
  if n = 2 then ⟨Values.ofFn fun k => X.eigpolysAt (k.1 + 1)⟩
  else
    let c := X.characteristic.v
    ⟨Values.ofFn fun k =>
      let e := getD c (n - 1 - k.1) / Coeff.ofInt (Leibniz.binomial n (k.1 + 1))
      if (k.1 + 1) % 2 == 1 then e * Coeff.ofInt (-1) else e⟩

/-- Julia `eigvals(X)` of a real grade-1 endomorphism (`forms.jl:1374-1383`):
the entry for `n = 1`, the closed-form roots of `characteristic(X)` for `n < 5`,
the dense eigensolver beyond (sorted by `(re, im)`). -/
def eigvals (X : Endomorphism V (.chain 1) Float) : Spectrum ((Layout.chain 1).size V.n) :=
  let n := (Layout.chain 1).size V.n
  if V.n < 5 then
    match Roots.monicroots? (n := n) X.characteristic.v with
    | some s => s
    | none => .real (Values.replicate 0)
  else
    let d := Eigen.eigen X.rowMajor n
    if d.real then .real (Values.ofFn fun i => d.re.get! i.1)
    else .complex (Values.ofFn fun i => ⟨d.re.get! i.1, d.im.get! i.1⟩)

/-- Julia `eigvalsreal(X)` (`forms.jl:1384-1393`): real eigenvalues, or Julia's
`DomainError` (`n < 5`, a complex root) / a complex spectrum (`n ≥ 5`). -/
def eigvalsreal (X : Endomorphism V (.chain 1) Float) :
    Except String (Values Float ((Layout.chain 1).size V.n)) :=
  let n := (Layout.chain 1).size V.n
  if V.n < 5 then
    match Roots.monicrootsreal? (n := n) X.characteristic.v with
    | some r => r
    | none => .error "unreachable"
  else
    let d := Eigen.eigen X.rowMajor n
    if d.real then .ok (Values.ofFn fun i => d.re.get! i.1)
    else .error "InexactError: Float64(complex eigenvalue)"

/-- Julia `eigvalscomplex(X)` (`forms.jl:1415-1427`): complex eigenvalues. -/
def eigvalscomplex (X : Endomorphism V (.chain 1) Float) : Values (Complex Float) ((Layout.chain 1).size V.n) :=
  let n := (Layout.chain 1).size V.n
  if V.n < 5 then
    match Roots.monicrootscomplex? (n := n) X.characteristic.v with
    | some r => r
    | none => Values.replicate ⟨0, 0⟩
  else
    let d := Eigen.eigen X.rowMajor n
    Values.ofFn fun i => ⟨d.re.get! i.1, d.im.get! i.1⟩

/-- The spectral decomposition, real- or complex-typed as Julia's `eigen` is. -/
inductive EigenResult (V : TensorBundle) where
  /-- Real eigenvalues and eigenvectors. -/
  | real (S : SpectralOperator V Float)
  /-- Complex eigenvalues and eigenvectors. -/
  | complex (S : SpectralOperator V (Complex Float))

/-- The complex decomposition of a real matrix from the dense eigensolver. -/
def eigenDecomposition (X : Endomorphism V (.chain 1) Float) : Eigen.Decomposition :=
  Eigen.eigen X.rowMajor ((Layout.chain 1).size V.n)

/-- Julia `eigencomplex(X)` (`forms.jl:1436-1439`): eigenvectors (unit columns)
and eigenvalues as a complex `SpectralOperator`. -/
def eigencomplex (X : Endomorphism V (.chain 1) Float) : SpectralOperator V (Complex Float) :=
  let d := X.eigenDecomposition
  let n := d.n
  ⟨TensorOperator.ofFn fun i j => ⟨d.vre.get! (i.1 * n + j.1), d.vim.get! (i.1 * n + j.1)⟩,
   Values.ofFn fun k => ⟨d.re.get! k.1, d.im.get! k.1⟩⟩

/-- Julia `eigenreal(X)` (`forms.jl:1432-1435`): the real decomposition, or an
error when an eigenvalue is complex (Julia's `InexactError`). -/
def eigenreal (X : Endomorphism V (.chain 1) Float) : Except String (SpectralOperator V Float) :=
  let d := X.eigenDecomposition
  let n := d.n
  if d.real then
    .ok ⟨TensorOperator.ofFn fun i j => d.vre.get! (i.1 * n + j.1), Values.ofFn fun k => d.re.get! k.1⟩
  else .error "InexactError: Float64(complex eigenvalue)"

/-- Julia `eigen(X)` (`forms.jl:1428-1431`): real-typed when every eigenvalue is
real, complex otherwise. -/
def eigen (X : Endomorphism V (.chain 1) Float) : EigenResult V :=
  match X.eigenreal with
  | .ok S => .real S
  | .error _ => .complex X.eigencomplex

/-- Julia `eigvecs(X)` (`forms.jl:1338-1348`): the eigenvectors as the columns of
an operator (complex-typed). -/
@[inline] def eigvecscomplex (X : Endomorphism V (.chain 1) Float) : Endomorphism V (.chain 1) (Complex Float) :=
  X.eigencomplex.vecs

/-- Julia `sylvester(X) = sylvester(eigvals(X))` (`forms.jl:1224`). -/
def sylvester (X : Endomorphism V (.chain 1) Float) : Spectrum ((Layout.chain 1).size V.n) :=
  match X.eigvals with
  | .real v => .real (sylvesterValues v)
  | .complex v => .complex (sylvesterValues v)

/-- Julia `eigmults(X) = eigmults(eigvals(X))` (`forms.jl:1228`). -/
def eigmults (X : Endomorphism V (.chain 1) Float) : Values Int ((Layout.chain 1).size V.n) :=
  match X.eigvals with
  | .real v => eigmultsValues v
  | .complex v => eigmultsValues v

/-- Julia `vandermonde(X) = vandermonde(eigvals(X))` (`forms.jl:1530`), complex-typed. -/
@[inline] def vandermondecomplex (X : Endomorphism V (.chain 1) Float) :
    Endomorphism (TensorBundle.euclidean ((Layout.chain 1).size V.n)) (.chain 1) (Complex Float) :=
  Forms.vandermonde X.eigvalscomplex

/-- Julia `vandermondereal(X) = vandermonde(eigvalsreal(X))` (`forms.jl:1531`). -/
@[inline] def vandermondereal (X : Endomorphism V (.chain 1) Float) :
    Except String (Endomorphism (TensorBundle.euclidean ((Layout.chain 1).size V.n)) (.chain 1) Float) :=
  X.eigvalsreal.map Forms.vandermonde

/-- Julia `discriminant(X)` (`forms.jl:1534-1536`): `tr² − 4 det` for `n = 2`,
else `det(vandermonde(eigvals X))²`, real for a real matrix. -/
def discriminant (X : Endomorphism V (.chain 1) Float) : Float :=
  if V.n = 2 then
    let t := X.tr
    t * t - 4 * X.det
  else
    match X.eigvals with
    | .real v => discriminantValues v
    | .complex v => (discriminantValues v).re

/-- Julia `discriminantcomplex(X)` (`forms.jl:1540-1542`). -/
def discriminantcomplex (X : Endomorphism V (.chain 1) Float) : Float :=
  if V.n = 2 then
    let t := X.tr
    t * t - 4 * X.det
  else (discriminantValues X.eigvalscomplex).re

end TensorOperator

namespace TensorOperator

variable {V : TensorBundle}

/-- The eigenvectors as a real-typed operator (the columns), from the dense eigensolver's
decomposition; the imaginary parts are dropped (callers check `d.real`). -/
def realVecs (d : Eigen.Decomposition) : Endomorphism V (.chain 1) Float :=
  TensorOperator.ofFn fun i j => d.vre.get! (i.1 * d.n + j.1)

/-- Julia `eigvecsreal(X)` of a real grade-1 endomorphism (`forms.jl:1342`,
`Endomorphism{V}(map(Float64, eigvecs(Matrix(X))))`): the eigenvectors (unit columns, in
the order of `eigvals`) as a real operator, or Julia's `InexactError` when an eigenvalue
is complex. -/
def eigvecsreal (X : Endomorphism V (.chain 1) Float) : Except String (Endomorphism V (.chain 1) Float) :=
  let d := X.eigenDecomposition
  if d.real then .ok (realVecs d) else .error "InexactError: Float64(complex eigenvector)"

/-- Julia's type-unstable `eigvecs(X)` (`forms.jl:1338`, LAPACK `eigvecs(Matrix(X))`): a
real operator when every eigenvalue is real, a complex one otherwise. -/
inductive EigVecs (V : TensorBundle) where
  /-- Real eigenvectors (Julia `Matrix{Float64}`). -/
  | real (T : Endomorphism V (.chain 1) Float)
  /-- Complex eigenvectors (Julia `Matrix{ComplexF64}`). -/
  | complex (T : Endomorphism V (.chain 1) (Complex Float))

/-- The eigenvectors as a complex operator, whatever Julia's type. -/
def EigVecs.toComplex : EigVecs V → Endomorphism V (.chain 1) (Complex Float)
  | .real T => T.map fun x => ⟨x, 0⟩
  | .complex T => T

/-- Julia `eigvecs(X)` of a real grade-1 endomorphism (`forms.jl:1338`): real-typed exactly
when every eigenvalue is real (then equal to `eigvecsreal X`), complex otherwise
(`eigvecscomplex X`). -/
def eigvecs (X : Endomorphism V (.chain 1) Float) : EigVecs V :=
  let d := X.eigenDecomposition
  if d.real then .real (realVecs d) else .complex X.eigvecscomplex

end TensorOperator

namespace Forms

open StaticVectors JuliaBase

/-! ## Polynomial roots of any degree (`composite.jl:1092-1226`)

`Forms.Roots` has Julia's closed forms (degree ≤ 4); Julia's `monicroots(a...)` of a
higher degree is `eigvals(companion(Values(a...)))` (`composite.jl:1113`), the LAPACK
eigenvalues of the companion matrix, here `Forms.Eigen` (sorted by `(re, im)` as Julia's
`eigsortby`), so those roots agree with Julia to rounding, not bit for bit. The non-monic
`roots(a₀, …, a_N)` divide by the leading coefficient first (`composite.jl:1094-1110`). -/

/-- The companion decomposition of `zⁿ + a_{n-1}zⁿ⁻¹ + … + a₀` (the dense eigensolver). -/
def companionEigen {n : Nat} (a : Values Float n) : Eigen.Decomposition :=
  Eigen.eigen (Endomorphism.companion a).rowMajor n

/-- Julia `monicroots(a₀, …, a_{n-1})` of any degree (`composite.jl:1112-1180`): the closed
forms for `n ≤ 4`, the eigenvalues of the companion matrix beyond, real-typed exactly
when Julia's result is. -/
def monicroots {n : Nat} (a : Values Float n) : Spectrum n :=
  match Roots.monicroots? a with
  | some s => s
  | none =>
    let d := companionEigen a
    if d.real then .real (Values.ofFn fun i => d.re.get! i.1)
    else .complex (Values.ofFn fun i => ⟨d.re.get! i.1, d.im.get! i.1⟩)

/-- Julia `monicrootsreal(a₀, …, a_{n-1})` of any degree (`composite.jl:1193-1214`): the real
roots, or Julia's `DomainError` (closed forms) / `InexactError` (a complex companion
eigenvalue, `n ≥ 5`). -/
def monicrootsreal {n : Nat} (a : Values Float n) : Except String (Values Float n) :=
  match Roots.monicrootsreal? a with
  | some r => r
  | none =>
    let d := companionEigen a
    if d.real then .ok (Values.ofFn fun i => d.re.get! i.1)
    else .error "InexactError: Float64(complex root)"

/-- Julia `monicrootscomplex(a₀, …, a_{n-1})` of any degree (`composite.jl:1216-1226`). -/
def monicrootscomplex {n : Nat} (a : Values Float n) : Values (Complex Float) n :=
  match Roots.monicrootscomplex? a with
  | some r => r
  | none =>
    let d := companionEigen a
    Values.ofFn fun i => ⟨d.re.get! i.1, d.im.get! i.1⟩

/-- The monic coefficients `(a₀/a_N, …, a_{N-1}/a_N)` of `a₀ + a₁z + … + a_N z^N` (Julia
`a[list(1,N-1)]./a[N]`, one division each). -/
@[inline] def monicOf {n : Nat} (a : Values Float (n + 1)) : Values Float n :=
  let lead := a.get ⟨n, Nat.lt_succ_self n⟩
  Values.ofFn fun i => a.get ⟨i.1, Nat.lt_succ_of_lt i.2⟩ / lead

/-- Julia `roots(a₀, a₁, …, a_N)` (`composite.jl:1094-1099`): the roots of
`a₀ + a₁z + … + a_N z^N`, `monicroots` of the coefficients divided by `a_N`. A constant
(`N = 0`) has no roots; Julia returns `zero(a₀)` there, which is `rootsConst`. -/
def roots {n : Nat} (a : Values Float (n + 1)) : Spectrum n := monicroots (monicOf a)

/-- Julia `rootsreal(a₀, …, a_N)` (`composite.jl:1101-1103`). -/
def rootsreal {n : Nat} (a : Values Float (n + 1)) : Except String (Values Float n) :=
  monicrootsreal (monicOf a)

/-- Julia `rootscomplex(a₀, …, a_N)` (`composite.jl:1105-1110`). -/
def rootscomplex {n : Nat} (a : Values Float (n + 1)) : Values (Complex Float) n :=
  monicrootscomplex (monicOf a)

/-- Julia `roots(a₀)`, `rootsreal(a₀)`, `rootscomplex(a₀)` of a constant: `zero(a₀)`
(`composite.jl:1095, 1102, 1106`), the degenerate value Julia returns for "no roots". -/
@[inline] def rootsConst (_ : Float) : Float := 0

/-- Julia `monicroots(a₀::Complex)`, `monicrootscomplex(a₀::Complex)` of `z + a₀`:
`-a₀` (`composite.jl:1115, 1219`). -/
@[inline] def monicrootsC1 (a0 : Complex Float) : Complex Float := -a0

/-- Julia `monicrootscomplex(a₀::Complex, a₁::Real)` of `z² + a₁z + a₀`
(`composite.jl:1220`, `quadratic(a0, a1, sqrt(Complex(a1*a1-4a0)))`, `composite.jl:1120-1126`)
with a complex constant term. (Julia has no method for a complex `a₁`: `quadratic`
compares `a1 < 0`.) -/
def monicrootscomplexC (a0 : Complex Float) (a1 : Float) : Values (Complex Float) 2 :=
  let rt := ComplexF64.sqrt ⟨a1 * a1 - 4 * a0.re, -(4 * a0.im)⟩
  let a02 : Complex Float := ⟨2 * a0.re, 2 * a0.im⟩
  if a1 < 0 then
    let s : Complex Float := ⟨-a1 + rt.re, rt.im⟩
    Values.ofFn fun i => if i.1 = 0 then ComplexF64.div a02 s else ⟨s.re / 2, s.im / 2⟩
  else
    let s : Complex Float := ⟨-a1 - rt.re, -rt.im⟩
    Values.ofFn fun i => if i.1 = 0 then ⟨s.re / 2, s.im / 2⟩ else ComplexF64.div a02 s

end Forms

namespace Outermorphism

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `characteristic_exact(O)` (`forms.jl:1511-1515`): from the traces of the
stored compounds. -/
@[specialize] def characteristicExact (O : Outermorphism V V α) : Chain V 1 α :=
  let n := V.n
  ⟨Values.ofFn fun k =>
    let t := (O.block (n - k.1)).tr
    if (n - (k.1 + 1)) % 2 == 1 then t else -t⟩

/-- Julia `characteristic(O)` (`forms.jl:1442-1444`): the grade-1 closed forms for
`n < 5`, the stored compounds otherwise. -/
@[specialize] def characteristic [Div α] (O : Outermorphism V V α) : Chain V 1 α :=
  if V.n < 5 then O.base.characteristic else O.characteristicExact

end Outermorphism

namespace DiagonalOperator

variable {V : TensorBundle} {α : Type} [Coeff α]

/-- Julia `characteristic(D) = characteristic_exact(D)` (`forms.jl:1441, 1505-1510`):
`cₖ₋₁ = ±e_{n-k+1}(d)`, the elementary symmetric polynomials of the diagonal. -/
@[specialize] def characteristic (D : DiagonalMorphism V α) : Chain V 1 α :=
  let n := V.n
  ⟨Values.ofFn fun k =>
    let t := (DiagonalMorphism.compound D (n - k.1)).tr
    if (n - (k.1 + 1)) % 2 == 1 then t else -t⟩

/-- Julia `eigpolys(D, G)` (`forms.jl:1258-1260`): `e_G(d)/C(n,G)`, or `Π d` for `G = n`. -/
@[specialize] def eigpolysAt [Div α] (D : DiagonalMorphism V α) (G : Nat) : α :=
  if G = 0 then Coeff.one
  else if V.n = G then DiagonalMorphism.det D
  else (DiagonalMorphism.compound D G).scalar

/-- Julia `eigpolys(D)` (`forms.jl:1241-1246, 1268`). -/
@[specialize] def eigpolys [Div α] (D : DiagonalMorphism V α) : Chain V 1 α :=
  ⟨Values.ofFn fun k => D.eigpolysAt (k.1 + 1)⟩

/-- Julia `eigvals(D)` (`forms.jl:1374-1383`): the roots of the characteristic
polynomial for `n < 5`, the dense eigensolver beyond. -/
def eigvals (D : DiagonalMorphism V Float) : Spectrum ((Layout.chain 1).size V.n) :=
  if V.n = 1 then .real D.d
  else if V.n < 5 then
    match Roots.monicroots? D.characteristic.v with
    | some s => s
    | none => .real D.d
  else D.toOperator.eigvals

/-- Julia `eigvecs(D) = DiagonalOperator(map(unit, value(D)))` (`forms.jl:1336`):
`dᵢ/|dᵢ|`. -/
def eigvecs [Div α] [Analytic α] (D : DiagonalMorphism V α) : DiagonalMorphism V α :=
  D.map fun x => x / Analytic.abs x

/-- Julia `gerschgorin(D)` (`forms.jl:1519`): zero radii. -/
@[inline] def gerschgorin (_ : DiagonalMorphism V α) : Values Float ((Layout.chain 1).size V.n) :=
  Values.replicate 0

/-- Julia `sylvester(D) = sylvester(eigvals(D))`. -/
def sylvester (D : DiagonalMorphism V Float) : Spectrum ((Layout.chain 1).size V.n) :=
  match D.eigvals with
  | .real v => .real (sylvesterValues v)
  | .complex v => .complex (sylvesterValues v)

end DiagonalOperator

end Grassmann
