/-
Matrix functions of operators: `exp`, `expm1`, `log` (Grassmann.jl
`src/composite.jl:196-297`, `src/forms.jl:606-612`; port-notes/grassmann-composite.md
§4.2.7, grassmann-forms.md §6.2).

`exp` is Grassmann's own implementation, ported operation for operation:

* `1 × 1`: the scalar `exp`;
* `2 × 2` real: the closed form from StaticArrays (`cosh`/`sinh` or `cos`/`sin` of
  half the discriminant's square root; Julia's `v == 0` branch hangs on
  `T(1.0)` with a tensor type `T`, here it is `z₁ = 1`, `z₂ = ½`);
* otherwise Higham's scaling-and-squaring Padé approximant (degree 3, 5, 7, 9 or
  13 by the 1-norm, no balancing), `(V − U) \ (V + U)` through the Cramer
  inverse of `Forms.Compound`.

`log` is Julia's `LinearAlgebra.log(Matrix)`: for a symmetric matrix
`V diag(log λ) Vᵀ` from the symmetric eigen-decomposition (as Julia's
`log(::Symmetric)`); otherwise the eigen-decomposition `V diag(log λ) V⁻¹` in
complex arithmetic (Julia uses the Schur-based inverse scaling and squaring:
the values agree to rounding for diagonalisable matrices). A real result is
returned when the logarithm is real (every eigenvalue positive for a symmetric
matrix, the imaginary parts vanish otherwise); `.error` otherwise (Julia returns
a complex matrix there).
-/
import Grassmann.Forms.Spectral

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms JuliaBase

namespace Forms.MatFun

variable {n : Nat}

/-- `c` as a `Float` (Julia `S(c)` for an integer literal `c`). -/
@[inline] def S (c : Int) : Float := Float.ofInt c

/-- Julia's `nA = maximum(sum.(value.(map.(abs, value(A)))))`: the largest column
absolute sum (the 1-norm), each column summed left to right. -/
def norm1 (A : Mat n n Float) : Float :=
  (List.range n).foldl (fun m j =>
    let s := (List.range n).foldl (fun acc i => if i == 0 then (A.getD i j).abs else acc + (A.getD i j).abs) 0
    if j == 0 then s else F64.max m s) 0

/-- `λI + M` (Julia `S(c)*I + M`, adding to the diagonal only). -/
@[inline] def addI (c : Float) (M : Mat n n Float) : Mat n n Float := M.addDiag c

/-- `32382376266240000` (Julia `S(32382376266240000)`). -/
def k32382376266240000 : Float := f64! 32382376266240000.0

/-- `16380` (Julia `S(16380)`). -/
def k16380 : Float := f64! 16380.0

/-- `40840800` (Julia `S(40840800)`). -/
def k40840800 : Float := f64! 40840800.0

/-- `33522128640` (Julia `S(33522128640)`). -/
def k33522128640 : Float := f64! 33522128640.0

/-- `10559470521600` (Julia `S(10559470521600)`). -/
def k10559470521600 : Float := f64! 10559470521600.0

/-- `1187353796428800` (Julia `S(1187353796428800)`). -/
def k1187353796428800 : Float := f64! 1187353796428800.0

/-- `64764752532480000` (Julia `S(64764752532480000)`). -/
def k64764752532480000 : Float := f64! 64764752532480000.0

/-- `182` (Julia `S(182)`). -/
def k182 : Float := f64! 182.0

/-- `960960` (Julia `S(960960)`). -/
def k960960 : Float := f64! 960960.0

/-- `1323241920` (Julia `S(1323241920)`). -/
def k1323241920 : Float := f64! 1323241920.0

/-- `670442572800` (Julia `S(670442572800)`). -/
def k670442572800 : Float := f64! 670442572800.0

/-- `129060195264000` (Julia `S(129060195264000)`). -/
def k129060195264000 : Float := f64! 129060195264000.0

/-- `7771770303897600` (Julia `S(7771770303897600)`). -/
def k7771770303897600 : Float := f64! 7771770303897600.0

/-- `8821612800` (Julia `S(8821612800)`). -/
def k8821612800 : Float := f64! 8821612800.0

/-- `302702400` (Julia `S(302702400)`). -/
def k302702400 : Float := f64! 302702400.0

/-- `2162160` (Julia `S(2162160)`). -/
def k2162160 : Float := f64! 2162160.0

/-- `3960` (Julia `S(3960)`). -/
def k3960 : Float := f64! 3960.0

/-- `17643225600` (Julia `S(17643225600)`). -/
def k17643225600 : Float := f64! 17643225600.0

/-- `2075673600` (Julia `S(2075673600)`). -/
def k2075673600 : Float := f64! 2075673600.0

/-- `30270240` (Julia `S(30270240)`). -/
def k30270240 : Float := f64! 30270240.0

/-- `110880` (Julia `S(110880)`). -/
def k110880 : Float := f64! 110880.0

/-- `90` (Julia `S(90)`). -/
def k90 : Float := f64! 90.0

/-- `8648640` (Julia `S(8648640)`). -/
def k8648640 : Float := f64! 8648640.0

/-- `277200` (Julia `S(277200)`). -/
def k277200 : Float := f64! 277200.0

/-- `1512` (Julia `S(1512)`). -/
def k1512 : Float := f64! 1512.0

/-- `17297280` (Julia `S(17297280)`). -/
def k17297280 : Float := f64! 17297280.0

/-- `1995840` (Julia `S(1995840)`). -/
def k1995840 : Float := f64! 1995840.0

/-- `25200` (Julia `S(25200)`). -/
def k25200 : Float := f64! 25200.0

/-- `56` (Julia `S(56)`). -/
def k56 : Float := f64! 56.0

/-- `15120` (Julia `S(15120)`). -/
def k15120 : Float := f64! 15120.0

/-- `420` (Julia `S(420)`). -/
def k420 : Float := f64! 420.0

/-- `30240` (Julia `S(30240)`). -/
def k30240 : Float := f64! 30240.0

/-- `3360` (Julia `S(3360)`). -/
def k3360 : Float := f64! 3360.0

/-- `30` (Julia `S(30)`). -/
def k30 : Float := f64! 30.0

/-- `60` (Julia `S(60)`). -/
def k60 : Float := f64! 60.0

/-- `120` (Julia `S(120)`). -/
def k120 : Float := f64! 120.0

/-- `12` (Julia `S(12)`). -/
def k12 : Float := f64! 12.0

/-- `2.1`, a Padé threshold. -/
def t21 : Float := f64! 2.1

/-- `0.95`, a Padé threshold. -/
def t095 : Float := f64! 0.95

/-- `0.25`, a Padé threshold. -/
def t025 : Float := f64! 0.25

/-- `0.015`, a Padé threshold. -/
def t0015 : Float := f64! 0.015

/-- `5.4`, a Padé threshold. -/
def t54 : Float := f64! 5.4

/-- Julia's generic `exp(A)` (Higham's Padé scaling and squaring,
`composite.jl:246-297`), with `inv` the matrix inverse for `(V - U) \ (V + U)`. The
coefficients are module constants (an integer or decimal literal inlined here would be
converted at every call). -/
def pade (inv : Mat n n Float → Mat n n Float) (A : Mat n n Float) : Mat n n Float :=
  let nA := norm1 A
  let solve := fun (V U : Mat n n Float) => (inv (V - U)).mul (V + U)
  if nA ≤ t21 then
    let A2 := A.mul A
    let (U, V) :=
      if nA > t095 then
        let U := addI k8821612800 (A2.mul (addI k302702400 (A2.mul (addI k2162160 (A2.mul (addI k3960 A2))))))
        let V := addI k17643225600 (A2.mul (addI k2075673600 (A2.mul (addI k30270240 (A2.mul (addI k110880 (k90 * A2)))))))
        (A.mul U, V)
      else if nA > t025 then
        let U := addI k8648640 (A2.mul (addI k277200 (A2.mul (addI k1512 A2))))
        let V := addI k17297280 (A2.mul (addI k1995840 (A2.mul (addI k25200 (k56 * A2)))))
        (A.mul U, V)
      else if nA > t0015 then
        let U := addI k15120 (A2.mul (addI k420 A2))
        let V := addI k30240 (A2.mul (addI k3360 (k30 * A2)))
        (A.mul U, V)
      else
        let U := addI k60 A2
        let V := addI k120 (k12 * A2)
        (A.mul U, V)
    solve V U
  else
    let s := Float.log2 (nA / t54)
    let si : Nat := if s > 0 then s.ceil.toUInt64.toNat else 0
    -- Julia `A /= 2^si`: the exact power of two
    let A := if s > 0 then A / Float.scaleB 1 si else A
    let A2 := A.mul A
    let A4 := A2.mul A2
    let A6 := A2.mul A4
    let U := addI k32382376266240000
      ((A6.mul ((A6 + k16380 * A4) + k40840800 * A2)) +
        ((k33522128640 * A6 + k10559470521600 * A4) + k1187353796428800 * A2))
    let U := A.mul U
    let V := addI k64764752532480000
      ((A6.mul ((k182 * A6 + k960960 * A4) + k1323241920 * A2)) +
        ((k670442572800 * A6 + k129060195264000 * A4) + k7771770303897600 * A2))
    let E := solve V U
    (List.range si).foldl (fun E _ => E.mul E) E

/-- Julia's `2 × 2` real closed form (`composite.jl:199-224`), column-major
`(m₁₁, m₂₁, m₁₂, m₂₂)`. -/
def exp2 (a c b d : Float) : Float × Float × Float × Float :=
  let v := (a - d) * (a - d) + 4 * b * c
  let (z1, z2) :=
    if v > 0 then
      let z := Float.sqrt v
      (Float.cosh (z / 2), Float.sinh (z / 2) / z)
    else if v < 0 then
      let z := Float.sqrt (-v)
      (Float.cos (z / 2), Float.sin (z / 2) / z)
    else (1, 0.5)
  let r := F64.exp ((a + d) / 2)
  (r * (z1 + (a - d) * z2), r * 2 * c * z2, r * 2 * b * z2, r * (z1 - (a - d) * z2))

end Forms.MatFun

namespace TensorOperator

variable {V : TensorBundle} {l : Layout}

/-- The inverse used by the Padé solve: Julia's Cramer inverse for a grade-1
operator, Gauss-Jordan for the other layouts (where Julia's `\` has no method). -/
def padeInv (V : TensorBundle) : (l : Layout) → Mat (l.size V.n) (l.size V.n) Float →
    Mat (l.size V.n) (l.size V.n) Float
  | .chain 1, M => (TensorOperator.invSquare (V := V) (W := V) ⟨M⟩).mat
  | _, M => TensorOperator.gaussJordan Float.abs M

open Forms.MatFun in
/-- Julia `exp(T)` of a square operator (`composite.jl:196-297`, `forms.jl:610`). -/
def exp (T : Endomorphism V l Float) : Endomorphism V l Float :=
  let n := l.size V.n
  if n = 1 then TensorOperator.ofFn fun _ _ => F64.exp (T.entry 0 0)
  else if n = 2 then
    let (m11, m21, m12, m22) := exp2 (T.entry 0 0) (T.entry 1 0) (T.entry 0 1) (T.entry 1 1)
    TensorOperator.ofFn fun i j => match i.1, j.1 with
      | 0, 0 => m11 | 1, 0 => m21 | 0, 1 => m12 | _, _ => m22
  else ⟨pade (padeInv V l) T.mat⟩

/-- Julia `expm1(T) = exp(T) - I` (`composite.jl:196`). -/
@[inline] def expm1 (T : Endomorphism V l Float) : Endomorphism V l Float := T.exp.addScalar (-1)

/-- Julia `log(T) = Endomorphism(log(Matrix(T)))` (`forms.jl:606`) for a grade-1
endomorphism: the real logarithm when it exists (see the module doc). -/
def log (T : Endomorphism V (.chain 1) Float) : Except String (Endomorphism V (.chain 1) Float) :=
  let n := (Layout.chain 1).size V.n
  let d := T.eigenDecomposition
  if Forms.Eigen.isSymmetric T.rowMajor n then
    if (List.range n).any fun k => d.re.get! k < 0 then
      .error "log of a symmetric matrix with a negative eigenvalue is complex"
    else
      .ok (TensorOperator.ofFn fun i j =>
        let t := fun (k : Nat) =>
          d.vre.get! (i.1 * n + k) * F64.log (d.re.get! k) * d.vre.get! (j.1 * n + k)
        (List.range (n - 1)).foldl (fun acc k => acc + t (k + 1)) (t 0))
  else
    let Vc : Mat n n (Complex Float) := Mat.ofFn fun i j =>
      ⟨d.vre.get! (i.1 * n + j.1), d.vim.get! (i.1 * n + j.1)⟩
    let Vi := TensorOperator.gaussJordan ComplexF64.abs Vc
    let L : Mat n n (Complex Float) := Mat.ofFn fun i j =>
      Vc.get i j * ComplexF64.log ⟨d.re.get! j.1, d.im.get! j.1⟩
    let M := L.mul Vi
    let real := (List.range (n * n)).all fun t =>
      let z := M.getD (t % n) (t / n)
      z.im.abs ≤ 1e-10 * (1 + z.re.abs)
    if real then .ok ⟨M.map (·.re)⟩ else .error "the matrix logarithm is complex"

end TensorOperator

/-! ## Outermorphisms, dyadics and projectors (Julia `forms.jl:401-458, 774-776`) -/

namespace Outermorphism

variable {V : TensorBundle}

/-- Julia `exp(t::Outermorphism) = Outermorphism(exp(t[1]))` (`forms.jl:774-776`): the
compounds of the grade-1 map's exponential. -/
def exp (O : Outermorphism V V Float) : Outermorphism V V Float := ofSimplex O.base.exp

/-- Julia `expm1(t::Outermorphism) = Outermorphism(expm1(t[1]))` (`forms.jl:774-776`). -/
def expm1 (O : Outermorphism V V Float) : Outermorphism V V Float := ofSimplex O.base.expm1

/-- Julia `log(t::Outermorphism) = Outermorphism(log(t[1]))` (`forms.jl:774-776`), where the
real logarithm of the grade-1 map exists. -/
def log (O : Outermorphism V V Float) : Except String (Outermorphism V V Float) :=
  O.base.log.map ofSimplex

end Outermorphism

namespace Dyadic

variable {V : TensorBundle} {G : Nat}

/-- Julia `exp(P::Dyadic) = exp(Endomorphism(P))` (`forms.jl:457`). -/
def exp (D : Dyadic V G V G Float) : Endomorphism V (.chain G) Float := D.toOperator.exp

/-- Julia `expm1(P::Dyadic) = expm1(Endomorphism(P))` (`forms.jl:456`). -/
def expm1 (D : Dyadic V G V G Float) : Endomorphism V (.chain G) Float := D.toOperator.expm1

/-- Julia `log(P::Dyadic) = log(Endomorphism(P))` (`forms.jl:458`), grade 1. -/
def log (D : Dyadic V 1 V 1 Float) : Except String (Endomorphism V (.chain 1) Float) := D.toOperator.log

end Dyadic

namespace Projector

variable {V : TensorBundle} {G : Nat}

/-- The first column `out` of an operator as Julia's `Proj{V}(out/√out[1])` (`forms.jl:401-408`:
the raw constructor, no renormalisation, `λ = 1`). -/
@[inline] def ofFirstColumn (M : Endomorphism V (.chain G) Float) : Projector V G Float :=
  let n := (Layout.chain G).size V.n
  let out : Values Float ((Layout.chain G).size V.n) := Values.ofFn fun i => M.entry i.1 0
  let s := Float.sqrt (M.entry 0 0)
  if n = 0 then ⟨⟨out⟩, 1⟩ else ⟨⟨out.map (· / s)⟩, 1⟩

/-- Julia `exp(P::Proj) = (out = exp(Chain(P))[1]; Proj{V}(out/√out[1]))` (`forms.jl:401-404`):
the first column of the exponential of `λ v ⊗ v`, scaled by the square root of its first
entry (Julia's heuristic; `λ = 1`). -/
def exp (P : Projector V G Float) : Projector V G Float := ofFirstColumn P.toOperator.exp

/-- Julia `log(P::Proj) = (out = log(Endomorphism(P))[1]; Proj{V}(out/√out[1]))`
(`forms.jl:405-408`), grade 1, where the real logarithm exists. -/
def log (P : Projector V 1 Float) : Except String (Projector V 1 Float) :=
  P.toOperator.log.map ofFirstColumn

end Projector

end Grassmann
