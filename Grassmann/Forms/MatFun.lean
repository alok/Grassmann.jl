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

/-- Julia's generic `exp(A)` (Higham's Padé scaling and squaring,
`composite.jl:246-297`), with `inv` the matrix inverse for `(V - U) \ (V + U)`. -/
def pade (inv : Mat n n Float → Mat n n Float) (A : Mat n n Float) : Mat n n Float :=
  let nA := norm1 A
  let solve := fun (V U : Mat n n Float) => (inv (V - U)).mul (V + U)
  if nA ≤ 2.1 then
    let A2 := A.mul A
    let (U, V) :=
      if nA > 0.95 then
        let U := addI (S 8821612800) (A2.mul (addI (S 302702400) (A2.mul (addI (S 2162160) (A2.mul (addI (S 3960) A2))))))
        let V := addI (S 17643225600) (A2.mul (addI (S 2075673600) (A2.mul (addI (S 30270240) (A2.mul (addI (S 110880) (S 90 * A2)))))))
        (A.mul U, V)
      else if nA > 0.25 then
        let U := addI (S 8648640) (A2.mul (addI (S 277200) (A2.mul (addI (S 1512) A2))))
        let V := addI (S 17297280) (A2.mul (addI (S 1995840) (A2.mul (addI (S 25200) (S 56 * A2)))))
        (A.mul U, V)
      else if nA > 0.015 then
        let U := addI (S 15120) (A2.mul (addI (S 420) A2))
        let V := addI (S 30240) (A2.mul (addI (S 3360) (S 30 * A2)))
        (A.mul U, V)
      else
        let U := addI (S 60) A2
        let V := addI (S 120) (S 12 * A2)
        (A.mul U, V)
    solve V U
  else
    let s := Float.log2 (nA / 5.4)
    let si : Nat := if s > 0 then s.ceil.toUInt64.toNat else 0
    let A := if s > 0 then A / Float.ofNat (2 ^ si) else A
    let A2 := A.mul A
    let A4 := A2.mul A2
    let A6 := A2.mul A4
    let U := addI (S 32382376266240000)
      ((A6.mul ((A6 + S 16380 * A4) + S 40840800 * A2)) +
        ((S 33522128640 * A6 + S 10559470521600 * A4) + S 1187353796428800 * A2))
    let U := A.mul U
    let V := addI (S 64764752532480000)
      ((A6.mul ((S 182 * A6 + S 960960 * A4) + S 1323241920 * A2)) +
        ((S 670442572800 * A6 + S 129060195264000 * A4) + S 7771770303897600 * A2))
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

end Grassmann
