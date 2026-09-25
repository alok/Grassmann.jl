/-
The exterior-algebra determinant family of a grade-1 operator (a "simplex" of
column vectors): compound matrices, `∧`, `det`, the Cramer adjugate, cofactor,
inverse and solve, the Pfaffian, point-in-simplex and the barycentric gradient
(Grassmann.jl `src/composite.jl:707-895`, `src/forms.jl:586-616`;
port-notes/grassmann-forms.md §4.4, §4.8, §4.13, grassmann-composite.md §4.8-4.9).

Everything is computed as Julia does, by **exterior products of the columns**
with the (metric-free) wedge of the reference kernels in the Euclidean space of
the right dimension:

* `compound(T, g)`: column `I` (a `g`-subset, lexicographic) is `∧_{i∈I} tᵢ`, so
  its entry at codomain blade `J` is the minor `det T[J,I]` (`composite.jl:715-720`);
* `∧(T) = t₁∧…∧tₙ` and `det(T) = !∧(T)`, the top coefficient (`composite.jl:952`);
* Cramer's rule through prefix wedges `xₖ = t₁∧…∧tₖ` and suffix wedges
  `yₖ = t_{n-k+1}∧…∧tₙ` (`Grassmann.Cramer`, `composite.jl:707-712`): the
  adjugate rows are `!(y_{n-i} ∧ x_{i-1})` with Julia's sign pattern
  (`_inv`, `composite.jl:749-759`), `inv = adjugate / det`, `t \ v` by
  numerators `x_{i-1} ∧ v ∧ y_{n-i}` (`composite.jl:722-732`).

All of it is exact over `Int`/`Rat` (only `±`, `*`; `inv` and `\` divide once
at the end) and metric-free: Julia's `!` of an `(n-1)`-blade and of the
pseudoscalar is the metric-independent right complement (verified identical
on `⟨+++⟩`, `⟨-++⟩`, `⟨---⟩`, `⟨2,3,5⟩`, port-notes §4.4).

Non-square inverses are the Moore-Penrose ones Julia computes for Euclidean
spaces: `(tᵀt)⁻¹tᵀ` for fewer columns than dimensions (Julia's reciprocal frame
`vector(valᵢ / (t₁∧…∧tₘ))`, which uses the codomain metric: identical for
Euclidean codomains) and `tᵀ(ttᵀ)⁻¹` for more (`composite.jl:761-772`).
-/
import Grassmann.Forms.Operator

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms

namespace Forms

variable {α : Type} [Coeff α]

/-- The Euclidean space of dimension `n`, whose metric-free kernels (`∧`, `!`)
the determinant family uses. -/
abbrev E (n : Nat) : TensorBundle := TensorBundle.euclidean n

/-- A grade-`g` vector of the `n`-space as raw coefficients. -/
abbrev GVec (α : Type) [Coeff α] (n g : Nat) := Values α (Leibniz.binomial n g)

/-- `a ∧ b` of a grade-`g` and a grade-`h` vector (the reference wedge kernel). -/
@[inline] def wedgeGH {n g h : Nat} (a : GVec α n g) (b : GVec α n h) : GVec α n (g + h) :=
  Kernel.refBin (E n) .wedge (.chain g) (.chain h) (.chain (g + h)) a b

/-- The source position and sign of each coefficient of the right complement of
a grade-`g` vector in `n` dimensions: `(!a)[j] = ±a[src j]` (every blade has a
single complement, `±e_{I∁}`). -/
def complementTable (n g : Nat) : Array (Nat × Bool) :=
  let out := Leibniz.indexBasis n (n - g)
  out.map fun c =>
    let b := c ^^^ DirectSum.Bits.lowMask n
    let neg := match (E n).apply₁ .complementright b with
      | .ok (.single q _) => q < 0
      | _ => false
    (Leibniz.bladeRank n b, neg)

/-- The right complement `!a` of a grade-`g` vector (metric-free), by direct
negation as Julia's generated complement does (so signed zeros survive:
`!(0.0 e₁₂) = -0.0 e₃` where the sign is negative). -/
def complementG {n g : Nat} (a : GVec α n g) : GVec α n (n - g) :=
  let tab := complementTable n g
  Values.ofFn fun j =>
    let (src, neg) := tab[j.1]!
    let x := getD a src
    if neg then -x else x

/-- The scalar `1` as a grade-0 vector. -/
@[inline] def oneG (n : Nat) : GVec α n 0 := Values.replicate Coeff.one

/-- Wedge the vectors `cs` onto `acc`, left to right: `((acc ∧ c₁) ∧ c₂) ∧ …`. -/
def wedgeFold {n : Nat} : (g : Nat) → GVec α n g → (cs : List (GVec α n 1)) → GVec α n (g + cs.length)
  | _, acc, [] => acc
  | g, acc, c :: cs => (wedgeFold (g + 1) (wedgeGH acc c) cs).cast (by
      rw [List.length_cons, Nat.add_assoc, Nat.add_comm 1 cs.length])

/-- `c₁ ∧ c₂ ∧ … ∧ cₖ` of grade-1 vectors (Julia `∧(x...)`, a left fold; `1` for
the empty list). -/
@[inline] def wedgeList {n : Nat} (cs : List (GVec α n 1)) : GVec α n cs.length :=
  (wedgeFold 0 (oneG n) cs).cast (by simp)

/-- The coefficient at position `i`, zero out of range. -/
@[inline] def at0 {k : Nat} (v : Values α k) (i : Nat := 0) : α := getD v i

/-- A runtime-checked cast of a vector length (the checks always succeed
where it is used; the fallback is zero). -/
@[inline] def castLen {k k' : Nat} (v : Values α k) : Values α k' :=
  if h : k = k' then v.cast h else zeroValues k'

/-- Julia `signbit` on a coefficient type (for the point-in-simplex test). -/
class SignBit (α : Type) where
  /-- Whether the sign bit is set (`-0.0` included for floats). -/
  signbit : α → Bool

instance : SignBit Float := ⟨JuliaBase.F64.signbit⟩
instance : SignBit Int := ⟨fun x => x < 0⟩
instance : SignBit Rat := ⟨fun x => x < 0⟩

end Forms

namespace TensorOperator

variable {V W : TensorBundle} {α : Type} [Coeff α]

open Forms

/-- The columns of a grade-1 operator as grade-1 vectors of the codomain. -/
def cols1 (T : Simplex V W α) : List (GVec α W.n 1) :=
  (List.finRange ((Layout.chain 1).size V.n)).map fun j => T.mat.col j

/-- The `g`-th compound `Λᵍ T` (Julia `compound(T, g)`, `composite.jl:715-720`,
`forms.jl:586`): column `I` is the wedge of the columns indexed by the
`g`-subset `I`, i.e. `(Λᵍ T)[J, I] = det T[J, I]`. `Λ⁰ T` is the `1×1` identity. -/
def compound (T : Simplex V W α) (g : Nat) : TensorOperator V (.chain g) W (.chain g) α :=
  let cs := T.cols1.toArray
  ⟨Mat.ofCols fun j =>
    let I := DirectSum.Bits.indices (Leibniz.indexBasis V.n g)[j.1]!
    castLen (wedgeList (I.toList.map fun i => cs[i - 1]!))⟩

/-- Julia `∧(T) = t₁ ∧ … ∧ tₙ` (`algebra.jl:115`, `forms.jl:596`): the wedge of
all columns, a grade-`n` element of the codomain (the pseudoscalar `det·I` for
a square operator). -/
def wedgeAll (T : Simplex V W α) : Chain W V.n α :=
  ⟨castLen (wedgeList T.cols1)⟩

/-- Julia `det(T) = !∧(T)` (`composite.jl:952`, `forms.jl:595`) for a square
grade-1 operator: the scalar coefficient (Julia prints it as the grade-0 chain
`-3v`). For a non-square operator this is the first coefficient of the wedge. -/
@[inline] def det (T : Simplex V W α) : α := at0 T.wedgeAll.v

/-- The wedge `a ∧ b` of raw coefficient arrays of grades `g`, `h` in `n` dimensions. -/
def wedgeRaw (n g h : Nat) (a b : Array α) : Array α :=
  (wedgeGH (n := n) (g := g) (h := h) (Values.ofFn fun i => a[i.1]?.getD Coeff.zero)
    (Values.ofFn fun i => b[i.1]?.getD Coeff.zero)).toArray

/-- The right complement of a raw grade-`g` coefficient array in `n` dimensions. -/
def complementRaw (n g : Nat) (a : Array α) : Array α :=
  (complementG (n := n) (g := g) (Values.ofFn fun i => a[i.1]?.getD Coeff.zero)).toArray

/-- Julia's `Cramer` symbols (`composite.jl:707-712`): the prefix wedges
`x₁ = t₁`, `xᵢ₊₁ = xᵢ ∧ tᵢ₊₁` and the suffix wedges `y₁ = tₘ`,
`yᵢ₊₁ = tₘ₋ᵢ ∧ yᵢ`, as raw coefficient arrays of grades `1 … m` (entry `k-1` is
grade `k`), built in Julia's association order. -/
def prefixSuffix (T : Simplex V W α) : Array (Array α) × Array (Array α) :=
  let n := W.n
  let cs := (T.cols1.map (·.toArray)).toArray
  let m := cs.size
  if m = 0 then (#[], #[])
  else
    let xs := (List.range (m - 1)).foldl (fun (acc : Array (Array α)) k =>
      acc.push (wedgeRaw n (k + 1) 1 acc[k]! cs[k + 1]!)) #[cs[0]!]
    let ys := (List.range (m - 1)).foldl (fun (acc : Array (Array α)) k =>
      acc.push (wedgeRaw n 1 (k + 1) cs[m - 2 - k]! acc[k]!)) #[cs[m - 1]!]
    (xs, ys)

/-- Julia's Cramer numerators `val` (`_inv`, `composite.jl:749-759`) for a
square operator with `m = n` columns: the `(n-1)`-blades whose complements are
the adjugate rows, with Julia's sign pattern. -/
def cramerVals (T : Simplex V W α) : Array (Array α) :=
  let n := W.n
  let m := V.n
  let (xs, ys) := T.prefixSuffix
  let m1 := m - 1
  if m1 = 0 then #[#[Coeff.one]]
  else
    let x := fun (i : Nat) => xs[i - 1]!   -- grade i
    let y := fun (i : Nat) => ys[i - 1]!   -- grade i
    let mid := fun (i : Nat) => wedgeRaw n (m1 - i) i (y (m1 - i)) (x i)
    let neg := fun (a : Array α) => a.map (- ·)
    if m1 % 2 == 0 then
      #[y m1] ++ ((List.range (m1 - 1)).map fun k => mid (k + 1)).toArray ++ #[x m1]
    else if m ≠ n then
      #[y m1] ++ ((List.range (m1 - 1)).map fun k =>
        let i := k + 1; if i % 2 == 0 then mid i else neg (mid i)).toArray ++ #[neg (x m1)]
    else
      #[neg (y m1)] ++ ((List.range (m1 - 1)).map fun k =>
        let i := k + 1; if i % 2 == 1 then mid i else neg (mid i)).toArray ++ #[x m1]

/-- The adjugate rows `!(valᵢ)` of a square operator (vectors of the codomain). -/
def adjugateRows (T : Simplex V W α) : Array (Array α) :=
  if V.n = 1 then #[#[Coeff.one]]
  else (T.cramerVals).map (complementRaw W.n (W.n - 1))

/-- Julia `adjugate(T)` of a square grade-1 operator (`composite.jl:796-803`,
`forms.jl:607-609`): the classical adjugate, `adj(T) T = det(T) I`, exact.
Its row `i` is `!(yₙ₋ᵢ ∧ xᵢ₋₁)` (with signs). -/
def adjugate (T : Simplex V W α) : Simplex W V α :=
  let rs := T.adjugateRows
  TensorOperator.ofFn fun i j => (rs[i.1]?.bind (·[j.1]?)).getD Coeff.zero

/-- Julia `cofactor(T) = transpose(adjugate(T))` (`composite.jl:805-812`). -/
@[inline] def cofactor (T : Simplex V W α) : Simplex V W α := T.adjugate.transpose

/-- Julia's Cramer determinant `dt = t₁ ∧ yₙ₋₁` (`_inv`, `composite.jl:758`): the
top coefficient of `t₁ ∧ (t₂ ∧ … ∧ tₙ)` (associated as Julia's suffix wedges,
so it can differ in the last bit from `det`, the left fold). -/
def cramerDet (T : Simplex V W α) : α :=
  let (xs, ys) := T.prefixSuffix
  let m := V.n
  if m ≤ 1 then T.det
  else ((wedgeRaw W.n 1 (m - 1) xs[0]! ys[m - 2]!)[0]?).getD Coeff.zero

/-- The inverse of a square grade-1 operator by Cramer's rule (Julia `inv`,
`composite.jl:761-772`): the adjugate times `1/dt`, Julia's `dt = t₁ ∧ yₙ₋₁`
(Julia computes `!(valᵢ / dt)`, and a tensor divided by a number is multiplied
by its reciprocal, `algebra.jl:704-706`). For one column, `c / c²` (Julia
`inv(t[1]) = ~t/abs2(t)` as a row). -/
def invSquare [Div α] (T : Simplex V W α) : Simplex W V α :=
  if V.n = 1 then
    let c := T.entry 0 0
    TensorOperator.ofFn fun _ _ => c / (c * c)
  else
    let r := Coeff.one / T.cramerDet
    T.adjugate.map (· * r)

/-- Checked write of raw packed storage (a no-op out of range). -/
@[inline] def wr (a : Packed.Arr α) (i : Nat) (x : α) : Packed.Arr α :=
  if h : i < Packed.size a then Packed.set a ⟨i, h⟩ x else a

/-- Gauss-Jordan elimination with partial pivoting (by `norm`) on the augmented
pair `(a | b)` of column-major `n × n` buffers, from column `k` on: at the end
`b` holds `A⁻¹`. Tail-recursive, in place on unshared buffers. -/
def gaussJordanLoop [Div α] (norm : α → Float) (n : Nat) (a b : Packed.Arr α) (k : Nat) :
    Packed.Arr α × Packed.Arr α :=
  if k < n then
    let idx := fun (i j : Nat) => j * n + i
    -- the pivot row
    let p := (List.range (n - k - 1)).foldl (fun (p : Nat × Float) t =>
      let i := k + 1 + t
      let v := norm (Mat.rd a (idx i k))
      if v > p.2 then (i, v) else p) (k, norm (Mat.rd a (idx k k)))
    let p := p.1
    let swap := fun (buf : Packed.Arr α) => (List.range n).foldl (fun buf j =>
      let t := Mat.rd buf (idx k j)
      let buf := wr buf (idx k j) (Mat.rd buf (idx p j))
      wr buf (idx p j) t) buf
    let (a, b) := if p != k then (swap a, swap b) else (a, b)
    let piv := Mat.rd a (idx k k)
    let scale := fun (buf : Packed.Arr α) => (List.range n).foldl (fun buf j =>
      wr buf (idx k j) (Mat.rd buf (idx k j) / piv)) buf
    let a := scale a
    let b := scale b
    let elim := fun (ab : Packed.Arr α × Packed.Arr α) (i : Nat) =>
      if i == k then ab
      else
        let (a, b) := ab
        let f := Mat.rd a (idx i k)
        (List.range n).foldl (fun (ab : Packed.Arr α × Packed.Arr α) j =>
          (wr ab.1 (idx i j) (Mat.rd ab.1 (idx i j) - f * Mat.rd ab.1 (idx k j)),
           wr ab.2 (idx i j) (Mat.rd ab.2 (idx i j) - f * Mat.rd ab.2 (idx k j)))) (a, b)
    let (a, b) := (List.range n).foldl elim (a, b)
    gaussJordanLoop norm n a b (k + 1)
  else (a, b)
termination_by n - k

/-- The inverse of a square matrix by Gauss-Jordan elimination with partial
pivoting (for the layouts Julia's Cramer inverse does not cover, and the
matrix functions). -/
def gaussJordan {n : Nat} [Div α] (norm : α → Float) (A : Mat n n α) : Mat n n α :=
  let (_, b) := gaussJordanLoop norm n A.v.data (Mat.identity : Mat n n α).v.data 0
  ⟨Mat.finish b⟩

/-- The inverse of a grade-1 operator (Julia `inv(T)`, `composite.jl:761-772`,
`forms.jl:607`): Cramer's rule when square; otherwise the Moore-Penrose
pseudo-inverse, `(TᵀT)⁻¹Tᵀ` with fewer columns than dimensions and `Tᵀ(TTᵀ)⁻¹`
with more. -/
def inv [Div α] (T : Simplex V W α) : Simplex W V α :=
  if V.n = W.n then T.invSquare
  else if V.n < W.n then
    let tt : Simplex W V α := T.transpose
    let g : Endomorphism V (.chain 1) α := tt.comp T
    (g.invSquare (W := V)).comp tt
  else
    let tt : Simplex W V α := T.transpose
    let g : Endomorphism W (.chain 1) α := T.comp tt
    tt.comp (g.invSquare (W := W))

/-- Julia `invdet(T) = (inv(T), det(T))` (`composite.jl:774-785`, `forms.jl:602-605`),
the determinant as Julia's `!(t₁ ∧ yₙ₋₁)`. -/
@[inline] def invdet [Div α] (T : Simplex V W α) : Simplex W V α × α :=
  (T.inv, if V.n = W.n then T.cramerDet else T.det)

/-- Julia `T \ v` (`composite.jl:722-732`): solve `T c = v` by Cramer's rule
(numerators `x_{i-1} ∧ v ∧ y_{n-i}` over `det`) for a square operator; the
least-norm / least-squares solution `pinv(T) v` otherwise. -/
def solve [Div α] (T : Simplex V W α) (v : Chain W 1 α) : Chain V 1 α :=
  if V.n = W.n ∧ V.n ≥ 2 then
    let n := W.n
    let (xs, ys) := T.prefixSuffix
    let m := V.n
    let N := m - 1
    let vv := v.v.toArray
    let x := fun (i : Nat) => xs[i - 1]!
    let y := fun (i : Nat) => ys[i - 1]!
    let top := fun (a : Array α) => a[0]?.getD Coeff.zero
    let first := top (wedgeRaw n 1 N vv (y N))
    let mid := (List.range (N - 1)).map fun k =>
      let i := k + 1
      top (wedgeRaw n (i + 1) (N - i) (wedgeRaw n i 1 (x i) vv) (y (N - i)))
    let last := top (wedgeRaw n N 1 (x N) vv)
    let nums := (first :: mid ++ [last]).toArray
    let detx := top (wedgeRaw n 1 N (x 1) (y N))
    Chain.ofFn fun i => nums[i.1]! / detx
  else
    ⟨T.inv.applyValues v.v⟩

/-- `k!`. -/
def factorialNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorialNat k

end TensorOperator

namespace Chain

variable {V : TensorBundle} {α : Type} [Coeff α]

open Forms

/-- `ω ∧ ω ∧ … ∧ ω` (`k` factors, a left fold) of a bivector, grade `2k`. -/
def wedgePower {n : Nat} (ω : GVec α n 2) : (k : Nat) → GVec α n (2 * k)
  | 0 => oneG n
  | 1 => ω
  | k + 2 => (wedgeGH (wedgePower ω (k + 1)) ω).cast (by congr 1)

/-- Julia `pfaffian(ω)` of a bivector (`composite.jl:887-895`): with `k = ⌊n/2⌋`,
`!(ω^∧k) / k!` (`!ω` when `k = 1`): the Pfaffian as a grade-0 chain in even
dimension, a vector in odd dimension (`pfaffian(2v₁₂ + 3v₁₃ + 6v₂₃) = 6v₁ - 3v₂ + 2v₃`).
The division by `k!` is Julia's tensor division, by the reciprocal. -/
def pfaffian [Div α] (ω : Chain V 2 α) : Chain V (V.n - 2 * (V.n / 2)) α :=
  let k := V.n / 2
  let c : GVec α V.n (V.n - 2 * k) := complementG (wedgePower (n := V.n) ω.v k)
  if k ≤ 1 then ⟨c⟩
  else
    let r : α := Coeff.one / Coeff.ofInt (TensorOperator.factorialNat k)
    ⟨c.map (· * r)⟩

end Chain

/-- Julia `pfaffian(A::Endomorphism) = pfaffian(bivector(A))` (`forms.jl:592`). -/
@[inline] def Endomorphism.pfaffian {V : TensorBundle} {α : Type} [Coeff α] [Div α]
    (A : Endomorphism V (.chain 1) α) : Chain V (V.n - 2 * (V.n / 2)) α :=
  (Endomorphism.bivector A).pfaffian

end Grassmann
