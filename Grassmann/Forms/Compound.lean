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
import Grassmann.Forms.Unrolled

namespace Grassmann

open DirectSum StaticVectors AbstractTensors Grassmann.Forms

namespace Forms

variable {α : Type} [Coeff α]

/-- The Euclidean space of dimension `n`, whose metric-free kernels (`∧`, `!`)
the determinant family uses. -/
abbrev E (n : Nat) : TensorBundle := TensorBundle.euclidean n

/-- A grade-`g` vector of the `n`-space as raw coefficients. -/
abbrev GVec (α : Type) [Coeff α] (n g : Nat) := Values α (Leibniz.binomial n g)

/-- The wedge plan `grade g ∧ grade h → grade g+h` of the `n`-space: DirectSum's
multiply-accumulate plan (`Kernel.build`), whose accumulation order is Julia's. -/
def wedgePlanBuild (n g h : Nat) : Kernel.Plan :=
  match Kernel.build { V := E n, op := .bin .wedge, la := .chain g, lb := .chain h, lc := .chain (g + h) } with
  | .ok p => p
  | .error _ => {}

/-- The largest dimension whose wedge plans and complement tables are cached. -/
def cacheDim : Nat := 8

/-- The wedge plans of the spaces up to `cacheDim`, built once on first use
(closed-term thunks: no hash lookup on the hot path). -/
def wedgePlans : Array (Array (Array (Thunk Kernel.Plan))) :=
  (Array.range (cacheDim + 1)).map fun n => (Array.range (n + 1)).map fun g =>
    (Array.range (n + 1)).map fun h => Thunk.mk fun _ => wedgePlanBuild n g h

/-- The wedge plan of `g ∧ h` in `n` dimensions (cached, or the memoized reference
plan beyond `cacheDim`). -/
@[inline] def wedgePlan (n g h : Nat) : Kernel.Plan :=
  if n ≤ cacheDim && g ≤ n && h ≤ n then (wedgePlans[n]![g]![h]!).get
  else match Kernel.plan { V := E n, op := .bin .wedge, la := .chain g, lb := .chain h, lc := .chain (g + h) } with
    | .ok p => p
    | .error _ => {}

/-- `a ∧ b` of raw grade-`g` and grade-`h` coefficient storage in `n` dimensions. -/
@[inline] def wedgeP (n g h : Nat) (a b : Packed.Arr α) : Packed.Arr α :=
  let p := wedgePlan n g h
  if ha : p.Aligned then Kernel.Plan.rows₂ p ha a b p.outputs 0 (Packed.mkEmpty p.outputs)
  else Packed.mkEmpty 0

/-- `a ∧ b` of a grade-`g` and a grade-`h` vector (the wedge plan). -/
@[inline] def wedgeGH {n g h : Nat} (a : GVec α n g) (b : GVec α n h) : GVec α n (g + h) :=
  Mat.finish (wedgeP n g h a.data b.data)

/-- Whether `e_A ∧ e_B = -e_{A∪B}` for disjoint blades: the parity of the pairs
`i ∈ A`, `j ∈ B` with `j < i`. -/
def mergeNeg (a b : UInt64) : Bool := go b 0 64
where
  /-- Scan the bits of `b`, counting the bits of `a` above each. -/
  go (b : UInt64) (acc : Nat) : Nat → Bool
    | 0 => acc % 2 == 1
    | fuel + 1 =>
      if b == 0 then acc % 2 == 1
      else
        let low := b &&& (0 - b)
        go (b ^^^ low) (acc + DirectSum.Bits.popcount (a &&& ~~~(low ||| (low - 1)))) fuel

/-- The source position and sign of each coefficient of the right complement of
a grade-`g` vector in `n` dimensions: `(!a)[j] = ±a[src j]`, `!e_B = ±e_{B∁}` with
the sign of `e_B ∧ e_{B∁}` (Euclidean; checked against DirectSum's complement). -/
def complementTable (n g : Nat) : Array (Nat × Bool) :=
  (Leibniz.indexBasis n (n - g)).map fun c =>
    let b := c ^^^ DirectSum.Bits.lowMask n
    (Leibniz.bladeRank n b, mergeNeg b c)

/-- The complement tables of the spaces up to `cacheDim`, built once on first use. -/
def complementTables : Array (Array (Thunk (Array (Nat × Bool)))) :=
  (Array.range (cacheDim + 1)).map fun n => (Array.range (n + 1)).map fun g =>
    Thunk.mk fun _ => complementTable n g

/-- The complement table of grade `g` in `n` dimensions (cached up to `cacheDim`). -/
@[inline] def complementTableC (n g : Nat) : Array (Nat × Bool) :=
  if n ≤ cacheDim && g ≤ n then (complementTables[n]![g]!).get else complementTable n g

/-- The right complement of raw grade-`g` storage in `n` dimensions, by direct
negation as Julia's generated complement does (so signed zeros survive:
`!(0.0 e₁₂) = -0.0 e₃` where the sign is negative). -/
@[inline] def complementP (n g : Nat) (a : Packed.Arr α) : Packed.Arr α :=
  let tab := complementTableC n g
  Mat.pushLoop (fun j =>
    let (src, neg) := tab[j]!
    let x := Mat.rd a src
    if neg then -x else x) tab.size 0 (Packed.mkEmpty tab.size)

/-- The right complement `!a` of a grade-`g` vector (metric-free). -/
@[inline] def complementG {n g : Nat} (a : GVec α n g) : GVec α n (n - g) :=
  Mat.finish (complementP n g a.data)

/-- Negate raw storage entrywise. -/
@[inline] def negP (a : Packed.Arr α) : Packed.Arr α :=
  Mat.pushLoop (fun i => -Mat.rd a i) (Packed.size a) 0 (Packed.mkEmpty (Packed.size a))

/-- Scale raw storage entrywise (`x * s`). -/
@[inline] def scaleP (a : Packed.Arr α) (s : α) : Packed.Arr α :=
  Mat.pushLoop (fun i => Mat.rd a i * s) (Packed.size a) 0 (Packed.mkEmpty (Packed.size a))

/-- Raw storage defaults to empty (for `xs[i]!` on arrays of raw columns; scoped:
`open Grassmann.Forms`). -/
scoped instance instInhabitedPackedArr : Inhabited (Packed.Arr α) := ⟨Packed.mkEmpty 0⟩

/-- The scalar `1` as a grade-0 vector. -/
@[inline] def oneG (n : Nat) : GVec α n 0 := Values.replicate Coeff.one

/-- Wedge the vectors `cs` onto `acc`, left to right: `((acc ∧ c₁) ∧ c₂) ∧ …`. -/
@[specialize] def wedgeFold {n : Nat} : (g : Nat) → GVec α n g → (cs : List (GVec α n 1)) → GVec α n (g + cs.length)
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

/-! ### Straight-line forms of the plans in 2 and 3 dimensions

The wedge plans evaluated symbolically: every output starts from `0` and adds or
subtracts the products in plan order (Julia's order), so these are bit-identical to
the plan interpreter (and to Julia), signed zeros included. -/

/-- `u ∧ v` of two vectors of the plane: `(0 + u₁v₂) − u₂v₁`. -/
@[inline] def wedge2 (u1 u2 v1 v2 : α) : α := (Coeff.zero + u1 * v2) - u2 * v1

/-- `u ∧ v` of two vectors of space: `(B₁₂, B₁₃, B₂₃)`. -/
@[inline] def wedge3 (u1 u2 u3 v1 v2 v3 : α) : α × α × α :=
  ((Coeff.zero + u1 * v2) - u2 * v1, (Coeff.zero + u1 * v3) - u3 * v1, (Coeff.zero + u2 * v3) - u3 * v2)

/-- `B ∧ w` of a bivector and a vector of space (the top coefficient). -/
@[inline] def wedge21 (b12 b13 b23 w1 w2 w3 : α) : α :=
  ((Coeff.zero + b12 * w3) - b13 * w2) + b23 * w1

/-- `u ∧ B` of a vector and a bivector of space (the top coefficient). -/
@[inline] def wedge12 (u1 u2 u3 b12 b13 b23 : α) : α :=
  ((Coeff.zero + u1 * b23) - u2 * b13) + u3 * b12

/-- The straight-line `4 × 4` determinant `((t₁∧t₂)∧t₃)∧t₄` (the wedge plans evaluated
symbolically; generated, bit-identical to the plan interpreter and to Julia). -/
@[inline] def det4 (raw : Packed.Arr α) : α :=
  let a1 := Mat.rd raw 0
  let a2 := Mat.rd raw 1
  let a3 := Mat.rd raw 2
  let a4 := Mat.rd raw 3
  let b1 := Mat.rd raw 4
  let b2 := Mat.rd raw 5
  let b3 := Mat.rd raw 6
  let b4 := Mat.rd raw 7
  let c1 := Mat.rd raw 8
  let c2 := Mat.rd raw 9
  let c3 := Mat.rd raw 10
  let c4 := Mat.rd raw 11
  let d1 := Mat.rd raw 12
  let d2 := Mat.rd raw 13
  let d3 := Mat.rd raw 14
  let d4 := Mat.rd raw 15
  let p12 := ((Coeff.zero + a1 * b2) - a2 * b1)
  let p13 := ((Coeff.zero + a1 * b3) - a3 * b1)
  let p14 := ((Coeff.zero + a1 * b4) - a4 * b1)
  let p23 := ((Coeff.zero + a2 * b3) - a3 * b2)
  let p24 := ((Coeff.zero + a2 * b4) - a4 * b2)
  let p34 := ((Coeff.zero + a3 * b4) - a4 * b3)
  let q123 := (((Coeff.zero + p12 * c3) - p13 * c2) + p23 * c1)
  let q124 := (((Coeff.zero + p12 * c4) - p14 * c2) + p24 * c1)
  let q134 := (((Coeff.zero + p13 * c4) - p14 * c3) + p34 * c1)
  let q234 := (((Coeff.zero + p23 * c4) - p24 * c3) + p34 * c2)
  let s1234 := ((((Coeff.zero + q123 * d4) - q124 * d3) + q134 * d2) - q234 * d1)
  s1234

/-- The straight-line `4 × 4` Cramer inverse (Julia `_inv(4, 4)`: `val = (−y₃, y₂∧x₁,
−(y₁∧x₂), x₃)`, `dt = t₁ ∧ y₃`, rows `!(valᵢ · (1/dt))` with `!e₂₃₄ = −e₁`,
`!e₁₃₄ = e₂`, `!e₁₂₄ = −e₃`, `!e₁₂₃ = e₄`), column-major. Generated from the wedge plans. -/
@[inline] def inv4 [Div α] (raw : Packed.Arr α) : Packed.Arr α :=
  let a1 := Mat.rd raw 0
  let a2 := Mat.rd raw 1
  let a3 := Mat.rd raw 2
  let a4 := Mat.rd raw 3
  let b1 := Mat.rd raw 4
  let b2 := Mat.rd raw 5
  let b3 := Mat.rd raw 6
  let b4 := Mat.rd raw 7
  let c1 := Mat.rd raw 8
  let c2 := Mat.rd raw 9
  let c3 := Mat.rd raw 10
  let c4 := Mat.rd raw 11
  let d1 := Mat.rd raw 12
  let d2 := Mat.rd raw 13
  let d3 := Mat.rd raw 14
  let d4 := Mat.rd raw 15
  let x12 := ((Coeff.zero + a1 * b2) - a2 * b1)
  let x13 := ((Coeff.zero + a1 * b3) - a3 * b1)
  let x14 := ((Coeff.zero + a1 * b4) - a4 * b1)
  let x23 := ((Coeff.zero + a2 * b3) - a3 * b2)
  let x24 := ((Coeff.zero + a2 * b4) - a4 * b2)
  let x34 := ((Coeff.zero + a3 * b4) - a4 * b3)
  let z123 := (((Coeff.zero + x12 * c3) - x13 * c2) + x23 * c1)
  let z124 := (((Coeff.zero + x12 * c4) - x14 * c2) + x24 * c1)
  let z134 := (((Coeff.zero + x13 * c4) - x14 * c3) + x34 * c1)
  let z234 := (((Coeff.zero + x23 * c4) - x24 * c3) + x34 * c2)
  let y12 := ((Coeff.zero + c1 * d2) - c2 * d1)
  let y13 := ((Coeff.zero + c1 * d3) - c3 * d1)
  let y14 := ((Coeff.zero + c1 * d4) - c4 * d1)
  let y23 := ((Coeff.zero + c2 * d3) - c3 * d2)
  let y24 := ((Coeff.zero + c2 * d4) - c4 * d2)
  let y34 := ((Coeff.zero + c3 * d4) - c4 * d3)
  let w123 := (((Coeff.zero + b1 * y23) - b2 * y13) + b3 * y12)
  let w124 := (((Coeff.zero + b1 * y24) - b2 * y14) + b4 * y12)
  let w134 := (((Coeff.zero + b1 * y34) - b3 * y14) + b4 * y13)
  let w234 := (((Coeff.zero + b2 * y34) - b3 * y24) + b4 * y23)
  let dt1234 := ((((Coeff.zero + a1 * w234) - a2 * w134) + a3 * w124) - a4 * w123)
  let m123 := (((Coeff.zero + y12 * a3) - y13 * a2) + y23 * a1)
  let m124 := (((Coeff.zero + y12 * a4) - y14 * a2) + y24 * a1)
  let m134 := (((Coeff.zero + y13 * a4) - y14 * a3) + y34 * a1)
  let m234 := (((Coeff.zero + y23 * a4) - y24 * a3) + y34 * a2)
  let k123 := (((Coeff.zero + d1 * x23) - d2 * x13) + d3 * x12)
  let k124 := (((Coeff.zero + d1 * x24) - d2 * x14) + d4 * x12)
  let k134 := (((Coeff.zero + d1 * x34) - d3 * x14) + d4 * x13)
  let k234 := (((Coeff.zero + d2 * x34) - d3 * x24) + d4 * x23)
  let r := Coeff.one / dt1234
  -- the four numerators (grade 3: 123, 124, 134, 234) with Julia's signs
  let n1 := ((-w123) * r, (-w124) * r, (-w134) * r, (-w234) * r)
  let n2 := (m123 * r, m124 * r, m134 * r, m234 * r)
  let n3 := ((-k123) * r, (-k124) * r, (-k134) * r, (-k234) * r)
  let n4 := (z123 * r, z124 * r, z134 * r, z234 * r)
  -- complement: row = (−v₂₃₄, v₁₃₄, −v₁₂₄, v₁₂₃)
  let row := fun (v : α × α × α × α) => (-v.2.2.2, v.2.2.1, -v.2.1, v.1)
  let (r11, r12, r13, r14) := row n1
  let (r21, r22, r23, r24) := row n2
  let (r31, r32, r33, r34) := row n3
  let (r41, r42, r43, r44) := row n4
  let push4 := fun (out : Packed.Arr α) (x y z w : α) =>
    Packed.push (Packed.push (Packed.push (Packed.push out x) y) z) w
  let out := push4 (Packed.mkEmpty 16) r11 r21 r31 r41
  let out := push4 out r12 r22 r32 r42
  let out := push4 out r13 r23 r33 r43
  push4 out r14 r24 r34 r44

end Forms

namespace TensorOperator

variable {V W : TensorBundle} {α : Type} [Coeff α]

open Forms

/-- The columns of a grade-1 operator as grade-1 vectors of the codomain. -/
@[specialize] def cols1 (T : Simplex V W α) : List (GVec α W.n 1) :=
  (List.finRange ((Layout.chain 1).size V.n)).map fun j => T.mat.col j

/-- The `g`-th compound `Λᵍ T` (Julia `compound(T, g)`, `composite.jl:715-720`,
`forms.jl:586`): column `I` is the wedge of the columns indexed by the
`g`-subset `I`, i.e. `(Λᵍ T)[J, I] = det T[J, I]`. `Λ⁰ T` is the `1×1` identity. -/
@[specialize] def compound (T : Simplex V W α) (g : Nat) : TensorOperator V (.chain g) W (.chain g) α :=
  let cs := T.cols1.toArray
  ⟨Mat.ofCols fun j =>
    let I := DirectSum.Bits.indices (Leibniz.indexBasis V.n g)[j.1]!
    castLen (wedgeList (I.toList.map fun i => cs[i - 1]!))⟩

/-- Julia `∧(T) = t₁ ∧ … ∧ tₙ` (`algebra.jl:115`, `forms.jl:596`): the wedge of
all columns, a grade-`n` element of the codomain (the pseudoscalar `det·I` for
a square operator). -/
@[specialize] def wedgeAll (T : Simplex V W α) : Chain W V.n α :=
  ⟨castLen (wedgeList T.cols1)⟩

/-- Julia `∧(T)` with more columns than dimensions (`algebra.jl:115-121`): the
`1 × C(n,m)` top compound `Λᵐ T` as a grade-`m` chain of the domain (Julia
`map(Real, compound(t, m))`). -/
@[specialize] def wedgeAllWide (T : Simplex V W α) : Chain V W.n α :=
  let C := T.compound W.n
  ⟨Values.ofFn fun j => C.entry 0 j.1⟩

/-- Julia `det(T) = !∧(T)` (`composite.jl:952`, `forms.jl:595`) for a square
grade-1 operator: the scalar coefficient (Julia prints it as the grade-0 chain
`-3v`). For a non-square operator this is the first coefficient of the wedge. -/
@[specialize] def det (T : Simplex V W α) : α :=
  -- raw column-major reads: `(i, j)` at `j·n + i`
  let a := T.mat.v.data
  if V.n = 2 ∧ W.n = 2 then wedge2 (Mat.rd a 0) (Mat.rd a 1) (Mat.rd a 2) (Mat.rd a 3)
  else if V.n = 3 ∧ W.n = 3 then
    let (b12, b13, b23) := wedge3 (Mat.rd a 0) (Mat.rd a 1) (Mat.rd a 2) (Mat.rd a 3) (Mat.rd a 4) (Mat.rd a 5)
    wedge21 b12 b13 b23 (Mat.rd a 6) (Mat.rd a 7) (Mat.rd a 8)
  else if V.n = 4 ∧ W.n = 4 then det4 a
  else if V.n = 5 ∧ W.n = 5 then Unrolled.det5 a
  else if V.n = 6 ∧ W.n = 6 then Unrolled.det6 a
  else at0 T.wedgeAll.v

/-- `det` by the generic wedge of the columns (`t₁ ∧ … ∧ tₙ` through the wedge plans), the
algorithm `Grassmann.Forms.Unrolled.det5`/`det6` are generated from. -/
@[specialize] def detGeneric (T : Simplex V W α) : α := at0 T.wedgeAll.v

/-- The wedge `a ∧ b` of raw coefficient storage of grades `g`, `h` in `n` dimensions. -/
@[inline] def wedgeRaw (n g h : Nat) (a b : Packed.Arr α) : Packed.Arr α := wedgeP n g h a b

/-- The right complement of raw grade-`g` storage in `n` dimensions. -/
@[inline] def complementRaw (n g : Nat) (a : Packed.Arr α) : Packed.Arr α := complementP n g a

/-- Column `j` of an operator as raw storage. -/
@[inline] def colP {ld lc : Layout} (T : TensorOperator V ld W lc α) (j : Nat) : Packed.Arr α :=
  let r := lc.size W.n
  let a := T.mat.v.data
  Mat.pushLoop (fun i => Mat.rd a (j * r + i)) r 0 (Packed.mkEmpty r)

/-- Julia's `Cramer` symbols (`composite.jl:707-712`): the prefix wedges
`x₁ = t₁`, `xᵢ₊₁ = xᵢ ∧ tᵢ₊₁` and the suffix wedges `y₁ = tₘ`,
`yᵢ₊₁ = tₘ₋ᵢ ∧ yᵢ`, as raw storage of grades `1 … m` (entry `k-1` is grade `k`),
built in Julia's association order. -/
@[specialize] def prefixSuffix (T : Simplex V W α) : Array (Packed.Arr α) × Array (Packed.Arr α) :=
  let n := W.n
  let m := (Layout.chain 1).size V.n
  let cs := (Array.range m).map T.colP
  if m = 0 then (#[], #[])
  else
    let xs := (List.range (m - 1)).foldl (fun (acc : Array (Packed.Arr α)) k =>
      acc.push (wedgeRaw n (k + 1) 1 acc[k]! cs[k + 1]!)) #[cs[0]!]
    let ys := (List.range (m - 1)).foldl (fun (acc : Array (Packed.Arr α)) k =>
      acc.push (wedgeRaw n 1 (k + 1) cs[m - 2 - k]! acc[k]!)) #[cs[m - 1]!]
    (xs, ys)

/-- Julia's Cramer numerators `val` (`_inv`, `composite.jl:749-759`) for a
square operator with `m = n` columns: the `(n-1)`-blades whose complements are
the adjugate rows, with Julia's sign pattern. -/
@[specialize] def cramerVals (_T : Simplex V W α) (xs ys : Array (Packed.Arr α)) : Array (Packed.Arr α) :=
  let n := W.n
  let m := V.n
  let m1 := m - 1
  if m1 = 0 then #[Packed.push (Packed.mkEmpty 1) Coeff.one]
  else
    let x := fun (i : Nat) => xs[i - 1]!   -- grade i
    let y := fun (i : Nat) => ys[i - 1]!   -- grade i
    let mid := fun (i : Nat) => wedgeRaw n (m1 - i) i (y (m1 - i)) (x i)
    if m1 % 2 == 0 then
      #[y m1] ++ ((List.range (m1 - 1)).map fun k => mid (k + 1)).toArray ++ #[x m1]
    else if m ≠ n then
      #[y m1] ++ ((List.range (m1 - 1)).map fun k =>
        let i := k + 1; if i % 2 == 0 then mid i else negP (mid i)).toArray ++ #[negP (x m1)]
    else
      #[negP (y m1)] ++ ((List.range (m1 - 1)).map fun k =>
        let i := k + 1; if i % 2 == 1 then mid i else negP (mid i)).toArray ++ #[x m1]

/-- The adjugate rows `!(valᵢ)` of a square operator (vectors of the codomain),
from the Cramer symbols. -/
@[specialize] def adjugateRowsOf (T : Simplex V W α) (xs ys : Array (Packed.Arr α)) : Array (Packed.Arr α) :=
  if V.n = 1 then #[Packed.push (Packed.mkEmpty 1) Coeff.one]
  else (T.cramerVals xs ys).map (complementRaw W.n (W.n - 1))

/-- The adjugate rows `!(valᵢ)` of a square operator (vectors of the codomain). -/
@[specialize] def adjugateRows (T : Simplex V W α) : Array (Packed.Arr α) :=
  let (xs, ys) := T.prefixSuffix
  T.adjugateRowsOf xs ys

/-- The operator with the given rows. -/
@[inline] def ofRowsP {V' W' : TensorBundle} (rs : Array (Packed.Arr α)) : Simplex V' W' α :=
  TensorOperator.ofFn fun i j => match rs[i.1]? with
    | some r => Mat.rd r j.1
    | none => Coeff.zero

/-- Julia `adjugate(T)` of a square grade-1 operator (`composite.jl:796-803`,
`forms.jl:607-609`): the classical adjugate, `adj(T) T = det(T) I`, exact.
Its row `i` is `!(yₙ₋ᵢ ∧ xᵢ₋₁)` (with signs). -/
@[specialize] def adjugateGeneric (T : Simplex V W α) : Simplex W V α := ofRowsP T.adjugateRows

/-- Raw column-major storage as an operator of the transposed spaces. -/
@[inline] def ofRawT (a : Packed.Arr α) : Simplex W V α := ⟨⟨Mat.finish a⟩⟩

/-- Julia `adjugate(T)`: the generated straight-line forms for `2 ≤ n ≤ 6`
(`Grassmann.Forms.Unrolled`, bit-identical to `adjugateGeneric`), the Cramer symbols beyond. -/
@[specialize] def adjugate (T : Simplex V W α) : Simplex W V α :=
  let a := T.mat.v.data
  if V.n = W.n then
    if V.n = 3 then ofRawT (Unrolled.adjugate3 a)
    else if V.n = 2 then ofRawT (Unrolled.adjugate2 a)
    else if V.n = 4 then ofRawT (Unrolled.adjugate4 a)
    else if V.n = 5 then ofRawT (Unrolled.adjugate5 a)
    else if V.n = 6 then ofRawT (Unrolled.adjugate6 a)
    else T.adjugateGeneric
  else T.adjugateGeneric

/-- Julia `cofactor(T) = transpose(adjugate(T))` (`composite.jl:805-812`). -/
@[inline] def cofactor (T : Simplex V W α) : Simplex V W α := T.adjugate.transpose

/-- Julia's Cramer determinant `dt = t₁ ∧ yₙ₋₁` (`_inv`, `composite.jl:758`): the
top coefficient of `t₁ ∧ (t₂ ∧ … ∧ tₙ)` (associated as Julia's suffix wedges,
so it can differ in the last bit from `det`, the left fold). -/
@[specialize] def cramerDetOf (T : Simplex V W α) (xs ys : Array (Packed.Arr α)) : α :=
  let m := V.n
  if m ≤ 1 then T.det
  else Mat.rd (wedgeRaw W.n 1 (m - 1) xs[0]! ys[m - 2]!) 0

/-- Julia's Cramer determinant `dt = t₁ ∧ yₙ₋₁` (`_inv`, `composite.jl:758`). -/
@[specialize] def cramerDet (T : Simplex V W α) : α :=
  let (xs, ys) := T.prefixSuffix
  T.cramerDetOf xs ys

/-- The Cramer inverse through the Cramer symbols (one pass for the adjugate rows and
`dt`): the algorithm `Grassmann.Forms.Unrolled.inv5`/`inv6` are generated from. -/
@[specialize] def invSquareGeneric [Div α] (T : Simplex V W α) : Simplex W V α :=
  let (xs, ys) := T.prefixSuffix
  let r := Coeff.one / T.cramerDetOf xs ys
  ofRowsP ((T.adjugateRowsOf xs ys).map (scaleP · r))

/-- The inverse of a square grade-1 operator by Cramer's rule (Julia `inv`,
`composite.jl:761-772`): the adjugate times `1/dt`, Julia's `dt = t₁ ∧ yₙ₋₁`
(Julia computes `!(valᵢ / dt)`, and a tensor divided by a number is multiplied
by its reciprocal, `algebra.jl:704-706`). For one column, `c · (1/c²)` (Julia
`inv(t[1]) = ~t/abs2(t)` as a row). -/
@[specialize] def invSquare [Div α] (T : Simplex V W α) : Simplex W V α :=
  if V.n = 1 then
    let c := T.entry 0 0
    let r := Coeff.one / (c * c)
    TensorOperator.ofFn fun _ _ => c * r
  else if V.n = 2 ∧ W.n = 2 then
    -- val = (−t₂, t₁), dt = t₁ ∧ t₂; rows `!(valᵢ · (1/dt))`, `!e₁ = e₂`, `!e₂ = −e₁`
    let raw := T.mat.v.data
    let e := fun (k : Nat) => Mat.rd raw k
    let (a, c, b, d) := (e 0, e 1, e 2, e 3)
    let r := Coeff.one / wedge2 a c b d
    let (p1, p2) := ((-b) * r, (-d) * r)
    let (q1, q2) := (a * r, c * r)
    -- column-major `[[-p₂, p₁], [-q₂, q₁]]`
    ⟨⟨Mat.finish (Packed.push (Packed.push (Packed.push (Packed.push (Packed.mkEmpty 4) (-p2)) (-q2)) p1) q1)⟩⟩
  else if V.n = 3 ∧ W.n = 3 then
    -- val = (y₂, y₁ ∧ x₁, x₂) = (t₂∧t₃, t₃∧t₁, t₁∧t₂), dt = t₁ ∧ y₂; rows `!(valᵢ · (1/dt))`,
    -- `!e₂₃ = e₁`, `!e₁₃ = −e₂`, `!e₁₂ = e₃`
    let raw := T.mat.v.data
    let e := fun (k : Nat) => Mat.rd raw k
    let (a1, a2, a3) := (e 0, e 1, e 2)
    let (b1, b2, b3) := (e 3, e 4, e 5)
    let (c1, c2, c3) := (e 6, e 7, e 8)
    let (y12, y13, y23) := wedge3 b1 b2 b3 c1 c2 c3
    let r := Coeff.one / wedge12 a1 a2 a3 y12 y13 y23
    let (m12, m13, m23) := wedge3 c1 c2 c3 a1 a2 a3
    let (x12, x13, x23) := wedge3 a1 a2 a3 b1 b2 b3
    let row := fun (v12 v13 v23 : α) => (v23 * r, -(v13 * r), v12 * r)
    let r1 := row y12 y13 y23
    let r2 := row m12 m13 m23
    let r3 := row x12 x13 x23
    -- rows r₁, r₂, r₃ stored column-major
    let push3 := fun (out : Packed.Arr α) (x y z : α) => Packed.push (Packed.push (Packed.push out x) y) z
    let out := push3 (Packed.mkEmpty 9) r1.1 r2.1 r3.1
    let out := push3 out r1.2.1 r2.2.1 r3.2.1
    let out := push3 out r1.2.2 r2.2.2 r3.2.2
    ⟨⟨Mat.finish out⟩⟩
  else if V.n = 4 ∧ W.n = 4 then ⟨⟨Mat.finish (inv4 T.mat.v.data)⟩⟩
  else if V.n = 5 ∧ W.n = 5 then ofRawT (Unrolled.inv5 T.mat.v.data)
  else if V.n = 6 ∧ W.n = 6 then ofRawT (Unrolled.inv6 T.mat.v.data)
  else T.invSquareGeneric

/-- Checked write of raw packed storage (a no-op out of range). -/
@[inline] def wr (a : Packed.Arr α) (i : Nat) (x : α) : Packed.Arr α :=
  if h : i < Packed.size a then Packed.set a ⟨i, h⟩ x else a

/-- Gauss-Jordan elimination with partial pivoting (by `norm`) on the augmented
pair `(a | b)` of column-major `n × n` buffers, from column `k` on: at the end
`b` holds `A⁻¹`. Tail-recursive, in place on unshared buffers. -/
@[specialize] def gaussJordanLoop [Div α] (norm : α → Float) (n : Nat) (a b : Packed.Arr α) (k : Nat) :
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
@[specialize] def gaussJordan {n : Nat} [Div α] (norm : α → Float) (A : Mat n n α) : Mat n n α :=
  let (_, b) := gaussJordanLoop norm n A.v.data (Mat.identity : Mat n n α).v.data 0
  ⟨Mat.finish b⟩

/-- The inverse of a grade-1 operator (Julia `inv(T)`, `composite.jl:761-772`,
`forms.jl:607`): Cramer's rule when square; otherwise the Moore-Penrose
pseudo-inverse, `(TᵀT)⁻¹Tᵀ` with fewer columns than dimensions and `Tᵀ(TTᵀ)⁻¹`
with more. -/
@[specialize] def inv [Div α] (T : Simplex V W α) : Simplex W V α :=
  if V.n = W.n then T.invSquare
  else if V.n < W.n then
    let tt : Simplex W V α := T.transpose
    let g : Endomorphism V (.chain 1) α := tt.comp T
    (g.invSquare (W := V)).comp tt
  else
    let tt : Simplex W V α := T.transpose
    let g : Endomorphism W (.chain 1) α := T.comp tt
    tt.comp (g.invSquare (W := W))

/-- The inverse of a square operator of any layout by Gauss-Jordan elimination with
partial pivoting (`norm` ranks the pivots, e.g. `Float.abs`): for the layouts Julia's
Cramer inverse does not cover (`Spinor`, `Multivector`, grade-`g` operators). -/
@[specialize] def inverse {l : Layout} [Div α] (norm : α → Float) (T : Endomorphism V l α) : Endomorphism V l α :=
  ⟨gaussJordan norm T.mat⟩

/-- Julia `invdet(T) = (inv(T), det(T))` (`composite.jl:774-785`, `forms.jl:602-605`),
the determinant as Julia's `!(t₁ ∧ yₙ₋₁)`. -/
@[inline] def invdet [Div α] (T : Simplex V W α) : Simplex W V α × α :=
  (T.inv, if V.n = W.n then T.cramerDet else T.det)

/-- Julia `T \ v` on a `TensorOperator` (AbstractTensors' generic
`\(a, b) = inv(a) * b`, `AbstractTensors.jl:323`): the inverse applied to `v`. -/
@[inline] def ldiv [Div α] (T : Simplex V W α) (v : Chain W 1 α) : Chain V 1 α :=
  ⟨T.inv.applyValues v.v⟩

/-- Julia `value(T) \ v` (`composite.jl:722-732`): solve `T c = v` by Cramer's rule
(numerators `x_{i-1} ∧ v ∧ y_{n-i}` over `det`) for a square operator; the
least-norm / least-squares solution `pinv(T) v` otherwise. -/
@[specialize] def solveGeneric [Div α] (T : Simplex V W α) (v : Chain W 1 α) : Chain V 1 α :=
  if V.n = W.n ∧ V.n ≥ 2 then
    let n := W.n
    let (xs, ys) := T.prefixSuffix
    let m := V.n
    let N := m - 1
    let vv := v.v.data
    let x := fun (i : Nat) => xs[i - 1]!
    let y := fun (i : Nat) => ys[i - 1]!
    let top := fun (a : Packed.Arr α) => Mat.rd a 0
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

/-- Julia `value(T) \ v` (`composite.jl:722-732`): the generated straight-line Cramer solves
for `2 ≤ n ≤ 6` (`Grassmann.Forms.Unrolled`, bit-identical to `solveGeneric`), the Cramer
symbols beyond, the least-squares / least-norm solution for a non-square operator. -/
@[specialize] def solve [Div α] (T : Simplex V W α) (v : Chain W 1 α) : Chain V 1 α :=
  let a := T.mat.v.data
  let b := v.v.data
  if V.n = W.n then
    if V.n = 3 then ⟨Mat.finish (Unrolled.solve3 a b)⟩
    else if V.n = 2 then ⟨Mat.finish (Unrolled.solve2 a b)⟩
    else if V.n = 4 then ⟨Mat.finish (Unrolled.solve4 a b)⟩
    else if V.n = 5 then ⟨Mat.finish (Unrolled.solve5 a b)⟩
    else if V.n = 6 then ⟨Mat.finish (Unrolled.solve6 a b)⟩
    else T.solveGeneric v
  else T.solveGeneric v

/-- `k!`. -/
def factorialNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorialNat k

end TensorOperator

namespace Chain

variable {V : TensorBundle} {α : Type} [Coeff α]

open Forms

/-- `ω ∧ ω ∧ … ∧ ω` (`k` factors, a left fold) of a bivector, grade `2k`. -/
@[specialize] def wedgePower {n : Nat} (ω : GVec α n 2) : (k : Nat) → GVec α n (2 * k)
  | 0 => oneG n
  | 1 => ω
  | k + 2 => (wedgeGH (wedgePower ω (k + 1)) ω).cast (by congr 1)

/-- Julia `pfaffian(ω)` of a bivector (`composite.jl:887-895`): with `k = ⌊n/2⌋`,
`!(ω^∧k) / k!` (`!ω` when `k = 1`): the Pfaffian as a grade-0 chain in even
dimension, a vector in odd dimension (`pfaffian(2v₁₂ + 3v₁₃ + 6v₂₃) = 6v₁ - 3v₂ + 2v₃`).
The division by `k!` is Julia's tensor division, by the reciprocal. -/
@[specialize] def pfaffian [Div α] (ω : Chain V 2 α) : Chain V (V.n - 2 * (V.n / 2)) α :=
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
