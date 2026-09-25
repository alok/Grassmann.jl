/-
Combinatorial topology of Grassmann elements read as simplicial complexes (Grassmann.jl
`src/Grassmann.jl:113-290`, Leibniz.jl `src/generic.jl:166-192`): a basis blade `v_{i₁…i_k}`
is the `(k-1)`-simplex on the vertices `i₁ … i_k`, and the boundary `∂` of `Grassmann.Calculus`
(`ω ⋅ V(∇)`) is its simplicial boundary.

| Julia | here |
|---|---|
| `absym(t)` | `absym`: the coefficients' absolute values |
| `skeleton(x, Val(true))` | `skeleton`: every face of every simplex of `x`, with multiplicity (vertices included, the empty face not) |
| `𝒫(t) = Δ(t, Val(false))` | `𝒫`: the skeleton with the empty face (Julia's `Δ` is not callable, defect `laplacian-not-callable`; this is its intended `skeleton(t, Val(false))`) |
| `subcomplex(x)` | `subcomplex`: `skeleton(absym(∂x))` (same defect in Julia) |
| `collapse(a, b)` | `collapse`: `a ⋅ absym(∂b)` |
| `chain(t)`, `path(t)` | `chain`, `path`: the closed / open edge path through a blade's vertices |
| `count_gdims(t)` | `countGdims`: the number of nonzero coefficients per grade (of the non-tangent part) |
| `χ(t)` | `χ`: Julia's `Σₚ (-1)ᵖ⁺¹ bₚ` over `count_gdims` (the sign opposite to the usual one) |
| `boundary_rank`, `boundary_null`, `betti` | `boundaryRank`, `boundaryNull`, `betti` |

Everything runs on multivectors at `Float` (Julia's `Int` values are exact here).
-/
import Grassmann.Calculus
import Grassmann.Composite.Fast

namespace Grassmann.Calculus

open DirectSum DirectSum.Bits StaticVectors AbstractTensors Composite

variable {V : TensorBundle} [Kernels V]

/-- The grade of the non-tangent part of blade `b` (Julia
`count_ones(symmetricmask(V, b, b)[1])`). -/
@[inline] def symGrade (V : TensorBundle) (b : UInt64) : Nat := popcount (b &&& ~~~V.diffmask)

/-- Julia `absym(t)` (`src/Grassmann.jl:246-250`): the absolute value of every coefficient. -/
@[inline] def absym (m : Multivector V Float) : Multivector V Float := ⟨vmap Float.abs m.v⟩

/-- The term `c·e_b` as a multivector. -/
@[inline] def termMV (V : TensorBundle) (b : UInt64) (c : Float) : Multivector V Float :=
  ⟨Values.ofFn fun i => if (Leibniz.indexBasisAll V.n)[i.1]?.getD 0 == b then c else 0⟩

mutual

/-- Julia `skeleton(x::Multivector, Val(T))` (`src/Grassmann.jl:280-292`): the sum of the
skeletons of the nonzero terms (of positive grade when `T`), in storage order. -/
def skeletonAux (T : Bool) (x : Multivector V Float) : Nat → Multivector V Float
  | 0 => Multivector.zero
  | fuel + 1 =>
    let bs := Leibniz.indexBasisAll V.n
    (List.range bs.size).foldl (init := Multivector.zero) fun acc i =>
      let b := bs[i]?.getD 0
      let c := getD x.v i
      if c != 0 && (!T || symGrade V b > 0) then acc + skeletonTerm T b c fuel else acc

/-- Julia `skeleton(x::TensorTerm, Val(T))` (`src/Grassmann.jl:258-261`): `absym(x) +
skeleton(absym(∂x))` for a term of positive grade; a scalar is dropped (`T`) or kept. -/
def skeletonTerm (T : Bool) (b : UInt64) (c : Float) : Nat → Multivector V Float
  | 0 => Multivector.zero
  | fuel + 1 =>
    if symGrade V b > 0 then
      termMV V b c.abs + skeletonAux T (absym (boundaryM (termMV V b c))) fuel
    else if T then Multivector.zero
    else termMV V b c.abs

end

/-- Julia `skeleton(x)` (`src/Grassmann.jl:258-292`): every face of every simplex of `x`
(the terms read as simplices), counted with multiplicity, without the empty face. (The fuel
covers the recursion: two steps per grade, `n` grades at most.) -/
def skeleton (x : Multivector V Float) : Multivector V Float := skeletonAux true x (2 * V.n + 4)

/-- Julia `𝒫(t) = Δ(t, Val(false))` (`src/Grassmann.jl:256`, broken in Julia: `Δ` is not
callable): the skeleton with the empty face (`skeleton(t, Val(false))`). -/
def 𝒫 (x : Multivector V Float) : Multivector V Float := skeletonAux false x (2 * V.n + 4)

/-- Julia `subcomplex(x) = Δ(absym(∂(x)))` (`src/Grassmann.jl:257`, broken in Julia): the
skeleton of the boundary. -/
def subcomplex (x : Multivector V Float) : Multivector V Float := skeleton (absym (boundaryM x))

/-- Julia `collapse(a, b) = a ⋅ absym(∂(b))` (`src/Grassmann.jl:252`). -/
def collapse (a b : Multivector V Float) : Multivector V Float := contraction a (absym (boundaryM b))

/-- The grade-2 chain with the listed edges (vertex pairs, 1-based) set to their values in
order (later writes win, as Julia's `setblade!`). -/
def edges (V : TensorBundle) (es : List ((Nat × Nat) × Float)) : Chain V 2 Float :=
  let bit := fun (k : Nat) => (1 : UInt64) <<< (k - 1).toUInt64
  ⟨Values.ofFn fun i =>
    let b := (Leibniz.indexBasis V.n 2)[i.1]?.getD 0
    es.foldl (fun acc ((p, q), x) => if (bit p ||| bit q) == b then x else acc) 0⟩

/-- Julia `chain(t, Val(true))` (`src/Grassmann.jl:233-247`): the closed edge path
`v_{i₁i₂} + … + v_{i_{k-1}i_k} - v_{i₁i_k}` through the vertices of a term of grade `k ≥ 3`
(the edge itself for `k = 2`; lower grades have none: zero here, the term itself in Julia). -/
def chain {G : Nat} (t : Single V G Float) (closed : Bool := true) : Chain V 2 Float :=
  let C := t.bits &&& ~~~V.diffmask
  let ind := (List.range V.n).filter (fun k => (C >>> k.toUInt64) &&& 1 == 1) |>.map (· + 1)
  let g := ind.length
  if g < 2 then Chain.zero
  else
    let first := ind.headD 0
    let last := ind.getLast?.getD 0
    let close := if closed || g == 2 then [((first, last), if g == 2 then t.val else -t.val)] else []
    let path := (ind.zip (ind.drop 1)).map fun (p, q) => ((p, q), t.val)
    edges V (close ++ path)

/-- Julia `path(t) = chain(t, Val(false))` (`src/Grassmann.jl:248`): the open edge path. -/
def path {G : Nat} (t : Single V G Float) : Chain V 2 Float := chain t false

/-- Julia `count_gdims(t::Multivector)` (`src/multivectors.jl:1219-1231`): the number of
nonzero coefficients per grade `0 … n` (of the blades' non-tangent parts). -/
def countGdims (x : Multivector V Float) : Array Nat :=
  let bs := Leibniz.indexBasisAll V.n
  (List.range bs.size).foldl (init := Array.replicate (V.n + 1) 0) fun acc i =>
    if getD x.v i != 0 then acc.modify (symGrade V (bs[i]?.getD 0)) (· + 1) else acc

/-- Julia `χ(t) = Σ_{p=1}^{n+1} B[p]·(-1)^p` over `B = count_gdims(t)` (Leibniz
`src/generic.jl:173`; `-Σ_g (-1)^g b_g`, the opposite of the usual Euler characteristic). -/
def χ (x : Multivector V Float) : Int :=
  (countGdims x).toList.zipIdx.foldl (fun acc (b, g) => if g % 2 == 0 then acc - b else acc + b) 0

/-- Julia `boundary_rank(t, d)` (`src/Grassmann.jl:121-128`): `count_gdims(∂t)` with the
scalar count zeroed and grade `k ∈ 1 … n-1` capped by `d[k+1]`. -/
def boundaryRank (x : Multivector V Float) (d : Array Nat := countGdims x) : Array Nat :=
  let out := (countGdims (boundaryM x)).set! 0 0
  (List.range out.size).foldl (fun o k =>
    if 1 ≤ k && k + 1 < out.size then o.set! k (min (o[k]?.getD 0) (d[k + 1]?.getD 0)) else o) out

/-- Julia `boundary_null(t)` (`src/Grassmann.jl:137-146`): `d[k+1] - r[k]` for `k < n`, `0`
last. -/
def boundaryNull (x : Multivector V Float) : Array Int :=
  let d := countGdims x
  let r := boundaryRank x d
  (Array.range d.size).map fun k =>
    if k + 1 < d.size then ((d[k + 1]?.getD 0 : Nat) : Int) - (r[k]?.getD 0 : Nat) else 0

/-- Julia `betti(t)` (`src/Grassmann.jl:152-161`): `d[k+1] - r[k] - r[k+1]` for `k < n` (the
combinatorial Betti numbers, `n` of them). -/
def betti (x : Multivector V Float) : Array Int :=
  let d := countGdims x
  let r := boundaryRank x d
  (Array.range (d.size - 1)).map fun k =>
    ((d[k + 1]?.getD 0 : Nat) : Int) - (r[k]?.getD 0 : Nat) - (r[k + 1]?.getD 0 : Nat)

end Grassmann.Calculus
