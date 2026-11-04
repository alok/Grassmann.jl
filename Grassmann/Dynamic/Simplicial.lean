/-
The combinatorial topology of `Grassmann.Calculus.Simplicial` on dynamic elements with
Julia's `Int64` coefficients: the simplicial boundary `∂`, `skeleton`, `𝒫`, `subcomplex`,
`collapse`, `chain`, `path`, `count_gdims`, `χ`, `boundary_rank`, `boundary_null` and `betti`
(Grassmann.jl `src/Grassmann.jl:113-292`, Leibniz.jl `src/generic.jl:166-192`).

A basis blade `v_{i₁…i_g}` is the `(g−1)`-simplex on its vertices, and

  `∂ v_{i₁…i_g} = Σₖ (−1)^(g−k) v_{i₁…îₖ…i_g}`,

the boundary Julia computes as `ω ⋅ V(∇)` in a Euclidean space (`∂v₁₂₃ = v₁₂ − v₁₃ + v₂₃`).
Elements are read through their dense coefficients, so every kind is accepted. Results keep
Julia's kinds: `∂` of a `Single` or `Chain` of grade `g` is a `Chain` of grade `g − 1`, of a
`Multivector` a `Multivector`; `skeleton` and its relatives are `Multivector`s; `chain` and
`path` are grade-2 `Chain`s. Only the non-tangent part of a blade is a simplex
(`symmetricmask`), as in the static version.
-/
import Grassmann.Dynamic.Basic

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors

namespace TA

namespace Simplicial

variable {V : TensorBundle}

/-- Dense coefficients indexed by blade bits (`2ⁿ` entries). -/
abbrev Dense := Array Int

/-- The coefficients of `x` by blade bits. -/
def dense (x : TA V Int) : Dense :=
  (Array.range (2 ^ V.n)).map fun b => x.coeff b.toUInt64

/-- The simplex part of blade `b` (its non-tangent bits). -/
@[inline] def simplexBits (V : TensorBundle) (b : UInt64) : UInt64 := b &&& ~~~V.diffmask

/-- The vertices (0-based bit positions) of the simplex part of `b`, increasing. -/
def vertices (V : TensorBundle) (b : UInt64) : List Nat :=
  (List.range V.n).filter fun k => (simplexBits V b >>> k.toUInt64) &&& 1 == 1

/-- `∂` on dense coefficients. -/
def boundaryD (V : TensorBundle) (d : Dense) : Dense :=
  (List.range d.size).foldl (init := Array.replicate d.size 0) fun out b =>
    let c := d[b]!
    if c == 0 then out else
    let vs := vertices V b.toUInt64
    let g := vs.length
    vs.zipIdx.foldl (fun out (v, k) =>
      let f := (b.toUInt64 ^^^ ((1 : UInt64) <<< v.toUInt64)).toNat
      out.modify f (· + (if (g - 1 - k) % 2 == 0 then c else -c))) out

/-- Julia `absym`: every coefficient's absolute value. -/
@[inline] def absymD (d : Dense) : Dense := d.map fun c => (c.natAbs : Int)

/-- `x + y` on dense coefficients. -/
@[inline] def addD (x y : Dense) : Dense := (Array.range x.size).map fun i => x[i]! + y[i]!

mutual

/-- Julia `skeleton(x, Val(T))` on dense coefficients: the sum of the skeletons of the
nonzero terms (of positive simplex grade when `T`). -/
def skeletonD (V : TensorBundle) (T : Bool) (d : Dense) : Nat → Dense
  | 0 => Array.replicate d.size 0
  | fuel + 1 =>
    (List.range d.size).foldl (init := Array.replicate d.size 0) fun acc b =>
      let c := d[b]!
      if c != 0 && (!T || (vertices V b.toUInt64).length > 0) then addD acc (skeletonTermD V T d.size b c fuel)
      else acc

/-- Julia `skeleton(x::TensorTerm, Val(T))`: `absym(x) + skeleton(absym(∂x))` for a term of
positive grade; a scalar is dropped (`T`) or kept. -/
def skeletonTermD (V : TensorBundle) (T : Bool) (size b : Nat) (c : Int) : Nat → Dense
  | 0 => Array.replicate size 0
  | fuel + 1 =>
    let unit := (Array.replicate size (0 : Int)).set! b (c.natAbs : Int)
    if (vertices V b.toUInt64).length > 0 then
      addD unit (skeletonD V T (absymD (boundaryD V ((Array.replicate size (0 : Int)).set! b c))) fuel)
    else if T then Array.replicate size 0 else unit

end

/-- A dense value as a multivector. -/
@[inline] def toMulti (V : TensorBundle) (d : Dense) : TA V Int := multi (multiOf V fun b => d[b.toNat]!)

/-- The grade of a homogeneous kind (`Single`, `Chain`, blade), else `none`. -/
def homogeneousGrade : TA V Int → Option Nat
  | blade b | single b _ => some (popcount b)
  | chain g _ => some g
  | _ => none

/-- Julia `∂(ω)` (`boundary`): the simplicial boundary, a `Chain` of one grade lower for a
`Single`/`Chain`, a `Multivector` otherwise. -/
def boundary (x : TA V Int) : TA V Int :=
  let d := boundaryD V (dense x)
  match homogeneousGrade x with
  | some 0 => zero
  | some g => chain (g - 1) (chainOf V (g - 1) fun b => d[b.toNat]!)
  | none => toMulti V d

/-- Julia `skeleton(x)`: every face of every simplex of `x`, with multiplicity, without the
empty face. -/
def skeleton (x : TA V Int) : TA V Int := toMulti V (skeletonD V true (dense x) (2 * V.n + 4))

/-- Julia `𝒫(t)` (intended `skeleton(t, Val(false))`, defect `laplacian-not-callable`): the
skeleton with the empty face. -/
def 𝒫 (x : TA V Int) : TA V Int := toMulti V (skeletonD V false (dense x) (2 * V.n + 4))

/-- Julia `subcomplex(x) = Δ(absym(∂x))` (intended): the skeleton of the boundary. -/
def subcomplex (x : TA V Int) : TA V Int :=
  toMulti V (skeletonD V true (absymD (boundaryD V (dense x))) (2 * V.n + 4))

/-- Julia `count_gdims(t)`: the number of nonzero coefficients per simplex grade `0 … n`. -/
def countGdimsD (V : TensorBundle) (d : Dense) : Array Nat :=
  (List.range d.size).foldl (init := Array.replicate (V.n + 1) 0) fun acc b =>
    if d[b]! != 0 then acc.modify (vertices V b.toUInt64).length (· + 1) else acc

/-- Julia `count_gdims(t)`. -/
def countGdims (x : TA V Int) : Array Nat := countGdimsD V (dense x)

/-- Julia `χ(t) = Σₚ (−1)ᵖ count_gdims(t)[p]` (1-based `p`). -/
def χ (x : TA V Int) : Int :=
  (countGdims x).toList.zipIdx.foldl (fun acc (b, g) => if g % 2 == 0 then acc - b else acc + b) 0

/-- Julia `boundary_rank(t)`: `count_gdims(∂t)`, scalar count zeroed, grade `k ∈ 1 … n−1`
capped by `count_gdims(t)[k+1]`. -/
def boundaryRank (x : TA V Int) : Array Nat :=
  let d := countGdims x
  let out := (countGdimsD V (boundaryD V (dense x))).set! 0 0
  (List.range out.size).foldl (fun o k =>
    if 1 ≤ k && k + 1 < out.size then o.set! k (min o[k]! (d[k + 1]?.getD 0)) else o) out

/-- Julia `boundary_null(t)`: `d[k+1] − r[k]` for `k < n`, `0` last. -/
def boundaryNull (x : TA V Int) : Array Int :=
  let d := countGdims x
  let r := boundaryRank x
  (Array.range d.size).map fun k =>
    if k + 1 < d.size then ((d[k + 1]! : Nat) : Int) - (r[k]! : Nat) else 0

/-- Julia `betti(t)`: `d[k+1] − r[k] − r[k+1]` for `k < n` (`n` numbers). -/
def betti (x : TA V Int) : Array Int :=
  let d := countGdims x
  let r := boundaryRank x
  (Array.range (d.size - 1)).map fun k =>
    ((d[k + 1]! : Nat) : Int) - (r[k]! : Nat) - (r[k + 1]?.getD 0 : Nat)

/-- Julia `collapse(a, b) = a ⋅ absym(∂b)` needs the contraction; `absym(∂b)` is this. -/
def absymBoundary (x : TA V Int) : TA V Int := toMulti V (absymD (boundaryD V (dense x)))

/-- Julia `chain(t, Val(closed))` of a term `c·v_{i₁…i_g}`: the edge path
`c(v_{i₁i₂} + … + v_{i_{g−1}i_g}) − c·v_{i₁i_g}` (closed) through its vertices; the edge itself
for `g = 2`; zero below. -/
def chainPath (x : TA V Int) (closed : Bool := true) : TA V Int :=
  match x.term? with
  | none => zero
  | some (b, c) =>
    let vs := vertices V b
    let g := vs.length
    if g < 2 then zero else
    let bit := fun (k : Nat) => (1 : UInt64) <<< k.toUInt64
    let first := vs.headD 0
    let last := vs.getLast?.getD 0
    let close := if closed || g == 2 then [((bit first ||| bit last), if g == 2 then c else -c)] else []
    let edges := (vs.zip (vs.drop 1)).map fun (p, q) => ((bit p ||| bit q), c)
    let es := close ++ edges
    chain 2 (chainOf V 2 fun β => es.foldl (fun acc (e, v) => if e == β then v else acc) 0)

/-- Julia `path(t) = chain(t, Val(false))`. -/
def path (x : TA V Int) : TA V Int := chainPath x false

end Simplicial

end TA

end Grassmann
