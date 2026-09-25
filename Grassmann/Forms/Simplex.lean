/-
Simplex utilities (Grassmann.jl `src/composite.jl:814-986`, `src/forms.jl:1711-1727`;
Cartan.jl `src/element.jl:416-472` for the per-element `gradienthat`;
port-notes/grassmann-forms.md Appendix A).

A simplex is a grade-1 operator whose columns are its vertices in homogeneous
coordinates (`Simplex V W α`: `n = V.n` vertices in `W`, first coordinate `1`, e.g.
2-D points as `(1, x, y)`).

* `affineframe(t)`: the edge vectors `tᵢ − t₁` with the homogeneous coordinate
  dropped (`↓(W)`), an operator on the `n − 1` edges (`composite.jl:899-906`);
* `mean`, `barycenter`, `centroid` (`composite.jl:935-941`): `Σ/n`, `Σ`, `s/s[1]`
  (a tensor divided by a number is multiplied by the reciprocal, as Julia does);
* `detsimplex` (`det/(n-1)!`), `volume` (`|detsimplex|`), `edgelength`;
* `t \ v` (Cramer, `Forms.Compound`), `v ∈ t` (all barycentric coordinates ≥ 0 by
  Julia's sign test on the Cramer numerators, `composite.jl:734-747`);
* `gradient(t)`: the gradients of the barycentric coordinates ("hat functions"),
  Julia's Cramer formula on the rows (`composite.jl:814-831`); `gradienthat`
  (Cartan's per-element form: `±1/length` for segments, the barycentric gradients
  otherwise);
* `area` of a polygon (the shoelace formula through wedges, `composite.jl:974-980`);
* `findfirst`, `findlast`, `findall` of a point in a list of simplices.

The mesh-level functions of Cartan/MeshTopology (`affinehull` of a mesh, `volumes`
of a mesh, `interp`) belong to those ports; `affinehull` of one element is its
vertex operator itself.
-/
import Grassmann.Forms.Lie

namespace Grassmann

open DirectSum DirectSum.Bits StaticVectors AbstractTensors Grassmann.Forms

namespace TensorOperator

variable {V W : TensorBundle} {α : Type} [Coeff α]

/-- A simplex from its vertices (Julia `Chain{V,1}(points…)`), if there is one
per generator of `V`. -/
@[inline] def ofPoints? (pts : List (Chain W 1 α)) : Option (Simplex V W α) := ofColumnList? pts

/-- Julia `↓(W)` of a vector: its coordinates without the first (homogeneous) one. -/
@[specialize] def dropFirst (x : Chain W 1 α) : Chain (Forms.drop1 W) 1 α :=
  Chain.ofFn fun i => getD x.v (i.1 + 1)

/-- Julia `affineframe(t, y = t[1])` (`composite.jl:900-903`): the edge vectors
`tᵢ − y` (`i = 2 … n`) without their homogeneous coordinate (`y` defaults to the
first vertex). -/
@[specialize] def affineframe (T : Simplex V W α) (y : Option (Chain W 1 α) := none) :
    Simplex (TensorBundle.euclidean (V.n - 1)) (Forms.drop1 W) α :=
  let y0 := fun (i : Nat) => match y with | some y => getD y.v i | none => T.entry i 0
  TensorOperator.ofFn fun i j => T.entry (i.1 + 1) (j.1 + 1) - y0 (i.1 + 1)

/-- The sum of the columns, a left fold from the first (Julia `sum(value(t))`). -/
@[specialize] def colSum (T : Simplex V W α) : Chain W 1 α :=
  let n := (Layout.chain 1).size V.n
  ⟨Values.ofFn fun i =>
    match n with
    | 0 => Coeff.zero
    | n + 1 => (List.range n).foldl (fun acc j => acc + T.entry i.1 (j + 1)) (T.entry i.1 0)⟩

/-- Julia `barycenter(t) = sum(t)` (`composite.jl:938`). -/
@[inline] def barycenter (T : Simplex V W α) : Chain W 1 α := T.colSum

/-- Julia `mean(t) = sum(t)/n` (`composite.jl:935-937`), times the reciprocal. -/
@[inline] def mean [Div α] (T : Simplex V W α) : Chain W 1 α :=
  let r : α := Coeff.one / Coeff.ofInt ((Layout.chain 1).size V.n)
  T.colSum * r

/-- Julia `centroid(t) = (s = sum(t); s/s[1])` (`composite.jl:939-941`). -/
@[inline] def centroid [Div α] (T : Simplex V W α) : Chain W 1 α :=
  let s := T.colSum
  s * (Coeff.one / getD s.v 0)

/-- `(n-1)!` as a coefficient. -/
def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

/-- Julia `detsimplex(t) = det(t)/(n-1)!` (`composite.jl:934`): the signed volume of
a full-dimensional simplex in homogeneous coordinates. -/
@[inline] def detsimplex [Div α] (T : Simplex V W α) : α :=
  T.det * (Coeff.one / Coeff.ofInt (factorial (W.n - 1)))

/-- Julia `volumes(m)` for one simplex (`composite.jl:933`): `|detsimplex(t)|`, or
the edge length of a segment in a 2-generator space. -/
@[specialize] def volume [Div α] [Analytic α] (T : Simplex V W α) : α :=
  if W.n = 2 && V.n = 2 then
    let dx := T.entry 1 1 - T.entry 1 0
    Analytic.abs dx
  else Analytic.abs T.detsimplex

/-- Julia `edgelength(e) = |p₂ − p₁|` (`composite.jl:931`), the Euclidean length
of the difference of the two vertices without the homogeneous coordinate. -/
@[specialize] def edgelength [Analytic α] (T : Simplex V W α) : α :=
  let d := fun (i : Nat) => T.entry i 1 - T.entry i 0
  let s := (List.range (W.n - 1)).foldl (fun acc i => acc + d (i + 1) * d (i + 1)) Coeff.zero
  Analytic.sqrt s

/-- Julia `v ∈ t` for a full simplex (`composite.jl:734-739`): whether every Cramer
numerator `v ∧ yₙ₋₁`, `xᵢ ∧ v ∧ yₙ₋₁₋ᵢ`, `xₙ₋₁ ∧ v` has the sign of
`det t = t₁ ∧ yₙ₋₁` (signed zeros count, as Julia's `signbit`). -/
@[specialize] def contains [SignBit α] (T : Simplex V W α) (v : Chain W 1 α) : Bool :=
  let n := W.n
  let N := V.n
  if N ≠ n ∨ N < 2 then false
  else
    let (xs, ys) := T.prefixSuffix
    let x := fun (i : Nat) => xs[i - 1]!
    let y := fun (i : Nat) => ys[i - 1]!
    let vv := v.v.data
    let top := fun (a : Packed.Arr α) => Mat.rd a 0
    let s := SignBit.signbit (top (wedgeRaw n 1 (N - 1) (x 1) (y (N - 1))))
    let first := top (wedgeRaw n 1 (N - 1) vv (y (N - 1)))
    let mid := (List.range (N - 2)).map fun k =>
      let i := k + 1
      top (wedgeRaw n (i + 1) (N - 1 - i) (wedgeRaw n i 1 (x i) vv) (y (N - 1 - i)))
    let last := top (wedgeRaw n (N - 1) 1 (x (N - 1)) vv)
    (first :: mid ++ [last]).all fun c => SignBit.signbit c == s

/-- Julia `gradient(t)` (`composite.jl:814-831`): the gradients of the barycentric
coordinates of a simplex (column `i` for vertex `i`), vectors of `↓(W)`. For a full
simplex Julia's Cramer formula on the rows of `t` (Hodge complements of the
numerators times `1/det`); with fewer vertices than dimensions `t (tᵀt)⁻¹` without
the homogeneous row. -/
@[specialize] def gradient [Div α] (T : Simplex V W α) : Simplex V (Forms.drop1 W) α :=
  let n := W.n
  let M := V.n
  if M < n then
    let tt : Simplex W V α := T.transpose
    let g : Endomorphism V (.chain 1) α := tt.comp T
    let P : Simplex V W α := T.comp (g.invSquare (W := V))
    TensorOperator.ofFn fun i j => P.entry (i.1 + 1) j.1
  else
    -- rows of `T` as `n` vectors of dimension `M` (= `n`)
    let t : Simplex W V α := T.transpose
    let N := n - 1
    let (xs, ys) := t.prefixSuffix
    let x := fun (i : Nat) => xs[i - 1]!
    let y := fun (i : Nat) => ys[i - 1]!
    let mid := fun (i : Nat) => wedgeRaw M (N - i) i (y (N - i)) (x i)
    let vals : List (Packed.Arr α) :=
      if N % 2 == 0 then ((List.range (N - 1)).map fun k => mid (k + 1)) ++ [x N]
      else ((List.range (N - 1)).map fun k => let i := k + 1; if i % 2 == 1 then mid i else negP (mid i)) ++ [x N]
    let det := Mat.rd (wedgeRaw M 1 N (x 1) (y N)) 0
    let r := Coeff.one / det
    -- `⋆(valₖ / det)`: an (M-1)-blade to a vector (Euclidean Hodge = right complement)
    ofRowsP (vals.toArray.map fun v => complementRaw M (M - 1) (scaleP v r))

/-- Cartan `gradienthat` of one element (`element.jl:458-472`): for a segment
(`W` of 2 generators) the columns `∓1/length`; otherwise the barycentric
gradients (Cartan's triangle formula through `curls` gives the same vectors). -/
@[specialize] def gradienthat [Div α] [Analytic α] (T : Simplex V W α) : Simplex V (Forms.drop1 W) α :=
  if W.n = 2 && V.n = 2 then
    let c := Coeff.one / T.volume
    TensorOperator.ofFn fun _ j => if j.1 = 0 then -c else c
  else T.gradient

/-- Julia `area(m)` of a polygon (`composite.jl:974-980`): `|⋆(m[end]∧m[1] + Σ mᵢ∧mᵢ₊₁)|/2`
for homogeneous 2-D points, with the Euclidean norm. -/
@[specialize] def area [Kernels W] [Div α] [Analytic α] (pts : List (Chain W 1 α)) : α :=
  match pts with
  | [] => Coeff.zero
  | p :: _ =>
    let arr := pts.toArray
    let last := arr[arr.size - 1]!
    let S := (List.range (arr.size - 1)).foldl (fun (acc : Chain W 2 α) i => acc + (arr[i]! ∧ arr[i + 1]!))
      (last ∧ p)
    let h : Chain W (W.n - 2) α := ⋆S
    let s := h.v.foldl (fun acc c => acc + c * c) Coeff.zero
    Analytic.sqrt s * (Coeff.one / Coeff.ofInt 2)

end TensorOperator

/-- Julia `findfirst(P, t)` (`composite.jl:917-922`): the first simplex (1-based)
containing `P`, `0` if none. -/
def findfirstSimplex {V W : TensorBundle} {α : Type} [Coeff α] [SignBit α]
    (P : Chain W 1 α) (ts : List (Simplex V W α)) : Nat :=
  match ts.findIdx? (·.contains P) with
  | some i => i + 1
  | none => 0

/-- Julia `findlast(P, t)` (`composite.jl:923-928`). -/
def findlastSimplex {V W : TensorBundle} {α : Type} [Coeff α] [SignBit α]
    (P : Chain W 1 α) (ts : List (Simplex V W α)) : Nat :=
  match (ts.reverse.findIdx? (·.contains P)) with
  | some i => ts.length - i
  | none => 0

/-- Julia `findall(P, t)` (`composite.jl:929`): the 1-based indices of the simplices
containing `P`. -/
def findallSimplex {V W : TensorBundle} {α : Type} [Coeff α] [SignBit α]
    (P : Chain W 1 α) (ts : List (Simplex V W α)) : List Nat :=
  (ts.zipIdx.filter fun (t, _) => t.contains P).map (·.2 + 1)

end Grassmann
