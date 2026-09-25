import FlowGeometry.Airfoil

/-!
# Structured meshes and point utilities

FlowGeometry.jl `src/FlowGeometry.jl:38-289`: the rectangle triangulation of a structured grid, its
boundary loop, the Rakich stretched C-mesh around a thin plate, rectangle and box corners, the
icosahedron and its subdivision onto a sphere, the rectangle-to-circle boundary points, closed edge
loops, a brute-force 2-D convex hull, the 3-D wing surface, and the geometry description that
`decsg` hands to MATLAB. Points are homogeneous `Chain`s (`(1, x, y)` in `ℝ3`, `(1, x, y, z)` in `ℝ4`)
stored flat in `Cartan.PointCloud`s; meshes are MeshTopology `SimplexTopology`s and Cartan
`SimplexBundle`s, as in Julia. Mesh indices are Julia's (1-based).

Everything agrees with Julia bit for bit (`oracle/golden/flowgeometry/{mesh,sphere,wing}.json`),
including the quirks: `rectcirc` omits the centre offsets from the edge points (port notes §4.2.6),
the sphere subdivision duplicates shared edge midpoints, and `RakichPlate` reads the interior of
its interval as a re-anchored range slice. The broken helpers `edgeslist!`, `addbound` and
`airfoilbox` (FG-B5, FG-B8) are implemented as intended.
-/

namespace FlowGeometry

open JuliaBase Cartan Grassmann DirectSum MeshTopology

/-- A homogeneous point `(1, x, y)` of `ℝ3`. -/
@[inline] def pt3 (x y : Float) : Chain ℝ3 1 Float := vecOf #[1, x, y]

/-- A homogeneous point `(1, x, y, z)` of `ℝ4`. -/
@[inline] def pt4 (x y z : Float) : Chain ℝ4 1 Float := vecOf #[1, x, y, z]

/-! ## Structured triangles -/

/-- Julia `rectangletriangle(i, j, m)` (`FlowGeometry.jl:87-90`): triangle `i` (1-based) of cell
row `j` in a grid with `m` points per column: `k = (j-1)m + i÷2 + 1`, `n = m + k`, then
`(k, n, k+1)` for odd `i` and `(k, n-1, n)` for even `i`. -/
def rectangletriangleIJ (i j m : Nat) : Vector Nat 3 :=
  let k := (j - 1) * m + i / 2 + 1
  let n := m + k
  if i % 2 == 1 then #v[k, n, k + 1] else #v[k, n - 1, n]

/-- Julia `rectangletriangle(i, m)` (`FlowGeometry.jl:86`): the `i`-th triangle (1-based) of a
structured grid with `m` points per column. -/
def rectangletriangle (i m : Nat) : Vector Nat 3 :=
  rectangletriangleIJ ((i - 1) % (2 * (m - 1)) + 1) ((i - 1) / (2 * (m - 1)) + 1) m

/-- The vertices of triangle `i` of cell row `j` lie in `1 … m·JL` (port notes §8.2: the mesh index
bounds). -/
theorem rectangletriangleIJ_bounds {i j JL m : Nat} (hi : 1 ≤ i ∧ i ≤ 2 * (JL - 1)) (hj : 1 ≤ j ∧ j + 1 ≤ m) :
    ∀ v ∈ (rectangletriangleIJ i j JL).toList, 1 ≤ v ∧ v ≤ m * JL := by
  have hq : (j - 1) * JL + JL + JL ≤ m * JL := by
    have h1 : (j - 1 + 2) * JL ≤ m * JL := Nat.mul_le_mul_right JL (by omega)
    have h2 : (j - 1 + 2) * JL = (j - 1) * JL + JL + JL := by
      rw [Nat.add_mul]; omega
    omega
  have hd : i / 2 + 1 ≤ JL := by omega
  intro v hv
  unfold rectangletriangleIJ at hv
  dsimp only at hv
  split at hv <;> simp at hv <;> omega

/-- Every vertex of `rectangletriangle i JL`, for `1 ≤ i ≤ 2(m-1)(JL-1)`, is a point of the `m × JL`
grid: `rectangletriangles m JL` only refers to existing points. -/
theorem rectangletriangle_bounds {i m JL : Nat} (hJL : 2 ≤ JL) (hi : 1 ≤ i ∧ i ≤ 2 * (m - 1) * (JL - 1)) :
    ∀ v ∈ (rectangletriangle i JL).toList, 1 ≤ v ∧ v ≤ m * JL := by
  unfold rectangletriangle
  have hpos : 0 < 2 * (JL - 1) := by omega
  have hr := Nat.mod_lt (i - 1) hpos
  have h : (i - 1) / (2 * (JL - 1)) < m - 1 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have : 2 * (m - 1) * (JL - 1) = (m - 1) * (2 * (JL - 1)) := by
      rw [Nat.mul_comm 2 (m - 1), Nat.mul_assoc]
    omega
  generalize (i - 1) / (2 * (JL - 1)) = q at h ⊢
  generalize (i - 1) % (2 * (JL - 1)) = r at hr ⊢
  exact rectangletriangleIJ_bounds ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

/-- The triangles of an `m × JL` structured grid (column `JL` points each). -/
def rectangletriangleList (m JL : Nat) : Array (Vector Nat 3) :=
  (Array.range (2 * (m - 1) * (JL - 1))).map fun i => rectangletriangle (i + 1) JL

/-- Julia `rectangletriangles(m = 51, JL = 51)` (`FlowGeometry.jl:93-95`): the `2(m-1)(JL-1)`
triangles of an `m × JL` grid, points numbered `k = (i-1)JL + j` (column `i`, row `j`). -/
def rectangletriangles (m : Nat := 51) (JL : Nat := 51) : SimplexTopology 3 :=
  SimplexTopology.ofElements (rectangletriangleList m JL) (p := some (m * JL))

/-- Julia's vertex loop of `rectanglebounds(n, JL)`: up column 1, along the last row, down the last
column, back along the first row, closed. -/
def rectangleboundLoop (n JL : Nat) : Array Nat :=
  let up := (Array.range n).map fun i => 1 + JL * i                      -- 1:JL:JL*n
  let top := (Array.range (JL - 1)).map fun i => JL * (n - 1) + 2 + i    -- JL*(n-1)+2:JL*n
  let down := (Array.range (n - 1)).map fun i => JL * (n - 1) - JL * i   -- JL*(n-1):-JL:JL
  let back := (Array.range (JL - 2)).map fun i => JL - 1 - i              -- JL-1:-1:2
  up ++ top ++ down ++ back ++ #[1]

/-- The boundary loop visits `2(n-1) + 2(JL-1)` points and returns to the first: it has
`2n + 2JL - 3` entries. -/
theorem rectangleboundLoop_size {n JL : Nat} (hn : 1 ≤ n) (hJL : 2 ≤ JL) :
    (rectangleboundLoop n JL).size = 2 * n + 2 * JL - 3 := by
  simp [rectangleboundLoop]
  omega

/-- The loop is closed: it starts and ends at point `1`. -/
theorem rectangleboundLoop_closed {n JL : Nat} (hn : 1 ≤ n) :
    (rectangleboundLoop n JL)[0]? = some 1 ∧ (rectangleboundLoop n JL).back? = some 1 := by
  refine ⟨?_, by simp [rectangleboundLoop, Array.back?_push]⟩
  unfold rectangleboundLoop
  rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left (by simp; omega),
    Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left (by simp; omega)]
  simp
  exact ⟨0, by simp [Array.getElem?_range]; omega, Nat.mul_zero JL⟩

/-- Julia `rectanglebounds(n = 51, JL = 51)` (`FlowGeometry.jl:96-99`): the boundary edges of the
grid as a closed loop. -/
def rectanglebounds (n : Nat := 51) (JL : Nat := 51) : SimplexTopology 2 :=
  let b := rectangleboundLoop n JL
  SimplexTopology.ofElements ((Array.range (b.size - 1)).map fun i => #v[b[i]!, b[i + 1]!]) (p := some (n * JL))

/-- Julia `FittedPoint(k, JL = 51)` (`FlowGeometry.jl:101`): the integer grid coordinates
`(1, (k-1)÷JL, (k-1)%JL)` of point `k`. -/
def fittedPoint (k : Nat) (JL : Nat := 51) : Chain ℝ3 1 Float :=
  pt3 ((k - 1) / JL).toUInt64.toFloat ((k - 1) % JL).toUInt64.toFloat

/-! ## Rakich stretching -/

/-- `n` as a `Float` (Julia's `Int` arguments). -/
@[inline] def natF (n : Nat) : Float := n.toUInt64.toFloat

/-- Julia `RakichNewton(D = 50, JL = 51, Δy = 6e-3)` (`FlowGeometry.jl:107-114`): ten Newton
steps for the stretching `κ` that makes the first of `JL-1` geometrically stretched cells over a
height `D` have height `Δy`. -/
def rakichNewton (D : Float := 50) (JL : Nat := 51) (Δy : Float := f64! 6e-3) : Float :=
  let j := 1 / natF (JL - 1)
  go j 10 1
where
  /-- the Newton iteration -/
  go (j : Float) : Nat → Float → Float
    | 0, κ => κ
    | n + 1, κ =>
      let eκ := F64.exp κ
      let ejκ := F64.exp (j * κ)
      go j n (κ - (((ejκ - 1) * D - (eκ - 1) * Δy) * (eκ - 1)) / ((ejκ * (eκ * (j - 1) - j) + eκ) * D))

/-- Julia `Rakich(κ, j, y0 = 0, D = 50, JL = 51)` (`FlowGeometry.jl:116`): the height of
row `j` (1-based) of a column stretched by `κ` from `y0` to `D`. -/
def rakich (κ : Float) (j : Nat) (y0 : Float := 0) (D : Float := 50) (JL : Nat := 51) : Float :=
  y0 + (D - y0) * (F64.exp (κ * natF (j - 1) / natF (JL - 1)) - 1) / (F64.exp κ - 1)

/-- Julia `RakichLine(y = 0, D = 50, JL = 51, Δy = 6e-3, κ = RakichNewton(D-y, JL, Δy))`
(`FlowGeometry.jl:117`): the `JL` stretched heights from `y` to `D`. -/
def rakichLine (y : Float := 0) (D : Float := 50) (JL : Nat := 51) (Δy : Float := f64! 6e-3) : FloatArray :=
  let κ := rakichNewton (D - y) JL Δy
  floatsOfFn JL fun j => rakich κ (j + 1) y D JL

/-- Julia `RakichPlate(::Profile{n}, D = 50, JL = 51)` (`FlowGeometry.jl:119-123`): the `JL` chord
stations of a C-mesh around the plate `[0, 1]` sampled at `n` points: stretched to `-D` ahead,
the interior samples, stretched to `1 + D` behind. -/
def rakichPlate (n : Nat) (D : Float := 50) (JL : Nat := 51) : FloatArray :=
  let x := interval n
  let x1 := x.first
  let m := ((Int.ofNat JL - Int.ofNat n).tdiv 2 + 1).toNat
  let r := rakichLine (-x1) D m (x.step?.getD 0)
  let inner := (sliceAxis x 2 (n - 1)).toFloatArray
  let shift := (if x1 > 0 then (2 : Float) else -1) * x1 + x.last
  let nr := r.size
  let ni := inner.size
  floatsOfFn (2 * nr + ni) fun i =>
    if i < nr then -(r.get! (nr - 1 - i))
    else if i < nr + ni then inner.get! (i - nr)
    else r.get! (i - nr - ni) + shift

/-- Julia `RakichPoint(k, x, y, s, κ, JL)` (`FlowGeometry.jl:125-128`) for the rows `yk … JL-1` of
chord station `xk`, appended to `acc`. -/
def rakichColumn (x y s κ : FloatArray) (yEnd : Float) (JL xk : Nat) : Nat → Nat → FloatArray → FloatArray
  | _, 0, acc => acc
  | yk, m + 1, acc =>
    let sk := s.get! xk
    let v := if sk != 0 then rakich (κ.get! xk) (yk + 1) sk yEnd JL else y.get! yk
    rakichColumn x y s κ yEnd JL xk (yk + 1) m (((acc.push 1).push (x.get! xk)).push v)

/-- The points `k = 1 … n·JL` of `rakichpoints`, column by column from station `xk`. -/
def rakichFill (x y s κ : FloatArray) (yEnd : Float) (JL : Nat) : Nat → Nat → FloatArray → FloatArray
  | _, 0, acc => acc
  | xk, c + 1, acc => rakichFill x y s κ yEnd JL (xk + 1) c (rakichColumn x y s κ yEnd JL xk 0 JL acc)

/-- Julia `rakichpoints(P::CircularArc{T,m} = CircularArc{6,21}(), D = 50, n = 51, JL = 51)`
(`FlowGeometry.jl:125-137`): the `n × JL` points of the stretched C-mesh around a circular arc of
thickness `T` percent (`m` samples): chord stations from `RakichPlate`, rows stretched from the
arc surface (or from `0` off the plate) to the outer boundary. -/
def rakichpoints (T : Num := 6) (m : Nat := 21) (D : Float := 50) (n : Nat := 51) (JL : Nat := 51) :
    PointCloud (Chain ℝ3 1 Float) :=
  let P : Profile := .circularArc T m
  let t := T.toFloat / 100
  let x := rakichPlate m D n
  let y := rakichLine 0 D JL (t / 10)
  let e := P.eval
  let s := floatsOfFn x.size fun i => e.value ((x.get! i - 0) / 1) * 1
  let κ := floatsOfFn s.size fun i => let k := s.get! i; if k != 0 then rakichNewton (D - k) JL (t / 10) else 0
  let yEnd := y.get! (y.size - 1)
  ⟨rakichFill x y s κ yEnd JL 0 n (FloatArray.emptyWithCapacity (3 * (n * JL))), .induced, 0⟩

/-- Julia `initrakich(P = CircularArc{6,61}(), D = 50, n = 101, JL = 51)` (`FlowGeometry.jl:139-142`):
the triangulated C-mesh and its boundary loop over the same points. -/
def initrakich (T : Num := 6) (m : Nat := 61) (D : Float := 50) (n : Nat := 101) (JL : Nat := 51) :
    SimplexBundle 3 (Chain ℝ3 1 Float) × SimplexBundle 2 (Chain ℝ3 1 Float) :=
  let p := rakichpoints T m D n JL
  (⟨p, rectangletriangles n JL⟩, ⟨p, rectanglebounds n JL⟩)

/-! ## Rectangles, boxes, polyhedra -/

/-- Julia `rectangle(xn, xm, yn, ym)` (`FlowGeometry.jl:150-152`): the corners, counter-clockwise
from the lower left, homogeneous in `ℝ3`. -/
def rectangle (xn xm yn ym : Float) : Array (Chain ℝ3 1 Float) :=
  #[pt3 xn yn, pt3 xm yn, pt3 xm ym, pt3 xn ym]

/-- Julia `square(xn, xm) = rectangle(xn, xm, xn, xm)` (`FlowGeometry.jl:149`). -/
def square (xn xm : Float) : Array (Chain ℝ3 1 Float) := rectangle xn xm xn xm

/-- Julia `square(x) = square(-x, x)` (`FlowGeometry.jl:148`). -/
def square1 (x : Float) : Array (Chain ℝ3 1 Float) := square (-x) x

/-- Julia `box(xn, xm, yn, ym, zn, zm)` (`FlowGeometry.jl:156-160`): the 8 corners in `ℝ4`, the
bottom face counter-clockwise, then the top face. -/
def box (xn xm yn ym zn zm : Float) : Array (Chain ℝ4 1 Float) :=
  #[pt4 xn yn zn, pt4 xm yn zn, pt4 xm ym zn, pt4 xn ym zn,
    pt4 xn yn zm, pt4 xm yn zm, pt4 xm ym zm, pt4 xn ym zm]

/-- Julia `cube(xn, xm) = box(xn, xm, xn, xm, xn, xm)` (`FlowGeometry.jl:155`). -/
def cube (xn xm : Float) : Array (Chain ℝ4 1 Float) := box xn xm xn xm xn xm

/-- Julia `cube(x) = cube(-x, x)` (`FlowGeometry.jl:154`). -/
def cube1 (x : Float) : Array (Chain ℝ4 1 Float) := cube (-x) x

/-- Julia `Float64(φ)`, the golden ratio. -/
def goldenRatio : Float := f64! 1.618033988749895

/-- Julia `icosahedron(a = 1, b = a·φ)` (`FlowGeometry.jl:162-167`): the 12 vertices, cyclic
permutations of `(0, ±a, ±b)`, in Julia's order. -/
def icosahedron (a : Float := 1) (b : Float := a * goldenRatio) : Array (Chain ℝ4 1 Float) :=
  #[pt4 0 a b, pt4 b 0 a, pt4 a b 0, pt4 0 a (-b), pt4 (-b) 0 a, pt4 a (-b) 0,
    pt4 0 (-a) b, pt4 b 0 (-a), pt4 (-a) b 0, pt4 0 (-a) (-b), pt4 (-b) 0 (-a), pt4 (-a) (-b) 0]

/-- Julia `sphere(r = 1) = icosahedron(r/sqrt(1+φ^2))` (`FlowGeometry.jl:174`): the icosahedron
with its vertices at radius `r`. -/
def sphere (r : Float := 1) : Array (Chain ℝ4 1 Float) :=
  icosahedron (r / (1 + goldenRatio * goldenRatio).sqrt)

/-- Julia `circlemid(x, r) = r*unit(x/2 - v₁) + v₁` (`FlowGeometry.jl:169-172`): the midpoint of a
sum of two homogeneous points, pushed out to radius `r`. Grassmann's `unit(t) = t/abs(t)` divides by
the scalar `abs(t)` as `t * (1/abs(t))`. -/
def circlemid (x : Chain ℝ4 1 Float) (r : Float) : Chain ℝ4 1 Float :=
  let t0 := x.v.get! 0 * f64! 0.5 - 1
  let t1 := x.v.get! 1 * f64! 0.5
  let t2 := x.v.get! 2 * f64! 0.5
  let t3 := x.v.get! 3 * f64! 0.5
  let inv := 1 / (((t0 * t0 + t1 * t1) + t2 * t2) + t3 * t3).sqrt
  vecOf #[r * (t0 * inv) + 1, r * (t1 * inv), r * (t2 * inv), r * (t3 * inv)]

/-- Push `circlemid(p_a + p_b, r)` of the points at offsets `a`, `b` of `pts` onto `acc`. -/
@[inline] def pushMid (pts : FloatArray) (a b : Nat) (r : Float) (acc : FloatArray) : FloatArray :=
  let t0 := (pts.get! a + pts.get! b) * f64! 0.5 - 1
  let t1 := (pts.get! (a + 1) + pts.get! (b + 1)) * f64! 0.5
  let t2 := (pts.get! (a + 2) + pts.get! (b + 2)) * f64! 0.5
  let t3 := (pts.get! (a + 3) + pts.get! (b + 3)) * f64! 0.5
  let inv := 1 / (((t0 * t0 + t1 * t1) + t2 * t2) + t3 * t3).sqrt
  (((acc.push (r * (t0 * inv) + 1)).push (r * (t1 * inv))).push (r * (t2 * inv))).push (r * (t3 * inv))

/-- Vertex `k` (0-based) of subspace face `e` (1-based) of a triangle topology (read from the flat
connectivity when the topology is its full mesh). -/
@[inline] def faceVertex (t : SimplexTopology 3) (e k : Nat) : Nat :=
  if t.sub.isOneTo || t.isFull then t.conn[3 * (t.getFacet e - 1) + k]! else (t.get e)[k]!

/-- The edge midpoints of the faces `e … e+k-1` (1-based) appended to the points, and the four
faces replacing each (new points numbered from `n + 1`). -/
def refineFaces (t : SimplexTopology 3) (r : Float) : Nat → Nat → Nat → FloatArray → Array (Vector Nat 3) →
    FloatArray × Array (Vector Nat 3)
  | _, 0, _, pts, out => (pts, out)
  | e, k + 1, n, pts, out =>
    let (v0, v1, v2) := (faceVertex t e 0, faceVertex t e 1, faceVertex t e 2)
    let (o0, o1, o2) := (4 * (v0 - 1), 4 * (v1 - 1), 4 * (v2 - 1))
    let pts := pushMid pts o2 o0 r (pushMid pts o1 o2 r (pushMid pts o0 o1 r pts))
    let out := (((out.push #v[v0, n + 1, n + 3]).push #v[n + 1, v1, n + 2]).push #v[n + 2, v2, n + 3]).push
      #v[n + 1, n + 2, n + 3]
    refineFaces t r (e + 1) k (n + 3) pts out

/-- Julia `sphere(fac::SimplexBundle, r = 1)` (`FlowGeometry.jl:175-193`): one 1→4 subdivision of
a triangulated sphere, the three edge midpoints of every face pushed to radius `r` and appended
(shared edges get duplicate points, as in Julia), each face replaced by
`(v₀,v₃,v₅), (v₃,v₁,v₄), (v₄,v₂,v₅), (v₃,v₄,v₅)`. -/
def sphereRefine (fac : SimplexBundle 3 (Chain ℝ4 1 Float)) (r : Float := 1) :
    SimplexBundle 3 (Chain ℝ4 1 Float) :=
  let ne := fac.top.elements
  let (pts, out) := refineFaces fac.top r 1 ne (fac.cloud.points.size / 4) fac.cloud.points (Array.mkEmpty (4 * ne))
  let np := pts.size / 4
  ⟨⟨pts, fac.cloud.metric, fac.cloud.id⟩, SimplexTopology.ofElements out (p := some np) (i := some (.oneTo np))⟩

/-! ## Boundary points -/

/-- Julia `rectcirc(n, xn, xm, yn, ym, c = (1, 0, 0))` (`FlowGeometry.jl:56-80`): points on the
rectangle's boundary at equal angles about `c`, `n - 1` per side starting at each corner. As in
Julia, the edge points omit the centre offset (`v/tan θ` rather than `c.x + v/tan θ`). -/
def rectcirc (n : Nat) (xn xm yn ym : Float) (c : Chain ℝ3 1 Float := pt3 0 0) : Array (Chain ℝ3 1 Float) :=
  let xs := #[yn, xm, ym, xn]
  let r := rectangle xn xm yn ym
  let cx := c.v.get! 1
  let cy := c.v.get! 2
  let off := #[piF, twoPiF, 0, piF]
  let ang := (Array.range 4).map fun i =>
    let p := r[i]!
    F64.atan ((p.v.get! 2 - cy) / (p.v.get! 1 - cx)) + off[i]!
  let nf := natF (n - 1)
  (Array.range 4).foldl (fun out i =>
    let out := out.push r[i]!
    let a := ang[i]!
    let d := F64.rem (ang[(i + 1) % 4]! - a + twoPiF) twoPiF
    let θ (k : Nat) := a + natF k * d / nf
    if i % 2 == 0 then
      let v := xs[i]! - cy
      (Array.range (n - 2)).foldl (fun out k => out.push (pt3 (v / F64.tan (θ (k + 1))) xs[i]!)) out
    else
      let v := xs[i]! - cx
      (Array.range (n - 2)).foldl (fun out k => out.push (pt3 xs[i]! (v * F64.tan (θ (k + 1))))) out) #[]

/-! ## Edge loops -/

/-- Julia `edgeslist(p)` (`FlowGeometry.jl:41-43`): the closed loop `(i, i % n + 1)` over the
points. -/
def edgeslistN (n : Nat) : Array (Vector Nat 2) := (Array.range n).map fun i => #v[i + 1, (i + 1) % n + 1]

/-- Julia `edgeslist(p::PointCloud)`. -/
def edgeslist {P : Type} [FlatFiber P] (p : PointCloud P) : Array (Vector Nat 2) := edgeslistN p.size

/-- Julia `edgeslist!(p, r)` (`FlowGeometry.jl:44-48`, which throws on a `PointCloud`, FG-B8) as
intended: the cloud with the points `r` appended, and the closed loop over the new points. -/
def edgeslistPush {P : Type} [FlatFiber P] (p : PointCloud P) (r : Array P) :
    PointCloud P × Array (Vector Nat 2) :=
  let l := p.size
  let n := r.size
  (⟨r.foldl FlatFiber.push p.points, p.metric, p.id⟩,
   (Array.range n).map fun i => #v[l + i + 1, l + (i + 1) % n + 1])

/-- Julia `airfoiledges(n) = edgeslist(PointCloud(points(n)))` (`FlowGeometry.jl:54`). -/
def airfoiledges (a : Airfoil) : Array (Vector Nat 2) := edgeslist a.points

/-- Julia `addbound(e, r)` (`FlowGeometry.jl:52`, broken upstream, FG-B5) as intended: the points
`r` appended to the cloud of the edge list `e`, and `e` followed by their closed loop. -/
def addbound (p : PointCloud (Chain ℝ3 1 Float)) (e : Array (Vector Nat 2)) (r : Array (Chain ℝ3 1 Float)) :
    PointCloud (Chain ℝ3 1 Float) × Array (Vector Nat 2) :=
  let (p', e') := edgeslistPush p r
  (p', e ++ e')

/-- Julia `airfoilbox(n)` (`FlowGeometry.jl:53`, broken upstream) with explicit bounds: the
airfoil outline and the rectangle `[xn, xm] × [yn, ym]`, as one point cloud with two closed loops. -/
def airfoilbox (a : Airfoil) (xn xm yn ym : Float) : PointCloud (Chain ℝ3 1 Float) × Array (Vector Nat 2) :=
  addbound a.points (airfoiledges a) (rectangle xn xm yn ym)

/-! ## Convex hull -/

/-- The trivector coefficient of `(a ∧ b) ∧ c` for homogeneous points `(w, x, y)` (Julia
`Real(pi∧pj∧pk)`), in the Grassmann kernels' operation order (bit-identical to the wedge
products; `Tests/FlowGeometry/Meshes.lean` checks it against them). -/
@[inline] def det3 (aw ax ay bw bx «by» cw cx cy : Float) : Float :=
  let b12 := aw * bx - ax * bw
  let b13 := aw * «by» - ay * bw
  let b23 := ax * «by» - ay * bx
  (b12 * cy - b13 * cx) + b23 * cw

/-- `(a ∧ b) ∧ c` with the Grassmann port's wedge kernels (the reference for `det3`). -/
def det3Chain (a b c : Chain ℝ3 1 Float) : Float := top ((a ∧ b : Chain ℝ3 2 Float) ∧ c : Chain ℝ3 3 Float)

/-- Julia `Real(abs(v))` of a vector `(u₀, u₁, u₂)`: `sqrt(v⋅v)`. -/
@[inline] def norm3 (u0 u1 u2 : Float) : Float := ((u0 * u0 + u1 * u1) + u2 * u2).sqrt

/-- Whether some point `k ∉ {i, j}` rules out the directed edge `(i, j)` (the inner loop of
Julia's `convhull`, with `pᵢ ∧ pⱼ = (b₁₂, b₁₃, b₂₃)`, the midpoint `m` and `|pᵢ - pⱼ|` computed once
per edge as Julia does; distances only where Julia computes them). -/
def hullBlocked (w x y : FloatArray) (i j : Nat) (rr : Float) (useR : Bool)
    (b12 b13 b23 mw mx my dw dx dy : Float) : Nat → Nat → Bool
  | _, 0 => false
  | k, fuel + 1 =>
    if k == i || k == j then hullBlocked w x y i j rr useR b12 b13 b23 mw mx my dw dx dy (k + 1) fuel else
    let wk := w.get! k
    let xk := x.get! k
    let yk := y.get! k
    let blocked :=
      if useR then
        let dk := norm3 (mw - wk) (mx - xk) (my - yk)
        if dk > rr then false
        else
          let d := (b12 * yk - b13 * xk) + b23 * wk
          if d == f64! 0.0 then dk < norm3 dw dx dy else d > f64! 0.0
      else
        let d := (b12 * yk - b13 * xk) + b23 * wk
        if d == f64! 0.0 then norm3 (mw - wk) (mx - xk) (my - yk) < norm3 dw dx dy else d > f64! 0.0
    blocked || hullBlocked w x y i j rr useR b12 b13 b23 mw mx my dw dx dy (k + 1) fuel

/-- Whether the directed edge `(i, j)` is on the hull. -/
@[inline] def hullEdge (w x y : FloatArray) (rr : Float) (useR : Bool) (n i j : Nat) : Bool :=
  let wi := w.get! i
  let xi := x.get! i
  let yi := y.get! i
  let wj := w.get! j
  let xj := x.get! j
  let yj := y.get! j
  !hullBlocked w x y i j rr useR (wi * xj - xi * wj) (wi * yj - yi * wj) (xi * yj - yi * xj)
    ((wi + wj) * f64! 0.5) ((xi + xj) * f64! 0.5) ((yi + yj) * f64! 0.5) (wi - wj) (xi - xj) (yi - yj) 0 n

/-- The accepted edges `(i, j)` for `j` from `j` on (tail-recursive). -/
def hullRow (w x y : FloatArray) (rr : Float) (useR : Bool) (n i : Nat) :
    Nat → Nat → Array (Vector Nat 2) → Array (Vector Nat 2)
  | _, 0, out => out
  | j, fuel + 1, out =>
    let out := if i != j && hullEdge w x y rr useR n i j then out.push #v[i + 1, j + 1] else out
    hullRow w x y rr useR n i (j + 1) fuel out

/-- The rows `i …` of the hull. -/
def hullRows (w x y : FloatArray) (rr : Float) (useR : Bool) (n : Nat) :
    Nat → Nat → Array (Vector Nat 2) → Array (Vector Nat 2)
  | _, 0, out => out
  | i, fuel + 1, out => hullRows w x y rr useR n (i + 1) fuel (hullRow w x y rr useR n i 0 n out)

/-- Julia `convhull(p)` / `convhull(p, r)` (`FlowGeometry.jl:219-280`): the O(n³) hull. The directed
edge `(i, j)` is kept iff no other point `k` (within distance `r` of the edge midpoint, when `r` is
given) lies strictly to its left (`det(pᵢ, pⱼ, pₖ) > 0`) or on the segment's line closer to the
midpoint than the segment is long. `isapprox(det, 0)` with Julia's default tolerances is
`det == 0`. The edges are ordered by `i`, then `j`. -/
def convhullEdges (pts : Array (Chain ℝ3 1 Float)) (r : Option Float := none) : Array (Vector Nat 2) :=
  let n := pts.size
  let w := floatsOfFn n fun i => pts[i]!.v.get! 0
  let x := floatsOfFn n fun i => pts[i]!.v.get! 1
  let y := floatsOfFn n fun i => pts[i]!.v.get! 2
  hullRows w x y (r.getD 0) r.isSome n 0 n #[]

/-- Julia `convhull(p::PointCloud)` / `convhull(p, r)` as a `SimplexTopology` of edges over the
cloud's points. -/
def convhull (p : PointCloud (Chain ℝ3 1 Float)) (r : Option Float := none) : SimplexTopology 2 :=
  let pts := (Array.range p.size).map p.get
  SimplexTopology.ofElements (convhullEdges pts r) (p := some p.size)

/-! ## Wing surface -/

/-- `x .+ s .* r` of a coordinate vector with Julia's lazy range broadcasts (`StepRangeLen` stays a
range in `TwicePrecision`, `base/broadcast.jl:1150-1181`). -/
def affineAxis (x s : Float) (a : Axis) : Axis :=
  match a with
  | .stepLen r => .stepLen ((r.bcastMul s).bcastAdd x)
  | _ => .explicit (floatsOfFn a.length fun k => x + s * a.get k)

/-- The grid of `wing(N)`: `interval(N) ⊕ (-1:step(interval(N)):1)`. -/
abbrev wingBase (a : Airfoil) : GridBundle 2 (AffinePoint 2) :=
  let int := a.interval 1 0
  GridBundle.ofSpace (.ofAxes #v[int, Axis.colon (-1) (int.step?.getD 0) 1])

/-- Append rows `k … np-1` of one wing column: `(o1[k], o2, s·Y[k])` (`Y` the imaginary parts of
an interleaved surface; `s = 0` with `zero` for the middle column), where `o1` is the range
`x .+ a .* int` of Julia's lazy broadcasts, evaluated in place (`rangeAt`). -/
def wingColumn (o1 : Axis) (o2 s : Float) (Y : FloatArray) (zero : Bool) (k : Nat) :
    Nat → FloatArray → FloatArray
  | 0, acc => acc
  | m + 1, acc =>
    let z := if zero then 0 else s * Y.get! (2 * k + 1)
    wingColumn o1 o2 s Y zero (k + 1) m (((acc.push (o1.get k)).push o2).push z)

/-- `wingColumn` for a `TwicePrecision` range `o1` (the usual case), its elements computed with a
running index offset `u` as in `rangeFill` (bit-identical to `Axis.get`). -/
def wingColumnRange (r : StepRangeLen) (u : Float) (o2 s : Float) (Y : FloatArray) (zero : Bool) (k : Nat) :
    Nat → FloatArray → FloatArray
  | 0, acc => acc
  | m + 1, acc =>
    let z := if zero then 0 else s * Y.get! (2 * k + 1)
    let x := TwicePrecision.add12 r.ref.hi (u * r.step.hi)
    let e := x.hi + (x.lo + (u * r.step.lo + r.ref.lo))
    wingColumnRange r (u + f64! 1.0) o2 s Y zero (k + 1) m (((acc.push e).push o2).push z)

/-- One wing column, with the fast loop for a range. -/
@[inline] def wingCol (o1 : Axis) (o2 s : Float) (Y : FloatArray) (zero : Bool) (np : Nat) (acc : FloatArray) :
    FloatArray :=
  match o1 with
  | .stepLen r => wingColumnRange r (Axis.intToFloat (1 - r.offset)) o2 s Y zero 0 np acc
  | _ => wingColumn o1 o2 s Y zero 0 np acc

/-- Julia `wing(N, λ = 0.7, σ = 0.5)` (`FlowGeometry.jl:195-217`): a swept (`σ`), tapered (`taper`,
Julia's `λ`) wing built from the airfoil's surfaces, an `np × (2np-1)` grid of points `(x, y, z)`:
the upper surface scaled along the span on one half, the lower one on the other. (Julia also
evaluates the unused `profile(N.c)`, which throws unless `N` has a camber line, FG-B10.) -/
def wing (a : Airfoil) (taper : Float := f64! 0.7) (σ : Float := f64! 0.5) :
    TensorField (wingBase a) (Chain ℝ3 1 Float) :=
  let int := a.interval 1 0
  let xs := axisValues int
  let (U, L) := a.surfaces 1 0
  let np := U.size / 2
  let rint (i : Nat) : Float := xs.get! (np - 1 - i)
  let column (c : Nat) (acc : FloatArray) : FloatArray :=
    if c + 1 < np then
      wingCol (affineAxis (σ * xs.get! c) (taper + (1 - taper) * rint c) int) (xs.get! c) (rint c) U false np acc
    else if c + 1 == np then
      wingCol (affineAxis (σ * xs.get! c) (taper * rint c) int) (xs.get! c) 0 U true np acc
    else
      let i := c - np + 1
      wingCol (affineAxis (σ * rint i) (taper + (1 - taper) * xs.get! i) int) (rint i) (xs.get! i) L false np acc
  let data := (List.range (2 * np - 1)).foldl (fun acc c => column c acc)
    (FloatArray.emptyWithCapacity (3 * np * (2 * np - 1)))
  fieldOf (wingBase a) data

/-! ## MATLAB geometry description -/

/-- The geometry description matrix `[R A]` that Julia's `decsg(N)` (`FlowGeometry.jl:282-289`)
passes to MATLAB's `decsg` with the set formula `"R-A"`: the rectangle
`[-1.5, 3.5] × [-1.5, 1.5]` (`R = [3, 4, x₁…x₄, y₁…y₄, 0…]`) minus the airfoil polygon
(`A = [2, pts, x…, y…]`), columns of length `2·pts + 2`. (Calling MATLAB is out of scope.) -/
def decsgGeometry (a : Airfoil) : FloatArray × FloatArray :=
  let z := a.outlineData
  let pts := a.samples
  let R := #[3, 4, f64! -1.5, f64! 3.5, f64! 3.5, f64! -1.5, f64! 1.5, f64! 1.5, f64! -1.5, f64! -1.5].foldl
    FloatArray.push (FloatArray.emptyWithCapacity (2 * pts + 2))
  let R := (List.range (2 * pts - 8)).foldl (fun acc _ => acc.push 0) R
  let A := (FloatArray.emptyWithCapacity (2 * pts + 2)).push 2 |>.push (natF pts)
  let A := (List.range pts).foldl (fun acc i => acc.push (z.get! (2 * i))) A
  let A := (List.range pts).foldl (fun acc i => acc.push (z.get! (2 * i + 1))) A
  (R, A)

end FlowGeometry
