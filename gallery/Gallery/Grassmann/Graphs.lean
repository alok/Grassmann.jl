import Gallery.Common
import Grassmann

/-!
# The graph figures of the Grassmann paper (`paper/paper.tex:320-329, 566-586`)

Grassmann.jl draws a multivector as a directed graph on its generators
(`ext/LightGraphsExt.jl:19-48`): every bivector term `c·vᵢⱼ` is the edge `i → j` (`j → i`
when `c < 0`), and a term of higher grade contributes the edges of its boundary `∂`,
recursively. `graph-1 … graph-3` are `v12+v34`, `v14+v24+v34`, `∂(v124)+v34` in `ℝ⁴`, and
`triangle-tetrahedron` is `v123 + !v123` in `ℝ⁷` (`Grassmann.graph`, removed upstream,
`src/Grassmann.jl:430-445`). The drawing follows GraphPlot's `circular_layout` (vertex `k` at
angle `2π(k-1)/n`, y down) with grey disks, labels and arrowed edges; nodes and arrowheads are
data-space polygons so both renderers draw the same geometry.
-/

namespace Gallery.Graphs

open Grassmann DirectSum LeanPlot

/-! ## Multivector → digraph -/

/-- Lexicographic order of the index lists of two blades of the same grade (Julia's storage
order within a grade). -/
def lexLt (a b : UInt64) : Bool := Bits.indicesList a < Bits.indicesList b

/-- Julia's `∂` of a term `c·e_B` (`B = i₁ < … < i_g`): `Σₘ (-1)^m c·e_{B∖iₘ}` (so
`∂v124 = v24 - v14 + v12`), in storage order. -/
def boundary (bits : UInt64) (c : Float) : Array (UInt64 × Float) :=
  let is := Bits.indicesList bits
  let terms := is.zipIdx.map fun (i, m) =>
    (bits &&& ~~~((1 : UInt64) <<< (i - 1).toUInt64), if m % 2 == 0 then c else -c)
  terms.toArray.qsort fun a b => lexLt a.1 b.1

/-- Add an edge unless present (`add_edge!` on a `SimpleDiGraph`). -/
def addEdge (E : Array (Nat × Nat)) (e : Nat × Nat) : Array (Nat × Nat) :=
  if E.contains e then E else E.push e

/-- `edges(x::TensorTerm)` (`ext/LightGraphsExt.jl:19-30`): a bivector is one edge (reversed
for a negative coefficient), a higher term the edges of its boundary. The fuel is the grade. -/
def termEdges : Nat → Array (Nat × Nat) → UInt64 × Float → Array (Nat × Nat)
  | 0, E, _ => E
  | fuel + 1, E, (b, c) =>
    match Bits.indicesList b with
    | [i, j] => addEdge E (if c < 0 then (j, i) else (i, j))
    | _ => (boundary b c).foldl (fun E t => if t.2 == 0 || Bits.popcount t.1 == 1 then E else termEdges fuel E t) E

/-- `SimpleDiGraph(x)` for a multivector given by its terms in storage order
(`ext/LightGraphsExt.jl:31-48`): terms of grade ≥ 2 with nonzero coefficients. -/
def digraph (terms : Array (UInt64 × Float)) : Array (Nat × Nat) :=
  terms.foldl (fun E (b, c) => if c == 0 || Bits.popcount b < 2 then E else termEdges (Bits.popcount b) E (b, c)) #[]

/-! ## The four inputs -/

section Inputs
-- `ℝ⁴` and `ℝ⁷` (Julia `@basis ℝ^4`, `Λ(ℝ^7)`)
namespace E4
basis! S!"++++"
end E4
namespace E7
basis! S!"+++++++"
end E7

/-- `v12+v34`. -/
def graph1 : Array (UInt64 × Float) := (Chain.ofBlade E4.v12 1 + Chain.ofBlade E4.v34 (1 : Float)).terms

/-- `v14+v24+v34`. -/
def graph2 : Array (UInt64 × Float) :=
  (Chain.ofBlade E4.v14 1 + Chain.ofBlade E4.v24 1 + Chain.ofBlade E4.v34 (1 : Float)).terms

/-- `∂(v124)+v34`: the boundary summed into a grade-2 chain with `v34`. -/
def graph3 : Array (UInt64 × Float) :=
  let d : Chain E4.V 2 Float := (boundary E4.v124.bits 1).foldl
    (fun acc (b, c) => acc + Chain.ofBlade (⟨b⟩ : Submanifold E4.V 2) c) Chain.zero
  (d + Chain.ofBlade E4.v34 1).terms

/-- `v123 + !v123` in `ℝ⁷` (the right complement of the triangle is the tetrahedron `v4567`). -/
def triangleTetrahedron : Array (UInt64 × Float) :=
  let t : Chain E7.V 3 Float := Chain.ofBlade E7.v123 1
  let c : Chain E7.V (7 - 3) Float := !t
  (toMultivector t + toMultivector c).terms

end Inputs

/-! ## Drawing -/

/-- GraphPlot's `circular_layout` drawn y-down: vertex `k` at `(cos θ, -sin θ)`,
`θ = 2π(k-1)/n`. -/
def layout (n : Nat) (k : Nat) : Float × Float :=
  let θ := 2 * 3.141592653589793 * (k - 1).toUInt64.toFloat / n.toUInt64.toFloat
  (Float.cos θ, -Float.sin θ)

/-- Node radius, arrowhead length and half width (data units). -/
def nodeR : Float := 0.12
/-- Arrowhead length. -/
def headL : Float := 0.11
/-- Arrowhead half width. -/
def headW : Float := 0.045

/-- A disk as a 48-gon. -/
def disk (x y r : Float) : Pts2 :=
  let n := 48
  Pts2.ofArrays ⟨(Array.range n).map fun i => x + r * Float.cos (2 * 3.141592653589793 * i.toUInt64.toFloat / n.toUInt64.toFloat)⟩
    ⟨(Array.range n).map fun i => y + r * Float.sin (2 * 3.141592653589793 * i.toUInt64.toFloat / n.toUInt64.toFloat)⟩

/-- The figure of a digraph on `n` vertices. -/
def graphFigure (n : Nat) (E : Array (Nat × Nat)) : Figure := Id.run do
  let light : ColorSpec := .solid ((RGBA.parse? "#D3D3D3").getD RGBA.black)
  let gray : ColorSpec := .solid ((RGBA.parse? "gray").getD RGBA.black)
  let dark : ColorSpec := .solid ((RGBA.parse? "#A9A9A9").getD RGBA.black)
  let mut ax := Axis2.new (aspect := .data) |>.hidedecorations |>.hidespines |>.limits (-1.3) 1.3 (-1.3) 1.3
  for (a, b) in E do
    let (px, py) := layout n a
    let (qx, qy) := layout n b
    let dx := qx - px
    let dy := qy - py
    let len := Float.sqrt (dx * dx + dy * dy)
    let ux := dx / len
    let uy := dy / len
    ax := ax.lines ⟨#[px + nodeR * ux, qx - (nodeR + headL) * ux]⟩ ⟨#[py + nodeR * uy, qy - (nodeR + headL) * uy]⟩
      (color := some light) (linewidth := 3)
    let tx := qx - nodeR * ux
    let ty := qy - nodeR * uy
    let bx := tx - headL * ux
    let by_ := ty - headL * uy
    ax := ax.poly (Pts2.ofArrays ⟨#[tx, bx - headW * uy, bx + headW * uy]⟩ ⟨#[ty, by_ + headW * ux, by_ - headW * ux]⟩)
      (color := some gray)
  for k in [1:n + 1] do
    let (x, y) := layout n k
    ax := ax.poly (disk x y nodeR) (color := some dark)
    ax := ax.text x y (toString k) (fontsize := 18) (halign := .center) (valign := .middle)
  return Figure.new (500, 500) |>.axis 1 1 ax

/-- The edge list as `a→b` pairs. -/
def showEdges (E : Array (Nat × Nat)) : String := ", ".intercalate (E.toList.map fun (a, b) => s!"{a}→{b}")

/-- The graph entries. -/
def entries : List Entry :=
  let mk (name title expr source : String) (n : Nat) (terms : Array (UInt64 × Float)) : Entry :=
    { name, title, group := "Grassmann paper graphs", source := s!"`{expr}` (Grassmann.jl {source})"
      build := fun j? => do
        let E := digraph terms
        let checks := match j? with
          | some j =>
            let je := (jarr (jget j "edges")).map fun e => (jnat ((jarr e)[0]?.getD .null), jnat ((jarr e)[1]?.getD .null))
            #[{ label := "edges (in insertion order)", ok := E == je
                detail := if E == je then s!"equal: {showEdges E}" else s!"Lean {showEdges E} ≠ Julia {showEdges je}" },
              eqCheck "vertices" n (jnat (jget j "nv"))]
          | none => #[]
        return { fig := graphFigure n E, checks } }
  [mk "grassmann-graph-1" "Digraph of v12 + v34" "SimpleDiGraph(v12+v34)" "`paper/paper.tex:566-586`, `ext/LightGraphsExt.jl`" 4 graph1,
   mk "grassmann-graph-2" "Digraph of v14 + v24 + v34" "SimpleDiGraph(v14+v24+v34)" "`paper/paper.tex:566-586`" 4 graph2,
   mk "grassmann-graph-3" "Digraph of ∂(v124) + v34" "SimpleDiGraph(∂(v124)+v34)" "`paper/paper.tex:566-586`" 4 graph3,
   mk "grassmann-triangle-tetrahedron" "Digraph of v123 + !v123 in ℝ⁷ (triangle and tetrahedron)"
     "x = Λ(ℝ^7).v123; Grassmann.graph(x+!x)" "`paper/paper.tex:320-329`, `src/Grassmann.jl:430-445`" 7 triangleTetrahedron]

end Gallery.Graphs
