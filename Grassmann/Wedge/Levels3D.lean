import Grassmann.Wedge.Types
import Grassmann.Wedge.Levels2D

/-!
# Spatial 3D PGA Wedge Campaign (Levels 10–16 in `PGA3 = Cl(3,0,1)`)

Extends Enkimute's coordinate-free Wedge gesture grammar cleanly into 3D space
for Web 3D and visionOS two-hand spatial manipulation:
- **Pull apart (`&` Join)**: `Point & Point → Line`; `Point & Line → Plane`
- **Push together (`^` Meet)**: `Plane ^ Plane → Line`; `Plane ^ Line → Point`
- **Same-grade Add (`+`)**: `Point + Point → Midpoint`; `Plane + Plane → Bisector Plane`
- **Hold + Drag toward (`<<` Dot)**: `Plane << Point → Altitude Line`;
  `Line << Point → Orthogonal Plane`; `Plane << Line → Orthogonal Plane containing Line`.

Levels 10–17:
10. 3D Join — Points → Line → Plane
11. 3D Meet — Three Planes → Line → Vertex Point
12. 3D Bisector Plane — `P₁ + P₂`
13. Perpendicular Bisector Plane — `(A & B) << (A + B)`
14. Tetrahedron Altitude — `(A & B & C) << D`
15. Tetrahedron Circumcenter — Meet of 3 Perpendicular Bisector Planes
16. 3D Monge Point — Concurrence of Opposite-Edge Midpoint Orthogonal Planes
17. Grand Finale: 3D Tetrahedron Circumcenter + Centroid Euler Axis (`O & G`)
-/

namespace Grassmann.Wedge

open Grassmann.Scene

private def p3 (x y z : Float) : PgaElem := .pt3 ⟨x, y, z⟩
private def pl3 (nx ny nz d : Float) : PgaElem :=
  (PgaElem.mkPlane3 ⟨nx, ny, nz⟩ d).getD (.plane3 ⟨0.0, 1.0, 0.0⟩ 0.0)
private def join3 (a b : PgaElem) : PgaElem := (PgaElem.join a b).getD a
private def meet3 (a b : PgaElem) : PgaElem := (PgaElem.meet a b).getD a
private def add3  (a b : PgaElem) : PgaElem := (PgaElem.addSameGrade a b).getD a
private def dot3  (a b : PgaElem) : PgaElem := (PgaElem.dotProject a b).getD a

/-- Spatial 3D Wedge campaign (Levels 10–16 in `PGA3 = Cl(3,0,1)`). -/
def levels3D : Array WedgeLevel :=
  -- L10: 3 points → line → plane
  let A10 := p3 (-1.0) (-0.4) 0.5
  let B10 := p3 1.0 (-0.4) 0.5
  let C10 := p3 0.0 1.1 (-0.6)
  let lAB10 := join3 A10 B10
  let plABC10 := join3 lAB10 C10

  -- L11: 3 non-parallel planes meeting in a point
  let P11a := pl3 1.0 0.0 0.2 (-0.4)
  let P11b := pl3 0.0 1.0 (-0.2) (-0.3)
  let P11c := pl3 0.2 (-0.1) 1.0 (-0.5)
  let lAB11 := meet3 P11a P11b
  let pt11 := meet3 lAB11 P11c

  -- L12: Angle bisector plane
  let P12a := pl3 1.0 0.5 0.0 0.0
  let P12b := pl3 1.0 (-0.5) 0.0 0.0
  let bis12 := add3 P12a P12b

  -- L13: Perpendicular bisector plane of A & B
  let A13 := p3 (-1.1) (-0.3) 0.4
  let B13 := p3 1.1 0.5 (-0.4)
  let lAB13 := join3 A13 B13
  let mid13 := add3 A13 B13
  let pb13 := dot3 lAB13 mid13

  -- L14: Tetrahedron altitude from apex D onto base plane ABC
  let A14 := p3 (-1.1) (-0.6) 0.7
  let B14 := p3 1.2 (-0.6) 0.6
  let C14 := p3 0.0 (-0.6) (-1.1)
  let D14 := p3 0.2 1.3 0.1
  let base14 := join3 (join3 A14 B14) C14
  let alt14 := dot3 base14 D14

  -- L15: Tetrahedron circumcenter (meet of 3 perpendicular bisector planes)
  let A15 := p3 1.0 0.8 0.6
  let B15 := p3 (-1.0) 0.6 0.8
  let C15 := p3 0.4 (-1.0) 0.6
  let D15 := p3 (-0.2) (-0.2) (-1.2)
  let pbAB15 := dot3 (join3 A15 B15) (add3 A15 B15)
  let pbAC15 := dot3 (join3 A15 C15) (add3 A15 C15)
  let pbAD15 := dot3 (join3 A15 D15) (add3 A15 D15)
  let axis15 := meet3 pbAB15 pbAC15
  let circ15 := meet3 axis15 pbAD15

  -- L16: 3D Monge Point (meet of 3 linearly independent Monge planes through opposite edge midpoints:
  -- edge CD ⊥ through mid(AB), edge BD ⊥ through mid(AC), edge AB ⊥ through mid(CD)!)
  let A16 := p3 1.1 0.9 0.5
  let B16 := p3 (-1.0) 0.7 0.7
  let C16 := p3 0.3 (-1.0) 0.6
  let D16 := p3 (-0.2) (-0.1) (-1.1)
  let eCD16 := join3 C16 D16
  let eBD16 := join3 B16 D16
  let eAB16 := join3 A16 B16
  let mAB16 := add3 A16 B16
  let mAC16 := add3 A16 C16
  let mCD16 := add3 C16 D16
  let mp1 := dot3 eCD16 mAB16
  let mp2 := dot3 eBD16 mAC16
  let mp3 := dot3 eAB16 mCD16
  let mongeLine16 := meet3 mp1 mp2
  let mongePt16 := meet3 mongeLine16 mp3

  -- L17 Grand Finale: 3D Tetrahedron Circumcenter O + Centroid G → 3D Euler Axis (O & G)
  -- Asymmetric well-conditioned tetrahedron so ‖O - G‖ > 0.35 and G = (O + M)/2!
  let A17 := p3 1.3 1.0 0.5
  let B17 := p3 (-1.0) 0.3 0.9
  let C17 := p3 0.2 (-1.0) 0.4
  let D17 := p3 (-0.5) (-0.2) (-1.1)
  let mAB17 := add3 A17 B17
  let mAC17 := add3 A17 C17
  let mAD17 := add3 A17 D17
  let mCD17 := add3 C17 D17
  let cent17 := add3 mAB17 mCD17
  let pbAB17 := dot3 (join3 A17 B17) mAB17
  let pbAC17 := dot3 (join3 A17 C17) mAC17
  let pbAD17 := dot3 (join3 A17 D17) mAD17
  let circ17 := meet3 (meet3 pbAB17 pbAC17) pbAD17
  let eulerAxis17 := join3 circ17 cent17

  #[
    { number := 10, dim := .dim3D
      title := "L10 · 3D Join (Line & Plane)"
      goal := "Pull A & B apart for their 3D line, then pull that line & C apart for the red plane."
      tutorialText := "Welcome to Wedge 3D (PGA3)! Pull apart = Join (&): 2 points → line, line + point → plane. Perfect for two-hand pinch-pull in visionOS!"
      hintText := "Join A & B → Line; then Join (A&B) & C → Plane!"
      givens := #[(A10, "A"), (B10, "B"), (C10, "C")]
      hints := #[(lAB10, "A&B")]
      targets := #[(plABC10, "A&B&C")] },

    { number := 11, dim := .dim3D
      title := "L11 · 3D Meet (Three Planes)"
      goal := "Push pairs of planes together to intersect them into the red corner point."
      tutorialText := "In 3D PGA, pushing two planes TOGETHER computes their intersection line (^); pushing that line and a third plane together yields their intersection point!"
      hintText := "Meet P1 ^ P2 → Line; then Meet Line ^ P3 → Point!"
      givens := #[(P11a, "P1"), (P11b, "P2"), (P11c, "P3")]
      hints := #[(lAB11, "P1^P2")]
      targets := #[(pt11, "P1^P2^P3")] },

    { number := 12, dim := .dim3D
      title := "L12 · 3D Bisector Plane"
      goal := "Pull two planes apart to Add them into the red bisecting plane."
      hintText := "Joining two planes is degenerate in 3D, so pulling P1 & P2 apart upgrades to Add (P1 + P2)!"
      givens := #[(P12a, "P1"), (P12b, "P2")]
      targets := #[(bis12, "P1+P2")] },

    { number := 13, dim := .dim3D
      title := "L13 · Perpendicular Bisector Plane"
      goal := "Construct the plane bisecting segment AB perpendicularly: (A&B) << (A+B)."
      hintText := "Join A&B for the line, Add A+B for the midpoint, then hold the midpoint and drag the line toward it (Dot)!"
      givens := #[(A13, "A"), (B13, "B")]
      hints := #[(lAB13, "A&B"), (mid13, "A+B")]
      targets := #[(pb13, "(A&B)<<(A+B)")] },

    { number := 14, dim := .dim3D
      title := "L14 · Tetrahedron Altitude"
      goal := "Drop the perpendicular altitude line from apex D onto the base plane ABC."
      hintText := "Join A&B, Join with C for base plane ABC, then hold apex D and drag the base plane toward D (Dot)!"
      givens := #[(A14, "A"), (B14, "B"), (C14, "C"), (D14, "D")]
      hints := #[(base14, "ABC")]
      targets := #[(alt14, "ABC<<D")] },

    { number := 15, dim := .dim3D
      title := "L15 · Tetrahedron Circumcenter"
      goal := "Find the center of the unique sphere through all four vertices A, B, C, D!"
      hintText := "Construct perpendicular bisector planes of AB, AC, AD, then Meet all three planes into the circumcenter!"
      givens := #[(A15, "A"), (B15, "B"), (C15, "C"), (D15, "D")]
      hints := #[(pbAB15, "PB(AB)"), (axis15, "PB(AB)^PB(AC)")]
      targets := #[(circ15, "Circumcenter")] },

    { number := 16, dim := .dim3D
      title := "L16 · 3D Monge Point"
      goal := "Construct the Monge point where planes through each edge midpoint ⊥ to the opposite edge concur!"
      hintText := "Dot opposite edges onto midpoints: (C&D)<<(A+B), (B&D)<<(A+C), and (A&B)<<(C+D); Meet all three planes!"
      givens := #[(A16, "A"), (B16, "B"), (C16, "C"), (D16, "D")]
      hints := #[(mAB16, "A+B"), (mp1, "(C&D)<<(A+B)"), (mongeLine16, "Monge Axis")]
      targets := #[(mongePt16, "Monge Point")] },

    { number := 17, dim := .dim3D
      title := "L17 · 3D Circumcenter + Centroid Euler Axis"
      goal := "Grand Finale: Construct the tetrahedron Circumcenter O, Centroid G = (A+B)+(C+D), and join them into the 3D Euler Axis (O & G)!"
      tutorialText := "Monge's 3D Euler Line Theorem: In every tetrahedron, the Circumcenter O, Centroid G, and Monge Point M lie on a single 3D Euler Axis with G = (O + M)/2!"
      hintText := "Build Centroid G = (A+B)+(C+D) in 3 moves, build Circumcenter O via 3 perpendicular bisector planes, then pull O & G apart for the 3D Euler Axis!"
      givens := #[(A17, "A"), (B17, "B"), (C17, "C"), (D17, "D")]
      hints := #[(mAB17, "A+B"), (mCD17, "C+D"), (pbAB17, "PB(AB)")]
      targets := #[(circ17, "O (Circumcenter)"), (cent17, "G (Centroid)"), (eulerAxis17, "3D Euler Axis O&G")] }
  ]

/-- Combined 17-level Wedge campaign (L1–L9 PGA2 + L10–L17 PGA3). -/
def allLevels : Array WedgeLevel := levels2D ++ levels3D

end Grassmann.Wedge
