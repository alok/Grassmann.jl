import Grassmann.Wedge.Types

/-!
# Classic 2D PGA Wedge Campaign (Levels 1–9 + 6 Tutorial Cards)

Faithful pure-Lean port of ALL 9 interactive puzzles and tutorials from Steven De Keninck's
(`enkimute`) `enkimute/ganja.js/examples/example_game_wedge.html` in `PGA2 = Cl(2,0,1)`:
1. Join (`A & B`)
2. Meet (`a ^ (A & B)`)
3. Add Points / Midpoint (`A + B`)
4. Add Lines / Angle Bisector (`c + b`)
5. Dot / Orthogonal Projection (`a << B`)
6. Multi-Target Combo (`a << B` AND `a + (a << B)`)
7. Orthocenter of a Triangle (`((A&B)<<C) ^ ((B&C)<<A)`)
8. Circumcenter of a Triangle (`((A&B)<<(A+B)) ^ ((B&C)<<(B+C))`)
9. Euler's Line (`ortho & circum`)
-/

namespace Grassmann.Wedge

private def p2 (x y : Float) : PgaElem := .pt2 x y
private def l2 (a b c : Float) : PgaElem := (PgaElem.mkLine2 a b c).getD (.line2 1.0 0.0 0.0)
private def join2 (a b : PgaElem) : PgaElem := (PgaElem.join a b).getD (.line2 1.0 0.0 0.0)
private def meet2 (a b : PgaElem) : PgaElem := (PgaElem.meet a b).getD (.pt2 0.0 0.0)
private def add2  (a b : PgaElem) : PgaElem := (PgaElem.addSameGrade a b).getD a
private def dot2  (a b : PgaElem) : PgaElem := (PgaElem.dotProject a b).getD a

/-- All 9 classic interactive Wedge 2D puzzles (preserving exact `example_game_wedge.html`
geometry, hints, and pedagogical progression). -/
def levels2D : Array WedgeLevel :=
  let A0 := p2 (-1.0) 0.0
  let B0 := p2 1.0 0.5
  let a0 := l2 0.0 1.0 0.0
  let b0 := l2 1.0 (-0.5) 0.0
  let c0 := l2 1.0 0.5 0.0
  let AB0 := join2 A0 B0

  -- Level 5 & 6 geometry
  let a5 := l2 1.0 0.0 0.0
  let B5 := p2 0.0 1.0
  let perp5 := dot2 a5 B5

  -- Level 7 & 8 triangle (exact coordinates from example_game_wedge.html:75-76)
  let A7 := p2 (-0.4) 1.5
  let B7 := p2 1.5 (-1.0)
  let C7 := p2 (-1.0) (-1.5)
  let eAB7 := join2 A7 B7
  let eBC7 := join2 B7 C7
  let altC7 := dot2 eAB7 C7
  let altA7 := dot2 eBC7 A7
  let ortho7 := meet2 altC7 altA7

  let midAB8 := add2 A7 B7
  let midBC8 := add2 B7 C7
  let bisAB8 := dot2 eAB7 midAB8
  let bisBC8 := dot2 eBC7 midBC8
  let circum8 := meet2 bisAB8 bisBC8

  -- Level 9 Euler's Line triangle (exact coordinates from example_game_wedge.html:78)
  let A9 := p2 1.2 1.3
  let B9 := p2 0.4 (-0.5)
  let C9 := p2 (-1.0) (-0.4)
  let eAB9 := join2 A9 B9
  let eBC9 := join2 B9 C9
  let ortho9 := meet2 (dot2 eAB9 C9) (dot2 eBC9 A9)
  let circum9 := meet2 (dot2 eAB9 (add2 A9 B9)) (dot2 eBC9 (add2 B9 C9))
  let euler9 := join2 ortho9 circum9

  #[
    { number := 1, dim := .dim2D
      title := "L1 · Join (A & B)"
      goal := "Drag points A and B apart to Join them into the red line."
      tutorialText := "Wedge — The math game free of charge and coordinates. White elements are interactive; Red elements are targets; Ghosted elements are hints. Pull two points APART to Join (&) them."
      hintText := "Select A & B and drag them away from each other → Join (A & B)."
      givens := #[(A0, "A"), (B0, "B")]
      targets := #[(AB0, "A&B")] },

    { number := 2, dim := .dim2D
      title := "L2 · Meet (a ^ b)"
      goal := "Drag the two white lines together to Meet them in the red point."
      tutorialText := "In 2D PGA, pushing two lines TOGETHER computes their exterior Meet (^), producing their intersection point."
      hintText := "Drag both lines toward each other → Meet (a ^ b)."
      givens := #[(a0, "a"), (AB0, "b")]
      targets := #[(meet2 a0 AB0, "a^b")] },

    { number := 3, dim := .dim2D
      title := "L3 · Add Points (Midpoint)"
      goal := "Drag points A and B together to Add them into their midpoint."
      tutorialText := "You cannot Meet two points in 2D — trying upgrades automatically to projective Addition (A + B), giving their exact midpoint!"
      hintText := "Drag A and B toward each other → Add (A + B)."
      givens := #[(A0, "A"), (B0, "B")]
      targets := #[(add2 A0 B0, "A+B")] },

    { number := 4, dim := .dim2D
      title := "L4 · Add Lines (Bisector)"
      goal := "Drag lines c and b apart to Add them into their angle bisector."
      tutorialText := "Similarly, you cannot Join two lines in 2D — pulling them apart upgrades to Addition (c + b), producing their angle bisector!"
      hintText := "Drag lines c and b away from each other → Add (c + b)."
      givens := #[(c0, "c"), (b0, "b")]
      targets := #[(add2 c0 b0, "c+b")] },

    { number := 5, dim := .dim2D
      title := "L5 · Dot / Orthogonal Projection"
      goal := "Hold point B still and drag line a toward it to Dot (a << B)."
      tutorialText := "Holding a point fixed while dragging a line toward it computes left contraction (a << B): the line through B orthogonal to a."
      hintText := "Hold B (zero drag) and drag line a toward B → Dot (a << B)."
      givens := #[(a5, "a"), (B5, "B")]
      targets := #[(perp5, "a<<B")] },

    { number := 6, dim := .dim2D
      title := "L6 · Perpendicular + 45° Bisector"
      goal := "Construct both red lines: the perpendicular (a << B) and its bisector with a."
      tutorialText := "Combine all five PGA2D operations: Join (&), Meet (^), Add points (+), Add lines (+), and Orthogonal Dot (<<)."
      hintText := "First Dot a << B, then drag a and (a << B) apart to Add them."
      givens := #[(a5, "a"), (B5, "B")]
      targets := #[(perp5, "a<<B"), (add2 a5 perp5, "a+(a<<B)")] },

    { number := 7, dim := .dim2D
      title := "L7 · Orthocenter"
      goal := "Find the orthocenter of triangle ABC (intersection of altitudes)."
      hintText := "Join A&B, Dot with C for altitude 1; Join B&C, Dot with A for altitude 2; Meet both altitudes!"
      givens := #[(A7, "A"), (B7, "B"), (C7, "C")]
      hints := #[(eAB7, "A&B"), (altC7, "(A&B)<<C")]
      targets := #[(ortho7, "Orthocenter")] },

    { number := 8, dim := .dim2D
      title := "L8 · Circumcenter"
      goal := "Find the circumcenter of triangle ABC (meet of perpendicular bisectors)."
      hintText := "Add A+B for midpoint, Dot (A&B)<<(A+B) for bisector 1; repeat on BC; Meet both bisectors!"
      givens := #[(A7, "A"), (B7, "B"), (C7, "C")]
      hints := #[(midAB8, "A+B"), (bisAB8, "(A&B)<<(A+B)")]
      targets := #[(circum8, "Circumcenter")] },

    { number := 9, dim := .dim2D
      title := "L9 · Euler's Line"
      goal := "Construct Euler's Line joining the orthocenter and circumcenter of ABC!"
      hintText := "Build the orthocenter (altitudes) and circumcenter (perp bisectors), then Join them apart!"
      givens := #[(A9, "A"), (B9, "B"), (C9, "C")]
      hints := #[(ortho9, "Ortho"), (circum9, "Circum")]
      targets := #[(euler9, "Euler Line")] }
  ]

end Grassmann.Wedge
