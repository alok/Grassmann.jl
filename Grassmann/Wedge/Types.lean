import Grassmann.Scene.Types

/-!
# Pure-Lean Wedge Game Core Types & PGA2/PGA3 Exact Algebra (`Grassmann.Wedge.Types`)

Port of Steven De Keninck's (`enkimute`) iconic `ganja.js` **Wedge** game
("The math game free of charge and coordinates", `examples/example_game_wedge.html`)
plus a full spatial **Wedge 3D** campaign in `PGA3 = Cl(3,0,1)` designed for
Web 3D and visionOS two-hand spatial manipulation.

All geometric algebra operations (`Join &`, `Meet ^`, `Add +`, `Dot <<`), projective
equivalence win checks, scoring, undo history, and `SceneIR` generation run 100% in Lean.
-/

namespace Grassmann.Wedge

open Grassmann.Scene

/-- Play mode: classic 2D PGA (`Cl(2,0,1)`) or spatial 3D PGA (`Cl(3,0,1)`). -/
inductive WedgeDim where
  | dim2D
  | dim3D
  deriving DecidableEq, Repr, Inhabited

/-- Role of a geometric element on the Wedge board. -/
inductive WedgeRole where
  | given       -- White, interactive starting element
  | constructed -- White, interactive player-created element
  | target      -- Red, non-interactive goal to reconstruct
  | hint        -- Ghosted scaffolding, non-interactive
  deriving DecidableEq, Repr, Inhabited

/-- Exact projective geometric element (unified for PGA2 & PGA3). -/
inductive PgaElem where
  /-- 2D PGA Point `(x, y)` (grade 2 in `Cl(2,0,1)`). -/
  | pt2 (x y : Float)
  /-- 2D PGA Line `a·x + b·y + c = 0` normalized (`a² + b² = 1`, grade 1 in `Cl(2,0,1)`). -/
  | line2 (a b c : Float)
  /-- 3D PGA Point `(x, y, z)` (grade 3 in `Cl(3,0,1)`). -/
  | pt3 (p : Vec3)
  /-- 3D PGA Plücker Line `(dir, mom)` with `‖dir‖ = 1, mom = origin × dir` (grade 2). -/
  | line3 (dir mom : Vec3)
  /-- 3D PGA Plane `n·p + d = 0` with `‖n‖ = 1` (grade 1 in `Cl(3,0,1)`). -/
  | plane3 (n : Vec3) (d : Float)
  deriving Repr, Inhabited

namespace PgaElem

/-- Construct normalized 2D line `a·x + b·y + c = 0`. -/
def mkLine2 (a b c : Float) : Option PgaElem :=
  let len := Float.sqrt (a * a + b * b)
  if len < 1e-9 then none
  else some (.line2 (a / len) (b / len) (c / len))

/-- Construct normalized 3D plane `n·p + d = 0`. -/
def mkPlane3 (n : Vec3) (d : Float) : Option PgaElem :=
  let len := Vec3.norm n
  if len < 1e-9 then none
  else some (.plane3 (Vec3.scale (1.0 / len) n) (d / len))

/-- Construct normalized 3D Plücker line `(dir, mom)` (enforces `dir · mom = 0`). -/
def mkLine3 (dir mom : Vec3) : Option PgaElem :=
  let len := Vec3.norm dir
  if len < 1e-9 then none
  else
    let u := Vec3.scale (1.0 / len) dir
    let m0 := Vec3.scale (1.0 / len) mom
    -- Project out any floating-point residual along u so Plücker identity holds
    let m := Vec3.sub m0 (Vec3.scale (Vec3.dot m0 u) u)
    some (.line3 u m)

/-- Closest point on a 3D Plücker line to the origin (`dir × mom`, since `‖dir‖ = 1`). -/
@[inline] def line3Origin (dir mom : Vec3) : Vec3 := Vec3.cross dir mom

/-- Grade of element in its native PGA algebra. -/
def grade : PgaElem → Nat
  | .pt2 _ _    => 2
  | .line2 ..   => 1
  | .pt3 _      => 3
  | .line3 ..   => 2
  | .plane3 ..  => 1

/-- Canonical 3D anchor position used for gesture direction classification & hit-testing. -/
def anchor : PgaElem → Vec3
  | .pt2 x y      => ⟨x, y, 0.0⟩
  | .line2 a b c  => ⟨-c * a, -c * b, 0.0⟩
  | .pt3 p        => p
  | .line3 d m    => line3Origin d m
  | .plane3 n d   => Vec3.scale (-d) n

/-- Human-readable algebraic formula string for the live Inspector. -/
def format : PgaElem → String
  | .pt2 x y     => s!"e12 + ({x})e02 + ({y})e01"
  | .line2 a b c => s!"({c})e0 + ({a})e1 + ({b})e2"
  | .pt3 p       => s!"e123 + ({p.x})e023 + ({p.y})e031 + ({p.z})e012"
  | .line3 d m   => s!"({m.x})e01 + ({m.y})e02 + ({m.z})e03 + ({d.z})e12 + ({-d.y})e13 + ({d.x})e23"
  | .plane3 n d  => s!"({d})e0 + ({n.x})e1 + ({n.y})e2 + ({n.z})e3"

/-! ### Exact PGA2 & PGA3 Operations (`Join`, `Meet`, `Add`, `Dot`) -/

/-- Regressive Join (`A & B`):
- 2D: `pt2 & pt2 → line2`
- 3D: `pt3 & pt3 → line3`, `pt3 & line3 → plane3`, `line3 & pt3 → plane3`. -/
def join : PgaElem → PgaElem → Option PgaElem
  | .pt2 x1 y1, .pt2 x2 y2 =>
    mkLine2 (y1 - y2) (x2 - x1) (x1 * y2 - y1 * x2)
  | .pt3 p1, .pt3 p2 =>
    mkLine3 (Vec3.sub p2 p1) (Vec3.cross p1 p2)
  | .pt3 p, .line3 dir mom | .line3 dir mom, .pt3 p =>
    let n := Vec3.sub mom (Vec3.cross p dir)
    mkPlane3 n (-(Vec3.dot n p))
  | _, _ => none

/-- Exterior Meet (`A ^ B`):
- 2D: `line2 ^ line2 → pt2`
- 3D: `plane3 ^ plane3 → line3`, `plane3 ^ line3 → pt3`, `line3 ^ plane3 → pt3`. -/
def meet : PgaElem → PgaElem → Option PgaElem
  | .line2 a1 b1 c1, .line2 a2 b2 c2 =>
    let w := a1 * b2 - b1 * a2
    if Float.abs w < 1e-8 then none
    else some (.pt2 ((b1 * c2 - c1 * b2) / w) ((c1 * a2 - a1 * c2) / w))
  | .plane3 n1 d1, .plane3 n2 d2 =>
    let dir := Vec3.cross n1 n2
    let mom := Vec3.sub (Vec3.scale d1 n2) (Vec3.scale d2 n1)
    mkLine3 dir mom
  | .plane3 n d, .line3 dir mom | .line3 dir mom, .plane3 n d =>
    let w := Vec3.dot n dir
    if Float.abs w < 1e-8 then none
    else
      let ph := Vec3.add (Vec3.scale (-d) dir) (Vec3.cross n mom)
      some (.pt3 (Vec3.scale (1.0 / w) ph))
  | _, _ => none

/-- Same-grade projective sum (`(A + B).Normalized`):
- Points → midpoint
- Lines / Planes → angle bisector (rejects mixed grades!). -/
def addSameGrade : PgaElem → PgaElem → Option PgaElem
  | .pt2 x1 y1, .pt2 x2 y2 => some (.pt2 (0.5 * (x1 + x2)) (0.5 * (y1 + y2)))
  | .line2 a1 b1 c1, .line2 a2 b2 c2 => mkLine2 (a1 + a2) (b1 + b2) (c1 + c2)
  | .pt3 p1, .pt3 p2 => some (.pt3 (Vec3.scale 0.5 (Vec3.add p1 p2)))
  | .plane3 n1 d1, .plane3 n2 d2 => mkPlane3 (Vec3.add n1 n2) (d1 + d2)
  | .line3 d1 m1, .line3 d2 m2 => mkLine3 (Vec3.add d1 d2) (Vec3.add m1 m2)
  | _, _ => none

/-- Orthogonal Projection / Left Contraction (`moved << held`):
- 2D: `line2 << pt2` → line through `pt2` perpendicular to `line2`
- 3D:
  - `plane3 << pt3` → line through `pt3` perpendicular to `plane3`
  - `line3 << pt3`  → plane through `pt3` perpendicular to `line3`
  - `plane3 << line3` → plane containing `line3` perpendicular to `plane3`. -/
def dotProject : PgaElem → PgaElem → Option PgaElem
  | .line2 a b _, .pt2 x y =>
    mkLine2 (-b) a (b * x - a * y)
  | .pt2 x y, .line2 a b _ =>
    -- Symmetric ergonomics if player holds line and drags point to it
    mkLine2 (-b) a (b * x - a * y)
  | .plane3 n _, .pt3 p =>
    mkLine3 n (Vec3.cross p n)
  | .line3 dir _, .pt3 p =>
    mkPlane3 dir (-(Vec3.dot dir p))
  | .plane3 n _, .line3 dir mom =>
    let n' := Vec3.cross n dir
    let orig := line3Origin dir mom
    mkPlane3 n' (-(Vec3.dot n' orig))
  | _, _ => none

/-- Projective equivalence check matching `example_game_wedge.html` (`tol = 0.015`):
lines/planes match up to sign `±1`, points match by Euclidean coincidence! -/
def approxEq (a b : PgaElem) (tol : Float := 0.015) : Bool :=
  match a, b with
  | .pt2 x1 y1, .pt2 x2 y2 =>
    let dx := x1 - x2; let dy := y1 - y2
    Float.sqrt (dx * dx + dy * dy) < tol
  | .line2 a1 b1 c1, .line2 a2 b2 c2 =>
    let dPos := Float.sqrt ((a1 - a2) * (a1 - a2) + (b1 - b2) * (b1 - b2) + (c1 - c2) * (c1 - c2))
    let dNeg := Float.sqrt ((a1 + a2) * (a1 + a2) + (b1 + b2) * (b1 + b2) + (c1 + c2) * (c1 + c2))
    min dPos dNeg < tol
  | .pt3 p1, .pt3 p2 =>
    Vec3.norm (Vec3.sub p1 p2) < tol
  | .plane3 n1 d1, .plane3 n2 d2 =>
    let dPos := Float.sqrt (Vec3.normSq (Vec3.sub n1 n2) + (d1 - d2) * (d1 - d2))
    let dNeg := Float.sqrt (Vec3.normSq (Vec3.add n1 n2) + (d1 + d2) * (d1 + d2))
    min dPos dNeg < tol
  | .line3 d1 m1, .line3 d2 m2 =>
    let dPos := Float.sqrt (Vec3.normSq (Vec3.sub d1 d2) + Vec3.normSq (Vec3.sub m1 m2))
    let dNeg := Float.sqrt (Vec3.normSq (Vec3.add d1 d2) + Vec3.normSq (Vec3.add m1 m2))
    min dPos dNeg < tol
  | _, _ => false

end PgaElem

/-- A numbered board item on a Wedge puzzle level. -/
structure BoardItem where
  id    : UInt32
  role  : WedgeRole
  elem  : PgaElem
  label : String := ""
  deriving Repr, Inhabited

/-- A single Wedge puzzle level (either a tutorial card or an interactive construction). -/
structure WedgeLevel where
  number       : UInt32
  dim          : WedgeDim
  title        : String
  goal         : String
  tutorialText : String := ""
  hintText     : String := ""
  givens       : Array (PgaElem × String) := #[]
  hints        : Array (PgaElem × String) := #[]
  targets      : Array (PgaElem × String) := #[]
  deriving Repr, Inhabited

/-- Complete mutable gameplay state owned purely in Lean. -/
structure WedgeState where
  dim           : WedgeDim := .dim2D
  levelIdx      : Nat      := 0
  items         : Array BoardItem := #[]
  nextId        : UInt32   := 1
  moves         : UInt32   := 0
  elapsedSec    : Float    := 0.0
  timerStarted  : Bool     := false
  lastOp        : String   := ""
  previewOp     : String   := ""
  previewElem   : Option PgaElem := none
  selectedIds   : Array UInt32 := #[]
  showHints     : Bool     := true
  solved        : Bool     := false
  undoStack     : Array (Array BoardItem × UInt32) := #[]
  deriving Repr, Inhabited

end Grassmann.Wedge
