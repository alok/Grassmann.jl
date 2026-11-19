import Grassmann.Scene.Types
import Grassmann.Scene.Json

/-!
# Pure-Lean Guided Geometric Algebra Tour (`Grassmann.CoffeeShop.Tour`)

Strictly `Init`-only (33rd runtime module: ZERO `Lean.*`, ZERO `Std.*`, ZERO `Lake.*`,
ZERO `DirectSum`, ZERO `sorry`/axioms) — single source of truth for the interactive 6-stop
Guided Tour across BOTH Web 3D Studio (WASM / `ga-server`) and native macOS / visionOS!

Each stop carries:
- `index` (`0..5`) and stable `id`
- Human-friendly `title` & plain-English `summary`
- Target `presetId` (`"wedge_2d"` on Stop 5 switches cleanly into Wedge 2D Level 1)
- Canonical `algebra` & KaTeX LaTeX `formula`
- Actionable `"tryIt"` prompt encouraging immediate hands-on 3D/2D manipulation!

Credits: Michael Reed (`chakravala` / `Grassmann.jl`) & Steven De Keninck (`enkimute` / `ganja.js`).
-/

namespace Grassmann.CoffeeShop.Tour

open Grassmann.Scene Grassmann.Scene.Json

/-- A single curated interactive Guided Tour stop. -/
structure TourStop where
  index    : Nat
  id       : String
  title    : String
  presetId : String
  mode     : String -- "coffeeShop" | "wedge"
  algebra  : String
  formula  : String
  summary  : String
  tryIt    : String
  deriving Repr, Inhabited

/-- Canonical 6-stop interactive Guided GA Tour (`0..5`) — single source of truth in Lean
for both Web Studio and Apple Vision Pro / macOS! -/
def tourStops : Array TourStop := #[
  { index    := 0
    id       := "tour_points_lines"
    title    := "1. Points & Lines (A ∨ B)"
    presetId := "pga2d_points_and_lines"
    mode     := "coffeeShop"
    algebra  := "PGA2"
    formula  := "L = A \\vee B,\\qquad P = L_1 \\wedge L_2 \\in \\mathrm{Cl}_{2,0,1}"
    summary  := "In Projective Geometric Algebra, points and lines are unified multivectors: join spans lines and meet intersects them without a single special case."
    tryIt    := "Drag points A, B, or C to watch the join line A ∨ B and intersection meet L₁ ∧ L₂ update live in Lean." },

  { index    := 1
    id       := "tour_bunny_slicing"
    title    := "2. 3D Bunny Plane Slicing"
    presetId := "pga3d_slicing"
    mode     := "coffeeShop"
    algebra  := "PGA3"
    formula  := "P_{\\text{cut}} = \\Pi \\wedge (A \\vee B),\\qquad \\Pi = d\\,e_0 + \\mathbf{n} \\in \\mathrm{Cl}_{3,0,1}"
    summary  := "A single PGA3 plane blade slices a 3D mesh into upper and lower halves while stitching the exact 2D cross-section contour live."
    tryIt    := "Drag the cyan Plane Center handle to slice up and down, then drag the amber Tilt Normal handle to tilt the cutting plane freely in 3D!" },

  { index    := 2
    id       := "tour_motors_physics"
    title    := "3. Rigid-Body Motors & Physics"
    presetId := "pga3d_bouncing_cube"
    mode     := "coffeeShop"
    algebra  := "PGA3"
    formula  := "\\dot{M} = -\\tfrac{1}{2}\\,M\\,B,\\qquad X' = M X \\widetilde{M}"
    summary  := "One 8-component PGA3 motor encodes both 3D rotation and translation, integrating full rigid-body RK4 dynamics and 8-corner impulses without gimbal lock."
    tryIt    := "Scrub the Gravity, Restitution, and Spin sliders below to watch the angular-momentum bivector and bounce trajectory respond in real time." },

  { index    := 3
    id       := "tour_conformal_barth"
    title    := "4. Conformal Spheres & Barth Sextic GPU Raymarch"
    presetId := "implicit_barth_sextic"
    mode     := "coffeeShop"
    algebra  := "R3 / CGA3"
    formula  := "4(\\varphi^2 x^2 - y^2)(\\varphi^2 y^2 - z^2)(\\varphi^2 z^2 - x^2) - (1+2\\varphi)(x^2+y^2+z^2-1)^2 = c"
    summary  := "Lean compiles algebraic surfaces and CGA3 null spaces straight into GLSL3, WGSL, and Metal MSL sphere-tracers alongside fast bytecode meshes."
    tryIt    := "Orbit around the 65 icosahedral double points and slide Golden Ratio φ or Iso-Level c to morph the algebraic singularity structure live!" },

  { index    := 4
    id       := "tour_terrell_penrose"
    title    := "5. Relativistic Terrell-Penrose Cl(3,1)"
    presetId := "sta_terrell_penrose"
    mode     := "coffeeShop"
    algebra  := "STA"
    formula  := "X' = B X \\widetilde{B},\\qquad B = \\exp\\!\\left(\\tfrac{\\eta}{2}\\,\\gamma_0\\gamma_1\\right),\\qquad \\theta_{\\text{TP}} = \\arcsin(\\beta)"
    summary  := "Spacetime Algebra Cl(3,1) models Lorentz boosts as hyperbolic rotors and solves exact past light-cone arrival times to show why fast cubes look rotated, not squished."
    tryIt    := "Slide Speed β = v/c from 0 up to 0.95c to compare the apparent optical rotation against the dashed Lorentz-contracted ghost cube." },

  { index    := 5
    id       := "tour_play_wedge"
    title    := "6. Play Wedge 2D/3D!"
    presetId := "wedge_2d"
    mode     := "wedge"
    algebra  := "PGA2 / PGA3"
    formula  := "A \\vee B \\;\\text{(pull)},\\quad a \\wedge b \\;\\text{(push)},\\quad A + B \\;\\text{(mid)},\\quad a \\rfloor B \\;\\text{(hold+drag)}"
    summary  := "Master coordinate-free geometry across 17 interactive 2D and 3D puzzles, 6 animated tutorials, and infinite procedural challenges — all evaluated in Lean."
    tryIt    := "Pull white points A and B apart to Join them into the red target line, then click Next or toggle 3D for spatial PGA3 puzzles!" }
]

/-- Look up a Guided Tour stop by 0-based index (clamped cleanly to `0..5`). -/
def getTourStop (index : Nat) : TourStop :=
  tourStops.getD (min index (tourStops.size - 1)) tourStops[0]!

/-- Serialize all 6 curated Guided Tour stops to strictly `Init`-only JSON for Web Studio & Apple clients. -/
def tourCatalogJson : String :=
  arrJson (tourStops.map fun s => objJson #[
    ("index", toString s.index),
    ("id", quote s.id),
    ("title", quote s.title),
    ("presetId", quote s.presetId),
    ("mode", quote s.mode),
    ("algebra", quote s.algebra),
    ("formula", quote s.formula),
    ("summary", quote s.summary),
    ("tryIt", quote s.tryIt)
  ])

end Grassmann.CoffeeShop.Tour
