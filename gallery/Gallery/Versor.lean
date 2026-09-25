import Grassmann

/-!
# Versors and sampled curves for the README figures

The composite functions and the up/down maps the Grassmann README figures need are in the
library (Grassmann.jl `src/composite.jl`, `src/Grassmann.jl:164-228, 312-314`):

* `Half.exp`, `Chain.expEven`: Julia's `exp` of an even element (the closed form
  `cos θ + t·sin θ/θ` when `t²` is a scalar, else `1 + expm1(t)` with Julia's series and its
  stopping rule, so the truncation error (≈1e-9 for the README versors) is Julia's);
* `Chain.up`/`Chain.down` (Julia `↑`/`↓`): the Riemann-sphere maps of a space with `∞` (or
  `∅`) alone and the conformal maps of `⟨∞∅…⟩`, with the null points chosen from the space;
* `Grassmann.Fields.points`/`pointsCoords`, `chainfield`, `vectorfield`.

This module keeps the gallery's two conveniences on top of them.
-/

namespace Gallery.Versor

open Grassmann DirectSum StaticVectors

variable {V : TensorBundle}

/-- A bivector as a spinor. -/
@[inline] def ofBivector (c : Chain V 2 Float) : Spinor V Float := (Half.ofChain c).cast rfl

/-- The coordinates `ω[i₁], ω[i₂], ω[i₃]` (0-based chain indices) of `f t` for every `t`
of `ts` (Julia `V(i₁+1, i₂+1, i₃+1).(points(f, ts))`), as three arrays:
`Grassmann.Fields.pointsCoords`. -/
@[inline] def points3 (f : Float → Chain V 1 Float) (i₁ i₂ i₃ : Nat) (ts : FloatArray) :
    FloatArray × FloatArray × FloatArray :=
  let cols := Grassmann.Fields.pointsCoords f #[i₁, i₂, i₃] ts
  (cols[0]!, cols[1]!, cols[2]!)

end Gallery.Versor
