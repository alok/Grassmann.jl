/-
Multilinear Lie brackets (Grassmann.jl `src/forms.jl:1545-1576`;
port-notes/grassmann-forms.md §2.12, §4.12).

`bracket(X, Y) = X(Y) - Y(X)` where `X(Y)` is function application; for operators
that is composition, so `𝓛[T, U] = T⋅U − U⋅T`. The 3-, 4- and 5-ary brackets are
Julia's explicit recursion formulas (Reed, "Multilinear Lie bracket recursion
formula", viXra 2412.0034), with their specific argument orders; more arguments use
Julia's generated alternating recursion
`Σᵢ (-1)^{i+1} Xᵢ(bracket(X₁ … X̂ᵢ … X_N))`.
-/
import Grassmann.Forms.Eval

namespace Grassmann

open DirectSum

/-- Julia `bracket(X…)` (`forms.jl:1561-1568`) for a type with an application
`app X Y` (Julia `X(Y)`) and `+`, `-`. -/
partial def bracket {X : Type} [Add X] [Sub X] [Inhabited X] (app : X → X → X) : List X → X
  | [] => default
  | [x] => x
  | [x, y] => app x y - app y x
  | [x, y, z] => app x (bracket app [y, z]) + app y (bracket app [z, x]) + app z (bracket app [x, y])
  | [w, x, y, z] =>
    app w (bracket app [x, y, z]) + app x (bracket app [w, z, y]) + app y (bracket app [w, x, z]) +
      app z (bracket app [w, y, x])
  | [v, w, x, y, z] =>
    app v (bracket app [w, x, y, z]) + app w (bracket app [v, x, z, y]) + app x (bracket app [v, w, y, z]) +
      app y (bracket app [v, w, z, x]) + app z (bracket app [v, w, x, y])
  | xs =>
    let terms := xs.zipIdx.map fun (xi, i) =>
      let rest := (xs.zipIdx.filter (·.2 != i)).map (·.1)
      (i, app xi (bracket app rest))
    match terms with
    | [] => default
    | (_, t) :: ts => ts.foldl (fun acc (i, s) => if i % 2 == 0 then acc + s else acc - s) t

/-- Julia `𝓛[X…]` / `LieBracket(X…)` of endomorphisms: brackets of composition. -/
def lieBracket {V : TensorBundle} {l : Layout} {α : Type} [AbstractTensors.Coeff α]
    (Xs : List (Endomorphism V l α)) : Endomorphism V l α :=
  bracket TensorOperator.comp Xs

/-- Julia `LieDerivative{X}` (`forms.jl:1548-1550`): a wrapped operator acting by
brackets, `𝓛(X)(Y…) = bracket(X, Y…)`. -/
structure LieDerivative (X : Type) where
  /-- The wrapped operator. -/
  v : X

namespace LieDerivative

variable {X : Type} [Add X] [Sub X] [Inhabited X]

/-- Julia `(X::LieDerivative)(Y…) = bracket(X.v, Y…)` (`forms.jl:1558`). -/
@[inline] def apply (app : X → X → X) (D : LieDerivative X) (Ys : List X) : X := bracket app (D.v :: Ys)

instance : Add (LieDerivative X) := ⟨fun a b => ⟨a.v + b.v⟩⟩
instance : Sub (LieDerivative X) := ⟨fun a b => ⟨a.v - b.v⟩⟩

end LieDerivative

/-- Julia `show(::LieBracket)` (`forms.jl:1554`). -/
def lieBracketString : String := "LieBracket[...]"

end Grassmann
