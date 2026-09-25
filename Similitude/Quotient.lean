import Similitude.Registry

/-!
# The quotient `U/~`

A unit system identifies the dimensions its homomorphism maps to the same
image: in `Metric`, `action` and `angularmomentum` coincide, as do `inertia` and
`mass`. `quotient U` (Julia `U/~`, `Similitude.jl:246-280`) lists these
equivalence classes of the 131 convertible quantities, each keyed by the image,
in Julia's order.
-/

namespace Similitude

open FieldAlgebra UnitSystems

/-- Julia `quotient(U)`: the classes of convertible quantities with equal image
under `U`, keyed by that image, in order of first appearance. -/
def quotient (U : Sys) : List (USQGroup × List Conv) :=
  let imgs : List (Conv × Exps 11) := Conv.all.map fun q => (q, U.image q.dim.toGroup.v)
  let classes := imgs.foldl (fun (acc : Array (USQGroup × List Conv)) (q, i) =>
    if acc.any (·.2.contains q) then acc
    else acc.push (Group.mk' i (.int 1), (imgs.filter fun (_, j) => j.beq i).map (·.1))) #[]
  classes.toList

/-- Julia `printquotient(U)`: one line per class, `    key => q (dim), …`. -/
def printQuotient (U : Sys) : String :=
  String.join <| (quotient U).map fun (k, qs) =>
    s!"    {k.print} => " ++ ", ".intercalate (qs.map fun q => s!"{q.name} ({q.dim.toGroup.print})") ++ "\n"

end Similitude
