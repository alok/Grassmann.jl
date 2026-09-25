import FieldAlgebra.Superscript
import FieldAlgebra.Group
import FieldAlgebra.LogExp

/-!
# FieldAlgebra

Lean port of `chakravala/FieldAlgebra.jl` (v0.1.10): free abelian groups over
named bases (`Group B`, with the basis as a type index), formal logarithms and
exponentials (`LogGroup`, `ExpGroup`), and FieldAlgebra's superscript/LaTeX
printing (`printexpo`, `makeint`, `showgroup`).

The experimental `Ring`, `Field`, `Composite` and `Polynomial` types are not
ported: nothing in Similitude or MeasureSystems uses them
(`docs/port-notes/similitude-fieldalgebra-measure.md` §1.1).
-/
