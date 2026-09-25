import FieldAlgebra.Superscript
import FieldAlgebra.Group
import FieldAlgebra.LogExp
import FieldAlgebra.Ring
import FieldAlgebra.Values
import FieldAlgebra.Command

/-!
# FieldAlgebra

Lean port of `chakravala/FieldAlgebra.jl` (v0.1.10): free abelian groups over
named bases (`Group B`, with the basis as a type index), formal logarithms and
exponentials (`LogGroup`, `ExpGroup`), sums of monomials (`Ring B`, Julia's
`Ring` with its insertion-ordered merge rules), bases with numeric generator
values (`GroupValues`: `product`, `factorize`, the ` = value` display), the
declaration commands `group!`/`group2!`/`constgroup!`/`ring!` (Julia `@group`,
`@group2`, `@constgroup`, `@ring`), and FieldAlgebra's superscript/LaTeX printing
(`printexpo`, `makeint`, `showgroup`).

The experimental, undocumented `Field`, `Composite` and `Polynomial` types
(`field.jl`, `polynomial.jl`) are not ported
(`docs/port-notes/similitude-fieldalgebra-measure.md` §1.1).
-/
