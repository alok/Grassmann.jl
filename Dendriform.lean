import Dendriform.Tree
import Dendriform.Order
import Dendriform.TotalGrove
import Dendriform.Arith
import Dendriform.Axioms
import Dendriform.Grove
import Dendriform.Poset
import Dendriform.Display
import Dendriform.Compose

/-! Dendriform: Lean port of chakravala/Dendriform.jl (see docs/port-notes/small-algebra.md
§2.4, §4.4, §8.5): Loday's arithmetic of planar binary trees.

* `Dendriform.Tree` / `PBTree n`: planar binary trees (degree-indexed), Loday names,
  graft `∨`, `σ`, over `/`, under `\`.
* `Dendriform.Grove n`: degree-indexed groves with `⊣ ⊢ : Grove a → Grove b → Grove (a+b)`,
  `+`, `*` (`Grove (a*b)`), `∪`; `Dendriform.Julia` for Julia's degenerate conventions.
* `Dendriform.Axioms`: the dendriform axioms and associativity, proven for all trees.
* Tree integers, total groves, grove indices, `GroveBin` and Julia-exact display
  (with `JuliaBase.Float16` for `GroveBin.ppos`), the Tamari poset and grove compositions. -/
