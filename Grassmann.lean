import Grassmann.Types.Dims
import Grassmann.Types.Single
import Grassmann.Types.Chain
import Grassmann.Types.Half
import Grassmann.Types.Multivector
import Grassmann.Types.Couple
import Grassmann.Types.Convert
import Grassmann.Types.Show
import Grassmann.Kernel.Plan
import Grassmann.Kernel.Reference
import Grassmann.Kernel.Class
import Grassmann.Algebra.Arith
import Grassmann.Algebra.Unary
import Grassmann.Algebra.Products
import Grassmann.Algebra.Norms
import Grassmann.Notation
import Grassmann.Basis
import Grassmann.Dynamic
import Grassmann.Composite
import Grassmann.Forms
import Grassmann.Calculus
import Grassmann.Calculus.Simplicial
import Grassmann.Fields
import Grassmann.Fuse
import Grassmann.Batch
import Grassmann.Spec

/-!
# Grassmann: ⟨Grassmann-Clifford-Hodge⟩ differential geometric algebra

Port of Julia's Grassmann.jl element layer (DESIGN.md §4-§5). `import Grassmann`
and `open Grassmann` give the spaces and literals of DirectSum, the element
types, the coefficient classes and the operator notation
(`Grassmann.Notation`; open `Grassmann` *or* `AbstractTensors`, not both).

## Map

* **Types** (`Grassmann.Types.*`): `Chain V G α`, `Half V odd α`
  (`Spinor`/`CoSpinor`), `Multivector V α` over `Values α n` in Julia's storage
  orders; `Single V G α`, `Couple V α`, `PseudoCouple V α`, `Phasor V α`;
  constructors, accessors (`coeff`, `grade`, `term`), conversions
  (`toMultivector`, `toHalf`, `gradePart`), equality, `isapprox`, Julia display.
* **Kernels** (`Grassmann.Kernel.*`): `Plan`s built from DirectSum's blade rules
  with Grassmann's container-level complement semantics, cached once per
  `(V, op, layouts)`, interpreted by tail-recursive loops specialized at the
  coefficient type; `class Kernels V` dispatches every typed operation, with a
  low-priority reference instance for every space and a documented extension
  point for generated kernels.
* **Basis** (`Grassmann.Basis`): `basis! S!"+++"` declares `V`, `v`, `v₁`, `v₁₂`, ... (Julia `@basis`).
* **Algebra** (`Grassmann.Algebra.*`): `+ - *` and scalar actions, the
  geometric/exterior/regressive products, contractions, sandwiches, complements,
  involutions and grade projections with the static result types of DESIGN.md
  §4.2; norms, `abs2`, `inv`.
* **Dynamic** (`Grassmann.Dynamic`): `TA V α`, the Julia-exact layer with Julia's
  result kinds and printing.
* **Composite, Forms, Calculus, Fields** (`Grassmann.Composite`, `Grassmann.Forms`,
  `Grassmann.Calculus`, `Grassmann.Fields`): `exp`/`log`/powers and the other
  composite functions, `TensorOperator`s and their spectral functions, `∇`/`d`/`∂`
  and the simplicial helpers, and `points`/`chainfield`/`vectorfield`.
* **Fusion and batches** (`Grassmann.Fuse`, `Grassmann.Batch`): `fused% e` compiles a
  whole typed expression into one straight-line kernel with one allocation;
  `batch%`/`batchInto%` run it over structure-of-arrays batches.
* **Spec** (`Grassmann.Spec`): the model `Cl g` and the theorems that the
  implementation agrees with it; `Grassmann.Tactic` (opt-in) adds `clifford`.

## Example

```lean
open Grassmann
def a : Chain ℝ3 1 Int := (Chain.ofList? [1, 2, 3]).get!
def b : Chain ℝ3 1 Int := (Chain.ofList? [4, 5, 6]).get!
#eval toString (a * b)   -- "32 - 3v₁₂ - 6v₁₃ - 3v₂₃"   (a Spinor)
#eval toString (a ∧ b)   -- "-3v₁₂ - 6v₁₃ - 3v₂₃"       (a Chain ℝ3 2)
```
-/
