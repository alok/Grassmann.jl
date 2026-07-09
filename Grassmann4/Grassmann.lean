/-
  # Grassmann

  Supported proof-free computational surface for the Lean 4 port.

  Dense/reference representations, theorem drafts, demos, code generators,
  visualization, and application experiments are deliberately opt-in.  Use
  `Grassmann.Reference` for the broad dense API and import experimental modules
  by name.
-/

-- Algebra and metric foundations.
import Grassmann.BitMask
import Grassmann.Manifold
import Grassmann.Blade
import Grassmann.SimplexChain
import Grassmann.Parity
import Grassmann.Products
import Grassmann.GATypeclass
import Grassmann.Notation

-- Native Float storage and packed geometric algebra runtime.
import Grassmann.DataArray
import Grassmann.NativeVector
import Grassmann.MV

-- High-performance Cl(3,0,1) constructors and transforms.
import Grassmann.PGA3Packed
