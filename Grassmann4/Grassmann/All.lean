-- Broad development and validation aggregate for the canonical workspace.
--
-- `import Grassmann` is meant to be reasonably lightweight for downstream users.
-- Import this module for the dense/reference API and the in-repository validation
-- suites. Application experiments and modules with optional dependencies remain
-- explicit imports by design.
import Grassmann.Reference

-- Validation suites (many run `#eval` at compile time).
import Grassmann.StressTests
import Grassmann.Tests
import Grassmann.MVArithmeticTests
import Grassmann.MVUnaryTests
import Grassmann.MVHodgeTests
import Grassmann.OracleTests
import Grassmann.DSLTests
import Grassmann.PropertyTests
