-- Kitchen-sink import for development.
--
-- `import Grassmann` is meant to be reasonably lightweight for downstream users.
-- If you want *all* demos, stress tests, and property tests (many of which run
-- `#eval` at compile time), import this module instead.
import Grassmann.Reference

-- Tests / demos (compile-time `#eval` heavy)
import Grassmann.StressTests
import Grassmann.Tests
import Grassmann.OracleTests
import Grassmann.DSLTests
import Grassmann.CoffeeshopExamples
import Grassmann.PropertyTests
import Grassmann.CurveShortening
