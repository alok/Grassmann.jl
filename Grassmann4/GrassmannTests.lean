import Grassmann.Reference

/-!
# Grassmann validation library

This is the lightweight import root for the `GrassmannTests` Lake library.
Building that library also builds `Grassmann.All`, the broad in-repository
validation aggregate. Import `Grassmann.All` explicitly to elaborate or run
the suites; merely importing this marker does not initialize their closed
property checks in a downstream native program.
-/
