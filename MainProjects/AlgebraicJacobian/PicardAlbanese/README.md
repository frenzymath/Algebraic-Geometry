# Picard-Albanese route

This route combines the source-faithful blueprint with the ported Lean library
from Horizon's `MainProjects/Algebraic-Jacobian-Challenge-Rebuild`.

The full from-scratch source tree has 1,176 library modules. Its active root
contains unfinished development cones, so the stable target currently checked
in this workspace is the two-lattice foundation:

```bash
lake build AlgebraicJacobian.Algebra.TwoLattice
```

Other modules remain available for explicit Lake targets as their dependencies
become green. The source keeps its named `sorry` obligations and linter
warnings; a green target certifies compilation only.
