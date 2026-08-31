# Milne-Kollar route

This route combines the source-faithful blueprint with the ported Lean library
from Horizon's `MainProjects/Algebraic-Jacobian-Challenge`.

The package has 387 library modules and uses Lean 4.31.0 with the pinned
mathlib/doc-gen4/checkdecls dependencies. Build the complete root from this
directory:

```bash
lake build AlgebraicJacobian
```

The route has been freshly checked with `lake build AlgebraicJacobian.Genus`;
the complete root is substantially slower because it elaborates every imported
challenge module.

The source keeps the challenge's named `sorry` obligations and linter
warnings. A green build therefore certifies compilation, not completion of the
mathematics.
