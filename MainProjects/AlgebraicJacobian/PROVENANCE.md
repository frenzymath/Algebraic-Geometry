# Provenance

The Lean library in `AlgebraicJacobian/` is ported from the original AJ package
at `LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge`.
Only the library sources and the pinned Lake metadata are included here; probes,
scratch files, generated build products, Horizon state, and the separate
experimental Rebuild tree are intentionally excluded.

The package was copied at a source revision for which
`lake build AlgebraicJacobian` completes successfully. The build still reports
the AJ project's named `sorry` obligations and ordinary linter warnings; this
port preserves those declarations and does not claim the open mathematical
milestones are proved. The source-independent `shared/` directory remains
reserved for declarations that can be reused without the AJ namespace or its
challenge-specific APIs.

The original challenge code and this port are covered by the workspace Apache
2.0 license.
