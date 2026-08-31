# Provenance

The two route-local Lean libraries are direct source ports from the Horizon
workspace:

- `MilneKollar/AlgebraicJacobian/` comes from
  `MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/`.
- `PicardAlbanese/AlgebraicJacobian/` comes from
  `MainProjects/Algebraic-Jacobian-Challenge-Rebuild/AlgebraicJacobian/`.

Each route also carries the corresponding root module and pinned Lake
metadata. Horizon probes, scratch files, generated graphs, and `.lake/` build
products are intentionally excluded. The dependency checkout is shared via
the ignored workspace `.lake-packages` link maintained by
`scripts/use-horizon-cache.sh`; route `.lake/` directories remain local.

The source trees retain their named `sorry` obligations and ordinary linter
warnings. A verified build of a target is not a claim that the open
mathematical milestones are proved. The original challenge code and this port
are covered by the workspace Apache 2.0 license.
