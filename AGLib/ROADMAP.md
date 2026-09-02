# AGLib roadmap

## Goal

Build a **mathlib-quality** algebraic geometry library (`AGLib`) inside
`frenzymath/Algebraic-Geometry`: well-named, general, documented Lean modules
that can be reused across source-faithful projects and flagship challenges.

Work is driven by maintainer issues and reviewed pull requests into the
Palimpsest source branch `palimpsest/aglib`. Merges from that branch into
`main` are **manual**.

## Principles

1. **Extract and generalize**, do not re-formalize whole cones from scratch.
2. Follow **mathlib** naming, docstring, and API conventions
   (`review.level: mathlib`).
3. Prefer **stable, source-independent** statements; leave challenge-specific
   scaffolding in the upstream package.
4. Cite the upstream module when promoting a declaration.
5. Keep the default Lake target green (`lake build AGLib`).
6. No blueprint is required for AGLib; documentation is Lean module docs plus
   this roadmap and the package README.

## Near-term spine (issue-sized)

- Foundations shim: schemes / morphisms helpers that repeatedly appear upstream
  and are missing or awkward in mathlib for our use.
- Cohomology and Čech utilities used by multiple routes.
- Line bundles / Picard functor pieces that are already stable and general.
- Curve and divisor degree APIs that do not depend on a single challenge
  construction.

Each item should become one focused PR with docs, tests via compilation, and
no drive-by refactors outside AGLib unless required for the extraction.

## Out of scope

- Horizon/Archon control plane and dashboard material.
- Source-faithful blueprint editing as the primary deliverable.
- Importing PicardAlbanese or MilneKollar as library dependencies.
- Unsolicited whole-repo rewrites; discovery only refines themes already on
  this roadmap or in open maintainer issues.

## Success signal

`AGLib` has a coherent import hierarchy, nontrivial documented public surface,
CI `lake-build` green on PRs into `palimpsest/aglib`, and selected modules
manually back-ported to `main` when stable.
