# AGLib

AGLib is a mathlib-style algebraic geometry library maintained in the
[Algebraic Geometry](https://github.com/frenzymath/Algebraic-Geometry)
repository. It contains general, documented declarations extracted from stable
formalizations in that repository.

AGLib is not a mirror of a book, blueprint, or flagship proof. Its only Lean
dependency is mathlib; source-faithful projects provide candidates and
provenance but are never imported.

## Build

The package pins Lean and mathlib together. From this directory, run:

```bash
lake build AGLib
```

The repository's protected CI status is the authoritative full build.

## Layout

```text
AGLib.lean           umbrella import for the stable public surface
AGLib/Basic.lean     minimal foundational import
ROADMAP.md           scope, dependency layers, and extraction policy
docs/references.bib  bibliography for precise literature citations
```

New code belongs in fine-grained modules organized by mathematical subject.
Declarations should use the established mathlib namespace for that subject,
carry faithful documentation and provenance, and avoid imports from
`FormalizedSources/` or `MainProjects/`.

## Contributions

Work is selected by maintainer issues and submitted as focused pull requests to
`palimpsest/aglib`. See [the roadmap](ROADMAP.md) for the promotion gates and
dependency order. Back-propagation to `main` is manual.
