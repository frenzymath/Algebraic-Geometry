# AGLib

Mathlib-style algebraic geometry library for the
[Algebraic Geometry](https://github.com/frenzymath/Algebraic-Geometry) workspace.

AGLib is a curated Lean package: reusable declarations with mathlib conventions
(naming, generality, docstrings, import hygiene). It is **not** a source-faithful
blueprint project. Upstream formalizations live under `FormalizedSources/` and
`MainProjects/`; material is promoted here by extraction and generalization.

## Build

```bash
# from the workspace root, ensure the shared Lake cache is linked
./scripts/use-horizon-cache.sh   # optional if .lake-packages already points at Horizon

cd AGLib
lake build AGLib
```

`packagesDir` is `../.lake-packages` so AGLib shares the workspace dependency
checkout with the other Lake packages.

## Layout

```text
AGLib.lean           package root
AGLib/Basic.lean     bootstrap / foundations entry
ROADMAP.md           intended end-state for library construction
```

Grow the tree the way mathlib does (topic directories, fine-grained modules),
not as a mirror of one book or challenge cone.

## Provenance

When a declaration is extracted from an upstream package, name the source module
in the docstring. Do not import unfinished challenge cones or probe files.
Back-propagation from Palimpsest working branches into `main` is manual.
