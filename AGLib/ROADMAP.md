# AGLib roadmap

## Mission and boundary

AGLib is a curated companion to mathlib for reusable algebraic geometry that
has matured in this repository's formalizations but is not yet available in
mathlib. The library is developed through maintainer-scoped issues and reviewed
pull requests into `palimpsest/aglib`; transfer to `main` remains manual.

Mathlib is the only Lean dependency. Files in `FormalizedSources/` and
`MainProjects/` are sources of candidates and provenance, never dependencies.
Blueprints and planning notes may help locate a candidate, but publications and
Lean source establish its mathematical and formal content.

Declarations should extend the established mathlib namespace for their subject.
The `AGLib` namespace is reserved for package-specific infrastructure rather
than used as a blanket namespace for mathematics.

## Dependency layers

The module graph grows in this order:

1. **Foundations:** reusable commutative algebra, topology, category theory,
   schemes, and morphism helpers.
2. **Local-to-global tools:** covers, descent, sheaves, Cech constructions, and
   cohomological utilities.
3. **Geometric objects:** line bundles, divisors, curves, projective geometry,
   and group schemes.
4. **Universal constructions:** Picard and Albanese objects, abelian varieties,
   and the stable interfaces they consume.

Within each layer, modules are maintained in a topological order: a module may
import mathlib, any earlier AGLib layer, and earlier modules in its own layer.
No module may import a later layer or a flagship route, and the within-layer
dependency graph must remain acyclic. `AGLib.lean` is the umbrella import for
the reviewed public surface; downstream code should prefer the narrowest topic
module it needs. The layers organize dependencies, not the work queue: a
maintainer issue must still name each extraction or API goal.

## Extraction policy

A merge-ready extraction must satisfy all of the following gates:

1. Search the pinned mathlib source and AGLib for the declaration or a more
   general equivalent. Reuse an existing API instead of creating a synonym.
2. Identify a stable source declaration and its actual consumers. Do not port a
   file wholesale merely because it occurs in a flagship proof.
3. Restate the result at its natural generality, in a canonical namespace and
   module, without route-specific data, names, or compatibility scaffolding.
4. Audit the proof and hypotheses against the source statement. Merge-ready code
   has no `sorry`, hidden axioms, or assumptions introduced only to bypass a
   missing argument.
5. Give every module a module docstring and every public definition or major
   result a faithful docstring. Name the source module; when mathematics comes
   from the literature, cite a precise result keyed in `docs/references.bib`.
6. Keep imports fine-grained, expose the module through the root only when its
   API is stable, and include a small compiling consumer when elaboration alone
   would not exercise the intended interface.
7. Finish local Lean diagnostics before publication and leave the full package
   build to the protected CI workflow.

General-purpose results that fit mathlib should be designed for eventual
upstreaming. AGLib may host them while local consumers need them, but should not
accumulate a parallel API indefinitely.

## Near-term route

After the bootstrap, issues should move upward through the dependency layers:

- foundations shared by at least two source or flagship modules;
- Cech, cohomology, line-bundle, and divisor utilities with independent APIs;
- curve, projective, and group-scheme results built on those utilities;
- Picard, Albanese, and abelian-variety interfaces only after their lower-layer
  dependencies are stable.

An issue may select a later theme when its dependencies already exist in
mathlib. The dependency rule, rather than this list, determines readiness.

## Replacement triggers

- When mathlib gains an equivalent canonical declaration, migrate consumers and
  remove or deprecate the AGLib declaration in a focused issue.
- When source audit reveals stronger hidden hypotheses or unstable semantics,
  revise or withdraw the candidate before building on it.
- When a module needs a later layer or route-specific import, split the API at
  that boundary rather than introducing a cycle.
- Update the Lean/mathlib pin in a dedicated infrastructure PR, separately from
  mathematical API changes.

Progress means a coherent, documented public surface with downward-only imports
and a green protected `lake-build` status, not the number of upstream files
copied into AGLib.
