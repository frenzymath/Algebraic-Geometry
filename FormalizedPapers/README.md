# Formalized Papers

Blueprint projects for the algebraic-geometry papers in this workspace. Each
project has a concise, rephrased mathematical guide, a direct source-PDF link,
project metadata, and its own hgraph configuration.

The machine-readable registry is [`paper-catalog.yaml`](paper-catalog.yaml).
The guides are distilled for formalization and should be read alongside their
original papers; they are not substitutes for the source text.

All project names use descriptive titles/slugs. MR identifiers are
cross-references only. Source-backed mathematical nodes are currently
`\notready`; this records that the content still needs translation into
checked Lean declarations.

## Categories

- [Abelian varieties and motives](AbelianVarietiesAndMotives/README.md)

- [Curves, Brill--Noether theory, and linear series](CurvesAndLinearSeries/README.md)

- [Sheaves, cohomology, and intersection theory](SheavesAndCohomology/README.md)

- [Arithmetic geometry and number theory](ArithmeticGeometry/README.md)

- [Moduli, Higgs bundles, and character varieties](ModuliHiggsCharacter/README.md)

- [Surfaces, birational geometry, and hyper-Kähler varieties](SurfacesBirationalHyperkahler/README.md)


## Blueprint conventions

Each project follows the established source-project conventions:

- `blueprint/src/content.tex` begins with “About This Blueprint”.
- `blueprint/src/macros.tex` declares theorem environments and metadata macros.
- `\label`, `\source`, `\uses`, and `\notready` live on mathematical
  statements.
- `hgraph/config.yaml` points to the blueprint and leaves the Lean list empty
  until a real library is added.

The current batch is a complete source-derived blueprint corpus, not a claim
that any of the 26 papers has already been formalized in Lean. Promote nodes
to `\leanok` only after kernel-checked Lean declarations and complete proofs
exist.
