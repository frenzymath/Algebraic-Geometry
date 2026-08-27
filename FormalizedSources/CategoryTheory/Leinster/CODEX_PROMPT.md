# Codex task: Leinster, Basic Category Theory

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. /home/axel/LeanAlgebraicGeometry-Horizon/references/leinster-basic-category-theory.md

Work in /home/axel/AlgebraicGeometry/FormalizedSources/CategoryTheory/Leinster.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- Complete PDF:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/leinster-basic-category-theory.pdf
  (191 pages; the open-access arXiv edition).
- Source card and chapter map:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/leinster-basic-category-theory.md.

Use `lbc-` as the stable label prefix. Process all mathematical chapters
in order: categories, functors and natural transformations; adjoints; sets;
representables and the Yoneda lemma; limits and colimits; and the
adjoint/representability applications. Preserve definitions, universal
properties, diagrams, numbered and unnumbered propositions, and complete
proofs. Omit only examples, exercises, bibliography, index, and explanatory
prose that carries no mathematical content.

Render every page and dispatch Luna for an exact visual transcription. Use the
PDF text layer only as a search aid. Determine the printed/PDF page mapping,
record \source{leinster-basic-category-theory:page-NNNN}, and use the exact
printed result number in `\dcref{<number>}`. Proofs must be outside
statement environments, and all named or explicit dependencies must be
represented by \uses.

Create modular chapter files, write PROVENANCE.md, run recursive hgraph,
label/uses, dcref, and page-coverage audits, and compile twice. Keep rendered
pages, logs, graphs, and Luna records under ignored .blueprint-work/.
