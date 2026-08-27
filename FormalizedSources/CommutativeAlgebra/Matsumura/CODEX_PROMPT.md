# Codex task: Matsumura, Commutative Ring Theory

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. /home/axel/LeanAlgebraicGeometry-Horizon/references/matsumura-commutative-ring-theory.md

Work in /home/axel/AlgebraicGeometry/FormalizedSources/CommutativeAlgebra/Matsumura.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- Complete PDF:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/matsumura-commutative-ring-theory.pdf
  (336 pages).
- Source card and chapter map:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/matsumura-commutative-ring-theory.md.

Use `mcrt-` as the stable label prefix. Transcribe the entire
mathematical book in order, including all definitions, lemmas, propositions,
theorems, corollaries, unnumbered assertions, and proofs. Pay particular
attention to Chapters 16--19 (depth, regular sequences, Cohen--Macaulay
rings, Auslander--Buchsbaum, and regular local rings), but do not omit the
earlier chapters that supply their hypotheses. Omit only examples, exercises,
historical/pedagogical prose, bibliography, and index.

Render every page and dispatch Luna for exact visual transcription; do not
trust a text layer or memory. Determine and record the printed/PDF page map.
Numbered statements retain the exact printed chapter/section number in
`\dcref{<number>}`; unnumbered items receive no fabricated number.
Record page evidence with
\source{matsumura-commutative-ring-theory:page-NNNN}. Proofs are complete
proof environments outside statements, and every mathematical dependency is
represented by \uses.

Build modular source files, write PROVENANCE.md, run recursive hgraph,
dcref, label/uses, and source-coverage audits, and compile twice. Keep all
generated artifacts and Luna records under ignored .blueprint-work/.
