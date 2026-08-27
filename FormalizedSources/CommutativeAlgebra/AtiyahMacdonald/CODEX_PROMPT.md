# Codex task: Atiyah--Macdonald, Introduction to Commutative Algebra

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. /home/axel/LeanAlgebraicGeometry-Horizon/references/atiyah-macdonald-commutative-algebra.md

Work in /home/axel/AlgebraicGeometry/FormalizedSources/CommutativeAlgebra/AtiyahMacdonald.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- Complete PDF:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/atiyah-macdonald-commutative-algebra.pdf
  (137 pages).
- Source card and chapter map:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/atiyah-macdonald-commutative-algebra.md.

Use `am-` as the stable label prefix. Process the complete mathematical
book in order. The blueprint must include the elementary ring, module,
localization, integral-dependence, primary-decomposition, chain condition,
Noetherian, valuation/DVR, completion, and dimension material, including
every unnumbered mathematical assertion and all proofs. Chapters 8 and 11
are especially important, but are not a license to omit their prerequisites.
Omit only examples, exercises, bibliography, index, and non-mathematical
exposition.

Render every page and dispatch Luna for exact visual transcription, with the
PDF text layer used only for search. Determine the printed/PDF page map and
record \source{atiyah-macdonald-commutative-algebra:page-NNNN}. Preserve
each printed statement number in `\dcref{<number>}` and never invent
numbers for unnumbered material. Put complete proofs outside statement
environments and attach every dependency via \uses.

Create modular source files, update PROVENANCE.md, run recursive hgraph and
coverage audits, and compile twice. Store generated files and Luna records
only under ignored .blueprint-work/.
