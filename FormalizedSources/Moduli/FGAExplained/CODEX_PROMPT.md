# Codex task: FGA Explained

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. /home/axel/LeanAlgebraicGeometry-Horizon/references/fga-explained.md

Work in /home/axel/AlgebraicGeometry/FormalizedSources/Moduli/FGAExplained.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- Complete volume PDF:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/fga-explained.pdf
  (352 physical pages, with an extractable but imperfect text layer).
- Source metadata and book-to-PDF page map:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/fga-explained.md.

Use `fga-` as the stable label prefix. Process the complete
mathematical volume in book order, preserving the chapter and section
boundaries and each contributor's theorem numbering. The main formalization
targets are Vistoli's representable functors and descent (Chapters 1--4),
Nitsure's Hilbert/Quot construction (Chapter 5), Illusie's formal existence
theorem (Chapter 8), and Kleiman's Picard scheme (Chapter 9), but do not
silently skip the intervening mathematical chapters. Omit only historical,
motivational, or pedagogical prose, worked examples, exercises, answers,
bibliography, and index; retain mathematical assertions in all chapters.

The book-page to PDF-page offset is +10 according to the source card. Render
and dispatch Luna for every physical PDF page. The text layer is a search aid
only and must not replace visual verification of formulas, diagrams, or
quantifiers. Record \source{fga-explained:page-NNNN} with the PDF page and
the printed book coordinate in the provenance ledger. Numbered statements use
the exact book number in `\dcref{<number>}`; never use a source prefix or synthetic chapter
counter. Proof environments must be outside statements and complete enough to
reconstruct the source argument; add every real \uses edge.

Write modular chapter files, update PROVENANCE.md, run recursive hgraph,
label/uses, dcref, and page-coverage audits, and compile twice. Keep rendered
pages and Luna work records only under ignored .blueprint-work/.
