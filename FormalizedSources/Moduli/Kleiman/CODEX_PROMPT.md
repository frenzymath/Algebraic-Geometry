# Codex task: Kleiman, The Picard Scheme

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. the source card at /home/axel/LeanAlgebraicGeometry-Horizon/references/kleiman-picard.md

Work in /home/axel/AlgebraicGeometry/FormalizedSources/Moduli/Kleiman.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- PDF: /home/axel/LeanAlgebraicGeometry-Horizon/references/kleiman-picard.pdf
  (83 physical pages, arXiv self-pagination equals printed pagination).
- Full source cross-check:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/kleiman-picard-src/kleiman-picard.tex.
- Focused complete proof of Theorem 4.8:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/Kleiman_The_Picard_Scheme_Theorem-4.8.tex.
- Source metadata:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml.

Use `kps-` as the stable label prefix. Process the entire mathematical
paper in source order. In particular, retain the several Picard functors,
relative effective divisors, the Picard-scheme existence theorem, the complete
Pic^0/Jacobian section, and Pic^tau finiteness. Skip only the introduction's
historical exposition, worked examples, exercises, bibliography, and index;
retain mathematical assertions appearing in otherwise omitted prose.

Render and send every PDF page to Luna for visual transcription. The bundled
TeX is a cross-check, not a replacement for the page-by-page vision pass.
Record page evidence with \source{kleiman-picard:page-NNNN}. Numbered results
must use only their printed numbers in \dcref (for example `\dcref{4.8}`);
do not invent
numbers for the many unnumbered definitions and remarks. Put every complete
proof in a proof environment outside its statement environment and add all
actual dependency edges with \uses.

Create the modular blueprint under blueprint/src/, update PROVENANCE.md, run
recursive hgraph and label/uses audits, and compile twice before reporting
completion. Do not copy the source PDF, page images, or Luna transcriptions
into this project.
