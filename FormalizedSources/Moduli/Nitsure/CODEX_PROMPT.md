# Codex task: Nitsure, Construction of Hilbert and Quot Schemes

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. /home/axel/LeanAlgebraicGeometry-Horizon/references/nitsure-hilbert-quot.md

Work in /home/axel/AlgebraicGeometry/FormalizedSources/Moduli/Nitsure.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- PDF: /home/axel/LeanAlgebraicGeometry-Horizon/references/nitsure-hilbert-quot.pdf
  (36 physical pages, arXiv self-pagination equals printed pagination).
- Full source cross-check:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/nitsure-hilbert-quot-src/nitsure-hilbert-quot.tex.
- Source metadata:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml.

Use `nhq-` as the stable label prefix. Process the complete paper in
order: the Hilbert and Quot functors; Castelnuovo--Mumford regularity;
semicontinuity and base change; generic flatness and flattening
stratification; the Grassmannian construction of Quot; and variants and
applications. Omit only introduction-level historical/pedagogical prose,
worked examples, exercises, bibliography, and index. Preserve every
definition, hypothesis, unnumbered claim, displayed construction, and proof.

Render and send every PDF page to Luna for exact visual transcription. Use the
bundled TeX only to locate and cross-check formulas. Record evidence as
\source{nitsure-hilbert-quot:page-NNNN}. Numbered results retain their printed
numbers in \dcref (for example `\dcref{5.1}`); unnumbered mathematical items get no
fabricated number. Proofs are complete proof environments outside the
corresponding statement environments, with all dependencies in \uses.

Build the modular source under blueprint/src/, update PROVENANCE.md, run
recursive hgraph and reference audits, and compile twice. Keep all generated
pages, logs, graphs, and Luna records under ignored .blueprint-work/ paths,
never in this project.
