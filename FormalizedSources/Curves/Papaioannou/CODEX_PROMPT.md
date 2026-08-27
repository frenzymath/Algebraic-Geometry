# Codex task: Papaioannou, Algebraic Riemann--Roch and Function Fields

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. the papaioannou-algebraic-rr entry in
   /home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml

Work in /home/axel/AlgebraicGeometry/FormalizedSources/Curves/Papaioannou.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- PDF:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/papaioannou-algebraic-rr/papaioannou-algebraic-rr.pdf
  (15 pages).
- Existing visual transcriptions and page images:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/papaioannou-algebraic-rr/tex/
  and /home/axel/LeanAlgebraicGeometry-Horizon/references/papaioannou-algebraic-rr/pages/.
- Source manifest:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml.

Use `par-` as the stable label prefix. Process all mathematical content:
valuations and places; weak approximation; divisors, Riemann--Roch spaces,
and genus; adeles and Weil differentials; duality; Theorems 1.23, 1.25, 1.26,
and 1.27; the corollaries; and the function-field arithmetic and Hurwitz
results in Section 2. Omit only exposition, worked examples, exercises,
bibliography, and index. Preserve every definition and unnumbered claim. The
source's visible typographical errors should be preserved when mathematically
relevant and noted in the private ledger.

Render and dispatch Luna for every page even though pages 3--15 already have
vision transcriptions; those files are cross-check aids, not authority.
Record \source{papaioannou-algebraic-rr:page-NNNN}. Use exact printed numbers
such as `\dcref{1.27}`. Put full proofs outside their statement
environments and add \uses for every dependency.

Create modular chapter files, update PROVENANCE.md, audit recursively, and
compile twice. Keep all generated images, logs, and transcription records
under ignored .blueprint-work/, not in the project.
