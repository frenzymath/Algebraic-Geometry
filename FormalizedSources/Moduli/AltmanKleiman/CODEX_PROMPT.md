# Codex task: Altman--Kleiman, Compactifying the Picard Scheme

Start by reading:

1. /home/axel/AlgebraicGeometry/FormalizedSources/BLUEPRINT_PROCESS_PROMPT.md
2. this file
3. /home/axel/LeanAlgebraicGeometry-Horizon/references/_project-notes/MR0555258-Compactifying-Picard/summary.md
4. /home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml

Work in /home/axel/AlgebraicGeometry/FormalizedSources/Moduli/AltmanKleiman.
Treat /home/axel/LeanAlgebraicGeometry-Horizon as read-only.

## Authoritative source

- PDF: /home/axel/LeanAlgebraicGeometry-Horizon/references/MR0555258-compactifying-picard.pdf
  (63 physical pages; determine the printed-page offset visually from the
  running page numbers).
- Existing page cross-checks:
  /home/axel/LeanAlgebraicGeometry-Horizon/references/MR0555258-compactifying-picard/tex/page-0018.tex
  through page-0022.tex. These cover printed pages 68--72 and Theorem 2.9,
  but are not a substitute for transcribing the remaining pages.

Use `akcp-` as the stable label prefix. Process every mathematical page
of the paper in order, including the full compactification argument,
definitions of the relevant Picard functors and equivalence relations, all
lemmas and propositions, and complete proofs. Omit only historical or
pedagogical prose, examples, exercises, bibliography, and index. Do not
silently omit an unnumbered assertion.

Render every page and dispatch Luna for an exact page-level mathematical
transcription. Use the five existing TeX page files only as visual
cross-checks. Record page evidence as
\source{MR0555258-compactifying-picard:page-NNNN} and preserve printed
statement numbers such as 2.9 in `\dcref{2.9}`. Keep every proof in a
complete proof environment outside its statement and record all \uses
dependencies.

Create modular files under blueprint/src/, document the physical/printed
page map and license status in PROVENANCE.md, run recursive hgraph and
coverage audits, and compile twice. Do not copy PDF pages, images, or
transcriptions into the repository.
