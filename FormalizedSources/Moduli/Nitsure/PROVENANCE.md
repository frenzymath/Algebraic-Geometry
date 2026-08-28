# Provenance: Nitsure - Construction of Hilbert and Quot Schemes

Status: complete. This blueprint follows the operational instructions in
`CODEX_PROMPT.md` and the shared fidelity and validation rules in
`../../BLUEPRINT_PROCESS_PROMPT.md`.

## Source

- Tier: A (authoritative local PDF and matching TeX source).
- PDF: `/home/axel/LeanAlgebraicGeometry-Horizon/references/nitsure-hilbert-quot.pdf`.
- TeX cross-check: `/home/axel/LeanAlgebraicGeometry-Horizon/references/nitsure-hilbert-quot-src/nitsure-hilbert-quot.tex`.
- Source identifier: `nitsure-hilbert-quot` (NHQ).
- Edition/page map: 36 physical pages; printed page numbers agree with
  physical pages (offset 0). Page images and Luna transcription records are
  retained in ignored `.blueprint-work/pages/` and `.blueprint-work/luna/`.
- License: the local arXiv source is used for this research blueprint; no
  separate license declaration is present in the local manifest or source
  bundle.

## Coverage

The six mathematical sections are transcribed in source order in
`blueprint/src/content.tex` and its six chapter files. Mathematical content is
covered through physical page 36 (Theorem 6.9 starts on printed page 35 and
continues onto page 36); bibliography and index material on page 36 is omitted.
Historical and pedagogical introduction prose, examples, and exercises are
omitted as allowed by the project protocol; the page-1 functor-of-points and
fpqc-descent definitions are retained because they are foundational
mathematical content.
Numbered results retain their printed numbers through `\dcref`; stable labels
use the `nhq-` prefix, and each retained result/claim carries a
`nitsure-hilbert-quot:page-NNNN` source anchor. Dependencies are declared with
`\uses` and are checked recursively by the audit report.

## Blueprint and validation

- Blueprint entry point: `blueprint/src/content.tex`.
- hgraph configuration: `hgraph/config.yaml`.
- Luna records: `.blueprint-work/luna/page-01.md` through `page-36.md`, one
  exact visual/transcription record per PDF page.
- Validation artifacts: `.blueprint-work/compile/` (two-pass `pdflatex`),
  `.blueprint-work/audit/`, and `.blueprint-work/hgraph-sync.log`.
- Validation commands: two `pdflatex` passes from `blueprint/src`,
  `/home/axel/.archon-env/bin/hgraph sync --blueprint blueprint/src/content.tex`,
  and the recursive label/reference/source/page audit in
  `.blueprint-work/audit/`.
