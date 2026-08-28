# Provenance: Papaioannou, Algebraic Riemann--Roch

This project is a source-faithful blueprint for Athanasios Papaioannou,
*An algebraic approach to the Riemann-Roch theorem and the arithmetic theory of
function fields*, PDF creation date 2005-02-06, hosted at
`http://www.fen.bilkent.edu.tr/~franz/mat/Riemann-Roch.pdf` (the
`papaioannou-algebraic-rr` entry in the workspace manifest, retrieved
2026-07-07). The authoritative local source is
`/home/axel/LeanAlgebraicGeometry-Horizon/references/papaioannou-algebraic-rr/papaioannou-algebraic-rr.pdf`.
The Horizon source tree is read-only; this project contains only blueprint
source and metadata, while rendered pages, Luna records, logs, and build output
are kept under the ignored `.blueprint-work/` directory.

The PDF has 15 pages. PDF and printed page numbers coincide on the mathematical
pages: page 1 is title/abstract, pages 2--5 are valuations and places, pages
6--9 are weak approximation, divisors, and genus, pages 9--12 are adeles and
Weil differentials, pages 13--14 are duality, Riemann--Roch, and arithmetic,
and page 15 is bibliography. Every page was rendered at 300 DPI and dispatched
to a Luna vision/transcription subagent. The page-addressable records and the
node map are in `.blueprint-work/luna/pages-01-05.md`,
`.blueprint-work/luna/pages-06-10.md`, `.blueprint-work/luna/pages-11-15.md`,
and `.blueprint-work/page-ledger.md`.

Coverage includes Definitions 1.1--1.14, Lemma 1.3 and Lemmas 1.13--1.14,
Theorems 1.1--1.2, 1.4--1.6, 1.9, 1.11, 1.15, 1.17--1.18, 1.23, 1.25--1.27,
Corollaries 1.7--1.8, 1.10, 1.12, 1.16, 1.28--1.29, Conjectures 2.1--2.2,
and Theorems 2.1--2.2. Unnumbered mathematical setup (residue fields, degree,
Riemann's inequality, index of speciality, scalar action, height, and separable
degree) is retained. Exposition, examples, exercises, bibliography, and index
are omitted. Printed typographical quirks that affect formulas are preserved
and cross-listed in the private ledger.

All numbered nodes use exactly one `\dcref{...}` containing the printed number
and every node has a `\source{papaioannou-algebraic-rr:page-NNNN}` anchor.
`\uses` edges record statement/proof dependencies; no Lean declarations are
claimed, so no `\lean`, `\leanok`, or `\mathlibok` tags are emitted.

The PDF does not state an explicit reuse license. The blueprint is therefore a
limited scholarly transcription with source attribution; no source PDF,
images, or full transcriptions are copied into the project.

Validation performed from this directory:

```text
/home/axel/.archon-env/bin/hgraph --root . sync --blueprint blueprint/src/content.tex -v
cd blueprint/src && pdflatex -interaction=nonstopmode -halt-on-error -output-directory ../../.blueprint-work/latex print.tex
cd blueprint/src && pdflatex -interaction=nonstopmode -halt-on-error -output-directory ../../.blueprint-work/latex print.tex
```

The final hgraph synchronization reports 55 blueprint nodes and 123 generated
hard dependency edges. Both LaTeX passes complete without errors or undefined
references; the first pass emits only the standard rerun notices, and the
second pass is clean.
