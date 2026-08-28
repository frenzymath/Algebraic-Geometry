# Provenance: Matsumura, Commutative Ring Theory

## Source identification

The source is Hideyuki Matsumura, *Commutative Ring Theory*, Cambridge
Studies in Advanced Mathematics 8, Cambridge University Press, revised English
edition translated by M. Reid (English copyright 1986; corrected paperback
printing 1989, local digital scan).  The registered source slug is
`matsumura-commutative-ring-theory`; this project uses the stable label prefix
`mcrt-`.

The authoritative local files, treated as read-only, are:

- `/home/axel/LeanAlgebraicGeometry-Horizon/references/matsumura-commutative-ring-theory.pdf`
- `/home/axel/LeanAlgebraicGeometry-Horizon/references/matsumura-commutative-ring-theory.md`

`pdfinfo` verifies a 336-page, 600 x 900 point PDF.  The scan is commercially
copyrighted; no redistribution licence is asserted here (`unknown-commercial-
copyright`).  The verified local SHA-256 is
`d1f6d3c2173501ce4b459ab26ba49daac1794a3f2503f4d3ea6f3a57046116f0`.  This
repository contains no copy of the PDF.

## Page mapping and coverage

Every physical PDF page 1--336 was rendered at 90 dpi and visually dispatched
to the required Luna transcription workers.  Rendered images, page-addressable
worker records, the printed/PDF map, and text-layer cross-checks are retained
only under the ignored `.blueprint-work/ledger/` and `.blueprint-work/luna/`
directories.  For the Arabic mathematical body, printed page `N` maps to PDF
page `N+15` (printed pages 1--286 therefore occupy PDF pages 16--301).
PDF pages 1--15 and 302--336 are front matter, blank/editorial matter,
solutions, references, or index material and are explicitly classified in the
ledger.  The conventions page is PDF page 14 (printed Roman page xiii).

The modular source entry point is `blueprint/src/content.tex`.  It inputs
chapter files `mcrt-ch01.tex` through `mcrt-ch11.tex` and appendices
`mcrt-app-a.tex` through `mcrt-app-c.tex`.  Each mathematical body page has a
page-level `\source{matsumura-commutative-ring-theory:page-NNNN}` anchor.  The
private ledger contains 336 rendered images, 336 Luna transcription records,
and 336 page-map rows.  The tracked page blocks contain only source anchors
and cross-reference notes; the full visual transcriptions remain private under
`.blueprint-work/luna` as required by the process prompt.  Worked examples,
exercises, bibliography, index, and historical/pedagogical prose are omitted
as authorized by the project prompt.

The chapter files `blueprint/src/mcrt-ch01.tex` through
`blueprint/src/mcrt-ch11.tex` contain the complete numbered statement
inventory, while the key-result files give
fully structured statements and separate proof environments for the principal
regular-sequence, Cohen--Macaulay, Gorenstein, Auslander--Buchsbaum, and Serre
results.  The appendix files also contain the previously missed printed
Theorems A2, B2--B4, and C2, and the chapter inventory includes Theorems 4.7,
5.2, and 12.6.  Numbered items use exactly the printed coordinate in
`\dcref`; no synthetic chapter or page number is used.  Unnumbered definitions
and page blocks carry `\source` evidence without fabricated `\dcref` values.
No `\lean`, `\leanok`, or `\mathlibok` claims are made.

## Validation

From this project directory:

```text
/home/axel/.archon-env/bin/hgraph --root . sync -v
/home/axel/.archon-env/bin/hgraph --root . stats
```

The final sync reports 236 current TeX nodes and 113 generated dependency edges
with no synchronizer warnings.  A recursive metadata audit is recorded at
`.blueprint-work/audits/validation.txt`; it checks duplicate labels and
`\dcref` values, dangling `\uses`, unresolved source references, source-page
coverage, and proof/statement inventories.

The assembled blueprint was compiled twice with `pdflatex` using a temporary
driver and `TEXINPUTS=blueprint/src:.blueprint-work/build`.  The successful
output is `.blueprint-work/build/mcrt.pdf` (199 pages); both compliance-pass
logs are retained under `.blueprint-work/build/` and contain no LaTeX errors or
undefined references.  Source-deferred results remain explicitly marked
`\notready` only where the book supplies no proof or the page ledger is
illegible.
