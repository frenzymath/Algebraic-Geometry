# Provenance: Atiyah--Macdonald, Introduction to Commutative Algebra

## Source

This blueprint transcribes M. F. Atiyah and I. G. Macdonald, *Introduction to
Commutative Algebra*, Addison--Wesley, 1969.  The authoritative read-only
artifacts are:

- `/home/axel/LeanAlgebraicGeometry-Horizon/references/atiyah-macdonald-commutative-algebra.pdf`
- `/home/axel/LeanAlgebraicGeometry-Horizon/references/atiyah-macdonald-commutative-algebra.md`

The scan has 137 physical PDF pages.  Physical pages 1--9 are front matter;
physical page 8 is the notation page and physical page 9 is blank.  From
physical page 10 onward, printed page `n` is physical page `n+9`.  The
mathematical chapter ranges are physical pages 10--18 (Chapter 1), 26--39
(Chapter 2), 45--52 (Chapter 3), 59--63 (Chapter 4), 68--76 (Chapter 5),
83--87 (Chapter 6), 89--93 (Chapter 7), 98--100 (Chapter 8), 102--107
(Chapter 9), 109--122 (Chapter 10), and 125--134 (Chapter 11).  The remaining
pages are exercises, index, or other end matter and are retained only in the
private page ledger.

## Blueprint coverage

The tracked entry point is `blueprint/src/content.tex`, which inputs one
modular file per chapter.  It includes the mathematical definitions,
unnumbered assertions and remarks, all numbered results in the chapter body,
and their proofs.  Examples, exercises, bibliography, index, and historical
or pedagogical exposition are omitted as authorized by `CODEX_PROMPT.md`.
Every node carries a source anchor of the form
`atiyah-macdonald-commutative-algebra:page-NNNN`.  Every numbered statement
uses exactly one `\dcref{...}` containing the source's printed coordinate;
unnumbered material has no fabricated number.  No Lean status claims are made.

Every one of the 137 physical pages was rendered at at least 220 DPI and
visually inspected by a Luna transcription worker.  The page images, direct
visual transcriptions, folio map, uncertainty notes, and validation artifacts
are private and ignored under `.blueprint-work/`; the PDF and full page
transcriptions are not copied into the tracked repository.

The 1969 publication is a copyrighted commercial work.  No redistribution
license is supplied by the source card, so the license status is
`unknown-commercial-copyright`.

## Validation

From this project directory:

```text
/home/axel/.archon-env/bin/hgraph --root . sync --blueprint blueprint/src/content.tex --verbose
/home/axel/.archon-env/bin/hgraph --root . stats
/home/axel/.archon-env/bin/hgraph --root . site --out .blueprint-work/site/index.html
TEXINPUTS="$PWD/blueprint/src:" pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=.blueprint-work/build .blueprint-work/build/wrapper.tex
TEXINPUTS="$PWD/blueprint/src:" pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=.blueprint-work/build .blueprint-work/build/wrapper.tex
```

The final recursive audit is recorded under `.blueprint-work/audits/` and
checks duplicate labels and printed numbers, resolved `\ref`/`\cref` targets,
resolved `\uses`, source-page coverage, statement/proof pairing, and complete
137-page Luna ledger coverage.
