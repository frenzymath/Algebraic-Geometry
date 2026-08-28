# Provenance: Altman--Kleiman, Compactifying the Picard Scheme

## Source and page map

This blueprint is an independent, source-faithful mathematical transcription
of Allen B. Altman and Steven L. Kleiman, *Compactifying the Picard Scheme*,
Advances in Mathematics 35 (1980), 50--112 (MR0555258).  The authoritative
local artifact is the read-only scan
`/home/axel/LeanAlgebraicGeometry-Horizon/references/MR0555258-compactifying-picard.pdf`.
The Horizon manifest and retrieval notes are also authoritative metadata:
`/home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml` and
`/home/axel/LeanAlgebraicGeometry-Horizon/references/_project-notes/MR0555258-Compactifying-Picard/summary.md`.
The five supplied TeX cross-checks are
`references/MR0555258-compactifying-picard/tex/page-0018.tex` through
`page-0022.tex`; they were used only to check the rendered scan.

The PDF has 63 physical pages.  Visual inspection of every page establishes
the constant map

```
physical page n  ->  printed page n + 49
```

Thus the mathematical body runs from printed page 53 (physical 4) through
printed page 111 (physical 62).  Physical pages 1--4 contain title and
introductory prose; physical page 63 is bibliography.  The ignored ledger and
page records under `.blueprint-work/transcriptions/` document all 63 visual
checks and identify the mathematical pages and omitted bibliography/prose.

## Blueprint coverage and metadata

The tracked source is `blueprint/src/content.tex`, organized into eight files
for Sections 1--8 in source order.  It retains definitions, conventions,
unnumbered mathematical constructions, all numbered results 1.1--8.8 and the
numbered remarks 4.4, 5.21, 7.5, and 7.7.  The examples (2.2, 8.9, and 8.10),
historical or pedagogical exposition, bibliography, and index are omitted as
permitted by the process prompt.  Proofs are separate `proof` environments
immediately following their statements.

Every mathematical node has a globally unique `akcp-` label.  Every numbered
node has exactly one `\dcref{...}` containing the printed coordinate alone
(for example `2.9`, never a page number or source prefix).  Every node has a
`\source{MR0555258-compactifying-picard:page-NNNN}` anchor using the physical
page ledger coordinate, and `\uses{...}` records explicit earlier blueprint
dependencies.  No `\lean`, `\leanok`, or `\mathlibok` claims are made.

## License status

The 1980 Academic Press scan is a copyrighted commercial publication.  The
local manifest and source card grant no redistribution license; public access
to the scan does not imply permission to redistribute it.  License status is
therefore **unknown-commercial-copyright / legal review required**.  This
repository contains no PDF, source image, extracted TeX, or full transcription;
the tracked blueprint is independently authored mathematical prose.  Rendered
pages, transcriptions, logs, generated graphs, and compilation artifacts remain
under ignored `.blueprint-work/` paths.

## Validation

From this project directory:

```text
HGRAPH=/home/axel/AlgebraicGeometry/.blueprint-work/milne-abelian-varieties/venv/bin/hgraph
$HGRAPH --root "$PWD" sync --blueprint "$PWD/blueprint/src/content.tex" --verbose
$HGRAPH --root "$PWD" stats
$HGRAPH --root "$PWD" site --out "$PWD/.blueprint-work/site/index.html"
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory .blueprint-work/build .blueprint-work/build/wrapper.tex
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory .blueprint-work/build .blueprint-work/build/wrapper.tex
```

The final audit also checks recursively that every file reachable from
`content.tex` is included, labels are unique, all `\uses` targets resolve,
numbered nodes have `\dcref`, all nodes have source anchors, and the 63-page
ledger has complete physical-page coverage.
