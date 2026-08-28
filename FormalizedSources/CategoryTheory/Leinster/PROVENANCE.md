# Provenance: Leinster - Basic Category Theory

The blueprint transcribes Tom Leinster, *Basic Category Theory*, Cambridge
Studies in Advanced Mathematics 143 (Cambridge University Press, 2014),
open-access arXiv edition arXiv:1612.09375v2 (26 August 2025), released under
CC BY-NC-SA 4.0. The authoritative local source is the read-only file
`/home/axel/LeanAlgebraicGeometry-Horizon/references/leinster-basic-category-theory.pdf`;
the source card is
`/home/axel/LeanAlgebraicGeometry-Horizon/references/leinster-basic-category-theory.md`.

The PDF has 191 physical pages. Front matter occupies PDF pages 1--16; the
mathematical body starts at PDF page 17 (printed page 9). For body pages the
verified mapping is `printed page p = PDF page p + 8`; appendix pages follow the
same offset. PDF pages 179--181 contain the GAFT appendix; PDF pages 182--191
contain further reading and indexes and are recorded in the private ledger but
omitted from the blueprint. Every PDF page
was rendered under `.blueprint-work/page-renders/` and dispatched to a Luna
vision/transcription worker; page-addressable records are under
`.blueprint-work/luna/`. The private ledger is
`.blueprint-work/page-ledger.tsv`.

Coverage follows Chapters 1--6 and the appendix in source order: categories,
functors and natural transformations; adjoints; sets; representables and the
Yoneda lemma; limits and colimits; adjoint/representability applications; and
the proof of GAFT. Definitions, universal properties, numbered results,
unnumbered mathematical assertions, diagrams expressed algebraically, and
proof arguments are retained. Examples, exercises, bibliography, index, and
non-mathematical exposition are omitted. Numbered items use exactly the
printed coordinate in `\dcref{...}`; every mathematical node has a stable
`lbc-` label, a `\source{leinster-basic-category-theory:page-NNNN}` anchor, and
explicit `\uses{...}` dependencies.

Validation was run from this directory:

```text
/home/axel/.archon-env/bin/hgraph --root . sync --blueprint blueprint/src/content.tex --verbose
/home/axel/.archon-env/bin/hgraph --root . stats
TEXINPUTS=blueprint/src: pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.blueprint-work .blueprint-work/compile.tex
TEXINPUTS=blueprint/src: pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.blueprint-work .blueprint-work/compile.tex
```

The generated hgraph nodes/edges, rendered PDF, logs, page images, and Luna
records are intentionally ignored and remain under `.blueprint-work/` or
`hgraph/`; only source and provenance files are tracked.
