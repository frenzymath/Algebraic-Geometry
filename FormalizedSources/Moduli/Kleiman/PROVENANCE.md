# Steven L. Kleiman, *The Picard Scheme*

This blueprint transcribes the mathematical body of the arXiv v1 / Trieste
lectures version (math/0504020, 1 April 2005), corresponding to the chapter in
*Fundamental Algebraic Geometry: Grothendieck's FGA Explained* (AMS 2005,
pp. 235--321). The authoritative local files are
`/home/axel/LeanAlgebraicGeometry-Horizon/references/kleiman-picard.pdf`,
`.../kleiman-picard-src/kleiman-picard.tex`, and the focused
`.../Kleiman_The_Picard_Scheme_Theorem-4.8.tex`; metadata is in
`.../manifest.yaml`. The source PDF has 83 physical pages, with physical and
printed pagination agreeing (offset zero).

The blueprint covers Sections 2--6 and the mathematically used Appendix B in
source order: the several Picard functors, relative effective divisors,
Picard-scheme representability, $\Pic^0$/Jacobians, $\Pic^\tau$ finiteness,
and the basic intersection theory used by Section 6. The introduction's
historical narrative is omitted, but its mathematical assertions about Abelian
integrals, Jacobians, surface invariants, and the Picard/Albanese construction
are retained.
Worked examples, Appendix A exercise answers, bibliography, and index are
omitted, except where an exercise/example carries a mathematical assertion
needed to state the theory. Every numbered item
retains its printed coordinate in exactly one `\dcref`; unnumbered setup and
remarks have no fabricated coordinate. Each node has a
`kleiman-picard:page-NNNN` source anchor and dependencies are encoded with
`\uses`.

The complete page-by-page visual pass was dispatched to Luna agents for pages
1--28, 29--56, and 57--83. Their rendered-page evidence and transcriptions are
private ignored records under `.blueprint-work/`; no PDF, image, or full source
transcription is included in this project. The source is copyrighted; this
repository contains an independently authored mathematical blueprint only.

Validation from this project directory:

```text
PYTHONPATH=/home/axel/HyperGraph python3 -m hgraph --root . sync --verbose
PYTHONPATH=/home/axel/HyperGraph python3 -m hgraph --root . stats
PYTHONPATH=/home/axel/HyperGraph python3 -m hgraph --root . site --out .blueprint-work/site/index.html
TEXINPUTS=blueprint/src//: pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.blueprint-work blueprint/src/content.tex
TEXINPUTS=blueprint/src//: pdflatex -interaction=nonstopmode -halt-on-error -output-directory=.blueprint-work blueprint/src/content.tex
```

The generated graph, site, PDF, logs, and Luna records belong under the ignored
`.blueprint-work/` directory.
