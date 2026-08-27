# Provenance: Mumford - Abelian Varieties

## Source

The primary source is David Mumford, *Abelian Varieties*, Tata Institute of
Fundamental Research Studies in Mathematics 5, published for TIFR by Oxford
University Press (1970; revised second edition 1974, with appendices by C. P.
Ramanujam and Yuri Manin).  The project uses the 290-page scanned second-edition
file already present in the read-only Horizon repository at
`references/mumford-abelian-varieties.pdf`.  The source card and page registry
are in Horizon's `references/mumford-abelian-varieties.md` and
`references/manifest.yaml`.

The Arabic body page `N` corresponds to PDF page `N+11`.  The contents map is
PDF pages 10--11; the mathematical body runs from book page 1 through the
appendices ending at page 275.  The blueprint keeps all source sections:
Chapters I (1--3), II (4--9), III (10--17), IV (18--24), Appendix I, and
Appendix II.  Bibliography and index are recorded in the source manifest but
are not mathematical chapters.

The rendered blueprint uses descriptive mathematical chapter and section names
so that its statements do not depend on the source's appendix or section
numbering.  Source division and page information remain available through the
stable labels, `\\dcref` anchors, and this provenance record.

## `\\dcref` anchor convention

`M` is the registered source identifier for Mumford's *Abelian Varieties*.
Each `\\dcref` uses a concise printed-coordinate anchor: `M:ch1:I.1` means
Chapter I, Section 1; `M:ch2:II.5` means Chapter II, Section 5; and the
explicitly numbered finite-complex main theorem of Section 5 is recorded as
`M:ch2:II.5.1`.
The appendices use `M:appI:I` and `M:appII:II`.  The scan and source card do
not expose reliable theorem numbers for most remaining items, so section
coordinates are used rather than invented numbers.  Page ranges are retained
in the source manifest and this provenance record for verification only.

## License and adaptation policy

The scanned commercial book's redistribution license is not stated in the
available manifest and has not been independently established.  It is therefore
treated as **unknown**.  No PDF, extracted source, page image, or source
transcription is copied into this repository.  The blueprint is an independent
expression of mathematical definitions, statements, dependency relations, and
reconstructed arguments, with source section/page anchors for verification.
Human legal review is required before distributing any wording substantially
closer to the source than the present mathematical paraphrase.  The repository's
original files are otherwise covered by the repository Apache 2.0 license; that
license does not change the status of the third-party source.

The Horizon cache contains vision transcriptions of the source pages used in
the current assembly.  PDF pages 0012--0290 were transcribed page-by-page from
rendered images.  The active blueprint assembly is source-faithful for Chapters
I--III (PDF pages 0012--0176), Chapter IV (PDF pages 0178--0250), Appendix I
(PDF pages 0251--0271), and Appendix II (PDF pages 0272--0286). This includes
the complete theta-group continuation, Tate's theorem and applications, and
the Mordell--Weil proof through the canonical height construction. Bibliography
and index pages 0287--0290 are cached but are not mathematical blueprint nodes.
These shared working artifacts are referenced by `\\source` anchors
and are not copied into this repository. Nodes
whose full proof is deferred by the source, or extends beyond the assembled
page range, carry `\\notready` rather than silently claiming a proof.

## Blueprint authorship and validation

All prose and mathematical organization in `blueprint/src/` was written for
this project.  Stable labels, concise printed-coordinate `\\dcref` anchors, and
explicit `\\uses` edges follow the hgraph blueprint conventions.  The retired
`\\group` metadata is intentionally absent.  Every labeled mathematical node
carries a `\\dcref` coordinate; page ranges remain in the source manifest and
provenance record.  No Lean declarations currently correspond to these nodes,
so no `\\lean` or `\\leanok` annotations are emitted.

Validation commands used for this project are:

```text
pip install "hgraph @ git+https://github.com/AxelDlv00/hgraph.git@d2e1fe51ea90e5854d689c4cebf26d00294e3190"
hgraph sync --manifest config.yaml
hgraph site --manifest config.yaml --out _site/index.html
TEXINPUTS=FormalizedSources/AbelianVarieties/Mumford/blueprint/src: \
  pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=.blueprint-work/mumford-abelian-varieties \
  .blueprint-work/mumford-abelian-varieties/compile-wrapper.tex
```

The wrapper is a temporary syntax/rendering smoke test because hgraph supplies
the final document wrapper and rendering CSS.  Mathematical coverage is audited against
`.blueprint-work/mumford-abelian-varieties/book-plan.yaml` and
`source-manifest.yaml`, which remain intentionally ignored by git.
