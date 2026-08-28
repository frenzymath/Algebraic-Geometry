# Provenance: FGA Explained

Status: complete blueprint transcription and validation.  The generated
numbered supplements were rebuilt from the page-addressable Luna ledger so
that each statement body is source-backed and each proof is in a separate
`proof` environment; source locations without a printed proof remain marked
`\notready` rather than being filled with an invented argument.

The source is B. Fantechi, L. Gottsche, L. Illusie, S. L. Kleiman and
N. Nitsure, *Fundamental Algebraic Geometry: Grothendieck's FGA Explained*,
AMS Mathematical Surveys and Monographs 123 (2005).  The authoritative local
files are the read-only PDF
`/home/axel/LeanAlgebraicGeometry-Horizon/references/fga-explained.pdf` and
its source card
`/home/axel/LeanAlgebraicGeometry-Horizon/references/fga-explained.md`.
The PDF contains 352 physical pages and has an extractable text layer; the
text layer was used only for locating passages.

The printed-page coordinate is related to the PDF coordinate by
`pdf page = printed page + 10`.  The private page ledger and rendered images
under `.blueprint-work/fga-explained/` cover physical pages 1--352, including
the front matter, appendices, bibliography, index, and back matter.  The
mathematical blueprint follows Chapters 1--9 in source order and covers PDF
pages 17--310.  PDF pages 115--116 and 189--190 are the two non-mathematical
part-divider pages in that interval and are intentionally not transcribed.
Exercises, worked examples, historical or motivational prose, bibliography,
and index entries are omitted; mathematical assertions occurring in those
contexts are retained as ordinary nodes.

Every numbered source statement has exactly one `\dcref{PRINTED-NUMBER}` with
the book's number (including compound numbers), a globally unique `fga-`
label, and one or more `\source{fga-explained:page-NNNN}` anchors using the PDF
page.  Unnumbered setup and assertions have no fabricated `\dcref`.  Each
node carries a `\uses{...}` list for actual earlier-node dependencies.  No
Lean declarations are claimed: the blueprint emits no `\lean`, `\leanok`, or
`\mathlibok` markers.  Source excerpts, rendered pages, and generated graphs
remain only in ignored `.blueprint-work/` paths; the AMS volume is
copyrighted and no source PDF or full transcription is redistributed here.

Validation performed in this project:

* Three Luna vision/transcription ledgers cover pages 1--120, 121--240, and
  241--352, with 352 matching rendered page images.
* Recursive source audit: 392 unique labels, 375 unique `\dcref` values,
  372 numbered source headings represented, 348 resolving `\uses` edges, no
  duplicate labels or dcrefs, no unresolved refs, and no missing mathematical
  source pages beyond the four documented divider pages.
* hgraph synchronizer (commit
  `d2e1fe51ea90e5854d689c4cebf26d00294e3190`):
  `.blueprint-work/venv/bin/hgraph --root . sync --blueprint
  blueprint/src/content.tex --verbose`, producing 383 blueprint nodes and
  348 generated hard edges with no warnings.
* The assembled wrapper
  `.blueprint-work/fga-explained/build/main.tex` was compiled twice with
  `pdflatex -interaction=nonstopmode -halt-on-error`; both runs succeeded and
  the second run settled cross-references.  Only non-fatal overfull-box
  warnings remain.
