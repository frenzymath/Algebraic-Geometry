# Provenance: Milne - Abelian Varieties

## Source and coverage

The source is J. S. Milne, *Abelian Varieties*, course notes version 2.00
(2008), available from the author's course-notes page at
<https://www.jmilne.org/math/CourseNotes/av.html>; the retrieved PDF artifact
is <https://www.jmilne.org/math/CourseNotes/AV.pdf>.
The local, read-only Horizon cache supplies the referenced PDF.  The PDF has
172 pages (notes pages 1--166 plus front matter).  Three independent visual
transcription passes covered every PDF page; their working records are kept
outside the tracked source under `.blueprint-work/milne-transcription/`.
The blueprint covers the mathematical statements and proof arguments in all
mathematical sections of Chapters I--IV.  The Appendix review, bibliography,
index, and purely historical or pedagogical prose are omitted.
Theorem-like statements are closed before their external `proof` environments;
source-deferred results are identified explicitly rather than assigned guessed
arguments.  The Shafarevich item retained from Chapter III is a conjecture and
is marked `\\notready`.

The source's printed section coordinates are retained in `\dcref` metadata.
Page ranges and PDF offsets are recorded here and in the work-area source map,
never in `\dcref` values.  The notes-page to PDF-page offset is +6 for the
body (for example, printed page 8 is PDF page 14).

## License status

The PDF states: “Copyright c 1998, 2008 J.S. Milne. Single paper copies for
noncommercial personal use may be made without explicit permission from the
copyright holder.”  This is not a general redistribution license.  The
author's web page provides access to the notes but does not grant broader
rights in the materials inspected.  License status is therefore **restricted /
unclear**.  This repository contains no copy of the PDF, page images, extracted
TeX, or source transcription.  The blueprint prose is independently authored
and expresses mathematical facts, definitions, and proof structures rather than
reproducing source wording.  Legal review is required before distributing
adaptations beyond the repository's own use.

## Authorship and metadata policy

All prose and organization in `blueprint/src/` were written for this project.
Each labeled mathematical node has exactly one concise printed-coordinate
`\dcref` using the registered identifier `MI`; chapter and section numbers are
used when a theorem number is not reliably exposed.  `\source` values identify
the Milne notes and printed section/page evidence.  `\uses` records blueprint
dependencies.  The obsolete group metadata macro is not used, and page-range anchors
are not used as `\dcref` values.

## Working records and validation

Temporary inventories, source maps, rendered pages, logs, and reports live only
under `.blueprint-work/milne-abelian-varieties/` and are ignored by the root
`.gitignore`.  Horizon files were treated as read-only.  The final project is
validated with the repository's hgraph parser/synchronizer and rendered site,
plus a local LaTeX smoke test where available.  The accepted chapter statuses
and node counts are maintained in the temporary `book-plan.yaml`; this file is
not part of the tracked blueprint.
