# Source-faithful blueprint process

Use this file as the common instruction set for every source project in
`FormalizedSources`. The project-local `CODEX_PROMPT.md` supplies the source
path, stable label prefix, and source-specific page map.

## Mission

Convert the named reference into a source-faithful hgraph blueprint. The
blueprint is an independent mathematical transcription and organization of the
reference, not an AI summary and not a list of only the most famous theorems.
Keep the mathematical content close to the order and level of detail of the
source. Remove only examples, exercises, bibliographies, indexes, and prose
whose purpose is historical, motivational, or pedagogical. Do not remove a
definition, convention, hypothesis, displayed calculation, unnumbered claim,
remark containing mathematical content, or proof merely because it is
unnumbered or appears in prose.

The result should be useful for later Lean formalization and should let a
reader check every node against the cited page of the original reference.
Never fill a gap from memory. If a page or formula is genuinely unreadable,
record the uncertainty in the private work log and mark the affected node
`\notready` until it has been checked.

## Page-by-page source reading

1. Read the project-local source card and this prompt before editing.
2. Inventory the complete PDF, including front matter and the end pages, and
   determine the mapping between physical PDF pages and printed page numbers.
3. Render every source page at a resolution at which subscripts, superscripts,
   accents, diagrams, and punctuation are legible. Dispatch the Luna vision /
   transcription subagent for every page (one page per request is preferred;
   batches are acceptable only when each output remains explicitly
   page-addressable). Ask Luna for an exact mathematical transcription, not a
   summary. Do not substitute ordinary OCR or a PDF text layer for the visual
   check.
4. Use bundled TeX or extracted text as a search and cross-check aid only.
   Resolve every discrepancy by looking again at the rendered page. Preserve
   the source's notation and visible typographical quirks when they affect the
   mathematics, while recording an unobtrusive clarification in the private
   work log when needed.
5. Maintain a private page ledger under `.blueprint-work/` containing the page
   image/transcription used, printed-page mapping, and unresolved questions.
   Do not copy PDFs, page images, or full source transcriptions into this
   repository.

## What to write

- Put the blueprint in modular chapter/section files under
  `blueprint/src/`, with a small `content.tex` that inputs them in source
  order. Keep files reasonably sized so a later page-level audit is possible.
- Preserve the source's own chapter, section, definition, theorem, lemma,
  proposition, corollary, remark, convention, construction, and hypothesis
  distinctions. Keep statements and their hypotheses complete. Include
  unnumbered statements and definitions; an unnumbered item must never be
  silently dropped just because hgraph cannot assign it a printed number.
- Keep every proof in a `proof` environment *outside* and immediately after
  its statement environment. Proofs must include the actual argument from the
  source, including reductions, constructions, diagram chases, calculations,
  and cited intermediate results; do not replace a proof with "standard" or
  "follows similarly". If the source defers a proof, say so explicitly and use
  `\notready` rather than inventing one.
- Retain formulas, quantifiers, side conditions, equivalences, and conclusion
  clauses exactly enough to preserve the theorem's meaning. Rephrase only
  authorial prose that is not mathematical content. It is fine, and often
  preferable, to leave a statement's mathematical wording nearly unchanged.
- Omit worked examples and exercises as units. If an example or exercise
  contains a general lemma, definition, or argument needed by a later result,
  extract that mathematical content into an ordinary node and cite its source
  page; do not include the pedagogical wrapper.

## Metadata rules

- Give every mathematical node a globally unique `\label{...}`. Use a stable
  source prefix and descriptive labels; never rename a label merely to make a
  sentence shorter.
- For every numbered statement, add exactly one `\dcref{PRINTED-NUMBER}`.
  Its complete value must be exactly the number printed by the source (for
  example `4.8`, `2.9`, `1.27`, `III.5.1`, or `4.1`), not a source-prefixed
  identifier or a chapter-local counter invented by the blueprint. Preserve
  compound numbering and lettered parts. Do not put a page number in
  `\dcref`. Unnumbered definitions, claims, and setup receive no fabricated
  `\dcref`; their `\source{...}` anchor still records the section/page
  evidence.
- Add `\source{SOURCE-SLUG:page-NNNN}` (or the exact source-sidecar anchor
  specified by the local prompt) to each node or coherent page block. Keep
  printed coordinates in the source metadata; never use a guessed coordinate.
- Add `\uses{label-a,label-b,...}` to every node whose statement or proof uses
  an earlier blueprint node. Include dependencies expressed by named results,
  explicit `\ref`/`\cref`/`\Cref`, definitions, hypotheses, and imported
  constructions. Do not add self-edges or merely topical edges. Audit all
  `\uses` after writing and eliminate every dangling target.
- Do not emit `\lean`, `\leanok`, or `\mathlibok` unless the corresponding
  declaration has actually been checked in the repository. Use `\notready` for
  source-deferred or unresolved mathematics, not as a substitute for reading.
- Avoid retired group/level metadata unless the project-local hgraph version
  explicitly requires it. Follow the syntax already used by the neighboring
  source projects.

## Verification and handoff

After each chapter and again at the end:

1. Run the project-local hgraph synchronizer and inspect warnings. Fix missing
   labels, malformed environments, duplicate labels, and dangling `\uses`.
2. Run a recursive audit over every file reachable from `content.tex`, not only
   the top-level chapter files. Check duplicate labels, unresolved refs,
   unresolved uses, missing `\dcref` on numbered statements, and source-page
   coverage.
3. Compile the assembled blueprint twice with `pdflatex` (or the repository's
   documented wrapper) so cross-references settle. Treat every LaTeX error or
   undefined reference as a defect to fix.
4. Compare the node inventory with the page ledger. In particular, check the
   first definition, all unnumbered mathematical assertions, every numbered
   result, and every proof. Do not declare completion from a clean compile
   alone.

Leave a concise `PROVENANCE.md` explaining the edition, exact local source
   paths, page mapping, coverage, `\dcref` policy, license status, and the
   validation commands. The final project must contain the blueprint source and
   metadata only; generated graphs, PDFs, logs, page images, and Luna working
   records belong under ignored `.blueprint-work/` paths.
