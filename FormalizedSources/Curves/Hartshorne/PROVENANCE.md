# Hartshorne, *Algebraic Geometry*

## Source identification

The source is Robin Hartshorne, *Algebraic Geometry*, Graduate Texts in
Mathematics 52, Springer-Verlag, New York, 1977 (first edition, XVI+496
printed pages). The official publisher record is [Springer Nature,
DOI 10.1007/978-1-4757-3849-0](https://link.springer.com/book/10.1007/978-1-4757-3849-0).
The registered Horizon slug is `hartshorne-algebraic-geometry` and the short
source identifier used by this blueprint is `HA`.

## Materials consulted

The read-only Horizon repository was consulted at:

- `/home/axel/LeanAlgebraicGeometry-Horizon/references/hartshorne-algebraic-geometry.pdf`;
- `/home/axel/LeanAlgebraicGeometry-Horizon/references/hartshorne-algebraic-geometry.md`;
- `/home/axel/LeanAlgebraicGeometry-Horizon/references/manifest.yaml`;
- `/home/axel/LeanAlgebraicGeometry-Horizon/references/hartshorne-algebraic-geometry/tex/`;
- `/home/axel/LeanAlgebraicGeometry-Horizon/references/hartshorne-algebraic-geometry/pages/`.

The PDF is a 514-page scanned-image file with no dependable text layer. The
contents were visually checked at PDF pages 10--12. For the Arabic body, the
verified mapping is printed page `N` to PDF page `N+17`; Roman front matter has
a separate offset. Existing vision transcriptions were used before any page
rendering. No OCR was used for mathematical transcription. Only temporary
rendered contents and worker notes were written under
`.blueprint-work/hartshorne-algebraic-geometry/`.

## Coverage

The blueprint follows the complete mathematical body in order: Chapters I--V
(8, 9, 12, 6, and 6 sections) followed by Appendices A--C (5, 5, and 4
sections). The body is PDF pages 18--475 (printed pages 1--458 under the
verified +17 offset), and every page is assigned to a page-level visual
transcription ledger under the ignored `.blueprint-work` directory. The
bibliography, results-from-algebra cross-reference list, glossary, and index
are excluded because they add no new proofs or statement content. Only source
examples, exercises, and authorial/pedagogical prose are omitted from the
source-faithful blueprint. Definitions, hypotheses, displayed formulas,
unnumbered mathematical assertions, numbered results, and their proof arguments
are retained in book order.

## License and authorship

The commercial Springer edition is protected by copyright. The available
Horizon manifest and source card do not grant a redistribution license, so the
license status is recorded as **unknown-commercial-copyright** pending legal
review. Public availability of a scan does not imply permission to redistribute
it. This repository contains no PDF, page image, extracted TeX, or Horizon
transcription. Every paragraph in the blueprint is independently authored and
reconstructs mathematical statements and proof dependencies without copying
source wording.

## Validation

The project-local hgraph configuration is `hgraph/config.yaml`. Validation uses
the repository's hgraph executable (created in the temporary work directory):

```text
HGRAPH=.blueprint-work/hartshorne-algebraic-geometry/venv/bin/hgraph
$HGRAPH --root FormalizedSources/Curves/Hartshorne sync \
  --blueprint /home/axel/AlgebraicGeometry/FormalizedSources/Curves/Hartshorne/blueprint/src/content.tex \
  --verbose
$HGRAPH --root FormalizedSources/Curves/Hartshorne stats
$HGRAPH --root FormalizedSources/Curves/Hartshorne site \
  --out /home/axel/AlgebraicGeometry/.blueprint-work/hartshorne-algebraic-geometry/site/index.html
```

The LaTeX smoke test is run through a temporary wrapper under the same ignored
work directory with `pdflatex` until references are stable. Automated audits
check duplicate labels, dangling `\uses`, undefined macros, bibliography
errors, stale source slugs, page/PDF anchors, and the absence of retired group
and level metadata.

## Coordinate policy

Every numbered theorem, proposition, lemma, and corollary carries a `\dcref`
equal to its printed book coordinate, such as `I.3.7`, `III.5.1`, or `IV.1.3`.
Unnumbered definitions and setup have no fabricated `\dcref`; their `\source`
field retains the printed section coordinate. The page-level ledgers record the
PDF and printed pages used for visual verification. No synthetic `HA:ch...`
coordinate is used.

Proofs are represented by `proof` environments placed immediately after, and
outside, the theorem-like environment containing the statement.

Dependency metadata follows the same source-faithful policy. Every explicit
internal `\ref`, `\cref`, `\Cref`, and named printed result used by a statement
or its proof is mirrored by a `\uses{...}` edge. Definitions and foundational
results introduce their terminology without fabricated prerequisites; they gain
`\uses` edges when they depend on an earlier blueprint node.
