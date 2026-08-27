# Provenance

This is the clean blueprint port of the Algebraic Jacobian Challenge (AJC)
route from `LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge`.

Only mathematical source files were ported: the chapter inputs, the shared macro file, and the
hgraph configuration. Generated web/print output, LaTeX build products, declaration snapshots,
informal worksheets, scratch probes, and Lean build caches are intentionally excluded.

The original declaration names remain in `\\lean{...}` metadata where available. Every labelled
statement uses `\\dcref{custom}`: the route is a custom blueprint, not a transcription of a
single published theorem numbering. External inspiration and close adaptations are identified in
the prose with `\\cite{...}` and the complete bibliography in `blueprint/src/refs.bib`. No
synthetic source/page identifiers or manual `thebibliography` block are used. The blueprint is a
mathematical reference layer and does not claim that the corresponding Lean declaration is
compiled in this repository.
