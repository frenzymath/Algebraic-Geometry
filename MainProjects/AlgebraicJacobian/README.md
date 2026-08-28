# Algebraic Jacobian

This custom flagship project contains two blueprint routes for constructing the
Algebraic Jacobian:

- `MilneKollar/`: the Picard-scheme construction following Milne-Kollar;
- `PicardAlbanese/`: the etale Picard, Albanese, and Jacobian construction.

The short names AJC and AJCR are retained only as provenance aliases for the
upstream projects. The route names use their mathematical constructions so they
remain clear in the workspace site and in future Lean namespaces. Each route
contains a concise, AI-authored mathematical blueprint assembled from its
route-local BibTeX references. External results are cited with
`\\cite{...}`, internal statements use `\\ref{...}`, and every node
records its printed source number with `\\dcref{...}`; custom is appended only
for a genuine specialization or synthesis. Generated graphs, rendered PDFs,
declaration snapshots, scratch files, and Lean caches are excluded.

## Lean library

The package root also contains the compiled AJ implementation under
`AlgebraicJacobian/`. It is the source AJ library ported from the original
challenge package, with its pinned `lakefile.toml`, `lake-manifest.json`, and
`lean-toolchain`. It currently contains 388 library modules and is deliberately
kept separate from the two blueprint routes so that their source-faithful
statements do not get confused with compiled declarations.

From this directory, run:

```bash
lake build AlgebraicJacobian
```

The package currently builds successfully. Existing named `sorry` obligations
and linter warnings remain visible in the build output; this port does not claim
the open mathematical milestones are proved. The workspace-level `shared/`
directory remains reserved for genuinely source-independent declarations. No
AJ module was moved there because this library is still organized around the
challenge namespace and its source-specific APIs.
