# Algebraic Jacobian

This custom flagship project contains two blueprint routes for constructing the
Algebraic Jacobian:

- `MilneKollar/`: the Picard-scheme construction following Milne-Kollar;
- `PicardAlbanese/`: the etale Picard, Albanese, and Jacobian construction.

The short names AJC and AJCR are retained only as provenance aliases for the
upstream projects. The route names use their mathematical constructions so they
remain clear in the workspace site and in future Lean namespaces. Each route
has a concise, AI-authored book-style blueprint assembled from its route-local
BibTeX references, plus a source-faithful formalization companion containing
the intermediary record. The indexed route keeps the nontrivial mathematics
and proofs needed for formalization, but does not reproduce standard
definitions, routine properties, or every Lean declaration. A mathematical
node may therefore correspond to several Lean declarations. External results
use BibTeX keys with \\cite{...}, internal statements use \\ref{...}, and
source-backed nodes use their printed reference in \\dcref; custom is appended
only for a genuine specialization or synthesis. Generated graphs, rendered
PDFs, declaration snapshots, scratch files, and Lean caches are excluded.

## Lean libraries

Each route owns its Lean package. The two packages intentionally use the same
`AlgebraicJacobian.*` namespace, but are built from separate directories and
therefore never mix declarations or build products.

`MilneKollar/` contains the legacy challenge implementation ported from
`MainProjects/Algebraic-Jacobian-Challenge` (387 library modules plus its root
module). The source package's root target is:

```bash
cd MilneKollar
lake build AlgebraicJacobian
```

The ported route has also been checked with the smaller
`lake build AlgebraicJacobian.Genus` target; a fresh root build can be much
slower because it elaborates the entire challenge cone.

`PicardAlbanese/` contains the newer from-scratch implementation ported from
`MainProjects/Algebraic-Jacobian-Challenge-Rebuild` (1,180 library modules).
The full Horizon root remains an active development cone, so the route keeps
all source modules available for explicit targets; the verified stable target
is:

```bash
cd PicardAlbanese
lake build AlgebraicJacobian.Algebra.TwoLattice
```

Both packages retain the Horizon declarations and their named `sorry`
obligations. A successful compile is not a claim that the open mathematical
milestones are proved.

The workspace-level `shared/` directory remains reserved for genuinely
source-independent declarations. No Algebraic Jacobian module was moved there
because these libraries still depend on their challenge-specific APIs.
