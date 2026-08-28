# Provenance

This route is an AI-authored mathematical blueprint for the Milne--Koll'ar
Picard-scheme construction of the Jacobian. It was assembled from the
references in blueprint/src/refs.bib and from the source-faithful Horizon
blueprint that mirrors the associated Lean development.

The indexed chapters are a concise, book-style account of the route. They
retain the nontrivial definitions, constructions, interfaces, and proofs that
guide the formalization, while omitting standard library facts and mechanical
transport. The complete source-faithful intermediary record remains available
in blueprint/src/content-formalization.tex and blueprint/src/chapters/detail/.
There is no one-to-one node/declaration requirement: one mathematical node may
be implemented by several Lean declarations and auxiliary proofs.

Source-backed nodes use their printed reference in \dcref; genuinely
project-specific adaptations may append custom. Bibliography citations use
BibTeX keys with \cite{...}, and internal dependencies use \ref{...}.

The route-local Lean package is the 387-module port of Horizon's
`MainProjects/Algebraic-Jacobian-Challenge`. Its pinned Lake metadata lives
beside this file; Horizon probes, scratch files, generated graphs, and build
products are not copied.
