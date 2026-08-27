# Stacks Project provenance

Blueprint text under `FormalizedSources/StacksProject/` is adapted from the
[Stacks Project](https://stacks.math.columbia.edu/) LaTeX sources
([github.com/stacks/stacks-project](https://github.com/stacks/stacks-project)).

## License

The Stacks Project is licensed under the **GNU Free Documentation License,
Version 1.2 or any later version**, with **no Invariant Sections**, **no
Front-Cover Texts**, and **no Back-Cover Texts**. Copyright (C) 2005–2025
Johan de Jong and contributors. A copy of the license is in
[`GFDL-1.2.txt`](GFDL-1.2.txt).

Blueprint derivatives that incorporate Stacks wording remain under the GFDL.
Original Lean code, hgraph configuration, and website chrome in this repository
remain under the repository [Apache 2.0](../../../../../LICENSE) license.

## Adaptation policy (verbatim vs rephrased)

**Keep mathematical content source-faithful; adapt presentation for hgraph.**

| Keep from Stacks | Adapt for hgraph |
|---|---|
| Definitions, lemmas, theorems, proofs | Environment titles as `\begin{lemma}[Short title]` |
| Section order and mathematical wording | Stable labels: `schemes-definition-…` (chapter-prefixed) |
| Cross-references, resolved via tags when possible | `\uses{…}` edges instead of free-standing `\ref` only |
| Bibliographical intent | `\source{stacks:<TAG>}` / `\dcref{…}` provenance |
| Slogans (as optional titles) | Drop Stacks-only UI macros (`\phantomsection`, multicols book chrome) |

Do **not** lightly paraphrase definitions: Stacks tags and wording are the
shared reference language of the field. Rephrase only when required for
Lean-facing clarity, and record the Stacks tag on the statement.

## Tags

Stacks permanent tags (four-character codes such as `01HB`) are recorded with
`\source{stacks:01HB}` on each imported statement when the tag is known. The
upstream tag list is `tags/tags` in the stacks-project repository.
