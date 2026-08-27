<h1 align="center">Algebraic Geometry</h1>
<p align="center">
  Frenzymath - PKU@AI4Math
</p>

<div align="center">

[![Website: Live](https://img.shields.io/badge/Website-Live-0f766e?style=flat-square)](https://frenzymath.github.io/Algebraic-Geometry/)
[![Status: Active](https://img.shields.io/badge/Status-Active-0f766e?style=flat-square)](#current-state)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow?style=flat-square)](LICENSE)
</div>

<p align="center">
  A shared hgraph workspace for source-faithful formalizations in algebraic geometry,<br>
  reusable Lean infrastructure, and flagship challenges.
</p>

> [!IMPORTANT]
> The workspace currently registers 11 active projects: the eight Stacks
> Project parts plus the Mumford, Milne, and Hartshorne reference blueprints.
> The source statements are indexed in hgraph; Lean declarations are added
> incrementally and are never claimed before they exist.

## The programme

The workspace is organized around three complementary layers:

- source-faithful formalizations of books, papers, and online references;
- source-independent infrastructure that can be reused across developments;
- flagship projects organized by mathematical dependency rather than by one
  source's chapter order.

The Algebraic Jacobian Challenge is the flagship direction. Stacks Project
routes follow the eight imported official parts on
[stacks.math.columbia.edu/browse](https://stacks.math.columbia.edu/browse).

## Repository structure

```text
shared/                  source-independent reusable infrastructure
MainProjects/            flagship formalizations
FormalizedSources/       source-faithful reference projects
config.yaml              hgraph workspace and website manifest
overview.html            hgraph landing-page content
site/algebraic-geometry.css  workspace-wide hgraph style override
```

## Formalization projects

| Project | Role |
|---|---|
| [`MainProjects/AlgebraicJacobian`](MainProjects/AlgebraicJacobian/) | Flagship algebraic-Jacobian challenge |
| [`shared/`](shared/) | Source-independent reusable Lean infrastructure |
| [`FormalizedSources/StacksProject/`](FormalizedSources/StacksProject/) | **8** part-level projects containing all **109** Stacks chapters |
| [`FormalizedSources/AbelianVarieties/Mumford`](FormalizedSources/AbelianVarieties/Mumford/) | Mumford's geometric treatment of abelian varieties |
| [`FormalizedSources/AbelianVarieties/Milne`](FormalizedSources/AbelianVarieties/Milne/) | Milne's geometric and arithmetic treatment |
| [`FormalizedSources/Curves/Hartshorne`](FormalizedSources/Curves/Hartshorne/) | Curves, divisors, and cohomology |

Stacks source chapter inventory (aggregated into one hgraph project per part):

| Part | Chapters |
|---|---:|
| 1 Preliminaries | 25 |
| 2 Schemes | 16 |
| 3 Topics in Scheme Theory | 23 |
| 4 Algebraic Spaces | 17 |
| 5 Topics in Geometry | 8 |
| 6 Deformation Theory | 4 |
| 7 Algebraic Stacks | 14 |
| 8 Topics in Moduli Theory | 2 |

## Formalization groups

| Group | Role |
|---|---|
| `MainProjects/` | Flagship formalizations organized by mathematical dependency |
| `shared/` | Lean declarations independent of one particular source |
| `Stacks/` | One hgraph group containing the eight Stacks part projects |
| `AbelianVarieties/` | Mumford, Milne, and related abelian-variety sources |
| `Curves/` | Curves, divisors, differentials, and Riemann-Roch |

Each Stacks part project aggregates numbered chapter files adapted from the
upstream LaTeX. The parent part route is the registered hgraph project; there
are no child project directories. Future routes can remain `planned: true`
until their blueprint or Lean sources exist.

## Current state

The current workspace provides:

- 11 registered hgraph project routes, including eight Stacks part projects;
- **109** Stacks chapter blueprints covering Parts 1–8 completely;
- source blueprints for Mumford, Milne, and Hartshorne;
- a workspace-level visual theme distinct from the default Poincare styling;
- GFDL provenance tracking for Stacks text and Apache 2.0 for original code.

## hgraph website

Build the static site from the repository root:

```bash
hgraph site --manifest config.yaml --out _site/index.html
```

Serve it live while working on a blueprint:

```bash
hgraph serve --manifest config.yaml --port 8000
```

`hgraph serve` prints the URL but does not open a browser. It binds to
`127.0.0.1` by default, which is the VM itself when this workspace runs on a
remote machine. Use SSH port forwarding to view it locally, or bind explicitly
with `--host 0.0.0.0` only on a trusted network.

The workspace-wide CSS override is declared in `config.yaml` and kept in
`site/algebraic-geometry.css`. hgraph inlines it into the document head in both
the static landing page and live project routes.

## Contributing

Contributions should start by defining the mathematical scope and the source
provenance of a future project. Add its root to `config.yaml`. Stacks chapters
belong under the matching `PartXX_…/` directory; update that part's aggregate
`blueprint/src/content.tex` when adding a chapter. Add a project-local
`hgraph/config.yaml` when the project has blueprint or Lean sources to
synchronize.

Keep source-faithful developments separate from the shared library and keep
flagship projects organized by their dependency structure. Reviews should make
the mathematical source, formalization status, and remaining assumptions clear.

## Provenance and license

This is an independent formalization workspace. Original Lean, blueprint
scaffolding, and website code is licensed under [Apache 2.0](LICENSE).
**Stacks Project mathematical text** incorporated into blueprints remains under
the **GNU Free Documentation License 1.2+** (no invariant sections); see
the per-Part provenance files, for example
[`FormalizedSources/StacksProject/Part01_Preliminaries/blueprint/src/PROVENANCE.md`](FormalizedSources/StacksProject/Part01_Preliminaries/blueprint/src/PROVENANCE.md).
Other third-party source material remains subject to its original license.
