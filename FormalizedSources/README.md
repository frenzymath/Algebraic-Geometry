# Formalized Sources

Source-faithful projects are grouped by mathematical area. Each project will
eventually have its own blueprint and Lean package; Stacks Project chapters
already ship hgraph blueprints adapted from the upstream LaTeX.

The source groups are `StacksProject`, `AbelianVarieties`, `Curves`,
`Moduli`, `CommutativeAlgebra`, and `CategoryTheory`.
The Algebraic Jacobian Challenge is a custom flagship project and lives under
`MainProjects/AlgebraicJacobian`, alongside its future Lean implementation.

The shared [blueprint process prompt](BLUEPRINT_PROCESS_PROMPT.md) records the
page-by-page Luna transcription workflow and the source-fidelity rules agreed
for this workspace. Each planned source project has a copy-ready
`CODEX_PROMPT.md` naming its exact Horizon reference path.

`StacksProject/` follows the eight imported official Stacks parts
([browse](https://stacks.math.columbia.edu/browse)). Each matching part
directory is a single hgraph project and blueprint; its numbered chapter files
live directly under blueprint/src/ (for example
Part02_Schemes/blueprint/src/ch01-schemes.tex).

Planned source projects:

- Tier A: `Moduli/Kleiman`, `Moduli/Nitsure`,
  `Moduli/AltmanKleiman`, and `Curves/Papaioannou`;
- Tier B: `Moduli/FGAExplained`;
- Tier C: `CommutativeAlgebra/Matsumura`,
  `CommutativeAlgebra/AtiyahMacdonald`, and `CategoryTheory/Leinster`.
