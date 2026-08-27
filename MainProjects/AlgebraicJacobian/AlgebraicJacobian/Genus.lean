/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.Carriers
import AlgebraicJacobian.Cohomology.StructureSheafModuleK

/-!
# Genus of a smooth proper curve

The genus of a smooth, proper, geometrically irreducible curve over a field.

## Status (closed iteration 011 — `genus`)

The iter-011 refactor added the `noncomputable` modifier (user-authorised
`2026-05-07`) and an import of `AlgebraicJacobian.Cohomology.StructureSheafModuleK`
so the body uses the project's `ModuleCat k`-flavoured cohomology
`Scheme.HModule` (iter-009) of the structure sheaf
`Scheme.toModuleKSheaf` (iter-006). The body is the probe-confirmed
one-liner

    Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1)

which is the honest mathematical definition `dim_k H^1(C, O_C)`.

See `blueprint/src/chapters/Genus.tex` for the informal proof sketch and
`.archon/STRATEGY.md` for the multi-phase build-out plan.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The genus of a smooth proper curve. -/
noncomputable def genus {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] : ℕ :=
  Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1)

end AlgebraicGeometry
