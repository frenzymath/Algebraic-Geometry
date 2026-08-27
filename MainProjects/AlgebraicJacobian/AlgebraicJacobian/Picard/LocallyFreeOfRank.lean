/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Locally free of rank `d` for sheaves of modules on a scheme

Mathlib (at the pinned commit) carries no rank-indexed local freeness predicate for
sheaves of modules on a scheme, so it is built here.  This module is deliberately
minimal: the predicate is stated purely in mathlib vocabulary
(`AlgebraicGeometry.Scheme.Modules`, `Scheme.Modules.pullback`,
`SheafOfModules.free`), so nothing in the project needs to be built before it.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsLocallyFreeOfRank` — `M` is locally free of
  rank `d` when the underlying scheme admits an open cover trivializing `M`.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace SheafOfModules

/-- **Locally free of rank `d`** for a sheaf of modules on a scheme.

A sheaf of modules `M` on a scheme `X` is *locally free of rank `d`* when `X`
admits an open cover `{U i}` on each member of which the restriction
`M|_{U i}` (the pullback of `M` along the open immersion `(U i).ι`) is
isomorphic to the free module of rank `d`, `O_{U i}^{⊕ d}` (encoded as
`SheafOfModules.free (ULift (Fin d))` over the structure-ring sheaf of the
open subscheme `(U i).toScheme`).

This predicate is project-local: Mathlib does not supply a rank-indexed local
freeness predicate for sheaves of modules on a scheme. Blueprint:
`def:is_locally_free_of_rank` (Nitsure §1, Exercise (2)). -/
def IsLocallyFreeOfRank {X : Scheme.{u}} (M : X.Modules) (d : ℕ) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens), (⨆ i, U i = ⊤) ∧
    ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj M ≅
      _root_.SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin d)))

end SheafOfModules

end AlgebraicGeometry
