/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Sheaf condition along the structure-sheaf forget composite

Phase A step 1 (per `STRATEGY.md`): the `HasSheafCompose` instance for the
forget composite `CommRingCat ⥤ RingCat ⥤ AddCommGrpCat` on the Grothendieck
topology of opens of an arbitrary topological space. This is the gateway to
computing `H¹(C, O_C)` as an abelian group (and ultimately as a `k`-vector
space for the genus).

See `blueprint/src/chapters/Cohomology_SheafCompose.tex`.

## Status (closed iteration 003)

The single instance below is honestly closed (5-line body via
`Limits.comp_preservesLimits` + `hasSheafCompose_of_preservesLimitsOfSize`).
Phase A step 1 of `STRATEGY.md`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Cohomology

/-- The forget composite `CommRingCat ⥤ RingCat ⥤ AddCommGrpCat` preserves the
sheaf condition on the Grothendieck topology of opens of any topological space.
Equivalently: a sheaf of commutative rings on a topological space is in
particular a sheaf of abelian groups (post-composing with the forgetful is
sound). -/
instance instHasSheafCompose_forget_CommRing_AddCommGrp (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).HasSheafCompose
      (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u} ⋙
       CategoryTheory.forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  haveI : PreservesLimitsOfSize.{u, u}
      (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u} ⋙
        CategoryTheory.forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
    Limits.comp_preservesLimits _ _
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize _

end AlgebraicGeometry.Cohomology
