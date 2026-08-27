/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Sites.Abelian
import Std.Tactic.BVDecide.LRAT.Internal.Clause
import AlgebraicJacobian.Cohomology.SheafCompose

/-!
# Structure sheaf as a sheaf of abelian groups, sheafification and Ext

Phase A steps 2–4 (per `STRATEGY.md`): the `HasSheafify` and `HasExt`
instances on the topology of opens of an arbitrary topological space (valued
in `AddCommGrpCat`), together with the structure sheaf of a scheme viewed as
a sheaf of abelian groups via the iter-004 `HasSheafCompose` instance.

See `blueprint/src/chapters/Cohomology_StructureSheafAb.tex`.

## Status (closed iteration 004)

All three declarations are honestly closed by the iter-004 multilane prover
round (lanes anthropic + deepseek; merged commit `2686f4e`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Cohomology

/-- Phase A step 2: sheafification on the topology of opens of any
topological space, valued in `AddCommGrpCat`. -/
instance instHasSheafify_Opens_AddCommGrp (X : TopCat.{u}) :
    CategoryTheory.HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{u} :=
  inferInstance

/-- Phase A step 3: `Ext` on the sheaf category. The universe annotation
`HasExt.{u+1}` is forced by the morphism universe of
`Sheaf (Opens.gT X) AddCommGrpCat.{u}`; other annotations produce a
`HasExt.{max ?u_1 ?u_2, ?u_2, ?u_1}` mismatch. -/
noncomputable instance instHasExt_Sheaf_Opens_AddCommGrp (X : TopCat.{u}) :
    CategoryTheory.HasExt.{u+1}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}) :=
  CategoryTheory.HasExt.standard _

end AlgebraicGeometry.Cohomology

namespace AlgebraicGeometry.Scheme

/-- Phase A step 4 first half: the structure sheaf of a scheme, viewed as a
sheaf of abelian groups via the iter-004 `HasSheafCompose` instance for the
forget composite `CommRingCat → RingCat → AddCommGrpCat`. -/
noncomputable def toAbSheaf (C : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology C.toTopCat)
      AddCommGrpCat.{u} :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology C.toTopCat)
    (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u} ⋙
      CategoryTheory.forget₂ RingCat.{u} AddCommGrpCat.{u})).obj C.sheaf

end AlgebraicGeometry.Scheme
