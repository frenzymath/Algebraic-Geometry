/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.Presheaf

/-!
# Sheaves of `k`-modules: the sheaf property and bundled structure sheaf

Sub-file (2/3) of the `StructureSheafModuleK` split (refactor iter-174). This file
discharges the sheaf condition for `toModuleKPresheaf` (helper 7) and bundles the
result as `toModuleKSheaf` (helper 8); the forget-and-recover natural iso to the
`AddCommGrpCat`-valued structure sheaf is also packaged here. The downstream
finite-length carriers live in the sibling `Carriers.lean`.

See `blueprint/src/chapters/Cohomology_StructureSheafModuleK.tex`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k]

/-- Phase A step 5 main, helper (7): the presheaf of (6) is a sheaf for the
Grothendieck topology of opens of `C.left.toTopCat`. -/
lemma toModuleKPresheaf_isSheaf (C : Over (Spec (CommRingCat.of k))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology C.left.toTopCat)
      (toModuleKPresheaf C) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget (ModuleCat.{u} k))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat.{u})).mp C.left.sheaf.property using 1 <;> rfl

/-- Phase A step 5 main: the structure sheaf of a `Spec k`-scheme as a sheaf
of `k`-modules. Bundles `toModuleKPresheaf` (helper 6) and
`toModuleKPresheaf_isSheaf` (helper 7) into the standard `Sheaf` shape. -/
noncomputable def toModuleKSheaf (C : Over (Spec (CommRingCat.of k))) :
    Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k) :=
  ⟨toModuleKPresheaf C, toModuleKPresheaf_isSheaf C⟩

/-- Phase A step 5 polish (iter-007): forget-and-recover natural iso between
the iter-006 `ModuleCat k`-valued structure sheaf and the iter-004
`AddCommGrpCat`-valued structure sheaf. The two sheaves agree on the nose at
the underlying-presheaf level: forgetting from `ModuleCat k` to `AddCommGrpCat`
via `forget₂` recovers the iter-004 `toAbSheaf C.left`. Closure body
`Iso.refl _`; probe-confirmed (`lean_run_code`, iter-007 plan-agent). -/
noncomputable def toModuleKSheaf_forgetCompare
    (C : Over (Spec (CommRingCat.of k))) :
    (sheafCompose (Opens.grothendieckTopology C.left.toTopCat)
        (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})).obj (toModuleKSheaf C)
      ≅ toAbSheaf C.left :=
  Iso.refl _

end AlgebraicGeometry.Scheme
