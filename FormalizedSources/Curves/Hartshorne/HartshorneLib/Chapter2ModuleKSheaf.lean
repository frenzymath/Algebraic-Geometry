/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Sheaves

/-!
# The structure sheaf as a module over the base field

For a scheme over `Spec k`, this file records the canonical `k`-action on every
section of the structure sheaf and packages the structure sheaf as a sheaf of
`ModuleCat k`.  The action is carried by an explicit map rather than a global
`Algebra` instance, avoiding the overlapping scalar structures that arise from
the tautological `Over` instance on affine schemes.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))]

/-- The structure morphism at the level of sections over an open. -/
noncomputable def Scheme.overAlgebraMap (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom

lemma Scheme.overAlgebraMap_naturality {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    ((X.presheaf.map i).hom).comp (X.overAlgebraMap k U.unop) =
      X.overAlgebraMap k V.unop := by
  rw [Scheme.overAlgebraMap, Scheme.overAlgebraMap, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc, ← X.presheaf.map_comp]
  congr 1

lemma Scheme.overAlgebraMap_apply_res {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : k) :
    (X.presheaf.map i).hom (X.overAlgebraMap k U.unop r) =
      X.overAlgebraMap k V.unop r :=
  DFunLike.congr_fun (X.overAlgebraMap_naturality k i) r

/-- Restriction of scalars along `overAlgebraMap`, kept local at use sites. -/
@[reducible] noncomputable def Scheme.overModule (U : X.Opens) : Module k Γ(X, U) :=
  (X.overAlgebraMap k U).toModule

attribute [local instance] Scheme.overModule

lemma Scheme.overModule_smul_def {U : X.Opens} (r : k) (s : Γ(X, U)) :
    r • s = X.overAlgebraMap k U r * s := rfl

/-- The structure sheaf viewed as a presheaf of `k`-modules. -/
noncomputable def Scheme.moduleKPresheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k Γ(X, U.unop)
  map {U V} i := ModuleCat.ofHom
    { toFun := (X.presheaf.map i).hom
      map_add' := map_add _
      map_smul' := fun r s ↦ by
        simp only [Scheme.overModule_smul_def, map_mul, RingHom.id_apply,
          X.overAlgebraMap_apply_res k i r] }
  map_id U := by
    ext s
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)) s
  map_comp {U V W} i j := by
    ext s
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (X.presheaf.map_comp i j)) s

noncomputable def Scheme.moduleKPresheafCompForgetIso :
    X.moduleKPresheaf k ⋙ CategoryTheory.forget (ModuleCat.{u} k) ≅
      X.presheaf ⋙ CategoryTheory.forget CommRingCat :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

lemma Scheme.isSheaf_moduleKPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat))
      (X.moduleKPresheaf k) := by
  have h : TopCat.Presheaf.IsSheaf (C := ModuleCat.{u} k) (X := (X : TopCat))
      (X.moduleKPresheaf k) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
      (CategoryTheory.forget (ModuleCat.{u} k)) (X.moduleKPresheaf k)]
    change Presheaf.IsSheaf (Opens.grothendieckTopology (X : TopCat)) _
    rw [Presheaf.isSheaf_of_iso_iff (X.moduleKPresheafCompForgetIso k)]
    exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
      (CategoryTheory.forget CommRingCat) X.presheaf).mp X.toSheafedSpace.IsSheaf
  exact h

/-- The module-valued structure sheaf on the small Zariski site. -/
noncomputable def Scheme.moduleKSheaf :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k) :=
  ⟨X.moduleKPresheaf k, X.isSheaf_moduleKPresheaf k⟩

@[simp] lemma Scheme.moduleKSheaf_obj (U : X.Opens) :
    (X.moduleKSheaf k).obj.obj (op U) = ModuleCat.of k Γ(X, U) := rfl

lemma Scheme.moduleKSheaf_map_apply {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (s : Γ(X, U.unop)) :
    ((X.moduleKSheaf k).obj.map i).hom s = (X.presheaf.map i).hom s := rfl

end AlgebraicGeometry
