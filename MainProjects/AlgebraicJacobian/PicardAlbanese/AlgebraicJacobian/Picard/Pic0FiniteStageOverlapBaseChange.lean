/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionBaseChange

/-!
# The overlap component of finite-stage Picard base change

The overlaps produced by `Scheme.Pullback.gluing` are nested pullbacks. We first
flatten that categorical presentation, using the certified pullback presentation of
the original overlap, and then apply the existing affine overlap comparison.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- Flatten the nested pullback obtained by first base-changing `U` and then
intersecting it with `V`. The only input about `W` is its displayed pullback
presentation as `U ×_X V`. -/
noncomputable def nestedPullbackFlatteningIso
    {U V X Y Z W : Scheme.{u}}
    (iU : U ⟶ X) (iV : V ⟶ X) (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : W ⟶ U) (b : W ⟶ V)
    (hab : a ≫ iU = b ≫ iV)
    (hW : IsLimit (PullbackCone.mk a b hab)) :
    pullback (pullback.fst (iU ≫ f) g ≫ iU) iV ≅
      pullback (a ≫ iU ≫ f) g := by
  let e : W ≅ pullback iU iV :=
    hW.conePointUniqueUpToIso (pullback.isLimit iU iV)
  have e_inv_fst : e.inv ≫ a = pullback.fst iU iV := by
    change e.inv ≫ (PullbackCone.mk a b hab).fst = _
    exact IsLimit.conePointUniqueUpToIso_inv_comp hW
      (pullback.isLimit iU iV) WalkingCospan.left
  exact
    asIso (pullback.map
      (pullback.fst (iU ≫ f) g ≫ iU) iV
      (pullback.snd g (iU ≫ f) ≫ iU) iV
      (pullbackSymmetry (iU ≫ f) g).hom (𝟙 V) (𝟙 X)
      (by simp) (by simp)) ≪≫
    pullbackAssoc g (iU ≫ f) iU iV ≪≫
    pullbackSymmetry g (pullback.fst iU iV ≫ (iU ≫ f)) ≪≫
    asIso (pullback.map
      (pullback.fst iU iV ≫ (iU ≫ f)) g
      (a ≫ iU ≫ f) g
      e.inv (𝟙 Y) (𝟙 Z)
      (by
        simpa only [Category.comp_id, Category.assoc] using
          congrArg (fun q => q ≫ iU ≫ f) e_inv_fst.symm)
      (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The first projection of the flattened pullback recovers the first projection
of the inner pullback after composing with the first leg of the displayed overlap. -/
@[reassoc]
theorem nestedPullbackFlatteningIso_hom_comp_fst_comp_a
    {U V X Y Z W : Scheme.{u}}
    (iU : U ⟶ X) (iV : V ⟶ X) (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : W ⟶ U) (b : W ⟶ V)
    (hab : a ≫ iU = b ≫ iV)
    (hW : IsLimit (PullbackCone.mk a b hab)) :
    (nestedPullbackFlatteningIso iU iV f g a b hab hW).hom ≫
        pullback.fst (a ≫ iU ≫ f) g ≫ a =
      pullback.fst (pullback.fst (iU ≫ f) g ≫ iU) iV ≫
        pullback.fst (iU ≫ f) g := by
  let e : W ≅ pullback iU iV :=
    hW.conePointUniqueUpToIso (pullback.isLimit iU iV)
  have e_inv_fst : e.inv ≫ a = pullback.fst iU iV := by
    change e.inv ≫ (PullbackCone.mk a b hab).fst = _
    exact IsLimit.conePointUniqueUpToIso_inv_comp hW
      (pullback.isLimit iU iV) WalkingCospan.left
  simp only [nestedPullbackFlatteningIso, Iso.trans_hom, asIso_hom,
    pullback.map, Category.assoc, pullback.lift_fst_assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  rw [e_inv_fst]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The first projection of the flattened pullback recovers the outer second
projection after composing with the second leg of the displayed overlap. -/
@[reassoc]
theorem nestedPullbackFlatteningIso_hom_comp_fst_comp_b
    {U V X Y Z W : Scheme.{u}}
    (iU : U ⟶ X) (iV : V ⟶ X) (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : W ⟶ U) (b : W ⟶ V)
    (hab : a ≫ iU = b ≫ iV)
    (hW : IsLimit (PullbackCone.mk a b hab)) :
    (nestedPullbackFlatteningIso iU iV f g a b hab hW).hom ≫
        pullback.fst (a ≫ iU ≫ f) g ≫ b =
      pullback.snd (pullback.fst (iU ≫ f) g ≫ iU) iV := by
  let e : W ≅ pullback iU iV :=
    hW.conePointUniqueUpToIso (pullback.isLimit iU iV)
  have e_inv_snd : e.inv ≫ b = pullback.snd iU iV := by
    change e.inv ≫ (PullbackCone.mk a b hab).snd = _
    exact IsLimit.conePointUniqueUpToIso_inv_comp hW
      (pullback.isLimit iU iV) WalkingCospan.right
  simp only [nestedPullbackFlatteningIso, Iso.trans_hom, asIso_hom,
    pullback.map, Category.assoc, pullback.lift_fst_assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  rw [e_inv_snd]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The second projection of the flattened pullback is the second projection of
the inner pullback after the outer first projection. -/
@[reassoc]
theorem nestedPullbackFlatteningIso_hom_comp_snd
    {U V X Y Z W : Scheme.{u}}
    (iU : U ⟶ X) (iV : V ⟶ X) (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : W ⟶ U) (b : W ⟶ V)
    (hab : a ≫ iU = b ≫ iV)
    (hW : IsLimit (PullbackCone.mk a b hab)) :
    (nestedPullbackFlatteningIso iU iV f g a b hab hW).hom ≫
        pullback.snd (a ≫ iU ≫ f) g =
      pullback.fst (pullback.fst (iU ≫ f) g ≫ iU) iV ≫
        pullback.snd (iU ≫ f) g := by
  simp [nestedPullbackFlatteningIso, pullback.map, Category.assoc]

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

set_option synthInstance.maxHeartbeats 3200000 in
-- Projecting the package unfolds the dependent finite-subextension towers.
set_option maxHeartbeats 12800000 in
/-- Flatten the overlap in the base-changed gluing to the pullback of the
original overlap structure map. -/
noncomputable def gluingOverlapFlatteningIso
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).V (U, V) ≅
    pullback
      (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  let g : Spec (.of k) ⟶ Spec (.of P.N.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))
  exact nestedPullbackFlatteningIso
    (P.glueData.ι U) (P.glueData.ι V) P.gluedMap g
    (P.glueData.f U V)
    (P.glueData.t U V ≫ P.glueData.f V U)
    (by
      simpa only [Category.assoc] using
        (P.glueData.glue_condition U V).symm)
    (P.glueData.vPullbackConeIsLimit U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Specializing the overlap projections unfolds the package's dependent scalar towers.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The flattened overlap's left restriction is the base-changed gluing restriction
followed by the first chart projection. -/
theorem gluingOverlapFlatteningIso_hom_comp_fst_comp_f
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (gluingOverlapFlatteningIso C P U V).hom ≫
        pullback.fst
          (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫
        P.glueData.f U V =
      (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫
        pullback.fst
          (P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  exact nestedPullbackFlatteningIso_hom_comp_fst_comp_a
    (P.glueData.ι U) (P.glueData.ι V) P.gluedMap
    (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
    (P.glueData.f U V)
    (P.glueData.t U V ≫ P.glueData.f V U)
    (by
      simpa only [Category.assoc] using
        (P.glueData.glue_condition U V).symm)
    (P.glueData.vPullbackConeIsLimit U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Specializing the overlap projections unfolds the package's dependent scalar towers.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The flattened overlap's right restriction is the second projection of the
base-changed gluing overlap. -/
theorem gluingOverlapFlatteningIso_hom_comp_fst_comp_t_f
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (gluingOverlapFlatteningIso C P U V).hom ≫
        pullback.fst
          (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫
        (P.glueData.t U V ≫ P.glueData.f V U) =
      pullback.snd
        (pullback.fst
            (P.glueData.ι U ≫ P.gluedMap)
            (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ≫
          P.glueData.ι U)
        (P.glueData.ι V) := by
  exact nestedPullbackFlatteningIso_hom_comp_fst_comp_b
    (P.glueData.ι U) (P.glueData.ι V) P.gluedMap
    (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
    (P.glueData.f U V)
    (P.glueData.t U V ≫ P.glueData.f V U)
    (by
      simpa only [Category.assoc] using
        (P.glueData.glue_condition U V).symm)
    (P.glueData.vPullbackConeIsLimit U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Specializing the overlap projections unfolds the package's dependent scalar towers.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The flattened overlap's base projection is the gluing restriction followed
by the base projection of its chart. -/
theorem gluingOverlapFlatteningIso_hom_comp_snd
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    (gluingOverlapFlatteningIso C P U V).hom ≫
        pullback.snd
          (P.glueData.f U V ≫ P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) =
      (Scheme.Pullback.gluing P.glueData.openCover P.gluedMap
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).f U V ≫
        pullback.snd
          (P.glueData.ι U ≫ P.gluedMap)
          (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) := by
  exact nestedPullbackFlatteningIso_hom_comp_snd
    (P.glueData.ι U) (P.glueData.ι V) P.gluedMap
    (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
    (P.glueData.f U V)
    (P.glueData.t U V ≫ P.glueData.f V U)
    (by
      simpa only [Category.assoc] using
        (P.glueData.glue_condition U V).symm)
    (P.glueData.vPullbackConeIsLimit U V)

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
