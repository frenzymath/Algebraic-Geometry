/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.RepresentableByCocycle

/-!
# Canonical equality transport for representability comparisons

The over-category coherence maps are equality transports.  Exposing that fact
keeps common-base comparison proofs independent of a choice of representatives
and avoids expanding the raw `Over.mapComp` components at every face.
-/

set_option autoImplicit false

universe v u

open CategoryTheory

namespace CategoryTheory.Functor.RepresentableBy.Over

variable {D : Type u} [Category.{v, u} D]

private lemma map_eqToHom_apply_heq
    {C : Type u} [Category.{v, u} C] (F : C ⥤ Type v)
    {A B : C} (h : A = B) (x : F.obj A) :
    HEq (F.map (eqToHom h) x) x := by
  cases h
  simp

private lemma eqToHom_apply_heq
    {A B : Type v} (h : A = B) (x : A) :
    HEq (eqToHom h x) x := by
  cases h
  rfl

private lemma id_apply_heq (A : Type v) (x : A) :
    HEq ((ConcreteCategory.hom (𝟙 A)) x) x := by
  rfl

private lemma op_map_eqToHom_apply_heq
    {C E : Type u} [Category.{v, u} C] [Category.{v, u} E]
    (G : C ⥤ E) (F : Eᵒᵖ ⥤ Type v)
    {A B : Cᵒᵖ} (h : A = B) (x : F.obj (G.op.obj A)) :
    HEq (F.map (G.op.map (eqToHom h)) x) x := by
  cases h
  rw [eqToHom_map]
  exact map_eqToHom_apply_heq F _ _

/-- `Over.mapComp` is the canonical equality transport between the two
functors mapping a composite arrow. -/
theorem mapComp_eqToIso {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CategoryTheory.Over.mapComp f g =
      eqToIso (CategoryTheory.Over.mapComp_eq f g) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  simp only [CategoryTheory.Over.mapComp, NatIso.ofComponents_hom_app]
  apply CategoryTheory.Over.OverMorphism.ext
  simp only [CategoryTheory.Over.isoMk_hom_left, Iso.refl_hom,
    eqToIso.hom, eqToHom_app]
  rw [CategoryTheory.Over.eqToHom_left]
  have hobj := congrArg
    (fun F : CategoryTheory.Over X ⥤ CategoryTheory.Over Z => (F.obj A).left)
    (CategoryTheory.Over.mapComp_eq (X := X) (Y := Y) (Z := Z) f g)
  exact (eqToHom_heq_id_dom _ _ hobj).eq.symm

/-- The presheaf comparison using only canonical equality transports. -/
noncomputable def mapCompPresheafCanonical
    {X Y Z : D} (r : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : r = f ≫ g) (F : (CategoryTheory.Over Z)ᵒᵖ ⥤ Type v) :
    (CategoryTheory.Over.map r).op ⋙ F ≅
      (CategoryTheory.Over.map f).op ⋙ ((CategoryTheory.Over.map g).op ⋙ F) :=
  eqToIso (congrArg (fun m => (CategoryTheory.Over.map m).op ⋙ F) h) ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (eqToIso (CategoryTheory.Over.mapComp_eq f g))).symm F

/-- The existing comparison and the canonical equality-transport comparison
are definitionally the same up to `mapComp_eqToIso`. -/
theorem mapCompPresheafOfEq_eq_canonical
    {X Y Z : D} (r : X ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : r = f ≫ g) (F : (CategoryTheory.Over Z)ᵒᵖ ⥤ Type v) :
    CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafOfEq
        r f g h F = mapCompPresheafCanonical r f g h F := by
  simp [CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafOfEq,
    mapCompPresheafCanonical, mapComp_eqToIso]

/-- Rebase through a fixed comparison `theta`, using canonical equality
transports for the final base map. -/
noncomputable def mapCompPresheafCommon
    {Y Z : D} (b : Y ⟶ Z)
    {FL : (CategoryTheory.Over Y)ᵒᵖ ⥤ Type v}
    {FK : (CategoryTheory.Over Z)ᵒᵖ ⥤ Type v}
    (theta : FL ≅ (CategoryTheory.Over.map b).op ⋙ FK)
    {S : D} (f : S ⟶ Y) :
    (CategoryTheory.Over.map f).op ⋙ FL ≅
      (CategoryTheory.Over.map (f ≫ b)).op ⋙ FK :=
  Functor.isoWhiskerLeft (CategoryTheory.Over.map f).op theta ≪≫
    (Functor.associator (CategoryTheory.Over.map f).op
      (CategoryTheory.Over.map b).op FK).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (eqToIso (CategoryTheory.Over.mapComp_eq f b))) FK

/-- Common-base comparisons compose along a pair of arrows.  The proof uses
naturality of `theta`; all remaining maps are equality transports. -/
theorem mapCompPresheafCommon_comp
    {W X Y Z : D} (q : W ⟶ X) (p : X ⟶ Y) (b : Y ⟶ Z)
    {FL : (CategoryTheory.Over Y)ᵒᵖ ⥤ Type v}
    {FK : (CategoryTheory.Over Z)ᵒᵖ ⥤ Type v}
    (theta : FL ≅ (CategoryTheory.Over.map b).op ⋙ FK) :
    mapCompPresheafCommon b theta (q ≫ p) =
      CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafOfEq
          (q ≫ p) q p rfl FL ≪≫
        Functor.isoWhiskerLeft (CategoryTheory.Over.map q).op
          (mapCompPresheafCommon b theta p) ≪≫
        (CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafOfEq
          ((q ≫ p) ≫ b) q (p ≫ b) (Category.assoc q p b) FK).symm := by
  rw [mapCompPresheafOfEq_eq_canonical,
    mapCompPresheafOfEq_eq_canonical]
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply ConcreteCategory.hom_ext
  intro x
  have htheta := congrArg (fun f => (ConcreteCategory.hom f) x)
    (theta.hom.naturality
      ((NatIso.op (eqToIso
        (CategoryTheory.Over.mapComp_eq q p))).inv.app A))
  simp only [mapCompPresheafCommon, mapCompPresheafCanonical,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    eqToIso.hom, eqToHom_app,
    Functor.associator_inv_app, types_comp_apply]
  simp only [types_comp_apply] at htheta
  simp only [types_id_apply, eqToHom_refl]
  erw [htheta]
  simp only [NatIso.op_hom, eqToIso.hom, NatTrans.op_app, eqToHom_app,
    eqToHom_op, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, eqToIso.inv, NatTrans.comp_app,
    Functor.whiskerRight_app, comp_apply, NatIso.op_inv, comp_map, op_map]
  apply eq_of_heq
  apply HEq.trans (map_eqToHom_apply_heq FK _ _)
  apply HEq.trans (id_apply_heq _ _)
  refine HEq.trans ?_ (eqToHom_apply_heq _ _).symm
  refine HEq.trans ?_ (map_eqToHom_apply_heq FK _ _).symm
  refine HEq.trans ?_ (map_eqToHom_apply_heq FK _ _).symm
  exact (op_map_eqToHom_apply_heq (CategoryTheory.Over.map b) FK _ _).symm

/-- Pulling a common-base comparison across an outer map agrees with the
comparison obtained directly from the two composite maps. -/
theorem mapCompPresheafFace_common
    {V W X Y : D} (t : V ⟶ Y) (r₀ r₁ : V ⟶ X) (q : V ⟶ W)
    (p₀ p₁ : W ⟶ X) (b : X ⟶ Y)
    {FL : (CategoryTheory.Over X)ᵒᵖ ⥤ Type v}
    {FK : (CategoryTheory.Over Y)ᵒᵖ ⥤ Type v}
    (theta : FL ≅ (CategoryTheory.Over.map b).op ⋙ FK)
    (hp : p₀ ≫ b = p₁ ≫ b)
    (hr₀ : r₀ = q ≫ p₀) (hr₁ : r₁ = q ≫ p₁)
    (h₀ : r₀ ≫ b = t) (h₁ : r₁ ≫ b = t) :
    CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafFace
        r₀ r₁ q p₀ p₁ hr₀ hr₁
        (mapCompPresheafCommon b theta p₀ ≪≫
          eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) hp) ≪≫
          (mapCompPresheafCommon b theta p₁).symm) =
      (mapCompPresheafCommon b theta r₀ ≪≫
          eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) h₀)) ≪≫
        (mapCompPresheafCommon b theta r₁ ≪≫
          eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) h₁)).symm := by
  subst r₀
  subst r₁
  simp only [CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafFace]
  rw [mapCompPresheafCommon_comp, mapCompPresheafCommon_comp]
  simp_rw [mapCompPresheafOfEq_eq_canonical]
  have htransport :
      Functor.isoWhiskerLeft (CategoryTheory.Over.map q).op
          (eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) hp)) =
        (mapCompPresheafCanonical ((q ≫ p₀) ≫ b) q (p₀ ≫ b)
            (Category.assoc q p₀ b) FK).symm ≪≫
          eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) h₀) ≪≫
          (eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) h₁)).symm ≪≫
          mapCompPresheafCanonical ((q ≫ p₁) ≫ b) q (p₁ ≫ b)
            (Category.assoc q p₁ b) FK := by
    apply Iso.ext
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro x
    simp only [mapCompPresheafCanonical, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, eqToIso.hom,
      eqToIso.inv, eqToHom_app, types_comp_apply]
    simp only [NatIso.op_inv, eqToIso.inv, NatTrans.op_app, eqToHom_app,
      eqToHom_op, Iso.symm_inv, NatIso.op_hom, eqToIso.hom]
    apply eq_of_heq
    apply HEq.trans (eqToHom_apply_heq _ x)
    symm
    apply HEq.trans (map_eqToHom_apply_heq FK _ _)
    apply HEq.trans (eqToHom_apply_heq _ _)
    apply HEq.trans (eqToHom_apply_heq _ _)
    apply HEq.trans (eqToHom_apply_heq _ _)
    apply HEq.trans (eqToHom_apply_heq _ _)
    exact map_eqToHom_apply_heq FK _ _
  simp only [Functor.isoWhiskerLeft_trans, Iso.trans_symm, Iso.trans_assoc]
  rw [htransport]
  simp [Functor.isoWhiskerLeft_symm]

/-- A named face comparison agrees with a named direct comparison when their
definitions are respectively the pullback and common-base constructions.  This
keeps clients from unfolding all three dependent isomorphisms simultaneously. -/
theorem mapCompPresheafFace_common_of_eq
    {V W X Y : D} (t : V ⟶ Y) (r₀ r₁ : V ⟶ X) (q : V ⟶ W)
    (p₀ p₁ : W ⟶ X) (b : X ⟶ Y)
    {FL : (CategoryTheory.Over X)ᵒᵖ ⥤ Type v}
    {FK : (CategoryTheory.Over Y)ᵒᵖ ⥤ Type v}
    (theta : FL ≅ (CategoryTheory.Over.map b).op ⋙ FK)
    (hp : p₀ ≫ b = p₁ ≫ b)
    (hr₀ : r₀ = q ≫ p₀) (hr₁ : r₁ = q ≫ p₁)
    (h₀ : r₀ ≫ b = t) (h₁ : r₁ ≫ b = t)
    (thetaOverlap :
      (CategoryTheory.Over.map p₀).op ⋙ FL ≅
        (CategoryTheory.Over.map p₁).op ⋙ FL)
    (thetaFace thetaDirect :
      (CategoryTheory.Over.map r₀).op ⋙ FL ≅
        (CategoryTheory.Over.map r₁).op ⋙ FL)
    (hoverlap : thetaOverlap =
      mapCompPresheafCommon b theta p₀ ≪≫
        eqToIso (congrArg
          (fun g => (CategoryTheory.Over.map g).op ⋙ FK) hp) ≪≫
        (mapCompPresheafCommon b theta p₁).symm)
    (hface : thetaFace =
      CategoryTheory.Functor.RepresentableBy.Over.mapCompPresheafFace
        r₀ r₁ q p₀ p₁ hr₀ hr₁ thetaOverlap)
    (hdirect : thetaDirect =
      (mapCompPresheafCommon b theta r₀ ≪≫
          eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) h₀)) ≪≫
        (mapCompPresheafCommon b theta r₁ ≪≫
          eqToIso (congrArg
            (fun g => (CategoryTheory.Over.map g).op ⋙ FK) h₁)).symm) :
    thetaFace = thetaDirect := by
  rw [hface, hoverlap, hdirect]
  exact mapCompPresheafFace_common t r₀ r₁ q p₀ p₁ b theta hp
    hr₀ hr₁ h₀ h₁

end CategoryTheory.Functor.RepresentableBy.Over
