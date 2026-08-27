/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid2

/-!
# Naturality of the Čech section comparison

This file identifies the push-pull map of an inclusion of intersection opens with direct
restriction on sections. It then uses that identification to prove the coordinatewise
naturality theorem `coreIso_comm_leg` (`lem:coreIso_comm_leg`).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}
set_option maxHeartbeats 800000 in
-- Transporting the composite adjunction unit through two restriction isomorphisms exceeds defaults.
/-- Step 2 (K4): the `pullbackComp` comparison, conjugated to restrict-world through
`restrictFunctorIsoPullback`, is the `restrictFunctorComp` identification. -/
lemma pullbackComp_rFIP_compat {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (F : X.Modules) :
    (Scheme.Modules.pullbackComp c q).hom.app F ≫
        (Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F =
      (Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
        (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
        (Scheme.Modules.restrictFunctorComp c q).inv.app F := by
  refine (((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction c)).homEquiv F
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  -- Side A: the composite unit absorbs the pullback comparison (`pushPull_unit_comp`),
  -- and the `rFIP (c≫q)` leg collapses by Step 0.
  have hcomp := pushPull_unit_comp c q F
  have e1 : (Scheme.Modules.pushforwardComp c q).hom.app
        ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback q).obj F)) ≫
        (Scheme.Modules.pushforward (c ≫ q)).map
          ((Scheme.Modules.pullbackComp c q).hom.app F) =
      (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.pullbackComp c q).hom.app F)) :=
    (congrArg (fun w => w ≫ (Scheme.Modules.pushforward (c ≫ q)).map
        ((Scheme.Modules.pullbackComp c q).hom.app F))
      (pushforwardComp_hom_app_id c q _)).trans (Category.id_comp _)
  have hA0 : (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ q)).unit.app F =
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.pullbackComp c q).hom.app F)) :=
    hcomp.trans (congrArg (fun w =>
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F)) ≫ w) e1)
  have hA : ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F))) ≫
      (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackComp c q).hom.app F ≫
          (Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F) =
      (Scheme.Modules.restrictAdjunction (c ≫ q)).unit.app F := by
    refine Eq.trans (congrArg (fun w =>
      ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F))) ≫ w)
      (Functor.map_comp (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q)
        ((Scheme.Modules.pullbackComp c q).hom.app F)
        ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F))) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun w => w ≫
        (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F))
      ((Category.assoc _ _ _).trans hA0.symm)) ?_
    exact unit_pushforward_rFIP_inv (c ≫ q) F
  -- Side B: unit naturality + Step 0 + Step 1.
  have hB : ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F))) ≫
      (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullback c).map
            ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
          (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
          (Scheme.Modules.restrictFunctorComp c q).inv.app F) =
      (Scheme.Modules.restrictAdjunction (c ≫ q)).unit.app F := by
    have hmerge : (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F)) ≫
        (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullback c).map
              ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
            (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
            (Scheme.Modules.restrictFunctorComp c q).inv.app F) =
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) := by
      refine ((Functor.map_comp (Scheme.Modules.pushforward q) _ _).symm.trans ?_).trans
        ((Functor.map_comp (Scheme.Modules.pushforward q) _ _).trans
          (congrArg (fun w => (Scheme.Modules.pushforward q).map
            ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫ w)
            (Functor.map_comp (Scheme.Modules.pushforward q) _ _)))
      refine congrArg (Scheme.Modules.pushforward q).map ?_
      exact (inner_beta_chain q c F).trans (Category.assoc _ _ _).symm
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun w =>
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫ w) hmerge) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun w => w ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)))
      (unit_pushforward_rFIP_inv q F)) ?_
    exact restrict_unit_comp q c F
  exact hA.trans hB.symm

/-- The restrict-world normal form of a push-pull map along an open inclusion in a slice. -/
noncomputable def pushPullRestrictComparison {A C' : Scheme.{u}} (q : A ⟶ X)
    [IsOpenImmersion q] (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X)
    [IsOpenImmersion pC] (wC : c ≫ q = pC) (F : X.Modules) :=
  (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
    (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
    (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
      ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫
    (Scheme.Modules.pushforwardCongr wC).hom.app
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F) ≫
    (Scheme.Modules.pushforward pC).map
      ((Scheme.Modules.restrictFunctorCongr wC).hom.app F)

set_option maxHeartbeats 1600000 in
-- Reducing the two proof-irrelevant over-triangle transports exceeds the default budget.
/-- Step 3: the push–pull map of a slice-level open inclusion, conjugated to restrict-world,
is the restriction unit followed by the `restrictFunctorComp` identification and the two
transport isos along the over-triangle (all with `rfl` section components). -/
lemma pushPull_toRestrict_comm {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X) [IsOpenImmersion pC]
    (wC : c ≫ q = pC) (F : X.Modules) :
    pushPullMap F (Over.homMk c wC : Over.mk pC ⟶ Over.mk q) ≫
        (Scheme.Modules.pushforward pC).map
          ((Scheme.Modules.restrictFunctorIsoPullback pC).inv.app F) =
      pushPullRestrictComparison q c pC wC F := by
  dsimp only [pushPullRestrictComparison]
  subst wC
  -- the two transport isos at `rfl` are identities (their section components are
  -- restriction maps along `eqToHom rfl`)
  have hPC : (Scheme.Modules.pushforwardCongr (rfl : c ≫ q = c ≫ q)).hom.app
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F) =
      𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
        ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)) := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
    rfl
  have hRC : (Scheme.Modules.restrictFunctorCongr (rfl : c ≫ q = c ≫ q)).hom.app F =
      𝟙 ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F) := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
    rfl
  have main : pushPullMap F (Over.homMk c rfl : Over.mk (c ≫ q) ⟶ Over.mk q) ≫
      (Scheme.Modules.pushforward (c ≫ q)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F) =
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
      (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) := by
    have hraw : pushPullMap F (Over.homMk c rfl : Over.mk (c ≫ q) ⟶ Over.mk q) =
        rawPushPullMap c q (c ≫ q) rfl F := rfl
    have hself := rawPushPullMap_self c q F
    refine Eq.trans (congrArg (fun w => w ≫ (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F)))
      (hraw.trans hself)) ?_
    refine Eq.trans ((Functor.map_comp _ _ _).symm) ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward q).map
      ((Category.assoc _ _ _).trans
        (congrArg (fun w => (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F) ≫ w)
          (Functor.map_comp _ _ _).symm))) ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward q).map
      (congrArg (fun w => (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
          (Scheme.Modules.pushforward c).map w)
        (pullbackComp_rFIP_compat q c F))) ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward q).map
      (inner_beta_chain q c F)) ?_
    exact (Functor.map_comp _ _ _).trans
      (congrArg (fun w => (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫ w)
        (Functor.map_comp _ _ _))
  refine main.trans ?_
  refine congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
    (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫ w) ?_
  refine Eq.symm ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫ w ≫
      (Scheme.Modules.pushforward (c ≫ q)).map
        ((Scheme.Modules.restrictFunctorCongr (rfl : c ≫ q = c ≫ q)).hom.app F)) hPC) ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫
      𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
        ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)) ≫
      (Scheme.Modules.pushforward (c ≫ q)).map w) hRC) ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫
      𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
        ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)) ≫ w)
    (CategoryTheory.Functor.map_id (Scheme.Modules.pushforward (c ≫ q))
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F))) ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫ w)
    (Category.id_comp (𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F))))) ?_
  exact Category.comp_id _

/-- Thin-category endgame: a four-restriction chain against an object-equality transport
agrees with the transported single restriction. -/
private lemma thin_resid5 (P : (TopologicalSpace.Opens ↥X)ᵒᵖ ⥤ Ab.{u})
    {A B C D E T W : TopologicalSpace.Opens ↥X}
    (i₁ : B ⟶ A) (i₂ : C ⟶ B) (i₃ : D ⟶ C) (i₄ : E ⟶ D)
    (h₄ : P.obj (Opposite.op E) = P.obj (Opposite.op T))
    (h₅ : P.obj (Opposite.op A) = P.obj (Opposite.op W))
    (i₆ : T ⟶ W) (e₄ : E = T) (e₅ : A = W) :
    (P.map i₁.op ≫ P.map i₂.op ≫ P.map i₃.op ≫ P.map i₄.op) ≫ eqToHom h₄ =
      eqToHom h₅ ≫ P.map i₆.op := by
  subst e₄ e₅
  change (P.map i₁.op ≫ P.map i₂.op ≫ P.map i₃.op ≫ P.map i₄.op) ≫
      𝟙 (P.obj (Opposite.op E)) = 𝟙 (P.obj (Opposite.op A)) ≫ P.map i₆.op
  rw [Category.comp_id, Category.id_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, ← op_comp]
  exact congrArg (fun t : E ⟶ A => P.map t.op) (Subsingleton.elim _ _)

private lemma map_comp_postcomp_of_eq {C D : Type*} [Category C] [Category D]
    (E : C ⥤ D) {A B C' : C} {T : D} (f : A ⟶ B) (g : B ⟶ C') (h : A ⟶ C')
    (e : f ≫ g = h) (k : E.obj C' ⟶ T) :
    E.map f ≫ E.map g ≫ k = E.map h ≫ k := by
  rw [← Category.assoc, ← E.map_comp, e]

private lemma iota_image_preimage_eq_inf (U V : TopologicalSpace.Opens X) :
    Scheme.Opens.ι U ''ᵁ (Scheme.Opens.ι U ⁻¹ᵁ V) = U ⊓ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

private noncomputable def openOverHomOfLE {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    Over.mk (Scheme.Opens.ι U) ⟶ Over.mk (Scheme.Opens.ι W) :=
  Over.homMk (X.homOfLE h) (Scheme.homOfLE_ι X h)

private noncomputable def openFaceRestrV (F : X.Modules) (V : TopologicalSpace.Opens X)
    {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (W ⊓ V)) ⟶
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (U ⊓ V)) :=
  ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
    (homOfLE (inf_le_inf_right V h)).op

private noncomputable def openLegSectionsHom (F : X.Modules)
    (U V : TopologicalSpace.Opens X) :=
  (sectionFunctorV V).map
      ((Scheme.Modules.pushforward (Scheme.Opens.ι U)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι U)).inv.app F)) ≫
    eqToHom (congrArg (fun W =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
      (iota_image_preimage_eq_inf U V))

private noncomputable def openRestrictChain (F : X.Modules)
    {U W : TopologicalSpace.Opens X} (h : U ≤ W) :=
  pushPullRestrictComparison (Scheme.Opens.ι W) (X.homOfLE h)
    (Scheme.Opens.ι U) (Scheme.homOfLE_ι X h) F

private lemma openOverHomOfLE_eq {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    openOverHomOfLE h =
      (Over.homMk (X.homOfLE h) (Scheme.homOfLE_ι X h) :
        Over.mk (Scheme.Opens.ι U) ⟶ Over.mk (Scheme.Opens.ι W)) :=
  rfl

private lemma openRestrictChain_eq (F : X.Modules)
    {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    openRestrictChain F h =
      pushPullRestrictComparison (Scheme.Opens.ι W) (X.homOfLE h)
        (Scheme.Opens.ι U) (Scheme.homOfLE_ι X h) F :=
  rfl

private lemma openLegSectionsHom_eq (F : X.Modules) (U V : TopologicalSpace.Opens X) :
    openLegSectionsHom F U V =
      (sectionFunctorV V).map
          ((Scheme.Modules.pushforward (Scheme.Opens.ι U)).map
            ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι U)).inv.app F)) ≫
        eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
          (iota_image_preimage_eq_inf U V)) :=
  rfl

/-- The restriction map on sections induced by deleting one index from a cover tuple. -/
private noncomputable def coverInterFaceRestrV (𝒰 : X.OpenCover) (F : X.Modules)
    (V : TopologicalSpace.Opens X) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀)
    (k : Fin (p + 2)) :=
  openFaceRestrV F V
    (coverInterOpen_comp_le 𝒰 (SimplexCategory.δ k).toOrderHom σ')

/-- Coordinate unfolding of the per-leg section identification: `pushPull_leg_sections`
is, by `rfl`, the evaluated pushforward of the `restrictFunctorIsoPullback` inverse
followed by the image-reindex transport. -/
private lemma pls_eq (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    {m : ℕ} (σ : Fin (m + 1) → 𝒰.I₀) (V : TopologicalSpace.Opens X) :
    (pushPull_leg_sections 𝒰 F σ V).hom =
      openLegSectionsHom F (coverInterOpen 𝒰 σ) V := rfl

set_option maxHeartbeats 800000 in
-- Normalizing the evaluated five-map pushforward chain exceeds the default heartbeat budget.
/-- The evaluated generic restriction chain is the direct restriction on sections. -/
private lemma openRestrictChain_sections (F : X.Modules) (V : TopologicalSpace.Opens X)
    {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    (sectionFunctorV V).map (openRestrictChain F h) ≫
        eqToHom (congrArg (fun Z =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op Z))
          (iota_image_preimage_eq_inf U V)) =
      openLegSectionsHom F W V ≫ openFaceRestrV F V h := by
  dsimp only [openRestrictChain, openLegSectionsHom, openFaceRestrV]
  have heq_U := iota_image_preimage_eq_inf U V
  have heq_W := iota_image_preimage_eq_inf W V
  have hcomp_image : (X.homOfLE h ≫ Scheme.Opens.ι W) ''ᵁ
          ((X.homOfLE h) ⁻¹ᵁ ((Scheme.Opens.ι W) ⁻¹ᵁ V)) =
      (Scheme.Opens.ι W) ''ᵁ
          ((X.homOfLE h) ''ᵁ ((X.homOfLE h) ⁻¹ᵁ ((Scheme.Opens.ι W) ⁻¹ᵁ V))) :=
    by rw [Scheme.Hom.comp_image]
  have hpreimg_eq : (Scheme.Opens.ι U) ⁻¹ᵁ V =
      (X.homOfLE h ≫ Scheme.Opens.ι W) ⁻¹ᵁ V :=
    by simp only [← Scheme.homOfLE_ι X h]
  have himg2_eq : (Scheme.Opens.ι U) ''ᵁ ((Scheme.Opens.ι U) ⁻¹ᵁ V) =
      (X.homOfLE h ≫ Scheme.Opens.ι W) ''ᵁ ((Scheme.Opens.ι U) ⁻¹ᵁ V) :=
    by simp only [← Scheme.homOfLE_ι X h]
  simp only [Category.assoc]
  erw [Functor.map_comp]
  erw [Category.assoc]
  refine congrArg (fun z => (sectionFunctorV V).map
    ((Scheme.Modules.pushforward (Scheme.Opens.ι W)).map
      ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι W)).inv.app F)) ≫ z) ?_
  exact thin_resid5 ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf
    ((Scheme.Hom.opensFunctor (Scheme.Opens.ι W)).map
      (homOfLE ((X.homOfLE h).image_preimage_le ((Scheme.Opens.ι W) ⁻¹ᵁ V))))
    (eqToHom hcomp_image)
    ((Scheme.Hom.opensFunctor (X.homOfLE h ≫ Scheme.Opens.ι W)).map
      (eqToHom hpreimg_eq))
    (eqToHom himg2_eq)
    (congrArg (fun Z =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op Z)) heq_U)
    (congrArg (fun Z =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op Z)) heq_W)
    (homOfLE (inf_le_inf_right V h)) heq_U heq_W

/-- The push-pull comparison for an inclusion of opens, with its five-map target kept opaque. -/
private lemma pushPull_openOverHom_restrict (F : X.Modules)
    {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    pushPullMap F (openOverHomOfLE h) ≫
        (Scheme.Modules.pushforward (Scheme.Opens.ι U)).map
          ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι U)).inv.app F) =
      openRestrictChain F h := by
  rw [openOverHomOfLE_eq h, openRestrictChain_eq F h]
  exact @pushPull_toRestrict_comm X
    (Scheme.Opens.toScheme W) (Scheme.Opens.toScheme U)
    (Scheme.Opens.ι W) inferInstance (X.homOfLE h) inferInstance
    (Scheme.Opens.ι U) inferInstance (Scheme.homOfLE_ι X h) F

/-- Evaluating the push-pull comparison gives the opaque restriction chain on sections. -/
private lemma pushPull_openOverHom_sections_prefix (F : X.Modules)
    (V : TopologicalSpace.Opens X) {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    (sectionFunctorV V).map (pushPullMap F (openOverHomOfLE h)) ≫
        (sectionFunctorV V).map
          ((Scheme.Modules.pushforward (Scheme.Opens.ι U)).map
            ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι U)).inv.app F)) ≫
        eqToHom (congrArg (fun Z =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op Z))
          (iota_image_preimage_eq_inf U V)) =
      (sectionFunctorV V).map (openRestrictChain F h) ≫
        eqToHom (congrArg (fun Z =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op Z))
          (iota_image_preimage_eq_inf U V)) :=
  map_comp_postcomp_of_eq (sectionFunctorV V)
    (pushPullMap F (openOverHomOfLE h))
    ((Scheme.Modules.pushforward (Scheme.Opens.ι U)).map
      ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι U)).inv.app F))
    (openRestrictChain F h) (pushPull_openOverHom_restrict F h)
    (eqToHom (congrArg (fun Z =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op Z))
      (iota_image_preimage_eq_inf U V)))

/-- The section comparison is natural for an arbitrary inclusion of opens. Keeping the
opens abstract prevents the kernel from normalizing a variable-length cover intersection. -/
private lemma pushPull_openOverHom_sections (F : X.Modules) (V : TopologicalSpace.Opens X)
    {U W : TopologicalSpace.Opens X} (h : U ≤ W) :
    (sectionFunctorV V).map (pushPullMap F (openOverHomOfLE h)) ≫
      openLegSectionsHom F U V =
      openLegSectionsHom F W V ≫ openFaceRestrV F V h := by
  rw [openLegSectionsHom_eq F U V]
  exact (pushPull_openOverHom_sections_prefix F V h).trans
    (openRestrictChain_sections F V h)

private lemma interLegHom_eq_openOverHomOfLE (𝒰 : X.OpenCover) {p : ℕ}
    (σ' : Fin (p + 2) → 𝒰.I₀) (k : Fin (p + 2))
    (h : coverInterOpen 𝒰 σ' ≤
      coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom)) :
    interLegHom 𝒰 σ' k = openOverHomOfLE h := by
  rfl

private lemma coverInterFaceRestrV_eq_openFaceRestrV (𝒰 : X.OpenCover) (F : X.Modules)
    (V : TopologicalSpace.Opens X) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀)
    (k : Fin (p + 2)) (h : coverInterOpen 𝒰 σ' ≤
      coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom)) :
    coverInterFaceRestrV 𝒰 F V σ' k = openFaceRestrV F V h := by
  rfl

/-- **Per-leg restriction naturality** (the sheaf-theoretic seam): the evaluated push–pull
map of the face inclusion `interLegHom : U_{σ'} ⊆ U_{σ'∘δᵏ}` acts on the identified leg
sections as the plain `F`-restriction along `U_{σ'} ⊓ V ⊆ U_{σ'∘δᵏ} ⊓ V`. -/
lemma pushPull_interLegHom_sections (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens ↥X) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀) (k : Fin (p + 2)) :
    (sectionFunctorV V).map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
        (pushPull_leg_sections 𝒰 F σ' V).hom =
      (pushPull_leg_sections 𝒰 F (σ' ∘ (SimplexCategory.δ k).toOrderHom) V).hom ≫
        coverInterFaceRestrV 𝒰 F V σ' k := by
  let h : coverInterOpen 𝒰 σ' ≤
      coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) :=
    coverInterOpen_comp_le 𝒰 (SimplexCategory.δ k).toOrderHom σ'
  rw [pls_eq 𝒰 F σ' V, pls_eq 𝒰 F (σ' ∘ (SimplexCategory.δ k).toOrderHom) V,
    interLegHom_eq_openOverHomOfLE 𝒰 σ' k h,
    coverInterFaceRestrV_eq_openFaceRestrV 𝒰 F V σ' k h]
  exact pushPull_openOverHom_sections F V h


/-- Thin-category fusion of presheaf restrictions against `eqToHom` reindexes: a
restriction map conjugated by object-equality transports equals any other restriction
map between the transported section groups (`Opens`-homs are subsingletons). -/
private lemma map_op_eqToHom_swap (P : (TopologicalSpace.Opens ↥X)ᵒᵖ ⥤ Ab.{u})
    {A B A' B' : TopologicalSpace.Opens ↥X} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') :
    P.map f.op ≫ eqToHom (congrArg (fun W => P.obj (Opposite.op W)) hA) =
      eqToHom (congrArg (fun W => P.obj (Opposite.op W)) hB) ≫ P.map g.op := by
  subst hA
  subst hB
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  exact congrArg (fun u => P.map u) (congrArg Quiver.Hom.op (Subsingleton.elim f g))

/-- **Per-leg naturality of the core comparison coface** (`lem:coreIso_comm_leg`).
For a fixed coface index `k` and multi-index `σ'`, the `σ'`-coordinate (the projection
`Pi.π … σ'`) of the evaluated push–pull coface `G_V(Ψ(δ^nerve_k))` followed by the
degree-`(p+1)` object iso equals the presheaf face restriction `sectionCechFaceRestr σ' k`
applied to the `(σ' ∘ d_k)`-coordinate of the degree-`p` object iso.  This is the genuine
geometric unwinding of `coreIso_objIso` through `pushPull_eval_prod_iso`,
`pushPull_sigma_iso`, the product-leg projection, and `pushPull_leg_sections`. -/
lemma coreIso_comm_leg (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀) :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom ≫
        Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ' =
      (coreIso_objIso 𝒰 F p V).hom ≫
        Pi.π (fun τ : Fin (p + 1) → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ l, (coverOpen 𝒰 (τ l) ⊓ V))))
          (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k := by
  -- The central exchange: nerve coface ≫ object-iso projection, expressed through the
  -- backbone seams.  All rewrites below act on terms introduced by the seam lemmas
  -- themselves, so the matching is syntactic.
  have hmid : (sectionFunctorV V).map (pushPullMap F
        ((coverCechNerveOver 𝒰).map (SimplexCategory.δ k).op)) ≫
      (sectionFunctorV V).map (pushPullMap F (backboneIncl 𝒰 (p + 1) σ')) ≫
      (pushPull_leg_sections 𝒰 F σ' V).hom ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 σ' V)) =
      (sectionFunctorV V).map (pushPullMap F
        (backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ≫
      (pushPull_leg_sections 𝒰 F (σ' ∘ (SimplexCategory.δ k).toOrderHom) V).hom ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) V)) ≫
      sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k := by
    rw [← Functor.map_comp_assoc, ← pushPullMap_comp, backboneIncl_nerveδ 𝒰 p k σ',
      pushPullMap_comp, Functor.map_comp_assoc,
      ← Category.assoc ((sectionFunctorV V).map (pushPullMap F (interLegHom 𝒰 σ' k))),
      pushPull_interLegHom_sections 𝒰 F V σ' k]
    refine congrArg (fun w => (sectionFunctorV V).map (pushPullMap F
      (backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ≫ w) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun w => (pushPull_leg_sections 𝒰 F
        (σ' ∘ (SimplexCategory.δ k).toOrderHom) V).hom ≫ w)
      (map_op_eqToHom_swap (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf)
        (coverInterOpen_inf_eq_iInf_inf 𝒰 σ' V)
        (coverInterOpen_inf_eq_iInf_inf 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) V)
        (homOfLE (inf_le_inf_right V (le_iInf (fun l => iInf_le
          (fun j => coverOpen 𝒰 (σ' j)) ((SimplexCategory.δ k).toOrderHom l)))))
        (homOfLE (le_iInf (fun l => iInf_le (fun j => coverOpen 𝒰 (σ' j) ⊓ V)
          ((SimplexCategory.δ k).toOrderHom l)))))
  -- Collapse the nerve coface to the push–pull of the geometric face (both definitional),
  -- then chain through `coreIso_objIso_π` on both sides.
  rw [cechNerve_drop_δ 𝒰 F k, GVΨ_map_eq]
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map (pushPullMap F
      ((coverCechNerveOver 𝒰).map (SimplexCategory.δ k).op)) ≫ w)
    (coreIso_objIso_π 𝒰 F (p + 1) V σ')) ?_
  refine Eq.trans hmid (Eq.symm ?_)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫ sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k)
    (coreIso_objIso_π 𝒰 F p V (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun w => (sectionFunctorV V).map
      (pushPullMap F (backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ≫ w)
    (Category.assoc _ _ _))


end AlgebraicGeometry
