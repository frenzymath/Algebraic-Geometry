/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationLegMid1

/-!
# Restriction identities for the Čech section comparison

These lemmas identify push-pull maps along open immersions with
restriction-adjunction units and describe how those units compose.
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}
set_option maxHeartbeats 800000 in
-- The final definitional equality unfolds proof-irrelevant transports beyond
-- the default heartbeat budget.
/-- For a general ambient open immersion, the push–pull map of an over-morphism `Over.homMk c` is,
through the canonical leg iso, the pushforward of the restriction unit. -/
private lemma pushPull_leg_coherence {A C' : Scheme.{u}} (q : A ⟶ X)
    (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X) (wC : c ≫ q = pC) (F : X.Modules) :
    pushPullMap F (Over.homMk c wC : Over.mk pC ⟶ Over.mk q) =
      (pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F)) ≫
        (pushPullLegIso q c pC wC F).hom := by
  have hraw : pushPullMap F (Over.homMk c wC : Over.mk pC ⟶ Over.mk q)
      = rawPushPullMap c q pC wC F := rfl
  rw [hraw, rawPushPullMap_self_gen]
  have hLAU : (Scheme.Modules.restrictAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) ≫
        (pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).hom.app
            ((Scheme.Modules.pullback q).obj F)) =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  subst wC
  simp only [pushPullLegIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Iso.app_hom, Category.comp_id,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  rw [← hLAU]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-! ### Restrict-world unit calculus for the per-leg face (Steps 0–3′ of
`lem:pushPull_interLegHom_sections`) -/

/-- Step 0: the pullback-pushforward adjunction unit, post-composed with the pushforward of
the `restrictFunctorIsoPullback` inverse component, is the restriction-adjunction unit. -/
lemma unit_pushforward_rFIP_inv {W₁ W₂ : Scheme.{u}} (j : W₁ ⟶ W₂) [IsOpenImmersion j]
    (N : W₂.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N ≫
        (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N) =
      (Scheme.Modules.restrictAdjunction j).unit.app N := by
  have h : (Scheme.Modules.restrictAdjunction j).unit.app N ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ N
  have h2 : (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N) =
      𝟙 ((Scheme.Modules.pushforward j).obj
        ((Scheme.Modules.restrictFunctor j).obj N)) :=
    ((Functor.map_comp _ _ _).symm.trans
      (congrArg (Scheme.Modules.pushforward j).map (Iso.hom_inv_id_app _ _))).trans
      (CategoryTheory.Functor.map_id _ _)
  calc (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N ≫
        (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N)
      = ((Scheme.Modules.restrictAdjunction j).unit.app N ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N)) ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N) :=
        congrArg (fun w => w ≫ (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N)) h.symm
    _ = (Scheme.Modules.restrictAdjunction j).unit.app N ≫
          ((Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) ≫
           (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N)) :=
        Category.assoc _ _ _
    _ = (Scheme.Modules.restrictAdjunction j).unit.app N :=
        (congrArg (fun w => (Scheme.Modules.restrictAdjunction j).unit.app N ≫ w) h2).trans
          (Category.comp_id _)

/-- Step 1 (K5): the iterated restriction-adjunction units compose, through the
`restrictFunctorComp` identification, to the unit of the composite open immersion. -/
lemma restrict_unit_comp {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (F : X.Modules) :
    (Scheme.Modules.restrictAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) =
      (Scheme.Modules.restrictAdjunction (c ≫ q)).unit.app F := by
  apply Scheme.Modules.hom_ext
  intro U
  have key : F.presheaf.map (homOfLE (q.image_preimage_le U)).op ≫
      F.presheaf.map ((Scheme.Hom.opensFunctor q).map
        (homOfLE (c.image_preimage_le (q ⁻¹ᵁ U)))).op ≫
      F.presheaf.map (eqToHom
        (show (c ≫ q) ''ᵁ (c ⁻¹ᵁ (q ⁻¹ᵁ U)) = q ''ᵁ (c ''ᵁ (c ⁻¹ᵁ (q ⁻¹ᵁ U))) by simp)).op =
      F.presheaf.map (homOfLE ((c ≫ q).image_preimage_le U)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    exact congrArg
      (fun t : ((c ≫ q) ''ᵁ (c ⁻¹ᵁ (q ⁻¹ᵁ U))) ⟶ U => F.presheaf.map t.op)
      (Subsingleton.elim _ _)
  exact key

/-- The β-chain collapse in the middle scheme: the pullback-pushforward unit followed by the
pushforward of the restrict-world conjugates is the restriction unit (with the
`restrictFunctorComp` tail kept). -/
lemma inner_beta_chain {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) ≫
      (Scheme.Modules.pushforward c).map
        ((Scheme.Modules.pullback c).map
            ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
          (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
          (Scheme.Modules.restrictFunctorComp c q).inv.app F) =
      (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) := by
  -- naturality of the `c`-unit against `(rFIP q).inv.app F`
  have hnat : (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q) =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) ≫
      (Scheme.Modules.pushforward c).map ((Scheme.Modules.pullback c).map
        ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction c).unit.naturality
      ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)
  have h0c := unit_pushforward_rFIP_inv c (F.restrict q)
  calc (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.pullback c).map
              ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
            (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
            (Scheme.Modules.restrictFunctorComp c q).inv.app F)
      = (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
        (Scheme.Modules.pushforward c).map ((Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F) ≫ w)
          ((Functor.map_comp _ _ _).trans
            (congrArg (fun w => (Scheme.Modules.pushforward c).map
                ((Scheme.Modules.pullback c).map
                  ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)) ≫ w)
              (Functor.map_comp _ _ _)))
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
        (Scheme.Modules.pushforward c).map ((Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F))) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => w ≫ (Scheme.Modules.pushforward c).map
            ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
          (Scheme.Modules.pushforward c).map
            ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) hnat.symm
    _ = (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        Category.assoc _ _ _
    _ = (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q))) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫ w)
          (Category.assoc _ _ _).symm
    _ = (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
          w ≫ (Scheme.Modules.pushforward c).map
            ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) h0c

end AlgebraicGeometry
