/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.PresheafDualPullback

/-!
# Composition of the presheaf dual pullback comparison

This file proves the composition law for `presheafDualPullbackComparison`.
Keeping the high-heartbeat cocycle proof separate lets its unit and naturality
consumers compile in parallel with this module.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

open Opposite

namespace Scheme

namespace Modules

/-- The presheaf underlying `M.restrict f` is definitionally the pushforward of
`M.val` along the inverse structure-ring comparison. The abstract comparison in
blueprint declaration `def:pushforward_obj_val_restrict_iso` therefore reduces to
the identity isomorphism. -/
noncomputable def pushforwardObjValRestrictIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) :
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    (PresheafOfModules.pushforward β).obj M.val ≅ (M.restrict f).val :=
  Iso.refl _

/-- The adjunction-uniqueness comparison for a composite open immersion factors
through the comparisons for its two factors. This is the dual-side `H1` cocycle
from blueprint lemma `lem:presheafdual_h1_cocycle`, obtained by instantiating
`Adjunction.leftAdjointUniq_leftAdjointCompIso_comm`. -/
lemma presheafDualH1Cocycle {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion h] [IsOpenImmersion f] :
    let φRf := (Scheme.Hom.toRingCatSheafHom f).hom
    let αf : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let βf : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight αf (forget₂ CommRingCat RingCat)
    let φRh := (Scheme.Hom.toRingCatSheafHom h).hom
    let αh : Z.presheaf ⟶ h.opensFunctor.op ⋙ Y.presheaf :=
      { app := fun U => (h.appIso U.unop).inv
        naturality := fun _ _ i => h.appIso_inv_naturality i }
    let βh : Z.ringCatSheaf.obj ⟶ h.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
      Functor.whiskerRight αh (forget₂ CommRingCat RingCat)
    let φRhf := (Scheme.Hom.toRingCatSheafHom (h ≫ f)).hom
    let αhf : Z.presheaf ⟶ (h ≫ f).opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => ((h ≫ f).appIso U.unop).inv
        naturality := fun _ _ i => (h ≫ f).appIso_inv_naturality i }
    let βhf : Z.ringCatSheaf.obj ⟶ (h ≫ f).opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight αhf (forget₂ CommRingCat RingCat)
    ∀ (hadjf : PresheafOfModules.pushforward βf ⊣ PresheafOfModules.pushforward φRf)
      (hadjh : PresheafOfModules.pushforward βh ⊣ PresheafOfModules.pushforward φRh)
      (hadjhf : PresheafOfModules.pushforward βhf ⊣ PresheafOfModules.pushforward φRhf),
    (Adjunction.leftAdjointCompIso hadjf hadjh hadjhf
        (PresheafOfModules.pushforwardComp φRf φRh)).hom ≫
      (hadjhf.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φRhf)).hom =
    Functor.whiskerRight
        (hadjf.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φRf)).hom
        (PresheafOfModules.pushforward βh) ≫
      Functor.whiskerLeft (PresheafOfModules.pullback φRf)
        (hadjh.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φRh)).hom ≫
      (PresheafOfModules.pullbackComp φRf φRh).hom := by
  intro φRf αf βf φRh αh βh φRhf αhf βhf hadjf hadjh hadjhf
  exact Adjunction.leftAdjointUniq_leftAdjointCompIso_comm hadjf hadjh hadjhf
    (PresheafOfModules.pullbackPushforwardAdjunction φRf)
    (PresheafOfModules.pullbackPushforwardAdjunction φRh)
    (PresheafOfModules.pullbackPushforwardAdjunction φRhf)
    (PresheafOfModules.pushforwardComp φRf φRh)

/-- The category-theoretic cancellation skeleton used in the composition proof.
Keeping it over one abstract category lets associativity, naturality, and the four
isomorphism cancellations proceed without exposing implementation-specific
category instances of the presheaf module category. -/
private lemma c2_assemble {C : Type*} [Category C]
    {A1 A2 A3 A4 A5 A6 A7 A8 A9 : C}
    (aHinv : A1 ⟶ A2) (aH : A2 ⟶ A1) (s : A2 ⟶ A3)
    (fc : A4 ⟶ A2) (fcinv : A2 ⟶ A4)
    (p0 : A1 ⟶ A5) (pc : A5 ⟶ A1)
    (phf : A4 ⟶ A6) (hh : A6 ⟶ A5) (Pfhif : A5 ⟶ A7)
    (Hhinv : A7 ⟶ A8) (sDTh : A8 ⟶ A9) (p3 : A9 ⟶ A3)
    (pushSDTf : A4 ⟶ A8) (Pushhif : A6 ⟶ A8) (hhdmf : A8 ⟶ A7)
    (h_aHinv : aHinv ≫ aH = 𝟙 A1)
    (h_fcinv : fcinv ≫ fc = 𝟙 A2)
    (hcoc : fc ≫ aH = phf ≫ hh ≫ pc)
    (h_pc : pc ≫ p0 = 𝟙 A5)
    (hnat : hh ≫ Pfhif = Pushhif ≫ hhdmf)
    (hfold : phf ≫ Pushhif = pushSDTf)
    (h_hh2 : hhdmf ≫ Hhinv = 𝟙 A8)
    (hstar : fc ≫ s = pushSDTf ≫ sDTh ≫ p3) :
    aHinv ≫ s = p0 ≫ Pfhif ≫ (Hhinv ≫ sDTh) ≫ p3 := by
  have key : fc ≫ aH ≫ p0 ≫ Pfhif ≫ (Hhinv ≫ sDTh) ≫ p3 = fc ≫ s := by
    rw [hstar, ← Category.assoc fc aH, hcoc]
    simp only [Category.assoc]
    rw [← Category.assoc pc p0, h_pc, Category.id_comp,
        ← Category.assoc hh Pfhif, hnat]
    simp only [Category.assoc]
    rw [← Category.assoc hhdmf Hhinv, h_hh2, Category.id_comp,
        ← Category.assoc phf Pushhif, hfold]
  have hX : aH ≫ p0 ≫ Pfhif ≫ (Hhinv ≫ sDTh) ≫ p3 = s := by
    have h2 := congrArg (fcinv ≫ ·) key
    simp only [← Category.assoc, h_fcinv, Category.id_comp] at h2
    simpa using h2
  rw [← hX, ← Category.assoc aHinv aH, h_aHinv, Category.id_comp]

open PresheafOfModules InternalHom Opposite in
/-- Naturality of a dual section along a morphism in the thin slice category over
`base`. The slice objects are implicit so the composition proof can infer them
from the two evaluations of `φ`. -/
private lemma hstar_naturality {X : Scheme.{u}} (M : X.Modules)
    {base : TopologicalSpace.Opens ↥X}
    (φ : restr base M.val ⟶
         restr base
           (𝟙_ (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))))
    {A B : (Over base)ᵒᵖ} (g : A ⟶ B)
    (z : ((restr base M.val).obj A : Type u)) :
    (ModuleCat.Hom.hom
        ((restr base
            (𝟙_ (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).map g))
        (ModuleCat.Hom.hom (φ.app A) z)
      = (ModuleCat.Hom.hom (φ.app B))
          (ModuleCat.Hom.hom ((restr base M.val).map g) z) :=
  (PresheafOfModules.naturality_apply φ g z).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
-- Expanding three adjunction comparisons creates a deep but terminating defeq problem.
/-- Composition law for `presheafDualPullbackComparison`, dual to
`pullbackTensorMap_restrict`. The comparison for `h ≫ f` factors through
`pullbackComp`, the comparisons for `f` and `h`, and the dual of
`restrictFunctorComp`. This is blueprint lemma
`lem:presheafdual_pullback_comparison_restrict`. -/
lemma presheafDualPullbackComparison_restrict {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion h] [IsOpenImmersion f] (M : X.Modules) :
    presheafDualPullbackComparison (h ≫ f) M =
      (PresheafOfModules.pullbackComp (Scheme.Hom.toRingCatSheafHom f).hom
          (Scheme.Hom.toRingCatSheafHom h).hom).symm.app
            (PresheafOfModules.dual (R₀ := X.presheaf) M.val)
      ≪≫ (PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom h).hom).mapIso
            (presheafDualPullbackComparison f M)
      ≪≫ presheafDualPullbackComparison h (M.restrict f)
      ≪≫ PresheafOfModules.dualIsoOfIso
            ((SheafOfModules.forget Z.ringCatSheaf).mapIso
              ((Scheme.Modules.restrictFunctorComp h f).app M)) := by
  -- Reduce to the forward natural transformations and expose the three comparisons.
  apply Iso.ext
  simp only [presheafDualPullbackComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  -- Reconstruct the three adjunctions used by the comparison definitions.
  let hadjf : PresheafOfModules.pushforward
        (Functor.whiskerRight
          ({ app := fun U => (f.appIso U.unop).inv
             naturality := fun _ _ i => f.appIso_inv_naturality i } :
          Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf) (forget₂ CommRingCat RingCat)) ⊣
      PresheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom f).hom :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction _ _
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  let hadjh : PresheafOfModules.pushforward
        (Functor.whiskerRight
          ({ app := fun U => (h.appIso U.unop).inv
             naturality := fun _ _ i => h.appIso_inv_naturality i } :
          Z.presheaf ⟶ h.opensFunctor.op ⋙ Y.presheaf) (forget₂ CommRingCat RingCat)) ⊣
      PresheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom h).hom :=
    PresheafOfModules.pushforwardPushforwardAdj h.isOpenEmbedding.isOpenMap.adjunction _ _
      (by ext U x; exact congr($((h.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(h.appIso_inv_app_presheafMap U.unop) x))
  let αhf : Z.presheaf ⟶ (h ≫ f).opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => ((h ≫ f).appIso U.unop).inv
      naturality := fun _ _ i => (h ≫ f).appIso_inv_naturality i }
  let hadjhf : PresheafOfModules.pushforward
        (Functor.whiskerRight αhf (forget₂ CommRingCat RingCat)) ⊣
      PresheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom (h ≫ f)).hom :=
    PresheafOfModules.pushforwardPushforwardAdj (h ≫ f).isOpenEmbedding.isOpenMap.adjunction _ _
      (by ext U x; exact congr($(((h ≫ f).app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($((h ≫ f).appIso_inv_app_presheafMap U.unop) x))
  have hcoc := presheafDualH1Cocycle h f hadjf hadjh hadjhf
  -- Package the H1 cancellations with `c2_assemble`; only the sectionwise
  -- `sliceDualTransport` compatibility remains in `hstar`.
  let βh : Z.ringCatSheaf.obj ⟶ (Hom.opensFunctor h).op ⋙ Y.ringCatSheaf.obj :=
    Functor.whiskerRight
      ({ app := fun U => (h.appIso U.unop).inv
         naturality := fun _ _ i => h.appIso_inv_naturality i } :
        Z.presheaf ⟶ (Hom.opensFunctor h).op ⋙ Y.presheaf)
      (forget₂ CommRingCat RingCat)
  let βf : Y.ringCatSheaf.obj ⟶ (Hom.opensFunctor f).op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight
      ({ app := fun U => (f.appIso U.unop).inv
         naturality := fun _ _ i => f.appIso_inv_naturality i } :
        Y.presheaf ⟶ (Hom.opensFunctor f).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat)
  let H1hf := hadjhf.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction (Scheme.Hom.toRingCatSheafHom (h ≫ f)).hom)
  let H1f := hadjf.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction (Scheme.Hom.toRingCatSheafHom f).hom)
  let H1h := hadjh.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction (Scheme.Hom.toRingCatSheafHom h).hom)
  let FC := hadjf.leftAdjointCompIso hadjh hadjhf
    (PresheafOfModules.pushforwardComp (Scheme.Hom.toRingCatSheafHom f).hom
      (Scheme.Hom.toRingCatSheafHom h).hom)
  let pbC := PresheafOfModules.pullbackComp (Scheme.Hom.toRingCatSheafHom f).hom
    (Scheme.Hom.toRingCatSheafHom h).hom
  let iMf := PresheafOfModules.isoMk (fun V => sliceDualTransport f M V)
    (by intro V W g; subsingleton)
  let gf := (H1f.app M.val.dual).inv ≫ iMf.hom
  refine c2_assemble
    (aHinv := (H1hf.app M.val.dual).inv) (aH := (H1hf.app M.val.dual).hom)
    (s := (PresheafOfModules.isoMk (fun V => sliceDualTransport (h ≫ f) M V)
      (by intro V W g; subsingleton)).hom)
    (fc := FC.hom.app M.val.dual) (fcinv := FC.inv.app M.val.dual)
    (p0 := (pbC.symm.app M.val.dual).hom) (pc := pbC.hom.app M.val.dual)
    (phf := (PresheafOfModules.pushforward βh).map (H1f.hom.app M.val.dual))
    (hh := H1h.hom.app
      ((PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f).hom).obj M.val.dual))
    (Pfhif := (PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom h).hom).map gf)
    (Hhinv := (H1h.app (M.restrict f).val.dual).inv)
    (sDTh := (PresheafOfModules.isoMk (fun V => sliceDualTransport h (M.restrict f) V)
      (by intro V W g; subsingleton)).hom)
    (p3 := (PresheafOfModules.dualIsoOfIso
      ((SheafOfModules.forget Z.ringCatSheaf).mapIso ((restrictFunctorComp h f).app M))).hom)
    (pushSDTf := (PresheafOfModules.pushforward βh).map iMf.hom)
    (Pushhif := (PresheafOfModules.pushforward βh).map gf)
    (hhdmf := H1h.hom.app (M.restrict f).val.dual)
    (h_aHinv := (H1hf.app M.val.dual).inv_hom_id)
    (h_fcinv := FC.inv_hom_id_app M.val.dual)
    (hcoc := NatTrans.congr_app hcoc M.val.dual)
    (h_pc := pbC.hom_inv_id_app M.val.dual)
    (hnat := (H1h.hom.naturality gf).symm)
    (hfold := ?hfold)
    (h_hh2 := H1h.hom_inv_id_app (M.restrict f).val.dual)
    (hstar := ?hstar)
  case hfold =>
    rw [← Functor.map_comp]
    refine congrArg (PresheafOfModules.pushforward βh).map ?_
    change H1f.hom.app M.val.dual ≫ gf = iMf.hom
    rw [← Category.assoc, show H1f.hom.app M.val.dual ≫ (H1f.app M.val.dual).inv = 𝟙 _ from
      (H1f.app M.val.dual).hom_inv_id, Category.id_comp]
  case hstar =>
    -- Prove the remaining pushforward-side compatibility sectionwise.
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [PresheafOfModules.comp_app, PresheafOfModules.isoMk_hom_app,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [sliceDualTransport_app_apply (h ≫ f) M V ((FC.hom.app M.val.dual).app V φ) W z]
    rw [dualUnitRingSwap_apply]
    -- RHS: reduce the inner pushforward.map + isoMk to `sliceDualTransport f M hV`
    erw [PresheafOfModules.pushforward_map_app_apply βh iMf.hom V φ]
    simp only [iMf, PresheafOfModules.isoMk_hom_app]
    -- LHS: split the composite structure-ring iso via the `appIso` cocycle `comp_appIso`,
    -- so the leading `(h ≫ f).appIso` matches the nested `h.appIso ∘ f.appIso` of the RHS.
    rw [Scheme.Hom.comp_appIso h f (unop W).left]
    simp only [Iso.trans_hom, CommRingCat.hom_comp, RingHom.comp_apply, Functor.mapIso_hom]
    -- RHS: reduce `dualIsoOfIso` (precomposition by the reindexed `rfc.hom`) and the two
    -- `sliceDualTransport`s to their `dualUnitRingSwap`/`appIso` forms.
    erw [sliceDualTransport_app_apply h (M.restrict f) V _ W]
    rw [dualUnitRingSwap_apply]
    erw [sliceDualTransport_app_apply f M (op ((Hom.opensFunctor h).obj (unop V))) φ
      (op (Over.mk ((Hom.opensFunctor h).map (unop W).hom)))]
    rw [dualUnitRingSwap_apply]
    -- cancel the two now-matching structure-ring iso layers (`h.appIso`, then `f.appIso`)
    refine congrArg (Hom.appIso h (unop W).left).hom.hom ?_
    refine congrArg (Hom.appIso f ((Hom.opensFunctor h).obj (unop W).left)).hom.hom ?_
    -- Expand the composition comparison into its unit and counit factors. After
    -- this reduction, the goal is naturality of `φ` in a thin slice category.
    simp only [FC]
    rw [Adjunction.leftAdjointCompIso_hom_app]
    -- Sectionwise reduction of `(FC.hom.app dM).app V φ`:
    --   * `pushforwardComp = Iso.refl` ⇒ the middle `e.inv` factor collapses to `𝟙`;
    --   * distribute `.app V` over the composite to a function composition.
    simp only [PresheafOfModules.pushforwardComp, Iso.refl_inv, NatTrans.id_app,
      PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    -- Peel the two `pushforward.map` wrappers of the `unit` factor (T1) with EXPLICIT args —
    -- the codebase pattern (cf. L868) that avoids the `restrictScalars` carrier-diamond `whnf`
    -- bomb that bare `erw`/`simp` matching triggers.
    erw [PresheafOfModules.pushforward_map_app_apply βh
          ((PresheafOfModules.pushforward βf).map (hadjhf.unit.app M.val.dual)) V φ,
        PresheafOfModules.pushforward_map_app_apply βf (hadjhf.unit.app M.val.dual)
          (op ((Hom.opensFunctor h).obj (unop V))) φ]
    -- peel the single `pushforward.map` wrapper of the `counit_f` factor (T3), explicit args.
    erw [PresheafOfModules.pushforward_map_app_apply βh
          (hadjf.counit.app ((PresheafOfModules.pushforward (Hom.toRingCatSheafHom h).hom).obj
            ((PresheafOfModules.pushforward
              (Functor.whiskerRight αhf (forget₂ CommRingCat RingCat))).obj M.val.dual))) V _]
    -- expose `pushforwardPushforwardAdj` from the `let`s, then reduce the three unit/counit
    -- factors to presheaf restriction maps of the dual via the local `rfl` value lemmas
    -- (explicit `adj` anchors the counit higher-order unification).
    simp only [hadjf, hadjh, hadjhf]
    -- Reduce the three unit/counit factors to dual restriction maps. The value lemmas are `rfl`,
    -- but both `rw` (coercion-form mismatch `ConcreteCategory.hom`/`ModuleCat.Hom.hom`) and bare
    -- `erw` (carrier-diamond `whnf` bomb) fail; give FULLY EXPLICIT anchoring args so `erw`
    -- matching is cheap (the codebase pattern).
    erw [PresheafOfModules.ppadj_unit_app_app_apply
          (adj := (h ≫ f).isOpenEmbedding.isOpenMap.adjunction)
          (φ := Functor.whiskerRight αhf (forget₂ CommRingCat RingCat))
          (ψ := (Hom.toRingCatSheafHom (h ≫ f)).hom) (M := M.val.dual)
          (U := op ((Hom.opensFunctor f).obj ((Hom.opensFunctor h).obj (unop V))))]
    erw [PresheafOfModules.ppadj_counit_app_app_apply
          (adj := f.isOpenEmbedding.isOpenMap.adjunction) (φ := βf)
          (ψ := (Hom.toRingCatSheafHom f).hom)
          (N := (PresheafOfModules.pushforward (Hom.toRingCatSheafHom h).hom).obj
            ((PresheafOfModules.pushforward
              (Functor.whiskerRight αhf (forget₂ CommRingCat RingCat))).obj M.val.dual))
          (U := op ((Hom.opensFunctor h).obj (unop V)))]
    erw [PresheafOfModules.ppadj_counit_app_app_apply
          (adj := h.isOpenEmbedding.isOpenMap.adjunction) (φ := βh)
          (ψ := (Hom.toRingCatSheafHom h).hom)
          (N := (PresheafOfModules.pushforward
            (Functor.whiskerRight αhf (forget₂ CommRingCat RingCat))).obj M.val.dual)
          (U := V)]
    -- Reduce the two pushforward-object restriction maps `N.map` to `M.val.dual.map` (`rfl`).
    erw [PresheafOfModules.pushforward_obj_map_apply
          (φ := Functor.whiskerRight αhf (forget₂ CommRingCat RingCat)) (M := M.val.dual)
          (f := (h.isOpenEmbedding.isOpenMap.adjunction.unit.app (unop V)).op)]
    erw [PresheafOfModules.pushforward_obj_map_apply (φ := (Hom.toRingCatSheafHom h).hom)
          (M := (PresheafOfModules.pushforward
            (Functor.whiskerRight αhf (forget₂ CommRingCat RingCat))).obj M.val.dual)
          (f := (f.isOpenEmbedding.isOpenMap.adjunction.unit.app
            (unop (op ((Hom.opensFunctor h).obj (unop V))))).op)]
    erw [PresheafOfModules.pushforward_obj_map_apply
          (φ := Functor.whiskerRight αhf (forget₂ CommRingCat RingCat)) (M := M.val.dual)
          (f := ((TopologicalSpace.Opens.map h.base).map
            (f.isOpenEmbedding.isOpenMap.adjunction.unit.app
              (unop (op ((Hom.opensFunctor h).obj (unop V))))).op.unop).op)]
    -- Reduce the three dual restrictions to one evaluation of `φ` at the
    -- corresponding reindexed slice object.
    erw [PresheafOfModules.dual_map_app_apply, PresheafOfModules.dual_map_app_apply,
      PresheafOfModules.dual_map_app_apply]
    -- Normalize the slice and apply naturality along its unique comparison map.
    simp only [unop_op]
    -- `g`'s underlying open inclusion: the two slice domains agree by `comp_image`.
    have hle : ((Hom.opensFunctor f).obj ((Hom.opensFunctor h).obj (unop W).left))
        ≤ ((Hom.opensFunctor (h ≫ f)).obj (unop W).left) :=
      le_of_eq (Scheme.Hom.comp_image h f (unop W).left).symm
    -- `key` = φ-naturality at the canonical slice morphism `sliceL ⟶ sliceR`.
    have key := hstar_naturality M φ
      (Over.homMk (homOfLE hle) (Subsingleton.elim _ _) :
        (Over.mk ((Hom.opensFunctor f).map ((Hom.opensFunctor h).map (unop W).hom)) :
            Over (f ''ᵁ h ''ᵁ unop V)) ⟶
          (Over.map ((h ≫ f).isOpenEmbedding.isOpenMap.adjunction.counit.app
                (f ''ᵁ h ''ᵁ unop V))).obj
            ((Over.map ((Hom.opensFunctor (h ≫ f)).map ((TopologicalSpace.Opens.map h.base).map
                  (f.isOpenEmbedding.isOpenMap.adjunction.unit.app (h ''ᵁ unop V))))).obj
              ((Over.map ((Hom.opensFunctor (h ≫ f)).map
                    (h.isOpenEmbedding.isOpenMap.adjunction.unit.app (unop V)))).obj
                (Over.mk ((Hom.opensFunctor (h ≫ f)).map (unop W).hom))))).op z
    -- The remaining carrier and `eqToIso` congruences are definitional.
    convert key using 2 <;> rfl

end Modules

end Scheme

end AlgebraicGeometry

end -- noncomputable section
