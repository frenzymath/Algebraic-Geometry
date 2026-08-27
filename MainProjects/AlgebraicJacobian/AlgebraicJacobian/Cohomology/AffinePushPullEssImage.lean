/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic.SetNotationForOrder
import AlgebraicJacobian.Cohomology.FlatBaseChange
import AlgebraicJacobian.Cohomology.QcohTildeSections
import AlgebraicJacobian.Cohomology.OpenImmersionPushforward
import AlgebraicJacobian.Cohomology.CechTermAcyclic

/-!
# Pullback of a pushforward from an affine open is a pushforward (essential-image form)

This file supplies the affine-local heart of the Stage-2 essential-image reduction of the
open-immersion Beck–Chevalley comparison (Stacks 02KG/02KH, blueprint
`lem:openimm_bareBC_app_isIso_affine`): for a morphism `gU : W ⟶ Y` of *affine* schemes, an
affine open `VU ⊆ Y` and a quasi-coherent `K` on `VU`, the pulled-back pushforward
`gU^*((VU.ι)_* K)` lies in the essential image of the pushforward along the preimage open
`gU ⁻¹ᵁ VU ↪ W` (`pullback_pushforward_affineOpen_essImage`).  The content is the sorry-free
affine termwise base change `affinePushforwardPullbackBaseChange` over the *abstract* ring
pushout `Γ(W) ⊗_{Γ(Y)} Γ(VU)`, whose `Spec` is identified with the preimage open by the
cartesianness of `Spec` of a pushout (`isPullback_SpecMap_of_isPushout`) and the range
computation of the base-changed open immersion (`IsOpenImmersion.range_pullbackSnd`).

Supporting general pieces, each reusable:

* `Scheme.Modules.pullbackIsoPushforwardInv` — for a scheme iso `e`, the pullback along
  `e.hom` is (uniqueness of left adjoints) the pushforward along `e.inv`;
* `pushforwardRestrictOpensIso` — the open-open pushforward–restriction commutation
  `(V₀.ι)_* ⋙ (-)|_U ≅ (-)|_{U∩V₀} ⋙ (U.ι⁻¹V₀).ι_*` (the `glueOverlapBaseChangeIso`
  pattern: both composites are site-level pushforwards along the same opens functor);
* `restrict_pullback_pushforward_essImage` — the full member-node assembly: for
  `g' : X' ⟶ X`, an affine open immersion `w : W ⟶ X'` whose `g'`-image lies in an affine
  open `U ⊆ X`, an affine open `V₀ ⊆ X` and quasi-coherent `F`, the restriction to `W` of
  `g'^*((V₀.ι)_* (V₀.ι)^* F)` is a pushforward from `w⁻¹(g'⁻¹(V₀))`.

Consumed by `openImmersion_pushPull_essImage_member` in
`Cohomology/CechHigherDirectImageUnconditional.lean`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

/-! ## Pullback along an iso is pushforward along the inverse -/

/-- **Pullback along a scheme isomorphism is pushforward along the inverse.**  For
`e : X ≅ Y`, the pushforward `(e.inv)_*` is quasi-inverse to `(e.hom)_*`
(`pushforwardEquivOfIso`), hence left adjoint to it; by uniqueness of left adjoints it is
isomorphic to `(e.hom)^*`.  Project-local; blueprint `lem:openimm_bareBC_app_isIso_affine`
(supporting piece). -/
noncomputable def Scheme.Modules.pullbackIsoPushforwardInv {X Y : Scheme.{u}} (e : X ≅ Y) :
    Scheme.Modules.pullback e.hom ≅ Scheme.Modules.pushforward e.inv :=
  Adjunction.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom)
    (Scheme.Modules.pushforwardEquivOfIso e).symm.toAdjunction

/-! ## Open-open pushforward–restriction commutation

For opens `V₀, U` of `X`, restricting a pushforward `(V₀.ι)_* K` to `U` agrees with pushing
the restriction of `K` to `U ∩ V₀` forward along `(U.ι ⁻¹ᵁ V₀).ι`.  All four functors are
site-level pushforwards; both composites are pushforwards along the SAME opens functor, so
the comparison is the `restrictFunctorComp`/`glueOverlapBaseChangeIso` pattern. -/

variable {X : Scheme.{u}}

/-- The range of `(U.ι ⁻¹ᵁ V₀).ι ≫ U.ι` is contained in `V₀`. -/
lemma range_opensInter_le (V₀ U : X.Opens) :
    Set.range ((U.ι ⁻¹ᵁ V₀).ι ≫ U.ι) ⊆ Set.range V₀.ι := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  exact (Set.image_preimage_subset _ _).trans (by simp)

/-- The open immersion `↑(U.ι ⁻¹ᵁ V₀) ⟶ ↑V₀` lifting `(U.ι ⁻¹ᵁ V₀).ι ≫ U.ι` through
`V₀.ι` — the "`U ∩ V₀` into `V₀`" leg of the open-open square.  Project-local. -/
noncomputable def opensInterLift (V₀ U : X.Opens) :
    (↑(U.ι ⁻¹ᵁ V₀) : Scheme.{u}) ⟶ (↑V₀ : Scheme.{u}) :=
  IsOpenImmersion.lift V₀.ι ((U.ι ⁻¹ᵁ V₀).ι ≫ U.ι) (range_opensInter_le V₀ U)

@[reassoc]
lemma opensInterLift_fac (V₀ U : X.Opens) :
    opensInterLift V₀ U ≫ V₀.ι = (U.ι ⁻¹ᵁ V₀).ι ≫ U.ι :=
  IsOpenImmersion.lift_fac _ _ _

instance (V₀ U : X.Opens) : IsOpenImmersion (opensInterLift V₀ U) :=
  haveI : IsOpenImmersion (opensInterLift V₀ U ≫ V₀.ι) := by
    rw [opensInterLift_fac]; infer_instance
  IsOpenImmersion.of_comp (opensInterLift V₀ U) V₀.ι

/-- **Opens identity of the open-open square**: for an open `O ⊆ U`, the preimage under
`V₀.ι` of its image in `X` is the image, under the `U ∩ V₀ → V₀` leg, of its preimage in
`U ∩ V₀`.  The underlying-opens form of the cartesianness of the open-open square; the
site-level input identifying the two composite pushforwards.  Project-local. -/
lemma opensInter_image_eq (V₀ U : X.Opens) (O : (↑U : Scheme.{u}).Opens) :
    V₀.ι ⁻¹ᵁ (U.ι ''ᵁ O) = opensInterLift V₀ U ''ᵁ ((U.ι ⁻¹ᵁ V₀).ι ⁻¹ᵁ O) := by
  have hpt : ∀ z, V₀.ι (opensInterLift V₀ U z) = U.ι ((U.ι ⁻¹ᵁ V₀).ι z) := fun z => by
    have := congrArg (fun m : (↑(U.ι ⁻¹ᵁ V₀) : Scheme.{u}) ⟶ X => m z) (opensInterLift_fac V₀ U)
    simpa using this
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyO, hyx⟩ := hx
    have hyx' : U.ι y = V₀.ι x := hyx
    -- `y ∈ U` lands in `V₀`, so it comes from `U ∩ V₀`
    have hyV : U.ι y ∈ (V₀ : Set X) := by
      rw [hyx', ← Scheme.Opens.range_ι V₀]; exact Set.mem_range_self x
    have hy' : y ∈ (U.ι ⁻¹ᵁ V₀ : (↑U : Scheme.{u}).Opens) := hyV
    refine ⟨⟨y, hy'⟩, hyO, ?_⟩
    change opensInterLift V₀ U ⟨y, hy'⟩ = x
    apply V₀.ι.isOpenEmbedding.injective
    show V₀.ι (opensInterLift V₀ U ⟨y, hy'⟩) = V₀.ι x
    rw [hpt ⟨y, hy'⟩, ← hyx']
    rfl
  · rintro ⟨z, hzO, rfl⟩
    change V₀.ι (opensInterLift V₀ U z) ∈ U.ι ''ᵁ O
    rw [hpt z]
    exact Set.mem_image_of_mem _ hzO

/-- `appLE` transport along an equality of morphisms (proof-irrelevant open-inequality
witnesses).  Project-local helper, mirrored from `Picard/GlueDescent`. -/
private lemma appLE_congr_mor' {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (U : B.Opens)
    (W : A.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

/-- **Structure-sheaf compatibility of the open-open square**: the two composite section
maps `Γ(U, O) ⟶ Γ(V₀, (U∩V₀→V₀) '' ((U∩V₀→U)⁻¹ O))` — "through `X`" (via `(U.ι.appIso O)⁻¹`,
`V₀.ι.app`, and the opens identity `opensInter_image_eq`) and "through `U ∩ V₀`" — coincide.
Both are the `appLE` of the two (equal) composites of the square.  Project-local. -/
lemma opensInter_appIso_compat (V₀ U : X.Opens) (O : (↑U : Scheme.{u}).Opens) :
    (U.ι.appIso O).inv ≫ V₀.ι.app (U.ι ''ᵁ O) ≫
        (↑V₀ : Scheme.{u}).presheaf.map (eqToHom (opensInter_image_eq V₀ U O).symm).op
      = (U.ι ⁻¹ᵁ V₀).ι.app O ≫
          ((opensInterLift V₀ U).appIso ((U.ι ⁻¹ᵁ V₀).ι ⁻¹ᵁ O)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_mor' (opensInterLift_fac V₀ U) _ _ _ _

/-- **The two composite opens functors of the open-open square are equal.**  Object-level
content is `opensInter_image_eq`; morphisms are proof-irrelevant in the opens preorder.
Project-local. -/
lemma opensInter_opensFunctor_eq (V₀ U : X.Opens) :
    U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map V₀.ι.base
      = TopologicalSpace.Opens.map (U.ι ⁻¹ᵁ V₀).ι.base ⋙ (opensInterLift V₀ U).opensFunctor :=
  CategoryTheory.Functor.ext (fun O => opensInter_image_eq V₀ U O)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- **Open-open pushforward–restriction commutation**: restricting a pushforward
`(V₀.ι)_* K` to `U` is the same as restricting `K` to `U ∩ V₀` (along `opensInterLift`)
and pushing forward along `(U.ι ⁻¹ᵁ V₀).ι`.  All four functors are site-level
pushforwards; both composites are pushforwards along the SAME opens functor
(`opensInter_opensFunctor_eq`), so the comparison is
`pushforwardComp ≪≫ pushforwardNatIso (eqToIso components) ≪≫ pushforwardCongr ≪≫
pushforwardComp.symm` — the `glueOverlapBaseChangeIso` pattern.  Project-local. -/
noncomputable def pushforwardRestrictOpensIso (V₀ U : X.Opens) :
    Scheme.Modules.pushforward V₀.ι ⋙ Scheme.Modules.restrictFunctor U.ι
      ≅ Scheme.Modules.restrictFunctor (opensInterLift V₀ U) ⋙
          Scheme.Modules.pushforward (U.ι ⁻¹ᵁ V₀).ι :=
  haveI h₁ : Functor.IsContinuous
      (U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map V₀.ι.base)
      (Opens.grothendieckTopology ↥(↑U : Scheme.{u}))
      (Opens.grothendieckTopology ↥(↑V₀ : Scheme.{u})) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥X) _
  haveI h₂ : Functor.IsContinuous
      (TopologicalSpace.Opens.map (U.ι ⁻¹ᵁ V₀).ι.base ⋙ (opensInterLift V₀ U).opensFunctor)
      (Opens.grothendieckTopology ↥(↑U : Scheme.{u}))
      (Opens.grothendieckTopology ↥(↑V₀ : Scheme.{u})) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥(↑(U.ι ⁻¹ᵁ V₀) : Scheme.{u})) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardNatIso _
      (NatIso.ofComponents
        (fun O => eqToIso (opensInter_image_eq V₀ U O).symm)
        (fun _ => Subsingleton.elim _ _)) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext O x
      exact congr($(opensInter_appIso_compat V₀ U (Opposite.unop O)) x)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-! ## The affine heart: pullback of a pushforward from an affine open -/

/-- **Pullback of a pushforward from an affine open along a morphism of affine schemes is
a pushforward from the preimage open** (Stacks 02KG, essential-image form; blueprint
`lem:openimm_bareBC_app_isIso_affine`, affine heart).  For `gU : W ⟶ Y` with `W`, `Y` affine,
an affine open
`VU ⊆ Y` and a quasi-coherent `K` on `VU`, the module `gU^*((VU.ι)_* K)` lies in the
essential image of `((gU ⁻¹ᵁ VU).ι)_*`.

Construction: present `VU.ι` and `gU` as `Spec` of ring maps `φ, ψ` over the `isoSpec`
identifications; `K ≅ (isoSpec.inv)_* (tilde M)` by the affine structure theorem (01I8,
`qcoh_iso_tilde_sections`); the sorry-free affine termwise base change
`affinePushforwardPullbackBaseChange` over the abstract ring pushout `B := Γ(W) ⊗_{Γ(Y)} Γ(VU)`
rewrites `(Spec ψ)^*((Spec φ)_* (tilde M))` as `(Spec σ)_*((Spec ρ)^*(tilde M))`; `Spec` of
the pushout square is cartesian (`isPullback_SpecMap_of_isPushout`), so `Spec σ` is an open
immersion with range the preimage of `VU` (`IsOpenImmersion.range_pullbackSnd`) and the
composite `Spec σ ≫ isoSpec.inv` matches `(gU ⁻¹ᵁ VU).ι` up to the `isoOfRangeEq`
identification.  Project-local. -/
theorem pullback_pushforward_affineOpen_essImage {W Y : Scheme.{u}} (gU : W ⟶ Y)
    [IsAffine W] [IsAffine Y] {VU : Y.Opens} (hVU : IsAffineOpen VU)
    (K : (↑VU : Scheme.{u}).Modules) (hK : K.IsQuasicoherent) :
    (Scheme.Modules.pushforward (gU ⁻¹ᵁ VU).ι).essImage
      ((Scheme.Modules.pullback gU).obj ((Scheme.Modules.pushforward VU.ι).obj K)) := by
  -- the ring maps presenting `VU.ι` and `gU` over the `isoSpec` identifications
  set φ := Spec.preimage (hVU.fromSpec ≫ Y.isoSpec.hom) with hφdef
  set ψ := Spec.preimage (W.isoSpec.inv ≫ gU ≫ Y.isoSpec.hom) with hψdef
  have hφmap : Spec.map φ = hVU.fromSpec ≫ Y.isoSpec.hom := Spec.map_preimage _
  have hψmap : Spec.map ψ = W.isoSpec.inv ≫ gU ≫ Y.isoSpec.hom := Spec.map_preimage _
  have heqφ : hVU.isoSpec.inv ≫ VU.ι = Spec.map φ ≫ Y.isoSpec.inv := by
    rw [hφmap, ← IsAffineOpen.isoSpec_inv_ι hVU]
    simp
  have heqψ : gU ≫ Y.isoSpec.hom = W.isoSpec.hom ≫ Spec.map ψ := by
    rw [hψmap, Iso.hom_inv_id_assoc]
  -- the abstract ring pushout and its cartesian `Spec` square
  set ρ := pushout.inl φ ψ with hρdef
  set σ := pushout.inr φ ψ with hσdef
  have hpush : IsPushout φ ψ ρ σ := IsPushout.of_hasPushout φ ψ
  have hpb : IsPullback (Spec.map ρ) (Spec.map σ) (Spec.map φ) (Spec.map ψ) :=
    isPullback_SpecMap_of_isPushout φ ψ ρ σ hpush
  haveI hφoi : IsOpenImmersion (Spec.map φ) := by
    rw [hφmap, ← IsAffineOpen.isoSpec_inv_ι hVU, Category.assoc]
    infer_instance
  haveI hσoi : IsOpenImmersion (Spec.map σ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hφoi
  -- the tilde model of `K` over `Spec Γ(Y, VU)`
  haveI hKq : ((Scheme.Modules.pushforward hVU.isoSpec.hom).obj K).IsQuasicoherent :=
    pushforward_iso_preserves_qcoh hVU.isoSpec K hK
  set M := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward hVU.isoSpec.hom).obj K)
    with hMdef
  have tK : (Scheme.Modules.pushforward hVU.isoSpec.hom).obj K ≅ tilde M :=
    qcoh_iso_tilde_sections _
  -- the transported open immersion `q` and its range
  set q : Spec (pushout φ ψ) ⟶ W := Spec.map σ ≫ W.isoSpec.inv with hqdef
  haveI : IsOpenImmersion q := inferInstance
  -- morphism-level commutations of the transported square
  have m2 : q ≫ W.isoSpec.hom = Spec.map σ := by
    rw [hqdef, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have m3 : q ≫ gU ≫ Y.isoSpec.hom = Spec.map σ ≫ Spec.map ψ := by
    rw [heqψ, ← Category.assoc, m2]
  have m6 : q ≫ gU = Spec.map ρ ≫ hVU.fromSpec := by
    have m5 : (q ≫ gU) ≫ Y.isoSpec.hom = (Spec.map ρ ≫ hVU.fromSpec) ≫ Y.isoSpec.hom := by
      rw [Category.assoc, m3, ← hpb.w, Category.assoc, ← hφmap]
    exact (cancel_mono Y.isoSpec.hom).mp m5
  -- the range identification of `q` with `(gU ⁻¹ᵁ VU).ι`
  have hrange' : Set.range q = Set.range (gU ⁻¹ᵁ VU).ι := by
    rw [Scheme.Opens.range_ι]
    -- range of the base-changed open immersion `Spec σ`
    have h1 : Set.range (Spec.map σ) = (Spec.map ψ) ⁻¹ᵁ (Spec.map φ).opensRange := by
      rw [← hpb.isoPullback_hom_snd]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr hpb.isoPullback.hom.surjective, Set.image_univ]
      exact IsOpenImmersion.range_pullbackSnd _ _
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      have hb : gU (q b) = hVU.fromSpec (Spec.map ρ b) := by
        rw [← Scheme.Hom.comp_apply, m6, Scheme.Hom.comp_apply]
      change gU (q b) ∈ (VU : Set Y)
      rw [hb, ← hVU.range_fromSpec]
      exact Set.mem_range_self _
    · intro hx
      -- `x` maps into `VU`; lift `gU x` through `fromSpec` and land in `range (Spec σ)`
      have hx' : gU x ∈ (VU : Set Y) := hx
      rw [← hVU.range_fromSpec] at hx'
      obtain ⟨t, ht⟩ := hx'
      have hWx : W.isoSpec.hom x ∈ Set.range (Spec.map σ) := by
        rw [h1]
        change Spec.map ψ (W.isoSpec.hom x) ∈ (Spec.map φ).opensRange
        rw [Scheme.Hom.mem_opensRange]
        refine ⟨t, ?_⟩
        have hl : Spec.map φ t = Y.isoSpec.hom (gU x) := by
          rw [hφmap, Scheme.Hom.comp_apply, ht]
        have hr : Spec.map ψ (W.isoSpec.hom x) = Y.isoSpec.hom (gU x) := by
          rw [← Scheme.Hom.comp_apply, ← heqψ, Scheme.Hom.comp_apply]
        rw [hl, hr]
      obtain ⟨b, hb⟩ := hWx
      refine ⟨b, ?_⟩
      have : (q ≫ W.isoSpec.hom) b = W.isoSpec.hom x := by rw [m2]; exact hb
      have h2 : W.isoSpec.hom (q b) = W.isoSpec.hom x := by
        rw [← Scheme.Hom.comp_apply]; exact this
      exact (Scheme.Hom.homeomorph W.isoSpec.hom).injective h2
  set e' := IsOpenImmersion.isoOfRangeEq q (gU ⁻¹ᵁ VU).ι hrange' with he'def
  have he' : e'.hom ≫ (gU ⁻¹ᵁ VU).ι = q :=
    IsOpenImmersion.isoOfRangeEq_hom_fac q (gU ⁻¹ᵁ VU).ι hrange'
  -- assemble the comparison chain
  -- c1 : `K ≅ (isoSpec.inv)_* (tilde M)`
  have c1 : K ≅ (Scheme.Modules.pushforward hVU.isoSpec.inv).obj (tilde M) :=
    ((Scheme.Modules.pushforwardComp hVU.isoSpec.hom hVU.isoSpec.inv).app K ≪≫
        (Scheme.Modules.pushforwardCongr hVU.isoSpec.hom_inv_id).app K ≪≫
        (Scheme.Modules.pushforwardId (↑VU : Scheme.{u})).app K).symm ≪≫
      (Scheme.Modules.pushforward hVU.isoSpec.inv).mapIso tK
  -- c2 : `(VU.ι)_* K ≅ (isoSpec_Y.inv)_* ((Spec φ)_* (tilde M))`
  have c2 : (Scheme.Modules.pushforward VU.ι).obj K ≅
      (Scheme.Modules.pushforward Y.isoSpec.inv).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) :=
    (Scheme.Modules.pushforward VU.ι).mapIso c1 ≪≫
      (Scheme.Modules.pushforwardComp hVU.isoSpec.inv VU.ι).app (tilde M) ≪≫
      (Scheme.Modules.pushforwardCongr heqφ).app (tilde M) ≪≫
      (Scheme.Modules.pushforwardComp (Spec.map φ) Y.isoSpec.inv).symm.app (tilde M)
  -- c3 : commute `gU^*` past `(isoSpec_Y.inv)_*` into `(isoSpec_W.inv)_* ∘ (Spec ψ)^*`
  have c3 : (Scheme.Modules.pullback gU).obj
      ((Scheme.Modules.pushforward Y.isoSpec.inv).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) ≅
      (Scheme.Modules.pushforward W.isoSpec.inv).obj
        ((Scheme.Modules.pullback (Spec.map ψ)).obj
          ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) :=
    (Scheme.Modules.pullback gU).mapIso
        ((Scheme.Modules.pullbackIsoPushforwardInv Y.isoSpec).symm.app _) ≪≫
      (Scheme.Modules.pullbackComp gU Y.isoSpec.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr heqψ).app _ ≪≫
      (Scheme.Modules.pullbackComp W.isoSpec.hom (Spec.map ψ)).symm.app _ ≪≫
      (Scheme.Modules.pullbackIsoPushforwardInv W.isoSpec).app _
  -- c4 : the sorry-free affine termwise base change (the genuine content)
  have c4 := affinePushforwardPullbackBaseChange φ ψ ρ σ hpush M
  -- final witness
  refine ⟨(Scheme.Modules.pushforward e'.hom).obj
    ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M)), ⟨?_⟩⟩
  calc (Scheme.Modules.pushforward (gU ⁻¹ᵁ VU).ι).obj
        ((Scheme.Modules.pushforward e'.hom).obj
          ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M)))
      ≅ (Scheme.Modules.pushforward q).obj
          ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M)) :=
        (Scheme.Modules.pushforwardComp e'.hom (gU ⁻¹ᵁ VU).ι).app _ ≪≫
          (Scheme.Modules.pushforwardCongr he').app _
    _ ≅ (Scheme.Modules.pushforward W.isoSpec.inv).obj
          ((Scheme.Modules.pushforward (Spec.map σ)).obj
            ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M))) :=
        (Scheme.Modules.pushforwardComp (Spec.map σ) W.isoSpec.inv).symm.app _
    _ ≅ (Scheme.Modules.pushforward W.isoSpec.inv).obj
          ((Scheme.Modules.pullback (Spec.map ψ)).obj
            ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) :=
        (Scheme.Modules.pushforward W.isoSpec.inv).mapIso c4.symm
    _ ≅ (Scheme.Modules.pullback gU).obj
          ((Scheme.Modules.pushforward Y.isoSpec.inv).obj
            ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) := c3.symm
    _ ≅ (Scheme.Modules.pullback gU).obj ((Scheme.Modules.pushforward VU.ι).obj K) :=
        (Scheme.Modules.pullback gU).mapIso c2.symm

/-! ## The member-node assembly -/

/-- **Restriction of the pulled-back push–pull module to an affine chart is a pushforward
from the preimage of `V₀`** (the Stage-2 member node; blueprint
`lem:openimm_bareBC_app_isIso_affine`).  For `g' : X' ⟶ X`, an open immersion `w : W ⟶ X'`
with `W` affine whose `g'`-image lies in an affine open `U ⊆ X`, an affine open `V₀ ⊆ X`,
`X` with affine absolute diagonal (e.g. separated) and `F` quasi-coherent, the restriction
`(g'^*((V₀.ι)_* (V₀.ι)^* F))|_W` lies in the essential image of the pushforward along
`w⁻¹(g'⁻¹(V₀)) ↪ W`.

Route: the pullback pseudofunctor rewrites the restriction as
`gU^*(((V₀.ι)_* (V₀.ι)^* F)|_U)` for the induced affine-schemes morphism `gU : W ⟶ U`;
the open-open commutation `pushforwardRestrictOpensIso` rewrites the restriction of the
pushforward as the pushforward `((U.ι⁻¹V₀).ι)_*` of the (quasi-coherent, iterated-opens)
restriction of `F`; `U ∩ V₀` is affine (`IsAffineOpen.inf`, affine diagonal), so the affine
heart `pullback_pushforward_affineOpen_essImage` applies.  Project-local. -/
theorem restrict_pullback_pushforward_essImage {X' W : Scheme.{u}}
    (g' : X' ⟶ X) {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    (w : W ⟶ X') [IsOpenImmersion w] [IsAffine W]
    {U : X.Opens} (hU : IsAffineOpen U) (hle : Set.range (w ≫ g') ⊆ (U : Set X))
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (Scheme.Modules.pushforward (w ⁻¹ᵁ g' ⁻¹ᵁ V₀).ι).essImage
      ((Scheme.Modules.restrictFunctor w).obj
        ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward V₀.ι).obj
          ((Scheme.Modules.pullback V₀.ι).obj F)))) := by
  haveI : IsAffine (↑U : Scheme.{u}) := hU
  -- the induced morphism of affine schemes `gU : W ⟶ U`
  set gU : W ⟶ (↑U : Scheme.{u}) :=
    IsOpenImmersion.lift U.ι (w ≫ g') (by rwa [Scheme.Opens.range_ι]) with hgUdef
  have hgU : gU ≫ U.ι = w ≫ g' := IsOpenImmersion.lift_fac _ _ _
  -- `U ∩ V₀` is an affine open of `U`
  have hVU : IsAffineOpen (U.ι ⁻¹ᵁ V₀) := by
    rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    exact hU.inf hV₀
  -- the opens identity `w⁻¹(g'⁻¹ V₀) = gU⁻¹(U.ι⁻¹ V₀)`
  have hO : w ⁻¹ᵁ g' ⁻¹ᵁ V₀ = gU ⁻¹ᵁ (U.ι ⁻¹ᵁ V₀) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hgU]
  rw [hO]
  -- the quasi-coherent restriction of `F` to `U ∩ V₀`
  set K : (↑(U.ι ⁻¹ᵁ V₀) : Scheme.{u}).Modules :=
    (Scheme.Modules.pullback (U.ι ⁻¹ᵁ V₀).ι).obj ((Scheme.Modules.pullback U.ι).obj F)
    with hKdef
  have hK : K.IsQuasicoherent :=
    isQuasicoherent_pullback_opens _ _ (isQuasicoherent_pullback_opens U F hF)
  refine Functor.essImage.ofIso ?_ (pullback_pushforward_affineOpen_essImage gU hVU K hK)
  -- identify the two modules by the pullback pseudofunctor + the open-open commutation
  -- Kid : `(restrictFunctor (opensInterLift V₀ U)).obj ((V₀.ι)^* F) ≅ K`
  have Kid : (Scheme.Modules.restrictFunctor (opensInterLift V₀ U)).obj
      ((Scheme.Modules.pullback V₀.ι).obj F) ≅ K :=
    (Scheme.Modules.restrictFunctorIsoPullback (opensInterLift V₀ U)).app _ ≪≫
      (Scheme.Modules.pullbackComp (opensInterLift V₀ U) V₀.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (opensInterLift_fac V₀ U)).app F ≪≫
      (Scheme.Modules.pullbackComp (U.ι ⁻¹ᵁ V₀).ι U.ι).symm.app F
  calc (Scheme.Modules.pullback gU).obj
        ((Scheme.Modules.pushforward (U.ι ⁻¹ᵁ V₀).ι).obj K)
      ≅ (Scheme.Modules.pullback gU).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj
            ((Scheme.Modules.pushforward V₀.ι).obj
              ((Scheme.Modules.pullback V₀.ι).obj F))) :=
        (Scheme.Modules.pullback gU).mapIso
          (((Scheme.Modules.pushforward (U.ι ⁻¹ᵁ V₀).ι).mapIso Kid.symm) ≪≫
            ((pushforwardRestrictOpensIso V₀ U).app
              ((Scheme.Modules.pullback V₀.ι).obj F)).symm)
    _ ≅ (Scheme.Modules.pullback gU).obj
          ((Scheme.Modules.pullback U.ι).obj
            ((Scheme.Modules.pushforward V₀.ι).obj
              ((Scheme.Modules.pullback V₀.ι).obj F))) :=
        (Scheme.Modules.pullback gU).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _)
    _ ≅ (Scheme.Modules.pullback (w ≫ g')).obj
          ((Scheme.Modules.pushforward V₀.ι).obj
            ((Scheme.Modules.pullback V₀.ι).obj F)) :=
        (Scheme.Modules.pullbackComp gU U.ι).app _ ≪≫
          (Scheme.Modules.pullbackCongr hgU).app _
    _ ≅ (Scheme.Modules.restrictFunctor w).obj
          ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pushforward V₀.ι).obj
            ((Scheme.Modules.pullback V₀.ι).obj F))) :=
        (Scheme.Modules.pullbackComp w g').symm.app _ ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback w).symm.app _

end AlgebraicGeometry
