/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneNativeBaseChangeLocalizing
import AlgebraicJacobian.Picard.Pic0RankOneFamilyCertificates
import AlgebraicJacobian.Picard.RelativeCurveAffineCover
import AlgebraicJacobian.Cohomology.RelativeSectionsLinear
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeTensor

/-!
# Arbitrary-cartesian base change for the native rank-one module

The vanishing of the first Cech cohomology of a basic-open cocycle datum makes
global sections commute with every scalar extension.  On each affine chart of
an arbitrary test scheme, the cartesian family is the corresponding scalar
extension of the relative curve.  The two affine section presentations then
identify the canonical Beck--Chevalley mate with that scalar-extension
equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Over.sectionsAlgebra

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

namespace BasicOpenCocycleDatum

noncomputable section

local instance nativeSectionsModuleCartesian
    (D : BasicOpenCocycleDatum C B pi)
    (W : (relCurve C B).Opens) : Module B Γ(D.nativeModule, W) :=
  Scheme.moduleKSections
    (Over.mk (relCurve C B ↘ Spec (.of B))) D.nativeModule W

private noncomputable def pullbackCongrCompSectionsEquiv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (eq : h = f ≫ g) (N : Z.Modules) :
    Γ((Scheme.Modules.pullback h).obj N, ⊤) ≃ₗ[Γ(X, ⊤)]
      Γ((Scheme.Modules.pullback g ⋙
        Scheme.Modules.pullback f).obj N, ⊤) := by
  let sheafIso := (Scheme.Modules.pullbackCongr eq).app N ≪≫
    (Scheme.Modules.pullbackComp f g).symm.app N
  let topAdd : Γ((Scheme.Modules.pullback h).obj N, ⊤) ≃+
      Γ((Scheme.Modules.pullback g ⋙
        Scheme.Modules.pullback f).obj N, ⊤) :=
    { toFun := fun x ↦ (Scheme.Modules.Hom.app sheafIso.hom ⊤).hom x
      invFun := fun x ↦ (Scheme.Modules.Hom.app sheafIso.inv ⊤).hom x
      left_inv := fun x ↦ by
        simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
          sheafIso.hom_inv_id, Scheme.Modules.Hom.id_app,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
      right_inv := fun x ↦ by
        simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
          sheafIso.inv_hom_id, Scheme.Modules.Hom.id_app,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
      map_add' := fun x y ↦
        (Scheme.Modules.Hom.app sheafIso.hom ⊤).hom.map_add x y }
  exact topAdd.toLinearEquiv (fun r x ↦
    Scheme.Modules.Hom.app_smul sheafIso.hom r x)

private lemma pullbackCongrCompSectionsEquiv_baseMap
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (eq : h = f ≫ g) (N : Z.Modules)
    {V : Y.Opens} {W : Z.Opens}
    (eV : V ≤ g ⁻¹ᵁ W) (eT : (⊤ : X.Opens) ≤ f ⁻¹ᵁ V)
    (eTW : (⊤ : X.Opens) ≤ h ⁻¹ᵁ W) (x : Γ(N, W)) :
    pullbackCongrCompSectionsEquiv f g h eq N
        (pullback_app_isoTensor_baseMap h N eTW x) =
      pullback_app_isoTensor_baseMap f
        ((Scheme.Modules.pullback g).obj N) eT
          (pullback_app_isoTensor_baseMap g N eV x) := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app
    ((Scheme.Modules.pullbackComp f g).hom.app N) ⊤)).injective
  change (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackComp f g).hom.app N) ⊤).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackComp f g).inv.app N) ⊤).hom
          ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackCongr eq).hom.app N) ⊤).hom
            (pullback_app_isoTensor_baseMap h N eTW x))) = _
  rw [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app,
    id_apply]
  rw [pullback_app_isoTensor_baseMap_congr eq N eTW
    (eT.trans (Scheme.Hom.preimage_mono f eV)) x]
  exact (pullback_app_isoTensor_baseMap_comp f g N eV eT
    (eT.trans (Scheme.Hom.preimage_mono f eV)) x).symm

private lemma affineChart_overSpecMap
    (T : Over (Spec (.of k))) (U : T.left.affineOpens)
    (gOver : T ⟶ overSpec k B) :
    let R := Γ(T.left, U.1)
    let phi : B →ₐ[k] R :=
      (Over.appLEAlgHom gOver ⊤ U.1 le_top).comp
        (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom
    letI : Algebra B R := phi.toRingHom.toAlgebra
    letI : IsScalarTower k B R :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (phi.commutes x).symm
    overSpecMap (k := k) B R = Over.fromSpecAffine T U ≫ gOver := by
  dsimp only
  let phi : B →ₐ[k] Γ(T.left, U.1) :=
    (Over.appLEAlgHom gOver ⊤ U.1 le_top).comp
      (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom
  letI : Algebra B Γ(T.left, U.1) := phi.toRingHom.toAlgebra
  letI : IsScalarTower k B Γ(T.left, U.1) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (phi.commutes x).symm
  have htop : Over.overSpecMap (k := k)
        (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom =
      Over.fromSpecAffine (overSpec k B) (overSpecTopAffine B) := by
    ext : 1
    change Spec.map (CommRingCat.ofHom
        (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom.toRingHom) =
      (isAffineOpen_top (Spec (.of B))).fromSpec
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    congr 1
  have hnat := Over.fromSpecAffine_naturality gOver
    (overSpecTopAffine B) U le_top
  have hmap : overSpecMap (k := k) B Γ(T.left, U.1) =
      Over.overSpecMap phi := by
    ext : 1
    rfl
  rw [hmap, show phi =
      (Over.appLEAlgHom gOver ⊤ U.1 le_top).comp
        (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom from rfl,
    Over.overSpecMap_comp, htop]
  simpa only [overSpecTopAffine] using hnat

private lemma cartesianAffineChart
    {T' X' : Scheme.{u}}
    (g : T' ⟶ Spec (.of B)) (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C B)
    (sq : IsPullback g' f'
      (relCurve C B ↘ Spec (.of B)) g)
    (U : T'.Opens) (hU : IsAffineOpen U) :
    let R := Γ(T', U)
    letI : Algebra k R :=
      Over.sectionsAlgebra
        (X := Over.mk (g ≫ (overSpec k B).hom)) U
    let phi : B →ₐ[k] R :=
      (Over.appLEAlgHom
          (Over.homMk g rfl :
            Over.mk (g ≫ (overSpec k B).hom) ⟶ overSpec k B)
          ⊤ U le_top).comp
        (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom
    letI : Algebra B R := phi.toRingHom.toAlgebra
    letI : IsScalarTower k B R :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (phi.commutes x).symm
    ∃ a : relCurve C R ⟶ X', ∃ ha : IsOpenImmersion a,
      @Scheme.Hom.opensRange _ _ a ha = f' ⁻¹ᵁ U ∧
      a ≫ g' = relCurveMap C B R ∧
      a ≫ f' = (snd C (overSpec k R)).left ≫ hU.fromSpec := by
  dsimp only
  let T : Over (Spec (.of k)) := Over.mk (g ≫ (overSpec k B).hom)
  let gOver : T ⟶ overSpec k B := Over.homMk g rfl
  let Ua : T.left.affineOpens := ⟨U, hU⟩
  let R := Γ(T.left, Ua.1)
  let phi : B →ₐ[k] R :=
    (Over.appLEAlgHom gOver ⊤ Ua.1 le_top).comp
      (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom
  letI : Algebra B R := phi.toRingHom.toAlgebra
  letI : IsScalarTower k B R :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (phi.commutes x).symm
  have hOverMap : overSpecMap (k := k) B R =
      Over.fromSpecAffine T Ua ≫ gOver :=
    affineChart_overSpecMap T Ua gOver
  let hcan := Over.isPullback_whiskerLeft_snd C gOver
  let eX : X' ≅ (C ⊗ T).left :=
    IsPullback.isoIsPullback (relCurve C B) T.left sq hcan
  have heXfst : eX.hom ≫ (C ◁ gOver).left = g' :=
    IsPullback.isoIsPullback_hom_fst _ _ sq hcan
  have heXsnd : eX.hom ≫ (snd C T).left = f' :=
    IsPullback.isoIsPullback_hom_snd _ _ sq hcan
  let W : (C ⊗ T).left.Opens := (snd C T).left ⁻¹ᵁ U
  have hpre : eX.hom ⁻¹ᵁ W = f' ⁻¹ᵁ U := by
    calc
      eX.hom ⁻¹ᵁ W = (eX.hom ≫ (snd C T).left) ⁻¹ᵁ U :=
        (Scheme.Hom.comp_preimage eX.hom (snd C T).left U).symm
      _ = f' ⁻¹ᵁ U := congrArg (fun q : X' ⟶ T' ↦ q ⁻¹ᵁ U) heXsnd
  let eU : relCurve C R ≅ (f' ⁻¹ᵁ U).toScheme :=
    relCurveAffineOpenIso C T Ua ≪≫
      pullbackRestrictIsoRestrict (snd C T).left U ≪≫
      (eX.hom.preimageIso W).symm ≪≫
      X'.isoOfEq hpre
  let a : relCurve C R ⟶ X' := eU.hom ≫ (f' ⁻¹ᵁ U).ι
  haveI : IsOpenImmersion a := by
    dsimp [a]
    infer_instance
  have haRange : a.opensRange = f' ⁻¹ᵁ U := by
    dsimp [a]
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  have hCover :
      (pullbackRestrictIsoRestrict (snd C T).left U).hom ≫ W.ι =
        (relCurveAffineCover C T).f Ua := by
    exact pullbackRestrictIsoRestrict_hom_ι (snd C T).left U
  have hPreimage :
      (eX.hom.preimageIso W).symm.hom ≫
          (eX.hom ⁻¹ᵁ W).ι ≫ eX.hom = W.ι := by
    change (eX.hom.preimageIso W).inv ≫
      (eX.hom ⁻¹ᵁ W).ι ≫ eX.hom = W.ι
    exact Scheme.Hom.preimageIso_inv_ι eX.hom W
  have ha_eX : a ≫ eX.hom =
      (C ◁ Over.fromSpecAffine T Ua).left := by
    calc
      a ≫ eX.hom =
          (relCurveAffineOpenIso C T Ua).hom ≫
            (pullbackRestrictIsoRestrict (snd C T).left U).hom ≫
              (eX.hom.preimageIso W).symm.hom ≫
                (X'.isoOfEq hpre).hom ≫ (f' ⁻¹ᵁ U).ι ≫ eX.hom := by
        simp only [a, eU, Iso.trans_hom, Category.assoc]
      _ = (relCurveAffineOpenIso C T Ua).hom ≫
            (pullbackRestrictIsoRestrict (snd C T).left U).hom ≫
              (eX.hom.preimageIso W).symm.hom ≫
                (eX.hom ⁻¹ᵁ W).ι ≫ eX.hom := by
        rw [Scheme.isoOfEq_hom_ι_assoc]
      _ = (relCurveAffineOpenIso C T Ua).hom ≫
            (pullbackRestrictIsoRestrict (snd C T).left U).hom ≫ W.ι := by
        simpa only [Category.assoc] using congrArg
          (fun q ↦ (relCurveAffineOpenIso C T Ua).hom ≫
            (pullbackRestrictIsoRestrict (snd C T).left U).hom ≫ q)
          hPreimage
      _ = (relCurveAffineOpenIso C T Ua).hom ≫
            (relCurveAffineCover C T).f Ua := by
        rw [hCover]
      _ = (C ◁ Over.fromSpecAffine T Ua).left :=
        relCurveAffineOpenIso_hom_f C T Ua
  have ha_f' : a ≫ f' =
      (snd C (overSpec k R)).left ≫ hU.fromSpec := by
    calc
      a ≫ f' = a ≫ (eX.hom ≫ (snd C T).left) := by rw [heXsnd]
      _ = (a ≫ eX.hom) ≫ (snd C T).left := (Category.assoc _ _ _).symm
      _ = (C ◁ Over.fromSpecAffine T Ua).left ≫ (snd C T).left := by rw [ha_eX]
      _ = (snd C (overSpec k R)).left ≫ hU.fromSpec := by
        exact congrArg Over.Hom.left
          (whiskerLeft_snd C (Over.fromSpecAffine T Ua))
  have ha_g' : a ≫ g' = relCurveMap C B R := by
    calc
      a ≫ g' = a ≫ (eX.hom ≫ (C ◁ gOver).left) := by rw [heXfst]
      _ = (a ≫ eX.hom) ≫ (C ◁ gOver).left := (Category.assoc _ _ _).symm
      _ = (C ◁ Over.fromSpecAffine T Ua).left ≫ (C ◁ gOver).left := by
        rw [ha_eX]
      _ = relCurveMap C B R := by
        rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← hOverMap]
        rfl
  exact ⟨a, inferInstance, haRange, ha_g', ha_f'⟩

private lemma cartesianAffineChart_appLE
    {T' X' : Scheme.{u}} (f' : X' ⟶ T')
    (U : T'.Opens) (hU : IsAffineOpen U)
    [Algebra k Γ(T', U)]
    (a : relCurve C Γ(T', U) ⟶ X') [IsOpenImmersion a]
    (haRange : a.opensRange = f' ⁻¹ᵁ U)
    (ha_f' : a ≫ f' =
      (snd C (overSpec k Γ(T', U))).left ≫ hU.fromSpec) :
    f'.appLE U a.opensRange haRange.le ≫
        a.appLE a.opensRange ⊤
          (le_of_eq (Scheme.Hom.preimage_opensRange a).symm) =
      (Scheme.ΓSpecIso Γ(T', U)).inv ≫
        (snd C (overSpec k Γ(T', U))).left.appLE ⊤ ⊤ le_top := by
  let ea : (⊤ : (relCurve C Γ(T', U)).Opens) ≤
      a ⁻¹ᵁ a.opensRange :=
    le_of_eq (Scheme.Hom.preimage_opensRange a).symm
  let eFrom : (⊤ : (Spec (.of Γ(T', U))).Opens) ≤
      hU.fromSpec ⁻¹ᵁ U :=
    le_of_eq hU.fromSpec_preimage_self.symm
  let eAF : (⊤ : (relCurve C Γ(T', U)).Opens) ≤
      (a ≫ f') ⁻¹ᵁ U :=
    ea.trans (Scheme.Hom.preimage_mono a haRange.le)
  let eSF : (⊤ : (relCurve C Γ(T', U)).Opens) ≤
      ((snd C (overSpec k Γ(T', U))).left ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [← ha_f']
    exact eAF
  have hFrom : hU.fromSpec.appLE U ⊤ eFrom =
      (Scheme.ΓSpecIso Γ(T', U)).inv := by
    simp [Scheme.Hom.appLE, hU.fromSpec_app_self, ← Functor.map_comp]
  calc
    f'.appLE U a.opensRange haRange.le ≫ a.appLE a.opensRange ⊤ ea =
        (a ≫ f').appLE U ⊤ eAF :=
      Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    _ = ((snd C (overSpec k Γ(T', U))).left ≫ hU.fromSpec).appLE U ⊤
          eSF :=
      Scheme.Hom.appLE_congr_hom ha_f' U ⊤ _ _
    _ = hU.fromSpec.appLE U ⊤ eFrom ≫
        (snd C (overSpec k Γ(T', U))).left.appLE ⊤ ⊤ le_top :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    _ = (Scheme.ΓSpecIso Γ(T', U)).inv ≫
        (snd C (overSpec k Γ(T', U))).left.appLE ⊤ ⊤ le_top := by
      rw [hFrom]

set_option maxHeartbeats 800000 in
private theorem affineSourceSectionsPresentationRaw
    {T' : Scheme.{u}} (g : T' ⟶ Spec (.of B))
    (U : T'.Opens) (hU : IsAffineOpen U)
    (N : (Spec (.of B)).Modules)
    [IsIso (Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of B) N)]
    (phi : B →+* Γ(T', U))
    (hSpec : Spec.map (CommRingCat.ofHom phi) = hU.fromSpec ≫ g) :
    letI : Algebra B Γ(T', U) := phi.toAlgebra
    Nonempty {e : Γ(T', U) ⊗[B]
        ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj N) ≃ₗ[Γ(T', U)]
        Γ((Scheme.Modules.pullback g).obj N, U) //
      ∀ x : Γ(N, ⊤), e (1 ⊗ₜ[B] x) =
        pullback_app_isoTensor_baseMap g N le_top x} := by
  let R : CommRingCat := Γ(T', U)
  letI : Algebra B R := phi.toAlgebra
  let phiCat : CommRingCat.of B ⟶ R :=
    CommRingCat.ofHom phi
  letI : Algebra R Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).inv.hom.toAlgebra
  letI sourceChartModule : Module R
      Γ((Scheme.Modules.pullback hU.fromSpec).obj
        ((Scheme.Modules.pullback g).obj N), ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso R).inv.hom
  obtain ⟨eSpec, heSpec⟩ :=
    (Scheme.Modules.pullback_app_isoTensor_baseMap_sectionLinearEquiv_of_fromTildeΓ
      phiCat N).some
  let eSourceChartRing :
      Γ((Scheme.Modules.pullback (Spec.map phiCat)).obj N, ⊤) ≃ₗ[Γ(Spec R, ⊤)]
        Γ((Scheme.Modules.pullback hU.fromSpec).obj
          ((Scheme.Modules.pullback g).obj N), ⊤) :=
    pullbackCongrCompSectionsEquiv hU.fromSpec g
      (Spec.map phiCat) hSpec N
  let eSourceChartAdd := eSourceChartRing.toAddEquiv
  let eSourceChart :
      Γ((Scheme.Modules.pullback (Spec.map phiCat)).obj N, ⊤) ≃ₗ[R]
        Γ((Scheme.Modules.pullback hU.fromSpec).obj
          ((Scheme.Modules.pullback g).obj N), ⊤) :=
    eSourceChartAdd.toLinearEquiv (by
      intro r x
      change eSourceChartRing
          ((Scheme.ΓSpecIso R).inv.hom r • x) =
        (Scheme.ΓSpecIso R).inv.hom r • eSourceChartRing x
      exact eSourceChartRing.map_smul _ _)
  obtain ⟨eFromSpec, heFromSpec⟩ :=
    (pullbackFromSpecSectionsEquiv
      ((Scheme.Modules.pullback g).obj N) hU).some
  let e : R ⊗[B]
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj N) ≃ₗ[R]
      Γ((Scheme.Modules.pullback g).obj N, U) :=
    eSpec.trans (eSourceChart.trans eFromSpec)
  have eSourceChart_baseMap (x : Γ(N, ⊤)) :
      eSourceChart
          (pullback_app_isoTensor_baseMap (Spec.map phiCat) N le_top x) =
        pullback_app_isoTensor_baseMap hU.fromSpec
          ((Scheme.Modules.pullback g).obj N)
          (le_of_eq hU.fromSpec_preimage_self.symm)
          (pullback_app_isoTensor_baseMap g N le_top x) :=
    by
      change (pullbackCongrCompSectionsEquiv hU.fromSpec g
        (Spec.map phiCat) hSpec N) _ = _
      exact pullbackCongrCompSectionsEquiv_baseMap hU.fromSpec g
        (Spec.map phiCat) hSpec N le_top
        (le_of_eq hU.fromSpec_preimage_self.symm) le_top x
  have he (x : Γ(N, ⊤)) :
      e (1 ⊗ₜ[B] x) =
        pullback_app_isoTensor_baseMap g N le_top x := by
    change eFromSpec (eSourceChart (eSpec (1 ⊗ₜ[B] x))) = _
    rw [heSpec x, eSourceChart_baseMap]
    rw [← heFromSpec, LinearEquiv.apply_symm_apply]
  exact ⟨e, he⟩

set_option maxHeartbeats 800000 in
private theorem affineSourceSectionsPresentation
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (datumPair D).H1)
    {T' X' : Scheme.{u}} (g : T' ⟶ Spec (.of B))
    (f' : X' ⟶ T') (g' : X' ⟶ relCurve C B)
    (sq : IsPullback g' f'
      (relCurve C B ↘ Spec (.of B)) g)
    (U : T'.Opens) (hU : IsAffineOpen U)
    (phi : B →+* Γ(T', U))
    (hSpec : Spec.map (CommRingCat.ofHom phi) = hU.fromSpec ≫ g) :
    letI : Algebra B Γ(T', U) := phi.toAlgebra
    Nonempty {e : Γ(T', U) ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[Γ(T', U)]
        Γ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pushforward
            (relCurve C B ↘ Spec (.of B))).obj D.nativeModule), U) //
      ∀ x : Γ(D.nativeModule, ⊤),
        (((canonicalBaseChangeMap sq).app D.nativeModule).app U).hom
            (e (1 ⊗ₜ[B] x)) =
          pullback_app_isoTensor_baseMap
            (U := f' ⁻¹ᵁ U) (V := ⊤) g' D.nativeModule le_top x} := by
  let R : CommRingCat := Γ(T', U)
  letI : Algebra B R := phi.toAlgebra
  let N : (Spec (.of B)).Modules :=
    (Scheme.Modules.pushforward
      (relCurve C B ↘ Spec (.of B))).obj D.nativeModule
  letI : IsIso (Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of B) N) :=
    D.isIso_nativePushforward_fromTildeΓ hH1
  obtain ⟨eRaw, heRaw⟩ :=
    affineSourceSectionsPresentationRaw g U hU N phi hSpec
  let ePushTop := D.nativePushforwardTopSectionsLinearEquiv
  let ePushTopR := LinearEquiv.baseChange B R _ _ ePushTop
  let e : R ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[R]
      Γ((Scheme.Modules.pullback g).obj N, U) :=
    ePushTopR.trans eRaw
  have he (x : Γ(D.nativeModule, ⊤)) :
      e (1 ⊗ₜ[B] x) =
        pullback_app_isoTensor_baseMap g N le_top (ePushTop x) := by
    change eRaw (ePushTopR (1 ⊗ₜ[B] x)) = _
    rw [LinearEquiv.baseChange_tmul]
    exact heRaw (ePushTop x)
  have heMate (x : Γ(D.nativeModule, ⊤)) :
      (((canonicalBaseChangeMap sq).app D.nativeModule).app U).hom
          (e (1 ⊗ₜ[B] x)) =
        pullback_app_isoTensor_baseMap
          (U := f' ⁻¹ᵁ U) (V := ⊤) g' D.nativeModule le_top x := by
    rw [he x]
    have hMate := canonicalBaseChangeMap_app_baseMap_compat sq D.nativeModule
      (V := ⊤) (U := U) le_top le_top (ePushTop x)
    have hePushTop : ePushTop x = x := by
      rw [nativePushforwardTopSectionsLinearEquiv_apply]
      change (D.nativeModule.presheaf.map _).hom x = x
      rw [show (eqToHom (Scheme.Hom.preimage_top
          (relCurve C B ↘ Spec (.of B)))).op =
            𝟙 (Opposite.op (⊤ : (relCurve C B).Opens)) from
          Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply]
    rw [hePushTop] at hMate
    rw [hePushTop]
    exact hMate
  exact ⟨e, heMate⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
private theorem cartesianTargetSectionsPresentation
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (datumPair D).H1)
    {T' X' : Scheme.{u}} (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C B)
    (U : T'.Opens) (hU : IsAffineOpen U)
    [Algebra k Γ(T', U)] [Algebra B Γ(T', U)]
    [IsScalarTower k B Γ(T', U)]
    (a : relCurve C Γ(T', U) ⟶ X') [IsOpenImmersion a]
    (haRange : a.opensRange = f' ⁻¹ᵁ U)
    (ha_g' : a ≫ g' = relCurveMap C B Γ(T', U))
    (ha_f' : a ≫ f' =
      (snd C (overSpec k Γ(T', U))).left ≫ hU.fromSpec) :
    Nonempty {e : Γ(T', U) ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[Γ(T', U)]
        Γ((Scheme.Modules.pushforward f').obj
          ((Scheme.Modules.pullback g').obj D.nativeModule), U) //
      ∀ x : Γ(D.nativeModule, ⊤), e (1 ⊗ₜ[B] x) =
        pullback_app_isoTensor_baseMap g' D.nativeModule le_top x} := by
  let R : CommRingCat := Γ(T', U)
  letI : Algebra R Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).inv.hom.toAlgebra
  letI nativeBaseChangedTopSectionsModule :
      Module R Γ((D.baseChange R).nativeModule, ⊤) :=
    Scheme.moduleKSections
      (Over.mk (relCurve C R ↘ Spec (.of R)))
      (D.baseChange R).nativeModule ⊤
  letI nativePullbackSectionsModule (W : (relCurve C R).Opens) :
      Module R Γ((Scheme.Modules.pullback
        (relCurveMap C B R)).obj D.nativeModule, W) :=
    Scheme.moduleKSections
      (Over.mk (relCurve C R ↘ Spec (.of R)))
      ((Scheme.Modules.pullback (relCurveMap C B R)).obj D.nativeModule) W
  let N' := (Scheme.Modules.pullback g').obj D.nativeModule
  letI nativeIteratedPullbackSectionsModule (W : (relCurve C R).Opens) :
      Module R Γ((Scheme.Modules.pullback a).obj N', W) :=
    Scheme.moduleKSections
      (Over.mk (relCurve C R ↘ Spec (.of R)))
      ((Scheme.Modules.pullback a).obj N') W
  letI nativeComposedPullbackTopSectionsModule :
      Module R Γ((Scheme.Modules.pullback g' ⋙
        Scheme.Modules.pullback a).obj D.nativeModule, ⊤) :=
    Scheme.moduleKSections
      (Over.mk (relCurve C R ↘ Spec (.of R)))
      ((Scheme.Modules.pullback g' ⋙
        Scheme.Modules.pullback a).obj D.nativeModule) ⊤
  let eH0 : R ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[R]
      Γ((D.baseChange R).nativeModule, ⊤) :=
    D.nativeH0BaseChange R hH1
  letI : IsIso (D.nativePullbackComparison R) :=
    D.isIso_nativePullbackComparison R
  let comparisonIso := asIso (D.nativePullbackComparison R)
  let eComparisonAdd : Γ((D.baseChange R).nativeModule, ⊤) ≃+
      Γ((Scheme.Modules.pullback
        (relCurveMap C B R)).obj D.nativeModule, ⊤) :=
    { toFun := fun x ↦
        (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom x
      invFun := fun x ↦
        (Scheme.Modules.Hom.app comparisonIso.hom ⊤).hom x
      left_inv := fun x ↦ by
        simp only [← AddCommGrpCat.comp_apply,
          ← Scheme.Modules.Hom.comp_app, comparisonIso.inv_hom_id,
          Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
          AddMonoidHom.id_apply]
      right_inv := fun x ↦ by
        simp only [← AddCommGrpCat.comp_apply,
          ← Scheme.Modules.Hom.comp_app, comparisonIso.hom_inv_id,
          Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
          AddMonoidHom.id_apply]
      map_add' := fun x y ↦
        (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom.map_add x y }
  let eComparison : Γ((D.baseChange R).nativeModule, ⊤) ≃ₗ[R]
      Γ((Scheme.Modules.pullback
        (relCurveMap C B R)).obj D.nativeModule, ⊤) :=
    eComparisonAdd.toLinearEquiv (by
      intro r x
      change (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom
          ((relCurve C R).overAlgebraMap R ⊤ r • x) =
        (relCurve C R).overAlgebraMap R ⊤ r •
          (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom x
      exact Scheme.Modules.Hom.app_smul comparisonIso.inv _ x)
  let eTargetChartRing : Γ((Scheme.Modules.pullback
        (relCurveMap C B R)).obj D.nativeModule, ⊤) ≃ₗ[R]
      Γ((Scheme.Modules.pullback a).obj N', ⊤) := by
    let eRing := pullbackCongrCompSectionsEquiv a g'
      (relCurveMap C B R) ha_g'.symm D.nativeModule
    exact eRing.toAddEquiv.toLinearEquiv (by
      intro r x
      change eRing ((relCurve C R).overAlgebraMap R ⊤ r • x) =
        (relCurve C R).overAlgebraMap R ⊤ r • eRing x
      exact eRing.map_smul _ _)
  let eTargetChart : Γ((Scheme.Modules.pullback
        (relCurveMap C B R)).obj D.nativeModule, ⊤) ≃ₗ[R]
      Γ((Scheme.Modules.pullback a).obj N', ⊤) :=
    eTargetChartRing
  letI nativeRangeSectionsModule : Module R Γ(N', a.opensRange) :=
    Module.compHom _ (f'.appLE U a.opensRange haRange.le).hom
  letI nativeOpenPullbackSectionsModule :
      Module Γ(X', a.opensRange)
        Γ((Scheme.Modules.pullback a).obj N', ⊤) :=
    Module.compHom _ (a.appLE a.opensRange ⊤
      (le_of_eq (Scheme.Hom.preimage_opensRange a).symm)).hom
  let eOpenAdd := pullbackOpenImmersionSectionsEquiv a N'
  let eOpen : Γ((Scheme.Modules.pullback a).obj N', ⊤) ≃ₗ[R]
      Γ(N', a.opensRange) :=
    eOpenAdd.toLinearEquiv (by
      intro r x
      change eOpenAdd ((relCurve C R).overAlgebraMap R ⊤ r • x) =
        (f'.appLE U a.opensRange haRange.le).hom r • eOpenAdd x
      apply eOpenAdd.symm.injective
      rw [eOpenAdd.symm_apply_apply,
        pullbackOpenImmersionSectionsEquiv_symm_apply]
      rw [(pullback_app_isoTensor_baseMap a N'
        (le_of_eq (Scheme.Hom.preimage_opensRange a).symm)).map_smul]
      rw [← pullbackOpenImmersionSectionsEquiv_symm_apply,
        eOpenAdd.symm_apply_apply]
      change (relCurve C R).overAlgebraMap R ⊤ r • x =
        (a.appLE a.opensRange ⊤
          (le_of_eq (Scheme.Hom.preimage_opensRange a).symm)).hom
            ((f'.appLE U a.opensRange haRange.le).hom r) • x
      exact congrArg (fun s ↦ s • x)
        (congrArg (fun q : Γ(T', U) ⟶ Γ(relCurve C R, ⊤) ↦ q.hom r)
          (cartesianAffineChart_appLE f' U hU a haRange ha_f')).symm)
  let eRangeHom := N'.presheaf.map (eqToHom haRange.symm).op
  let eRangeAdd : Γ(N', a.opensRange) ≃+
      Γ((Scheme.Modules.pushforward f').obj N', U) :=
    AddEquiv.ofBijective eRangeHom.hom
      (ConcreteCategory.bijective_of_isIso eRangeHom)
  let eRange : Γ(N', a.opensRange) ≃ₗ[R]
      Γ((Scheme.Modules.pushforward f').obj N', U) :=
    eRangeAdd.toLinearEquiv (by
      intro r x
      change eRangeHom.hom
          ((f'.appLE U a.opensRange haRange.le).hom r • x) =
        (f'.app U).hom r • eRangeHom.hom x
      rw [N'.map_smul]
      congr 1
      have hAppLE :
          f'.appLE U a.opensRange haRange.le ≫
              X'.presheaf.map (eqToHom haRange.symm).op =
            f'.app U := by
        calc
          f'.appLE U a.opensRange haRange.le ≫
                X'.presheaf.map (eqToHom haRange.symm).op =
              f'.appLE U a.opensRange
                  (haRange.symm ▸ (le_rfl : f' ⁻¹ᵁ U ≤ f' ⁻¹ᵁ U)) ≫
                X'.presheaf.map (eqToHom haRange.symm).op := by
                  congr 2
          _ = f'.appLE U (f' ⁻¹ᵁ U) le_rfl :=
            f'.appLE_map' le_rfl haRange.symm
          _ = f'.app U := f'.appLE_eq_app
      exact congrArg (fun q ↦ q.hom r) hAppLE)
  let e := eH0.trans
    (eComparison.trans (eTargetChart.trans (eOpen.trans eRange)))
  have eComparison_sectionsMap (x : Γ(D.nativeModule, ⊤)) :
      eComparison (D.sectionsMap R le_rfl x) =
        pullback_app_isoTensor_baseMap (relCurveMap C B R) D.nativeModule
          le_top x := by
    change (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom
      (D.sectionsMap R le_rfl x) = _
    have hComparison :
        (Scheme.Modules.Hom.app comparisonIso.hom ⊤).hom
            (pullback_app_isoTensor_baseMap
              (relCurveMap C B R) D.nativeModule le_top x) =
          D.sectionsMap R le_rfl x := by
      change ((D.nativePullbackComparison R).app ⊤).hom _ = _
      simpa only [Scheme.Hom.preimage_top] using
        D.nativePullbackComparison_baseMap R
          (⊤ : (relCurve C B).Opens) x
    rw [← hComparison, ← AddCommGrpCat.comp_apply,
      ← Scheme.Modules.Hom.comp_app, comparisonIso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    exact CategoryTheory.id_apply _
  have eTargetChart_baseMap (x : Γ(D.nativeModule, ⊤)) :
      eTargetChart
          (pullback_app_isoTensor_baseMap (relCurveMap C B R)
            D.nativeModule le_top x) =
        pullback_app_isoTensor_baseMap a N'
          (le_of_eq (Scheme.Hom.preimage_opensRange a).symm)
          (pullback_app_isoTensor_baseMap g' D.nativeModule le_top x) :=
    by
      change (pullbackCongrCompSectionsEquiv a g'
        (relCurveMap C B R) ha_g'.symm D.nativeModule) _ = _
      exact pullbackCongrCompSectionsEquiv_baseMap a g'
        (relCurveMap C B R) ha_g'.symm D.nativeModule le_top
        (le_of_eq (Scheme.Hom.preimage_opensRange a).symm) le_top x
  have eOpen_baseMap (x : Γ(D.nativeModule, ⊤)) :
      eOpen
          (pullback_app_isoTensor_baseMap a N'
            (le_of_eq (Scheme.Hom.preimage_opensRange a).symm)
            (pullback_app_isoTensor_baseMap g' D.nativeModule le_top x)) =
        pullback_app_isoTensor_baseMap g' D.nativeModule le_top x := by
    change eOpenAdd _ = _
    rw [← pullbackOpenImmersionSectionsEquiv_symm_apply,
      eOpenAdd.apply_symm_apply]
  have eRange_baseMap (x : Γ(D.nativeModule, ⊤)) :
      eRange (pullback_app_isoTensor_baseMap g' D.nativeModule le_top x) =
        pullback_app_isoTensor_baseMap g' D.nativeModule le_top x := by
    change eRangeHom.hom _ = _
    have hres := pullback_app_isoTensor_baseMap_res g' D.nativeModule
      (V' := ⊤) (V'' := ⊤)
      (W' := a.opensRange) (W'' := f' ⁻¹ᵁ U)
      le_top le_top le_rfl haRange.symm.le x
    simpa only [eRangeHom,
      show homOfLE haRange.symm.le = eqToHom haRange.symm from
        Subsingleton.elim _ _,
      show homOfLE (le_rfl : (⊤ : (relCurve C B).Opens) ≤ ⊤) =
        𝟙 (⊤ : (relCurve C B).Opens) from rfl,
      op_id, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply] using hres
  have he (x : Γ(D.nativeModule, ⊤)) :
      e (1 ⊗ₜ[B] x) =
        pullback_app_isoTensor_baseMap g' D.nativeModule le_top x := by
    change eRange (eOpen (eTargetChart (eComparison (eH0 (1 ⊗ₜ[B] x))))) = _
    rw [show eH0 (1 ⊗ₜ[B] x) = D.sectionsMap R le_rfl x from
      D.nativeH0BaseChange_one_tmul_eq_sectionsMap R hH1 x]
    rw [eComparison_sectionsMap, eTargetChart_baseMap, eOpen_baseMap,
      eRange_baseMap]
  exact ⟨e, he⟩

set_option maxHeartbeats 800000 in
private theorem isIso_canonicalBaseChangeMap_nativeModule_app
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (datumPair D).H1)
    {T' X' : Scheme.{u}}
    (g : T' ⟶ Spec (.of B)) (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C B)
    (sq : IsPullback g' f'
      (relCurve C B ↘ Spec (.of B)) g)
    (U : T'.Opens) (hU : IsAffineOpen U) :
    IsIso (((canonicalBaseChangeMap sq).app D.nativeModule).app U) := by
  let T : Over (Spec (.of k)) := Over.mk (g ≫ (overSpec k B).hom)
  let gOver : T ⟶ overSpec k B := Over.homMk g rfl
  let Ua : T.left.affineOpens := ⟨U, hU⟩
  let R : CommRingCat := Γ(T', U)
  letI : Algebra k R := Over.sectionsAlgebra (X := T) U
  let phi : B →ₐ[k] R :=
    (Over.appLEAlgHom gOver ⊤ U le_top).comp
      (Over.overSpecΓTopAlgEquiv k B).symm.toAlgHom
  letI : Algebra B R := phi.toRingHom.toAlgebra
  letI : IsScalarTower k B R :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (phi.commutes x).symm
  let phiCat : CommRingCat.of B ⟶ R :=
    CommRingCat.ofHom phi.toRingHom
  have hOverMap : overSpecMap (k := k) B R =
      Over.fromSpecAffine T Ua ≫ gOver :=
    affineChart_overSpecMap T Ua gOver
  have hSpec : Spec.map phiCat = hU.fromSpec ≫ g := by
    have h := congrArg Over.Hom.left hOverMap
    change Spec.map phiCat = hU.fromSpec ≫ g at h
    exact h
  obtain ⟨a, ha, haRange, ha_g', ha_f'⟩ :=
    cartesianAffineChart g f' g' sq U hU
  letI : IsOpenImmersion a := ha

  let N : (Spec (.of B)).Modules :=
    (Scheme.Modules.pushforward
      (relCurve C B ↘ Spec (.of B))).obj D.nativeModule
  obtain ⟨eL, hMate⟩ :=
    affineSourceSectionsPresentation
      D hH1 g f' g' sq U hU phi.toRingHom hSpec
  let N' := (Scheme.Modules.pullback g').obj D.nativeModule
  obtain ⟨eR, heR⟩ :=
    cartesianTargetSectionsPresentation
      D hH1 f' g' U hU a haRange ha_g' ha_f'

  let χ : Γ((Scheme.Modules.pullback g).obj N, U) →ₗ[R]
      Γ((Scheme.Modules.pushforward f').obj N', U) :=
    { toFun := (((canonicalBaseChangeMap sq).app D.nativeModule).app U).hom
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun r x ↦
        Scheme.Modules.Hom.app_smul
          ((canonicalBaseChangeMap sq).app D.nativeModule) r x }
  have hgen (x : Γ(D.nativeModule, ⊤)) :
      χ (eL (1 ⊗ₜ[B] x)) = eR (1 ⊗ₜ[B] x) := by
    rw [show χ (eL (1 ⊗ₜ[B] x)) =
      pullback_app_isoTensor_baseMap g' D.nativeModule le_top x from hMate x,
      heR x]
  have hall (z : R ⊗[B] Γ(D.nativeModule, ⊤)) :
      χ (eL z) = eR z := by
    induction z using TensorProduct.induction_on with
    | zero =>
      calc
        χ (eL 0) = χ 0 := congrArg χ eL.map_zero
        _ = 0 := χ.map_zero
        _ = eR 0 := eR.map_zero.symm
    | tmul r x =>
      have hr : (r ⊗ₜ[B] x : R ⊗[B] Γ(D.nativeModule, ⊤)) =
          r • ((1 : R) ⊗ₜ[B] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hr, map_smul, map_smul, map_smul, hgen x]
    | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, h₁, h₂]
  have hbij : Function.Bijective
      ⇑(((canonicalBaseChangeMap sq).app D.nativeModule).app U).hom := by
    have hfun : ∀ p,
        (((canonicalBaseChangeMap sq).app D.nativeModule).app U).hom p =
          eR (eL.symm p) := by
      intro p
      have h := hall (eL.symm p)
      rwa [LinearEquiv.apply_symm_apply] at h
    rw [show ⇑(((canonicalBaseChangeMap sq).app D.nativeModule).app U).hom =
      ⇑eR ∘ ⇑eL.symm from funext hfun]
    exact eR.bijective.comp eL.symm.bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- The canonical pushforward base-change map for the native module is an
isomorphism for every cartesian square over the affine coefficient base. -/
theorem isIso_canonicalBaseChangeMap_nativeModule
    (D : BasicOpenCocycleDatum C B pi)
    (hH1 : Subsingleton (datumPair D).H1)
    {T' X' : Scheme.{u}}
    (g : T' ⟶ Spec (.of B)) (f' : X' ⟶ T')
    (g' : X' ⟶ relCurve C B)
    (sq : IsPullback g' f'
      (relCurve C B ↘ Spec (.of B)) g) :
    IsIso ((canonicalBaseChangeMap sq).app D.nativeModule) := by
  refine isIso_canonicalBaseChangeMap_app_of_affine sq D.nativeModule ?_
  intro U hU
  exact isIso_canonicalBaseChangeMap_nativeModule_app
    D hH1 g f' g' sq U hU

end

end BasicOpenCocycleDatum

namespace PicRankOneNativePresentation

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}

/-- Assemble a native rank-one presentation directly from the family
certificates.  The arbitrary-cartesian base-change field is supplied by
`isIso_canonicalBaseChangeMap_nativeModule`, rather than accepted as an
additional certificate. -/
noncomputable def ofCertificatesWithNativeBaseChange
    (E : Algebra.EtaleCover A)
    (x : descentClasses C E)
    (hrep : PicEtAff.mk C E x = picEtAffineEquiv C A lam.1)
    (D : BasicOpenCocycleDatum C E.Carrier pi)
    (hclass :
      (x : relPic C (overSpec k E.Carrier)) =
        relPicMk C (overSpec k E.Carrier) D.cechPicClass)
    (cert : RankOneFamilyCertificates D) :
    PicRankOneNativePresentation pi lam :=
  ofCertificates E x hrep D hclass
    (fun g f' g' sq ↦
      D.isIso_canonicalBaseChangeMap_nativeModule
        ((subsingleton_datumPair_h1_iff D).mpr cert.h1_vanishing)
        g f' g' sq)
    cert

end PicRankOneNativePresentation

end AlgebraicGeometry
