/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.Pic0RankOneNativeBaseChangeH0
import AlgebraicJacobian.Picard.Pic0RankOneNativeBaseChangePullback
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeOpen
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Affine presentation of the native rank-one pushforward

The native degree-zero base-change equivalence identifies localization of global
sections with sections after base change.  The native pullback comparison and the
open-immersion sections equivalence then identify those sections with restriction
to the corresponding principal open.  Thus the actual native pushforward is
localizing on `Spec B`, so its canonical affine presentation is an isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

namespace BasicOpenCocycleDatum

noncomputable section

variable (D : BasicOpenCocycleDatum C B pi)

local instance nativeLocalizingSectionsModule (U : (relCurve C B).Opens) :
    Module B Γ(D.nativeModule, U) :=
  Scheme.moduleKSections
    (Over.mk (relCurve C B ↘ Spec (.of B))) D.nativeModule U

/-- Native global sections agree linearly with the global sections used by the
affine `modulesSpecToSheaf` presentation of the native pushforward. -/
noncomputable def nativePushforwardTopSectionsLinearEquiv :
    Γ(D.nativeModule, ⊤) ≃ₗ[B]
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
        ((Scheme.Modules.pushforward
          (relCurve C B ↘ Spec (.of B))).obj D.nativeModule)) := by
  let f := relCurve C B ↘ Spec (.of B)
  let hTop : (⊤ : (relCurve C B).Opens) =
      f ⁻¹ᵁ (⊤ : (Spec (.of B)).Opens) :=
    (Scheme.Hom.preimage_top f).symm
  let topAdd : Γ(D.nativeModule, ⊤) ≃+
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
        ((Scheme.Modules.pushforward f).obj D.nativeModule)) :=
    AddEquiv.ofBijective
      (D.nativeModule.presheaf.map (eqToHom hTop.symm).op).hom
      (ConcreteCategory.bijective_of_isIso
        (D.nativeModule.presheaf.map (eqToHom hTop.symm).op))
  exact topAdd.toLinearEquiv (by
    intro b x
    change (D.nativeModule.presheaf.map
        (eqToHom hTop.symm).op).hom
          ((relCurve C B).overAlgebraMap B ⊤ b • x) = _
    rw [D.nativeModule.map_smul]
    change ((relCurve C B).presheaf.map
          (eqToHom hTop.symm).op).hom
            ((relCurve C B).overAlgebraMap B ⊤ b) •
          (show Γ(D.nativeModule,
            f ⁻¹ᵁ (⊤ : (Spec (.of B)).Opens)) from topAdd x) =
      (f.app ⊤).hom ((Scheme.ΓSpecIso (.of B)).inv.hom b) •
        (show Γ(D.nativeModule,
          f ⁻¹ᵁ (⊤ : (Spec (.of B)).Opens)) from topAdd x)
    congr 1
    rw [(relCurve C B).overAlgebraMap_apply_res B]
    have hcomp : f ≫ (Spec (.of B) ↘ Spec (.of B)) =
        relCurve C B ↘ Spec (.of B) := by
      simp [f]
    have hcoeff := f.appLE_overAlgebraMap hcomp
      (U := (⊤ : (Spec (.of B)).Opens))
      (V := f ⁻¹ᵁ (⊤ : (Spec (.of B)).Opens))
      (le_rfl : f ⁻¹ᵁ (⊤ : (Spec (.of B)).Opens) ≤
        f ⁻¹ᵁ (⊤ : (Spec (.of B)).Opens)) b
    rw [f.appLE_eq_app] at hcoeff
    simpa [Scheme.overAlgebraMap] using hcoeff.symm)

@[simp]
theorem nativePushforwardTopSectionsLinearEquiv_apply
    (x : Γ(D.nativeModule, ⊤)) :
    D.nativePushforwardTopSectionsLinearEquiv x =
      (D.nativeModule.presheaf.map
        (eqToHom (Scheme.Hom.preimage_top
          (relCurve C B ↘ Spec (.of B)))).op).hom x :=
  rfl

private noncomputable def nativePushforwardSectionsLinearEquiv
    (U : (Spec (.of B)).Opens) :
    ((modulesSpecToSheaf.obj
      ((Scheme.Modules.pushforward
        (relCurve C B ↘ Spec (.of B))).obj D.nativeModule)).presheaf.obj
          (op U)) ≃ₗ[B]
      Γ(D.nativeModule,
        (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ U) := by
  let p := relCurve C B ↘ Spec (.of B)
  let sectionsAdd :
      ((modulesSpecToSheaf.obj
        ((Scheme.Modules.pushforward p).obj D.nativeModule)).presheaf.obj
          (op U)) ≃+
        Γ(D.nativeModule, p ⁻¹ᵁ U) :=
    AddEquiv.refl _
  exact sectionsAdd.toLinearEquiv (by
    intro b x
    change (p.app U).hom ((Spec (.of B)).overAlgebraMap B U b) •
        (show Γ(D.nativeModule, p ⁻¹ᵁ U) from sectionsAdd x) =
      (relCurve C B).overAlgebraMap B (p ⁻¹ᵁ U) b •
        (show Γ(D.nativeModule, p ⁻¹ᵁ U) from sectionsAdd x)
    have hcomp : p ≫ (Spec (.of B) ↘ Spec (.of B)) =
        relCurve C B ↘ Spec (.of B) := by
      simp [p]
    have hcoeff := p.appLE_overAlgebraMap hcomp
      (U := U) (V := p ⁻¹ᵁ U) le_rfl b
    rw [p.appLE_eq_app] at hcoeff
    exact congrArg
      (fun s ↦ s • (show Γ(D.nativeModule, p ⁻¹ᵁ U) from sectionsAdd x)) hcoeff)

private lemma cast_restrict_eq {X : Scheme.{u}} {R : Type u} [CommRing R]
    (N : X.Modules) [∀ U : X.Opens, Module R Γ(N, U)]
    {U V : X.Opens} (h : U = V) (x : Γ(N, ⊤)) :
    (LinearEquiv.cast (R := R) (M := fun W : X.Opens ↦ Γ(N, W)) h)
        ((N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom x := by
  subst V
  rfl

set_option maxHeartbeats 1200000 in
private theorem nativePrincipalOpenPresentation
    (hH1 : Subsingleton (datumPair D).H1) (f : B) :
    Nonempty { e : Localization.Away f ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[B]
        Γ(D.nativeModule,
          (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ PrimeSpectrum.basicOpen f) //
      ∀ x : Γ(D.nativeModule, ⊤), e (1 ⊗ₜ[B] x) =
        (D.nativeModule.presheaf.map
          (homOfLE (le_top :
            (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ
              PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x } := by
  let S := Localization.Away f
  haveI : IsOpenImmersion (overSpecMap (k := k) B S).left := by
    rw [overSpecMap_left]
    exact IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion (relCurveMap C B S) := by
    unfold relCurveMap
    infer_instance
  have hRange : (relCurveMap C B S).opensRange =
      (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen f := by
    apply Opens.ext
    change Set.range ((C ◁ overSpecMap (k := k) B S).left).base =
      (snd C (overSpec k B)).left.base ⁻¹'
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B))
    rw [Over.range_whiskerLeft C (overSpecMap (k := k) B S)]
    rw [overSpecMap_left]
    change (snd C (overSpec k B)).left.base ⁻¹'
        Set.range (PrimeSpectrum.comap (algebraMap B S)) = _
    rw [PrimeSpectrum.localization_away_comap_range S f]
  letI nativeBaseChangedSectionsModule
      (U : (relCurve C S).Opens) :
      Module S Γ((D.baseChange S).nativeModule, U) :=
    Scheme.moduleKSections
      (Over.mk (relCurve C S ↘ Spec (.of S)))
      (D.baseChange S).nativeModule U
  letI nativePullbackSectionsModule
      (U : (relCurve C S).Opens) :
      Module S Γ((Scheme.Modules.pullback
        (relCurveMap C B S)).obj D.nativeModule, U) :=
    Scheme.moduleKSections
      (Over.mk (relCurve C S ↘ Spec (.of S)))
      ((Scheme.Modules.pullback (relCurveMap C B S)).obj D.nativeModule) U
  let eH0S : S ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[S]
      Γ((D.baseChange S).nativeModule, ⊤) :=
    D.nativeH0BaseChange S hH1
  letI : IsIso (D.nativePullbackComparison S) :=
    D.isIso_nativePullbackComparison S
  let comparisonIso := asIso (D.nativePullbackComparison S)
  let eComparisonAdd : Γ((D.baseChange S).nativeModule, ⊤) ≃+
      Γ((Scheme.Modules.pullback
        (relCurveMap C B S)).obj D.nativeModule, ⊤) :=
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
  let eComparisonS : Γ((D.baseChange S).nativeModule, ⊤) ≃ₗ[S]
      Γ((Scheme.Modules.pullback
        (relCurveMap C B S)).obj D.nativeModule, ⊤) :=
    eComparisonAdd.toLinearEquiv (by
      intro s x
      change (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom
          ((relCurve C S).overAlgebraMap S ⊤ s • x) =
        (relCurve C S).overAlgebraMap S ⊤ s •
          (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom x
      exact Scheme.Modules.Hom.app_smul comparisonIso.inv _ x)
  letI nativeBaseChangedSectionsModuleB
      (U : (relCurve C S).Opens) :
      Module B Γ((D.baseChange S).nativeModule, U) :=
    Module.compHom _ (algebraMap B S)
  letI nativePullbackSectionsModuleB
      (U : (relCurve C S).Opens) :
      Module B Γ((Scheme.Modules.pullback
        (relCurveMap C B S)).obj D.nativeModule, U) :=
    Module.compHom _ (algebraMap B S)
  let eH0 : S ⊗[B] Γ(D.nativeModule, ⊤) ≃ₗ[B]
      Γ((D.baseChange S).nativeModule, ⊤) :=
    eH0S.toAddEquiv.toLinearEquiv (by
      intro b x
      calc
        eH0S.toAddEquiv (b • x) =
            eH0S ((algebraMap B S b) • x) :=
          congrArg (fun y ↦ eH0S y)
            (IsScalarTower.algebraMap_smul S b x).symm
        _ = (algebraMap B S b) • eH0S x :=
          eH0S.map_smul (algebraMap B S b) x
        _ = b • eH0S.toAddEquiv x := rfl)
  let eComparison : Γ((D.baseChange S).nativeModule, ⊤) ≃ₗ[B]
      Γ((Scheme.Modules.pullback
        (relCurveMap C B S)).obj D.nativeModule, ⊤) :=
    eComparisonS.toAddEquiv.toLinearEquiv (by
      intro b x
      change eComparisonS ((algebraMap B S b) • x) =
        (algebraMap B S b) • eComparisonS x
      rw [map_smul])
  letI nativePullbackRangeSectionsModule :
      Module Γ(relCurve C B, (relCurveMap C B S).opensRange)
        Γ((Scheme.Modules.pullback
          (relCurveMap C B S)).obj D.nativeModule, ⊤) :=
    Module.compHom _ ((relCurveMap C B S).appLE
      (relCurveMap C B S).opensRange ⊤
        (le_of_eq (Scheme.Hom.preimage_opensRange
          (relCurveMap C B S)).symm)).hom
  let eOpenAdd := pullbackOpenImmersionSectionsEquiv
    (relCurveMap C B S) D.nativeModule
  let eOpen : Γ((Scheme.Modules.pullback
        (relCurveMap C B S)).obj D.nativeModule, ⊤) ≃ₗ[B]
      Γ(D.nativeModule, (relCurveMap C B S).opensRange) :=
    eOpenAdd.toLinearEquiv (by
      intro b x
      change eOpenAdd (b • x) = b • eOpenAdd x
      apply eOpenAdd.symm.injective
      rw [eOpenAdd.symm_apply_apply,
        pullbackOpenImmersionSectionsEquiv_symm_apply]
      change b • x = pullback_app_isoTensor_baseMap
        (relCurveMap C B S) D.nativeModule
          (le_of_eq (Scheme.Hom.preimage_opensRange
            (relCurveMap C B S)).symm)
          ((relCurve C B).overAlgebraMap B
            (relCurveMap C B S).opensRange b • eOpenAdd x)
      rw [(pullback_app_isoTensor_baseMap
        (relCurveMap C B S) D.nativeModule
          (le_of_eq (Scheme.Hom.preimage_opensRange
            (relCurveMap C B S)).symm)).map_smul]
      rw [← pullbackOpenImmersionSectionsEquiv_symm_apply,
        eOpenAdd.symm_apply_apply]
      change b • x = ((relCurveMap C B S).appLE
          (relCurveMap C B S).opensRange ⊤
            (le_of_eq (Scheme.Hom.preimage_opensRange
              (relCurveMap C B S)).symm)).hom
        ((relCurve C B).overAlgebraMap B
          (relCurveMap C B S).opensRange b) • x
      rw [relCurveMap_appLE_overAlgebraMap]
      rfl)
  let eRange : Γ(D.nativeModule, (relCurveMap C B S).opensRange) ≃ₗ[B]
      Γ(D.nativeModule,
        (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ
          PrimeSpectrum.basicOpen f) :=
    LinearEquiv.cast (M := fun U : (relCurve C B).Opens ↦ Γ(D.nativeModule, U)) hRange
  let e := eH0.trans (eComparison.trans (eOpen.trans eRange))
  have eComparison_sectionsMap (x : Γ(D.nativeModule, ⊤)) :
      eComparison (D.sectionsMap S le_rfl x) =
        pullback_app_isoTensor_baseMap (relCurveMap C B S) D.nativeModule
          (le_refl (relCurveMap C B S ⁻¹ᵁ (⊤ : (relCurve C B).Opens))) x := by
    change (Scheme.Modules.Hom.app comparisonIso.inv ⊤).hom
      (D.sectionsMap S le_rfl x) = _
    have hComparison :
        (Scheme.Modules.Hom.app comparisonIso.hom ⊤).hom
            (pullback_app_isoTensor_baseMap
              (relCurveMap C B S) D.nativeModule
                (le_refl (relCurveMap C B S ⁻¹ᵁ
                  (⊤ : (relCurve C B).Opens))) x) =
          D.sectionsMap S le_rfl x := by
      change ((D.nativePullbackComparison S).app ⊤).hom _ = _
      simpa only [Scheme.Hom.preimage_top] using
        D.nativePullbackComparison_baseMap S
          (⊤ : (relCurve C B).Opens) x
    rw [← hComparison, ← AddCommGrpCat.comp_apply,
      ← Scheme.Modules.Hom.comp_app, comparisonIso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    exact CategoryTheory.id_apply _
  have eOpen_baseMap (x : Γ(D.nativeModule, ⊤)) :
      eOpen
          (pullback_app_isoTensor_baseMap (relCurveMap C B S) D.nativeModule
            (le_refl (relCurveMap C B S ⁻¹ᵁ (⊤ : (relCurve C B).Opens))) x) =
        (D.nativeModule.presheaf.map
          (homOfLE (le_top : (relCurveMap C B S).opensRange ≤ ⊤)).op).hom x := by
    change eOpenAdd _ = _
    apply eOpenAdd.symm.injective
    rw [eOpenAdd.symm_apply_apply,
      pullbackOpenImmersionSectionsEquiv_symm_apply]
    have hres := pullback_app_isoTensor_baseMap_res
      (relCurveMap C B S) D.nativeModule
      (le_refl (relCurveMap C B S ⁻¹ᵁ (⊤ : (relCurve C B).Opens)))
      (le_of_eq (Scheme.Hom.preimage_opensRange (relCurveMap C B S)).symm)
      (le_top : (relCurveMap C B S).opensRange ≤ ⊤)
      (le_of_eq (Scheme.Hom.preimage_top (relCurveMap C B S)).symm) x
    simpa only [Scheme.Hom.preimage_top,
      show (homOfLE (le_refl (⊤ : (relCurve C S).Opens))).op =
        𝟙 (Opposite.op (⊤ : (relCurve C S).Opens)) from rfl,
      CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply] using hres
  have e_one_tmul (x : Γ(D.nativeModule, ⊤)) :
      e (1 ⊗ₜ[B] x) =
        (D.nativeModule.presheaf.map
          (homOfLE (le_top :
            (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ
              PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom x := by
    change eRange (eOpen (eComparison (eH0 (1 ⊗ₜ[B] x)))) = _
    rw [show eH0 (1 ⊗ₜ[B] x) = D.sectionsMap S le_rfl x from
      D.nativeH0BaseChange_one_tmul_eq_sectionsMap S hH1 x]
    rw [eComparison_sectionsMap, eOpen_baseMap]
    exact cast_restrict_eq D.nativeModule hRange x
  exact ⟨⟨e, e_one_tmul⟩⟩

set_option maxHeartbeats 1200000 in
private noncomputable def nativePrincipalOpenRestriction (f : B) :
    Γ(D.nativeModule, ⊤) →ₗ[B]
      Γ(D.nativeModule,
        (relCurve C B ↘ Spec (.of B)) ⁻¹ᵁ
          PrimeSpectrum.basicOpen f) :=
  ((Scheme.toModuleKSheafOfModules
    (Over.mk (relCurve C B ↘ Spec (.of B))) D.nativeModule).obj.map
      (homOfLE le_top).op).hom

set_option maxHeartbeats 1200000 in
private noncomputable def nativeAffinePushforwardRestriction (f : B) :=
  ((modulesSpecToSheaf.obj
    ((Scheme.Modules.pushforward
      (relCurve C B ↘ Spec (.of B))).obj D.nativeModule)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom

set_option maxHeartbeats 1200000 in
private theorem nativePushforwardRestriction_naturality (f : B) :
    (D.nativePushforwardSectionsLinearEquiv
        (PrimeSpectrum.basicOpen f)).toLinearMap ∘ₗ
        D.nativeAffinePushforwardRestriction f =
      D.nativePrincipalOpenRestriction f ∘ₗ
        D.nativePushforwardTopSectionsLinearEquiv.symm.toLinearMap := by
  let p := relCurve C B ↘ Spec (.of B)
  apply LinearMap.ext
  intro x
  change (D.nativeModule.presheaf.map
        ((Opens.map p.base).map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))).op).hom x =
    (D.nativeModule.presheaf.map
      (homOfLE (le_top : p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
        (D.nativePushforwardTopSectionsLinearEquiv.symm x)
  nth_rewrite 1 [← D.nativePushforwardTopSectionsLinearEquiv.apply_symm_apply x]
  rw [nativePushforwardTopSectionsLinearEquiv_apply]
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  rfl

set_option maxHeartbeats 1200000 in
private theorem isLocalizedModule_nativeAffinePushforwardRestriction
    (hH1 : Subsingleton (datumPair D).H1) (f : B) :
    IsLocalizedModule (Submonoid.powers f)
      (D.nativeAffinePushforwardRestriction f) := by
  let S := Localization.Away f
  obtain ⟨⟨e, e_one_tmul⟩⟩ :=
    D.nativePrincipalOpenPresentation hH1 f
  have heq : e.toLinearMap ∘ₗ
      TensorProduct.mk B S Γ(D.nativeModule, ⊤) 1 =
        D.nativePrincipalOpenRestriction f := by
    apply LinearMap.ext
    intro x
    exact e_one_tmul x
  have hres : IsLocalizedModule (Submonoid.powers f)
      (D.nativePrincipalOpenRestriction f) := by
    rw [← heq]
    exact IsLocalizedModule.of_linearEquiv _ _ e
  rw [← IsLocalizedModule.comp_iff_of_bijective_left
      (Submonoid.powers f)
      (D.nativePushforwardSectionsLinearEquiv
        (PrimeSpectrum.basicOpen f)).toLinearMap
      (D.nativePushforwardSectionsLinearEquiv
        (PrimeSpectrum.basicOpen f)).bijective,
    D.nativePushforwardRestriction_naturality f,
    IsLocalizedModule.comp_iff_of_bijective_right
      (Submonoid.powers f)
      D.nativePushforwardTopSectionsLinearEquiv.symm.toLinearMap
      D.nativePushforwardTopSectionsLinearEquiv.symm.bijective]
  exact hres

set_option maxHeartbeats 200000 in
/-- The actual native pushforward on the affine base is presented by its module
of global sections as soon as the datum has vanishing first cohomology. -/
theorem isIso_nativePushforward_fromTildeΓ
    (hH1 : Subsingleton (datumPair D).H1) :
    IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of B)
      ((Scheme.Modules.pushforward
        (relCurve C B ↘ Spec (.of B))).obj D.nativeModule)) := by
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  intro f
  exact D.isLocalizedModule_nativeAffinePushforwardRestriction hH1 f

end

end BasicOpenCocycleDatum

end AlgebraicGeometry
