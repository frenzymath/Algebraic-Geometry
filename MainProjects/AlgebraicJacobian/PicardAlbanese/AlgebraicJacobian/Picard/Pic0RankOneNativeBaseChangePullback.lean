/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.Pic0RankOneLocusNative
import AlgebraicJacobian.Cohomology.GluedSheafDatumBaseChange
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeAffine
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeMate
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeOpen
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
  [IsScalarTower k B B']
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

namespace BasicOpenCocycleDatum

noncomputable section

variable (D : BasicOpenCocycleDatum C B pi)

/-!
# Native pullback comparison

The datum-level `sectionsMap` is already linear over the structure-sheaf map and
commutes with restriction.  It therefore gives a morphism from the native module
to the pushforward of the base-changed native module.  Its adjoint is the
canonical comparison from the geometric pullback of `D.nativeModule` to the
native module rebuilt from `D.baseChange B'`.
-/

/-- `sectionsMap`, assembled as an `O_{C_B}`-linear map into pushforward. -/
noncomputable def nativeModuleSectionsMap :
    D.nativeModule ⟶
      (Scheme.Modules.pushforward (relCurveMap C B B')).obj
        (D.baseChange B').nativeModule :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun s ↦ D.sectionsMap B' le_rfl s)
        (fun s t ↦ D.sectionsMap_add B' le_rfl s t)
      naturality := fun {U V} i ↦ by
        ext s
        change D.sectionsMap B' le_rfl
            (gluedRes B D.pieces D.unit i.unop.le s) =
          gluedRes B' (D.baseChange B').pieces (D.baseChange B').unit
            (Scheme.Hom.preimage_mono (relCurveMap C B B') i.unop.le)
            (D.sectionsMap B' le_rfl s)
        exact (D.gluedRes_sectionsMap B' i.unop.le le_rfl le_rfl
          (Scheme.Hom.preimage_mono (relCurveMap C B B') i.unop.le) s).symm }
    (fun U r s ↦ by
      change D.sectionsMap B' le_rfl
          (gluedQsmul B D.pieces D.unit le_rfl r s) =
        gluedQsmul B' (D.baseChange B').pieces (D.baseChange B').unit le_rfl
          (((relCurveMap C B B').app U.unop).hom r) (D.sectionsMap B' le_rfl s)
      simpa only [Scheme.Hom.appLE_eq_app] using
        D.sectionsMap_gluedQsmul B'
          (W := U.unop) (W' := relCurveMap C B B' ⁻¹ᵁ U.unop)
          (V := U.unop) (V' := relCurveMap C B B' ⁻¹ᵁ U.unop)
          le_rfl le_rfl le_rfl le_rfl r s)⟩

@[simp]
theorem nativeModuleSectionsMap_app_apply (U : (relCurve C B).Opens)
    (s : Γ(D.nativeModule, U)) :
    (D.nativeModuleSectionsMap B').app U s = D.sectionsMap B' le_rfl s :=
  rfl

/-- The native module rebuilt from the base-changed datum receives the geometric
pullback of the original native module.  This is adjoint to `sectionsMap` on
every open, with no flatness or finiteness hypothesis on `B → B'`. -/
noncomputable def nativePullbackComparison :
    (Scheme.Modules.pullback (relCurveMap C B B')).obj D.nativeModule ⟶
      (D.baseChange B').nativeModule :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (relCurveMap C B B')).homEquiv D.nativeModule
      (D.baseChange B').nativeModule).symm (D.nativeModuleSectionsMap B')

/-- The adjunct of `nativePullbackComparison` is exactly the morphism assembled
from the datum-level `sectionsMap`. -/
@[simp]
theorem nativePullbackComparison_adjunct :
    (Scheme.Modules.pullbackPushforwardAdjunction
      (relCurveMap C B B')).homEquiv D.nativeModule
        (D.baseChange B').nativeModule (D.nativePullbackComparison B') =
      D.nativeModuleSectionsMap B' := by
  exact Equiv.apply_symm_apply _ _

/-- On a full preimage open, the native pullback comparison sends the
adjunction-unit base-map section to the datum-level base-changed section. -/
theorem nativePullbackComparison_baseMap (V : (relCurve C B).Opens)
    (s : Γ(D.nativeModule, V)) :
    ((D.nativePullbackComparison B').app (relCurveMap C B B' ⁻¹ᵁ V)).hom
        (pullback_app_isoTensor_baseMap (relCurveMap C B B') D.nativeModule
          (le_refl (relCurveMap C B B' ⁻¹ᵁ V)) s) =
      D.sectionsMap B' (le_refl (relCurveMap C B B' ⁻¹ᵁ V)) s := by
  have h := congrArg
    (fun (f : D.nativeModule ⟶
        (Scheme.Modules.pushforward (relCurveMap C B B')).obj
          (D.baseChange B').nativeModule) ↦
      (Scheme.Modules.Hom.app f V).hom s)
    (D.nativePullbackComparison_adjunct B')
  rw [Adjunction.homEquiv_unit] at h
  rw [pullback_app_isoTensor_baseMap_le_refl]
  exact h

private theorem unit_hom_ext_top {X : Scheme.{u}} {M : X.Modules}
    (f g : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (h : f.val.app (.op (⊤ : X.Opens)) (1 : Γ(X, ⊤)) =
      g.val.app (.op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) : f = g := by
  apply (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Γ(X, U.unop) at x
  change f.val.app U x = g.val.app U x
  rw [show x = x • (1 : Γ(X, U.unop)) by simp, map_smul, map_smul]
  congr 1
  have hf := congrArg (fun k ↦ k.hom (1 : Γ(X, ⊤)))
    ((Scheme.Modules.Hom.mapPresheaf f).naturality
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op)
  have hg := congrArg (fun k ↦ k.hom (1 : Γ(X, ⊤)))
    ((Scheme.Modules.Hom.mapPresheaf g).naturality
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op)
  change f.val.app U ((X.presheaf.map
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op).hom 1) =
    (M.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op).hom
      (f.val.app (.op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) at hf
  change g.val.app U ((X.presheaf.map
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op).hom 1) =
    (M.presheaf.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op).hom
      (g.val.app (.op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) at hg
  rw [map_one] at hf hg
  exact hf.trans ((congrArg
    (fun z ↦ (M.presheaf.map
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op).hom z) h).trans hg.symm)

private theorem open_hom_baseMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (y : Γ(N, f.opensRange)) :
    (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N)
        (⊤ : Y.Opens)).hom
      ((N.presheaf.map
        (eqToHom (Scheme.Hom.image_top_eq_opensRange f)).op).hom y) =
      pullback_app_isoTensor_baseMap f N
        (le_of_eq (Scheme.Hom.preimage_opensRange f).symm) y := by
  change (pullbackOpenImmersionSectionsEquiv f N).symm y = _
  exact pullbackOpenImmersionSectionsEquiv_symm_apply f N y

private theorem pullbackRestrictIso_baseMap_top
    {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)
    (N : X.Modules) (x : Γ(N, U)) :
    (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackRestrictIso g U).hom.app N)
        (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom
      (pullback_app_isoTensor_baseMap g N
        (show (g ⁻¹ᵁ U).ι ''ᵁ (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤ g ⁻¹ᵁ U by simp) x) =
      pullback_app_isoTensor_baseMap (g ∣_ U)
        ((Scheme.Modules.restrictFunctor U.ι).obj N)
        (le_top : (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤
          (g ∣_ U) ⁻¹ᵁ (⊤ : U.toScheme.Opens))
        ((N.presheaf.map
          (eqToHom (Scheme.Opens.ι_image_top U)).op).hom x) := by
  let f := (g ⁻¹ᵁ U).ι
  have eRange : f.opensRange ≤ g ⁻¹ᵁ U :=
    le_of_eq (Scheme.Opens.opensRange_ι (g ⁻¹ᵁ U))
  have eImage : f ''ᵁ (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤ g ⁻¹ᵁ U := by
    simp [f]
  have ePreRange : (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤ f ⁻¹ᵁ f.opensRange :=
    le_of_eq (Scheme.Hom.preimage_opensRange f).symm
  have eCompSource : (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤ (f ≫ g) ⁻¹ᵁ U := by
    rw [← morphismRestrict_ι g U]
    simp
  have hInput :
      ((((Scheme.Modules.pullback g).obj N).presheaf.map
        (eqToHom (Scheme.Hom.image_top_eq_opensRange f)).op).hom
          (pullback_app_isoTensor_baseMap g N eRange x)) =
        pullback_app_isoTensor_baseMap g N eImage x := by
    have heq : eqToHom (Scheme.Hom.image_top_eq_opensRange f) =
        homOfLE (le_of_eq (Scheme.Hom.image_top_eq_opensRange f)) :=
      Subsingleton.elim _ _
    rw [heq]
    simpa only [show homOfLE (le_refl U) = 𝟙 U from rfl,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply] using
      (pullback_app_isoTensor_baseMap_res g N eRange eImage le_rfl
        (le_of_eq (Scheme.Hom.image_top_eq_opensRange f)) x)
  have hOpenSource :
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          ((Scheme.Modules.pullback g).obj N)) ⊤).hom
        (pullback_app_isoTensor_baseMap g N eImage x) =
      pullback_app_isoTensor_baseMap f
        ((Scheme.Modules.pullback g).obj N) ePreRange
        (pullback_app_isoTensor_baseMap g N eRange x) := by
    rw [← hInput]
    exact open_hom_baseMap f ((Scheme.Modules.pullback g).obj N)
      (pullback_app_isoTensor_baseMap g N eRange x)
  have hCompSource := pullback_app_isoTensor_baseMap_comp f g N
    (T := (⊤ : (g ⁻¹ᵁ U).toScheme.Opens))
    (V := f.opensRange) (U := U)
    eRange ePreRange eCompSource x
  have eCompTarget : (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤
      ((g ∣_ U) ≫ U.ι) ⁻¹ᵁ U := by
    rw [morphismRestrict_ι]
    exact eCompSource
  have hCongr := pullback_app_isoTensor_baseMap_congr
    (morphismRestrict_ι g U).symm N
    (U := (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)) (V := U)
    eCompSource eCompTarget x
  have eOpenTarget : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have ePullbackTarget : (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤
      (g ∣_ U) ⁻¹ᵁ (⊤ : U.toScheme.Opens) := le_top
  have hCompTarget := pullback_app_isoTensor_baseMap_comp
    (g ∣_ U) U.ι N
    (T := (⊤ : (g ⁻¹ᵁ U).toScheme.Opens))
    (V := (⊤ : U.toScheme.Opens)) (U := U)
    eOpenTarget ePullbackTarget eCompTarget x
  have hCompTargetInv :
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).inv.app N) ⊤).hom
        (pullback_app_isoTensor_baseMap ((g ∣_ U) ≫ U.ι) N eCompTarget x) =
      pullback_app_isoTensor_baseMap (g ∣_ U)
        ((Scheme.Modules.pullback U.ι).obj N) ePullbackTarget
        (pullback_app_isoTensor_baseMap U.ι N eOpenTarget x) := by
    have h := congrArg
      (fun z => (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).inv.app N) ⊤).hom z)
      hCompTarget
    simpa only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply] using h.symm
  have hTargetRange : U.ι.opensRange = U := Scheme.Opens.opensRange_ι U
  have hUTargetRange : U ≤ U.ι.opensRange := le_of_eq hTargetRange.symm
  let yTarget : Γ(N, U.ι.opensRange) :=
    (N.presheaf.map (eqToHom hTargetRange).op).hom x
  have hyTarget :
      (N.presheaf.map (homOfLE hUTargetRange).op).hom yTarget = x := by
    dsimp only [yTarget]
    rw [← AddCommGrpCat.comp_apply, ← CategoryTheory.Functor.map_comp]
    have hm : (eqToHom hTargetRange).op ≫ (homOfLE hUTargetRange).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hm, CategoryTheory.Functor.map_id]
    change x = x
    rfl
  have hCastTarget :
      (N.presheaf.map
          (eqToHom (Scheme.Hom.image_top_eq_opensRange U.ι)).op).hom yTarget =
        (N.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U)).op).hom x := by
    dsimp only [yTarget]
    rw [← AddCommGrpCat.comp_apply, ← CategoryTheory.Functor.map_comp]
    have hm : (eqToHom hTargetRange).op ≫
        (eqToHom (Scheme.Hom.image_top_eq_opensRange U.ι)).op =
          (eqToHom (Scheme.Opens.ι_image_top U)).op :=
      Subsingleton.elim _ _
    rw [hm]
  have eRangeTarget : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U.ι.opensRange :=
    le_of_eq (Scheme.Hom.preimage_opensRange U.ι).symm
  have hBaseTarget :
      pullback_app_isoTensor_baseMap U.ι N eRangeTarget yTarget =
        pullback_app_isoTensor_baseMap U.ι N eOpenTarget x := by
    have hres := pullback_app_isoTensor_baseMap_res U.ι N
      eRangeTarget eOpenTarget hUTargetRange (le_refl (⊤ : U.toScheme.Opens)) yTarget
    rw [hyTarget] at hres
    simpa only [show homOfLE (le_refl (⊤ : U.toScheme.Opens)) = 𝟙 _ from rfl,
      op_id, CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply] using hres
  have hOpenTargetHom := open_hom_baseMap U.ι N yTarget
  have hOpenTarget :
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app N) ⊤).hom
        (pullback_app_isoTensor_baseMap U.ι N eOpenTarget x) =
      (N.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U)).op).hom x := by
    have h := congrArg
      (fun z => (Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app N) ⊤).hom z)
      hOpenTargetHom
    simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply] at h
    rw [hCastTarget] at h
    rw [← hBaseTarget]
    exact h.symm
  have hNatural := pullback_app_isoTensor_baseMap_naturality (g ∣_ U)
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app N)
    (U := (⊤ : (g ⁻¹ᵁ U).toScheme.Opens))
    (V := (⊤ : U.toScheme.Opens)) ePullbackTarget
    (pullback_app_isoTensor_baseMap U.ι N eOpenTarget x)
  change
    (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback (g ∣_ U)).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app N)) ⊤).hom
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).inv.app N) ⊤).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackCongr
            (morphismRestrict_ι g U).symm).hom.app N) ⊤).hom
          ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackComp f g).hom.app N) ⊤).hom
            ((Scheme.Modules.Hom.app
              ((Scheme.Modules.restrictFunctorIsoPullback
                f).hom.app
                ((Scheme.Modules.pullback g).obj N)) ⊤).hom
              (pullback_app_isoTensor_baseMap g N eImage x))))) = _
  rw [hOpenSource, hCompSource, hCongr, hCompTargetInv, hNatural, hOpenTarget]

private theorem pullbackUnitIso_baseMap_one {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.Hom.app (Scheme.Modules.pullbackUnitIso g).hom
      (⊤ : Y.Opens)).hom
      (pullback_app_isoTensor_baseMap g
        (SheafOfModules.unit X.ringCatSheaf)
        (le_top : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (⊤ : X.Opens))
        (1 : Γ(X, ⊤))) = (1 : Γ(Y, ⊤)) := by
  let oneX : Γ(SheafOfModules.unit X.ringCatSheaf, (⊤ : X.Opens)) :=
    (1 : Γ(X, ⊤))
  have h := congrArg
    (fun (f : SheafOfModules.unit X.ringCatSheaf ⟶
        (Scheme.Modules.pushforward g).obj
          (SheafOfModules.unit Y.ringCatSheaf)) =>
      (Scheme.Modules.Hom.app f (⊤ : X.Opens)).hom oneX)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      g.toRingCatSheafHom)
  rw [Adjunction.homEquiv_unit] at h
  rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply] at h
  change
    (Scheme.Modules.Hom.app
      (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
        (g ⁻¹ᵁ (⊤ : X.Opens))).hom
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (SheafOfModules.unit X.ringCatSheaf)) (⊤ : X.Opens)).hom
          (show Γ((𝟭 X.Modules).obj
            (SheafOfModules.unit X.ringCatSheaf), ⊤) from oneX)) =
      (g.app (⊤ : X.Opens)).hom oneX at h
  have hfull :
      (Scheme.Modules.Hom.app (Scheme.Modules.pullbackUnitIso g).hom
        (g ⁻¹ᵁ (⊤ : X.Opens))).hom
        (pullback_app_isoTensor_baseMap g
          (SheafOfModules.unit X.ringCatSheaf)
          (le_refl (g ⁻¹ᵁ (⊤ : X.Opens))) oneX) =
        (g.app (⊤ : X.Opens)).hom oneX := by
    rw [pullback_app_isoTensor_baseMap_le_refl]
    change
      (Scheme.Modules.Hom.app
        (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
          (g ⁻¹ᵁ (⊤ : X.Opens))).hom
        ((Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            (SheafOfModules.unit X.ringCatSheaf)) (⊤ : X.Opens)).hom
            (show Γ((𝟭 X.Modules).obj
              (SheafOfModules.unit X.ringCatSheaf), ⊤) from oneX)) =
        (g.app (⊤ : X.Opens)).hom oneX
    exact h
  simpa only [oneX, Scheme.Hom.preimage_top] using
    hfull.trans (map_one (g.app ⊤).hom)

/-- On every cocycle piece, the geometric pullback of the native module is canonically
trivial: restrict pullback to the full preimage, pull back the original piece
trivialization, then identify the pullback of the unit module with the unit module. -/
noncomputable def nativePullbackPieceSheafIso (j : D.index) :
    (Scheme.Modules.restrictFunctor
      (relCurveMap C B B' ⁻¹ᵁ D.pieces j).ι).obj
        ((Scheme.Modules.pullback (relCurveMap C B B')).obj D.nativeModule) ≅
      SheafOfModules.unit
        (relCurveMap C B B' ⁻¹ᵁ D.pieces j).toScheme.ringCatSheaf :=
    (Scheme.Modules.pullbackRestrictIso (relCurveMap C B B') (D.pieces j)).app
        D.nativeModule ≪≫
      (Scheme.Modules.pullback ((relCurveMap C B B') ∣_ D.pieces j)).mapIso
        (D.nativeModulePieceSheafIso j) ≪≫
      Scheme.Modules.pullbackUnitIso ((relCurveMap C B B') ∣_ D.pieces j)

private theorem nativeTargetPieceCoordinate_one (j : D.index)
    (s : Γ(D.nativeModule, D.pieces j))
    (hs : gluedTriv B D.isGluingCocycle j (le_refl (D.pieces j)) s = 1)
    (W : (relCurve C B').Opens)
    (hW : W = (D.baseChange B').pieces j) :
    let eOpen : W.ι ''ᵁ (⊤ : W.toScheme.Opens) ≤
        relCurveMap C B B' ⁻¹ᵁ D.pieces j := by
      rw [hW]
      exact (((D.baseChange B').pieces j).ι_image_le ⊤).trans
        (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' j)
    let eT :
      (Scheme.Modules.restrictFunctor W.ι).obj
          (D.baseChange B').nativeModule ≅
        SheafOfModules.unit W.toScheme.ringCatSheaf := by
      rw [hW]
      exact (D.baseChange B').nativeModulePieceSheafIso j
    let t := D.sectionsMap B' eOpen s
    let oneW : Γ(SheafOfModules.unit W.toScheme.ringCatSheaf,
        (⊤ : W.toScheme.Opens)) :=
      (show Γ(W.toScheme, ⊤) from 1)
    (Scheme.Modules.Hom.app eT.hom
      (⊤ : W.toScheme.Opens)).hom t = oneW := by
  subst W
  dsimp only
  let eTargetOpen :
      ((D.baseChange B').pieces j).ι ''ᵁ
          (⊤ : ((D.baseChange B').pieces j).toScheme.Opens) ≤
        relCurveMap C B B' ⁻¹ᵁ D.pieces j :=
    (((D.baseChange B').pieces j).ι_image_le ⊤).trans
      (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' j)
  have htriv := D.gluedTriv_sectionsMap B'
    eTargetOpen (le_refl (D.pieces j))
      (((D.baseChange B').pieces j).ι_image_le ⊤) s
  rw [hs, map_one] at htriv
  change
    (((D.baseChange B').pieces j).ι.appIso
      (⊤ : ((D.baseChange B').pieces j).toScheme.Opens)).commRingCatIsoToRingEquiv
      (gluedTriv B' (D.baseChange B').isGluingCocycle j
        (((D.baseChange B').pieces j).ι_image_le ⊤)
        (D.sectionsMap B' eTargetOpen s)) = 1
  rw [htriv, map_one]

set_option maxHeartbeats 1600000 in
/-- The canonical comparison from the geometric pullback of the native module to the
native module rebuilt from the base-changed cocycle datum is an isomorphism for every
affine base change. -/
theorem isIso_nativePullbackComparison :
    IsIso (D.nativePullbackComparison B') := by
  classical
  apply Scheme.Modules.isIso_of_isIso_restrict_cover
    (D.nativePullbackComparison B')
    (fun j : D.index => relCurveMap C B B' ⁻¹ᵁ D.pieces j)
  · intro x
    obtain ⟨j, hj⟩ := (D.baseChange B').exists_mem_pieces x
    change D.index at j
    refine ⟨j, ?_⟩
    rw [← D.toBasicOpenCoverData.pieces_baseChange B' j]
    exact hj
  · intro j
    let g := relCurveMap C B B'
    let U := D.pieces j
    let eS := D.nativePullbackPieceSheafIso B' j
    let eT :
        (Scheme.Modules.restrictFunctor
          (g ⁻¹ᵁ U).ι).obj
            (D.baseChange B').nativeModule ≅
          SheafOfModules.unit
            (g ⁻¹ᵁ U).toScheme.ringCatSheaf := by
      dsimp only [g, U]
      rw [← D.toBasicOpenCoverData.pieces_baseChange B' j]
      exact (D.baseChange B').nativeModulePieceSheafIso j
    let r := (Scheme.Modules.restrictFunctor
      (g ⁻¹ᵁ U).ι).map
        (D.nativePullbackComparison B')
    let s : Γ(D.nativeModule, U) :=
      (gluedTriv B D.isGluingCocycle j (le_refl U)).symm 1
    have hs : gluedTriv B D.isGluingCocycle j (le_refl U) s = 1 := by
      simp only [s, LinearEquiv.apply_symm_apply]
    let eOpen : (g ⁻¹ᵁ U).ι ''ᵁ (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤ g ⁻¹ᵁ U := by
      simp
    let z := pullback_app_isoTensor_baseMap g D.nativeModule
      eOpen s
    let oneP : Γ(SheafOfModules.unit (g ⁻¹ᵁ U).toScheme.ringCatSheaf,
        (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)) :=
      (show Γ((g ⁻¹ᵁ U).toScheme, ⊤) from 1)
    have hPiece :
        (Scheme.Modules.Hom.app (D.nativeModulePieceSheafIso j).hom
          (⊤ : U.toScheme.Opens)).hom
            ((D.nativeModule.presheaf.map
              (eqToHom (Scheme.Opens.ι_image_top U)).op).hom s) =
          (1 : Γ(U.toScheme, ⊤)) := by
      change
        (U.ι.appIso (⊤ : U.toScheme.Opens)).commRingCatIsoToRingEquiv
          (gluedTriv B D.isGluingCocycle j (U.ι_image_le ⊤)
            ((D.nativeModule.presheaf.map
              (eqToHom (Scheme.Opens.ι_image_top U)).op).hom s)) = 1
      have hm : eqToHom (Scheme.Opens.ι_image_top U) =
          homOfLE (U.ι_image_le (⊤ : U.toScheme.Opens)) :=
        Subsingleton.elim _ _
      rw [hm]
      change
        (U.ι.appIso (⊤ : U.toScheme.Opens)).commRingCatIsoToRingEquiv
          (gluedTriv B D.isGluingCocycle j (U.ι_image_le ⊤)
            (gluedRes B D.pieces D.unit (U.ι_image_le ⊤) s)) = 1
      rw [gluedTriv_res B D.isGluingCocycle j (U.ι_image_le ⊤)
        (show U ≤ D.pieces j from le_rfl) s, hs, map_one, map_one]
    have hSource :
        (Scheme.Modules.Hom.app eS.hom
          (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom z = oneP := by
      have hRestrict := pullbackRestrictIso_baseMap_top g U D.nativeModule s
      have hNatural := pullback_app_isoTensor_baseMap_naturality (g ∣_ U)
        (D.nativeModulePieceSheafIso j).hom
        (le_top : (⊤ : (g ⁻¹ᵁ U).toScheme.Opens) ≤
          (g ∣_ U) ⁻¹ᵁ (⊤ : U.toScheme.Opens))
        ((D.nativeModule.presheaf.map
          (eqToHom (Scheme.Opens.ι_image_top U)).op).hom s)
      rw [hPiece] at hNatural
      have hFirst := congrArg
        (fun y =>
          (Scheme.Modules.Hom.app (Scheme.Modules.pullbackUnitIso (g ∣_ U)).hom
            (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom
            ((Scheme.Modules.Hom.app
              ((Scheme.Modules.pullback (g ∣_ U)).map
                (D.nativeModulePieceSheafIso j).hom)
              (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom y)) hRestrict
      have hSecond := congrArg
        (fun y =>
          (Scheme.Modules.Hom.app (Scheme.Modules.pullbackUnitIso (g ∣_ U)).hom
            (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom y) hNatural
      dsimp only [eS, nativePullbackPieceSheafIso]
      simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app,
        AddCommGrpCat.comp_apply]
      exact hFirst.trans (hSecond.trans (pullbackUnitIso_baseMap_one (g ∣_ U)))
    have hInv :
        (Scheme.Modules.Hom.app eS.inv
          (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom oneP = z := by
      have h := congrArg
        (fun x => (Scheme.Modules.Hom.app eS.inv
          (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom x) hSource
      simpa only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
        eS.hom_inv_id, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
        AddMonoidHom.id_apply] using h.symm
    let t := D.sectionsMap B' eOpen s
    have hCompare :
        (Scheme.Modules.Hom.app r
          (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom z =
          t := by
      let zFull := pullback_app_isoTensor_baseMap g D.nativeModule
        (le_refl (g ⁻¹ᵁ U)) s
      let sourceRes := (((Scheme.Modules.pullback g).obj D.nativeModule).presheaf.map
        (homOfLE eOpen).op).hom
      let targetRes := ((D.baseChange B').nativeModule.presheaf.map
        (homOfLE eOpen).op).hom
      have hSourceRes : sourceRes zFull = z := by
        have hres := pullback_app_isoTensor_baseMap_res g D.nativeModule
          (le_refl (g ⁻¹ᵁ U)) eOpen (le_refl U) eOpen s
        simpa only [sourceRes, zFull, z,
          show homOfLE (le_refl U) = 𝟙 U from rfl, op_id,
          CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id,
          AddMonoidHom.id_apply] using hres
      have hFull := D.nativePullbackComparison_baseMap B' U s
      have hNat := congrArg (fun k => k.hom zFull)
        ((Scheme.Modules.Hom.mapPresheaf (D.nativePullbackComparison B')).naturality
          (homOfLE eOpen).op)
      rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at hNat
      change
        ((D.nativePullbackComparison B').app
          ((g ⁻¹ᵁ U).ι ''ᵁ (⊤ : (g ⁻¹ᵁ U).toScheme.Opens))).hom
            (sourceRes zFull) =
          targetRes ((D.nativePullbackComparison B').app (g ⁻¹ᵁ U) zFull) at hNat
      have hsSelf : gluedRes B D.pieces D.unit (le_refl U) s = s := by
        apply Subtype.ext
        funext i
        rw [gluedRes_coe, Scheme.resHom_self]
      have hTargetRes :
          targetRes (D.sectionsMap B' (le_refl (g ⁻¹ᵁ U)) s) = t := by
        have hres := D.gluedRes_sectionsMap B' (le_refl U)
          (le_refl (g ⁻¹ᵁ U)) eOpen eOpen s
        rw [hsSelf] at hres
        exact hres
      dsimp only [r]
      change
        ((D.nativePullbackComparison B').app
          ((g ⁻¹ᵁ U).ι ''ᵁ (⊤ : (g ⁻¹ᵁ U).toScheme.Opens))).hom z = t
      calc
        _ = ((D.nativePullbackComparison B').app
            ((g ⁻¹ᵁ U).ι ''ᵁ (⊤ : (g ⁻¹ᵁ U).toScheme.Opens))).hom
              (sourceRes zFull) := congrArg _ hSourceRes.symm
        _ = targetRes ((D.nativePullbackComparison B').app (g ⁻¹ᵁ U) zFull) := hNat
        _ = targetRes (D.sectionsMap B' (le_refl (g ⁻¹ᵁ U)) s) :=
          congrArg targetRes hFull
        _ = t := hTargetRes
    have hTarget :
        (Scheme.Modules.Hom.app eT.hom
          (⊤ : (g ⁻¹ᵁ U).toScheme.Opens)).hom
            t = oneP := by
      exact nativeTargetPieceCoordinate_one (D := D) (B' := B') j s hs (g ⁻¹ᵁ U) (by
        dsimp only [g, U]
        exact (D.toBasicOpenCoverData.pieces_baseChange B' j).symm)
    have hconj : eS.inv ≫ r ≫ eT.hom = 𝟙 _ := by
      apply unit_hom_ext_top
      change
        (Scheme.Modules.Hom.app eT.hom ⊤).hom
          ((Scheme.Modules.Hom.app r ⊤).hom
            ((Scheme.Modules.Hom.app eS.inv ⊤).hom oneP)) = oneP
      rw [hInv, hCompare, hTarget]
    haveI : IsIso (eS.inv ≫ r ≫ eT.hom) := by
      rw [hconj]
      infer_instance
    haveI : IsIso (eS.inv ≫ r) :=
      IsIso.of_isIso_comp_right (eS.inv ≫ r) eT.hom
    exact IsIso.of_isIso_comp_left eS.inv r

/-- The canonical native-module pullback isomorphism for an arbitrary affine base change. -/
noncomputable def nativePullbackIso :
    (Scheme.Modules.pullback (relCurveMap C B B')).obj D.nativeModule ≅
      (D.baseChange B').nativeModule := by
  letI := D.isIso_nativePullbackComparison B'
  exact asIso (D.nativePullbackComparison B')

end

end BasicOpenCocycleDatum

end AlgebraicGeometry
