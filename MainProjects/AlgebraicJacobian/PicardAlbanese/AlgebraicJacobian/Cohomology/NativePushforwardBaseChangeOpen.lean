/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeMate
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Pullback sections over an affine open

This file identifies top sections after pullback along the canonical map from
the spectrum of the coordinate ring of an affine open.  The inverse of the
identification is pinned to `pullback_app_isoTensor_baseMap`, so it can be used
directly in canonical base-change mate calculations.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-! ## Sections along an open immersion -/

/-- Top sections of a pullback along an open immersion are sections over its image. -/
noncomputable def pullbackOpenImmersionSectionsEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (N : Y.Modules) :
    Γ((Scheme.Modules.pullback f).obj N, ⊤) ≃+ Γ(N, f.opensRange) := by
  let isoSheaf : (Scheme.Modules.pullback f).obj N ≅ N.restrict f :=
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N).symm
  have hImg : (f ''ᵁ (⊤ : X.Opens) : Y.Opens) = f.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange]
  let toFun : Γ((Scheme.Modules.pullback f).obj N, ⊤) → Γ(N, f.opensRange) := fun x =>
    (N.presheaf.map (eqToHom hImg.symm).op).hom
      ((Scheme.Modules.Hom.app isoSheaf.hom ⊤).hom x)
  let invFun : Γ(N, f.opensRange) → Γ((Scheme.Modules.pullback f).obj N, ⊤) := fun y =>
    (Scheme.Modules.Hom.app isoSheaf.inv ⊤).hom
      ((N.presheaf.map (eqToHom hImg).op).hom y)
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro x
    simp only [invFun, toFun, ← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp,
      eqToHom_trans, eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
      AddCommGrpCat.hom_id, AddMonoidHom.id_apply, ← Scheme.Modules.Hom.comp_app,
      isoSheaf.hom_inv_id, Scheme.Modules.Hom.id_app]
  · intro y
    simp only [invFun, toFun, ← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
      isoSheaf.inv_hom_id, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  · intro x y
    change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom hImg.symm).op))
      ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) (x + y)) = _
    rw [show ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) (x + y)) =
      (AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) x +
      (AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) y from
      AddMonoidHom.map_add _ _ _]
    exact AddMonoidHom.map_add _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma modules_res_res_hom
    {Y : Scheme.{u}} (N : Y.Modules) {W₁ W₂ W₃ : Y.Opens}
    (i₁ : W₁ ⟶ W₂) (i₂ : W₂ ⟶ W₃) (i₃ : W₁ ⟶ W₃) (x : Γ(N, W₃)) :
    (N.presheaf.map i₁.op).hom ((N.presheaf.map i₂.op).hom x) =
      (N.presheaf.map i₃.op).hom x := by
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact (congrArg (fun (i : W₁ ⟶ W₃) =>
    (AddCommGrpCat.Hom.hom (N.presheaf.map i.op)) x) (Subsingleton.elim _ _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `pullbackOpenImmersionSectionsEquiv` is exactly the pullback
adjunction unit on the full inverse image of the immersion's range. -/
theorem pullbackOpenImmersionSectionsEquiv_symm_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (N : Y.Modules) (y : Γ(N, f.opensRange)) :
    (pullbackOpenImmersionSectionsEquiv f N).symm y =
      pullback_app_isoTensor_baseMap f N
        (le_of_eq (Scheme.Hom.preimage_opensRange f).symm) y := by
  let isoSheaf : (Scheme.Modules.pullback f).obj N ≅ N.restrict f :=
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N).symm
  have hImg : (f ''ᵁ (⊤ : X.Opens) : Y.Opens) = f.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange]
  dsimp [pullbackOpenImmersionSectionsEquiv]
  change (Scheme.Modules.Hom.app isoSheaf.inv ⊤).hom
      ((N.presheaf.map (eqToHom hImg).op).hom y) = _
  have hk := congrArg
    (fun (k : N ⟶ (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pullback f).obj N)) =>
      (Scheme.Modules.Hom.app k f.opensRange).hom y)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f) N)
  have hnat := congrArg
    (fun (k : Γ(N.restrict f, f ⁻¹ᵁ f.opensRange) ⟶
        Γ((Scheme.Modules.pullback f).obj N, ⊤)) =>
      (AddCommGrpCat.Hom.hom k)
        ((N.presheaf.map (homOfLE (f.image_preimage_le f.opensRange)).op).hom y))
    ((Scheme.Modules.Hom.mapPresheaf
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N)).naturality
      (homOfLE (le_of_eq (Scheme.Hom.preimage_opensRange f).symm)).op)
  have hcol := modules_res_res_hom N
    (f.opensFunctor.map
      (homOfLE (le_of_eq (Scheme.Hom.preimage_opensRange f).symm)))
    (homOfLE (f.image_preimage_le f.opensRange)) (eqToHom hImg) y
  exact (congrArg (fun w =>
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N) ⊤).hom w)
    hcol.symm).trans
    (hnat.trans (congrArg (fun w =>
      ((((Scheme.Modules.pullback f).obj N).presheaf.map
        (homOfLE (le_of_eq (Scheme.Hom.preimage_opensRange f).symm)).op).hom) w) hk))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The section transport expands the affine `fromSpec` equivalence and both adjunction units.
/-- Top sections after pullback along `hU.fromSpec` are canonically the sections
over the affine open `U`.  The inverse is exactly the adjunction-unit base map. -/
theorem pullbackFromSpecSectionsEquiv
    {Y : Scheme.{u}} (N : Y.Modules) {U : Y.Opens} (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y, U) Γ((Spec Γ(Y, U)), ⊤) :=
      (Scheme.ΓSpecIso _).inv.hom.toAlgebra
    letI : Module Γ(Y, U) Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso _).inv.hom
    Nonempty {f : Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) ≃ₗ[Γ(Y, U)]
        Γ(N, U) //
      ∀ (y : Γ(N, U)),
        f.symm y = pullback_app_isoTensor_baseMap hU.fromSpec N
          (le_of_eq hU.fromSpec_preimage_self.symm) y} := by
  letI : Algebra Γ(Y, U) Γ((Spec Γ(Y, U)), ⊤) :=
    (Scheme.ΓSpecIso _).inv.hom.toAlgebra
  letI : Module Γ(Y, U) Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso _).inv.hom
  let isoSheaf : (Scheme.Modules.pullback hU.fromSpec).obj N ≅ N.restrict hU.fromSpec :=
    ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app N).symm
  have hImg : (hU.fromSpec ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens) : Y.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hU.opensRange_fromSpec
  let toFun : Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) → Γ(N, U) := fun x =>
    (N.presheaf.map (eqToHom hImg.symm).op).hom
      ((Scheme.Modules.Hom.app isoSheaf.hom ⊤).hom x)
  let invFun : Γ(N, U) → Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) := fun y =>
    (Scheme.Modules.Hom.app isoSheaf.inv ⊤).hom
      ((N.presheaf.map (eqToHom hImg).op).hom y)
  have left_inv : Function.LeftInverse invFun toFun := by
    intro x
    simp only [invFun, toFun, ← AddCommGrpCat.comp_apply, ← Functor.map_comp, ← op_comp,
      eqToHom_trans, eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
      AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply, ← Scheme.Modules.Hom.comp_app, isoSheaf.hom_inv_id,
      Scheme.Modules.Hom.id_app]
  have right_inv : Function.RightInverse invFun toFun := by
    intro y
    simp only [invFun, toFun, ← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
      isoSheaf.inv_hom_id, Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id,
      AddMonoidHom.id_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
      eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  have map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom hImg.symm).op))
      ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) (x + y)) =
      _ + _
    rw [show ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) (x + y)) =
      (AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) x +
      (AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤)) y from
      AddMonoidHom.map_add _ _ _]
    exact AddMonoidHom.map_add _ _ _
  let addEq : Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤) ≃+ Γ(N, U) :=
    { toFun := toFun
      invFun := invFun
      left_inv := left_inv
      right_inv := right_inv
      map_add' := map_add' }
  refine ⟨⟨addEq.toLinearEquiv ?_, ?_⟩⟩
  · intro r x
    change (AddCommGrpCat.Hom.hom (N.presheaf.map (eqToHom hImg.symm).op))
      ((AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app isoSheaf.hom ⊤))
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso _).inv) r • x)) = _
    rw [Scheme.Modules.Hom.app_smul]
    set y : ↑Γ(N, hU.fromSpec ''ᵁ ⊤) :=
      (Scheme.Modules.Hom.app isoSheaf.hom ⊤).hom x with hy
    change (N.presheaf.map (eqToHom hImg.symm).op).hom
      (((hU.fromSpec.appIso ⊤).inv.hom ((Scheme.ΓSpecIso Γ(Y, U)).inv.hom r)) • y) =
      r • (N.presheaf.map (eqToHom hImg.symm).op).hom y
    rw [Scheme.Modules.map_smul]
    congr 1
    have e₀ : (⊤ : (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U :=
      le_of_eq hU.fromSpec_preimage_self.symm
    have h_appLE : hU.fromSpec.appLE U ⊤ e₀ = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
      simp [Scheme.Hom.appLE, hU.fromSpec_app_self, ← Functor.map_comp]
    have h_combine :
        (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (hU.fromSpec.appIso ⊤).inv =
          Y.presheaf.map (homOfLE (le_of_eq hImg)).op := by
      rw [← h_appLE]
      exact Scheme.Hom.appLE_appIso_inv hU.fromSpec e₀
    have h_key :
        (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ (hU.fromSpec.appIso ⊤).inv ≫
          Y.presheaf.map (eqToHom hImg.symm).op = 𝟙 _ := by
      rw [← Category.assoc, h_combine, ← Functor.map_comp, ← op_comp]
      simp
    exact congr($h_key r)
  · intro y
    have hk := congrArg
      (fun (k : N ⟶ (Scheme.Modules.pushforward hU.fromSpec).obj
          ((Scheme.Modules.pullback hU.fromSpec).obj N)) =>
        (Scheme.Modules.Hom.app k U).hom y)
      (Adjunction.unit_leftAdjointUniq_hom_app
        (Scheme.Modules.restrictAdjunction hU.fromSpec)
        (Scheme.Modules.pullbackPushforwardAdjunction hU.fromSpec) N)
    have hnat := congrArg
      (fun (k : Γ(N.restrict hU.fromSpec, hU.fromSpec ⁻¹ᵁ U) ⟶
          Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤)) =>
        (AddCommGrpCat.Hom.hom k)
          ((N.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op).hom y))
      ((Scheme.Modules.Hom.mapPresheaf
        ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app N)).naturality
        (homOfLE (le_of_eq hU.fromSpec_preimage_self.symm)).op)
    have hcol := modules_res_res_hom N
      (hU.fromSpec.opensFunctor.map (homOfLE (le_of_eq hU.fromSpec_preimage_self.symm)))
      (homOfLE (hU.fromSpec.image_preimage_le U)) (eqToHom hImg) y
    exact (congrArg (fun w =>
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app N) ⊤).hom w)
      hcol.symm).trans
      (hnat.trans (congrArg (fun w =>
        ((((Scheme.Modules.pullback hU.fromSpec).obj N).presheaf.map
          (homOfLE (le_of_eq hU.fromSpec_preimage_self.symm)).op).hom) w) hk))

end AlgebraicGeometry
