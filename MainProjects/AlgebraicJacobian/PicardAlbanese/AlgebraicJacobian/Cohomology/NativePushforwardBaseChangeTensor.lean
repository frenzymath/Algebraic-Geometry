/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import AlgebraicJacobian.Cohomology.NativePushforwardBaseChangeMate

/-!
# Pullback of unit and tilde modules

This file supplies the unit and affine tensor dictionaries needed by native pushforward base
change.  For every map of schemes, inverse image on opens is final: the top open gives a terminal
object in each structured-arrow category.  Consequently, pullback carries the unit module
canonically to the unit module.

For a ring map `A \to B`, pullback along `Spec B \to Spec A` takes the tilde sheaf of an
`A`-module to the tilde sheaf of its scalar extension to `B`.

The proof uses uniqueness of left adjoints.  The only comparison required on the right-adjoint
side is that global sections after pushforward along `Spec.map phi` are restriction of scalars
along `phi`; on underlying sections this is restriction along `top <= (Spec.map phi) ^-1(top)`,
which is the identity.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Scheme.Modules

/-! ## Pullback of the unit module -/

private noncomputable def opensMapStructuredArrowTerminal {X Y : TopCat.{u}}
    (f : X ⟶ Y) (U : Opens X) :
    IsTerminal (StructuredArrow.mk (Opens.leMapTop f U)) :=
  IsTerminal.ofUniqueHom
    (fun s => StructuredArrow.homMk (Opens.leTop s.right) (Subsingleton.elim _ _))
    (fun _ _ => by
      apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _)

@[reducible]
private noncomputable def opensMapFinal {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (Opens.map f).Final where
  out U := isConnected_of_isTerminal _ (opensMapStructuredArrowTerminal f U)

/-- Pullback along any morphism of schemes carries the unit module to the unit module by an
isomorphism.  No openness, flatness, or finiteness hypothesis is needed. -/
theorem Scheme.Modules.isIso_pullbackObjUnitToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
  letI : (Opens.map f.base).Final := opensMapFinal f.base
  infer_instance

/-- The canonical isomorphism from the pullback of the unit module to the unit module. -/
noncomputable def Scheme.Modules.pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  @asIso _ _ _ _ _ (Scheme.Modules.isIso_pullbackObjUnitToUnit f)

/-! ## Pullback of an affine tilde module -/

set_option backward.isDefEq.respectTransparency false in
private lemma modulesRestrictionPreimageTopEqId {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : Y.Modules) (e : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) :
    N.presheaf.map (homOfLE e).op = 𝟙 _ :=
  (congrArg N.presheaf.map
    (show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : Y.Opens)) from rfl)).trans
    (N.presheaf.map_id _)

set_option backward.isDefEq.respectTransparency false in
private lemma ringRestrictionPreimageTopEqId {X Y : Scheme.{u}} (g : Y ⟶ X)
    (e : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤) :
    Y.presheaf.map (homOfLE e).op = 𝟙 _ :=
  (congrArg Y.presheaf.map
    (show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : Y.Opens)) from rfl)).trans
    (Y.presheaf.map_id _)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pullbackTildeGammaBridgeHom {A B : CommRingCat.{u}}
    (phi : A ⟶ B) (N : (Spec B).Modules) :
    (Scheme.Modules.pushforward (Spec.map phi) ⋙ moduleSpecΓFunctor (R := A)).obj N ⟶
      (moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars phi.hom).obj N :=
  ConcreteCategory.ofHom
    { toFun := fun x =>
        (N.presheaf.map (homOfLE (le_top :
          (⊤ : (Spec B).Opens) ≤ Spec.map phi ⁻¹ᵁ ⊤)).op).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x =>
        (Scheme.Modules.map_smul N (homOfLE (le_top :
          (⊤ : (Spec B).Opens) ≤ Spec.map phi ⁻¹ᵁ ⊤))
          (((Spec.map phi).app ⊤).hom ((Scheme.ΓSpecIso A).inv.hom a)) x).trans
        (congrArg (fun r => r • (N.presheaf.map (homOfLE (le_top :
            (⊤ : (Spec B).Opens) ≤ Spec.map phi ⁻¹ᵁ ⊤)).op).hom x)
          ((congrArg (fun (k : Γ(Spec B, Spec.map phi ⁻¹ᵁ ⊤) ⟶ Γ(Spec B, ⊤)) =>
              k.hom (((Spec.map phi).app ⊤).hom ((Scheme.ΓSpecIso A).inv.hom a)))
            (ringRestrictionPreimageTopEqId (Spec.map phi) le_top)).trans
           ((congrArg (fun (psi : A ⟶ Γ(Spec B, ⊤)) => psi.hom a)
              (Scheme.ΓSpecIso_inv_naturality phi)).symm))) }

set_option backward.isDefEq.respectTransparency false in
private lemma pullbackTildeGammaBridgeHom_isIso {A B : CommRingCat.{u}}
    (phi : A ⟶ B) (N : (Spec B).Modules) :
    IsIso (pullbackTildeGammaBridgeHom phi N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun x => (N.presheaf.map (homOfLE (le_top :
    (⊤ : (Spec B).Opens) ≤ Spec.map phi ⁻¹ᵁ ⊤)).op).hom x)
  rw [modulesRestrictionPreimageTopEqId (Spec.map phi) N le_top]
  exact Function.bijective_id

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pullbackTildeGammaBridge {A B : CommRingCat.{u}}
    (phi : A ⟶ B) :
    Scheme.Modules.pushforward (Spec.map phi) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars phi.hom := by
  refine NatIso.ofComponents
    (fun N => @asIso _ _ _ _ _ (pullbackTildeGammaBridgeHom_isIso phi N))
    (fun {N N'} h => ?_)
  ext x
  exact (congrArg (fun (k : Γ(N, Spec.map phi ⁻¹ᵁ ⊤) ⟶ Γ(N', ⊤)) => k.hom x)
    ((Scheme.Modules.Hom.mapPresheaf h).naturality (homOfLE (le_top :
      (⊤ : (Spec B).Opens) ≤ Spec.map phi ⁻¹ᵁ ⊤)).op)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pullback along `Spec.map phi` carries a tilde module to the tilde of scalar extension.

This is the affine `pullback of tilde = tilde of tensor product` comparison (Stacks 01HQ).
It is canonical: it is the uniqueness isomorphism between two left adjoints of global sections
with restriction of scalars. -/
noncomputable def Scheme.Modules.pullbackTildeIso {A B : CommRingCat.{u}}
    (phi : A ⟶ B) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map phi) ≅
      ModuleCat.extendScalars phi.hom ⋙ tilde.functor B :=
  Adjunction.leftAdjointUniq
    (((tilde.adjunction (R := A)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi))).ofNatIsoRight
      (pullbackTildeGammaBridge phi))
    ((ModuleCat.extendRestrictScalarsAdj phi.hom).comp (tilde.adjunction (R := B)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Unfolding both composed adjunction units traverses the pullback/tilde comparison.
/-- On top sections, `pullbackTildeIso` sends the adjunction-unit image of a tilde section
to the corresponding pure tensor. -/
theorem Scheme.Modules.pullbackTildeIso_baseMap {A B : CommRingCat.{u}}
    (phi : A ⟶ B) (M : ModuleCat.{u} A) (m : M) :
    letI : Algebra A B := phi.hom.toAlgebra
    letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
      ((Spec.map phi).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module Γ(Spec A, ⊤)
        Γ((Scheme.Modules.pullback (Spec.map phi)).obj (tilde M), ⊤) :=
      Module.compHom _ ((Spec.map phi).appLE ⊤ ⊤ le_top).hom
    (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackTildeIso phi).hom.app M) ⊤).hom
        (pullback_app_isoTensor_baseMap (Spec.map phi) (tilde M) le_top
          ((tilde.toOpen M ⊤).hom m)) =
      (tilde.toOpen (ModuleCat.of B (TensorProduct A B M)) ⊤).hom
        (1 ⊗ₜ[A] m) := by
  letI : Algebra A B := phi.hom.toAlgebra
  letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
    ((Spec.map phi).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module Γ(Spec A, ⊤)
      Γ((Scheme.Modules.pullback (Spec.map phi)).obj (tilde M), ⊤) :=
    Module.compHom _ ((Spec.map phi).appLE ⊤ ⊤ le_top).hom
  let adj1 : (tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map phi)) ⊣
      (moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars phi.hom) :=
    ((tilde.adjunction (R := A)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map phi))).ofNatIsoRight
      (pullbackTildeGammaBridge phi)
  let adj2 : (ModuleCat.extendScalars phi.hom ⋙ tilde.functor B) ⊣
      (moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars phi.hom) :=
    (ModuleCat.extendRestrictScalarsAdj phi.hom).comp (tilde.adjunction (R := B))
  have key := Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 M
  exact congrArg (fun (f : M ⟶ (moduleSpecΓFunctor (R := B) ⋙
    ModuleCat.restrictScalars phi.hom).obj ((ModuleCat.extendScalars phi.hom ⋙
      tilde.functor B).obj M)) => f.hom m) key

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- On affine spectra, a module identified with the tilde of its global sections pulls back
to scalar extension on top sections.  The equivalence is normalized by the canonical pullback
base map. -/
theorem Scheme.Modules.pullback_app_isoTensor_baseMap_sectionLinearEquiv_of_fromTildeΓ
    {A B : CommRingCat.{u}} (phi : A ⟶ B) (N : (Spec A).Modules) [IsIso N.fromTildeΓ] :
    letI : Algebra A B := phi.hom.toAlgebra
    letI : Algebra B Γ(Spec B, ⊤) := (Scheme.ΓSpecIso B).inv.hom.toAlgebra
    letI : Module B Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso B).inv.hom
    letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
      ((Spec.map phi).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module Γ(Spec A, ⊤)
        Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) :=
      Module.compHom _ ((Spec.map phi).appLE ⊤ ⊤ le_top).hom
    Nonempty {e : TensorProduct A B
        ((moduleSpecΓFunctor (R := A)).obj N) ≃ₗ[B]
          Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) //
      ∀ x : Γ(N, ⊤), e (1 ⊗ₜ[A] x) =
        pullback_app_isoTensor_baseMap (Spec.map phi) N le_top x} := by
  letI : Algebra A B := phi.hom.toAlgebra
  letI : Algebra B Γ(Spec B, ⊤) := (Scheme.ΓSpecIso B).inv.hom.toAlgebra
  letI : Module B Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso B).inv.hom
  letI : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
    ((Spec.map phi).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module Γ(Spec A, ⊤)
      Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) :=
    Module.compHom _ ((Spec.map phi).appLE ⊤ ⊤ le_top).hom
  let M : ModuleCat A := (moduleSpecΓFunctor (R := A)).obj N
  let TR : ModuleCat B := ModuleCat.of B (TensorProduct A B M)
  let sheafIso : (Scheme.Modules.pullback (Spec.map phi)).obj N ≅ tilde TR :=
    (Scheme.Modules.pullback (Spec.map phi)).mapIso (asIso N.fromTildeΓ).symm ≪≫
      (Scheme.Modules.pullbackTildeIso phi).app M
  letI : Module B Γ(tilde TR, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso B).inv.hom
  let topAdd : Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) ≃+
      Γ(tilde TR, ⊤) :=
    { toFun := fun x => (Scheme.Modules.Hom.app sheafIso.hom ⊤).hom x
      invFun := fun y => (Scheme.Modules.Hom.app sheafIso.inv ⊤).hom y
      left_inv := fun x => by
        simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
          sheafIso.hom_inv_id, Scheme.Modules.Hom.id_app,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
      right_inv := fun y => by
        simp only [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
          sheafIso.inv_hom_id, Scheme.Modules.Hom.id_app,
          AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
      map_add' := fun x y => (Scheme.Modules.Hom.app sheafIso.hom ⊤).hom.map_add x y }
  let topLin : Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) ≃ₗ[B]
      Γ(tilde TR, ⊤) := by
    refine topAdd.toLinearEquiv ?_
    intro r x
    change (Scheme.Modules.Hom.app sheafIso.hom ⊤).hom
        ((Scheme.ΓSpecIso B).inv.hom r • x) =
      (Scheme.ΓSpecIso B).inv.hom r •
        (Scheme.Modules.Hom.app sheafIso.hom ⊤).hom x
    exact Scheme.Modules.Hom.app_smul sheafIso.hom _ x
  let e : TensorProduct A B M ≃ₗ[B]
      Γ((Scheme.Modules.pullback (Spec.map phi)).obj N, ⊤) :=
    (tilde.isoTop TR).toLinearEquiv.trans topLin.symm
  refine ⟨⟨e, ?_⟩⟩
  intro x
  have hcancel : ∀ w : Γ((Scheme.Modules.pullback (Spec.map phi)).obj (tilde M), ⊤),
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackTildeIso phi).inv.app M) ⊤).hom
          ((Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackTildeIso phi).hom.app M) ⊤).hom w) = w :=
    fun w => congrArg
      (fun (k : (Scheme.Modules.pullback (Spec.map phi)).obj (tilde M) ⟶
          (Scheme.Modules.pullback (Spec.map phi)).obj (tilde M)) =>
        (Scheme.Modules.Hom.app k ⊤).hom w)
      ((Scheme.Modules.pullbackTildeIso phi).app M).hom_inv_id
  have h1 := (congrArg
    (fun w => (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackTildeIso phi).inv.app M) ⊤).hom w)
    (Scheme.Modules.pullbackTildeIso_baseMap phi M x).symm).trans (hcancel _)
  have h2 := pullback_app_isoTensor_baseMap_naturality (Spec.map phi) N.fromTildeΓ
    (U := (⊤ : (Spec B).Opens)) (V := (⊤ : (Spec A).Opens)) le_top
    ((tilde.toOpen M ⊤).hom x)
  have h3 : (Scheme.Modules.Hom.app N.fromTildeΓ ⊤).hom
      ((tilde.toOpen M ⊤).hom x) = x := by
    have h := congrArg (fun k => k.hom x)
      (Scheme.Modules.toOpen_fromTildeΓ_app N (⊤ : (Spec A).Opens))
    have happ : ∀ z : Γ(tilde M, ⊤),
        (Scheme.Modules.Hom.app N.fromTildeΓ ⊤).hom z =
          ((modulesSpecToSheaf.map N.fromTildeΓ).hom.app (.op ⊤)).hom z :=
      fun _ => rfl
    rw [happ]
    convert h using 1
    · rfl
    · rfl
    · simp
  change (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback (Spec.map phi)).map N.fromTildeΓ) ⊤).hom
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackTildeIso phi).inv.app M) ⊤).hom
        ((tilde.toOpen TR ⊤).hom (1 ⊗ₜ[A] x))) =
    pullback_app_isoTensor_baseMap (Spec.map phi) N le_top x
  exact (congrArg (fun w => (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback (Spec.map phi)).map N.fromTildeΓ) ⊤).hom w) h1).trans
    (h2.trans (congrArg
      (fun w => pullback_app_isoTensor_baseMap (Spec.map phi) N le_top w) h3))

end AlgebraicGeometry
