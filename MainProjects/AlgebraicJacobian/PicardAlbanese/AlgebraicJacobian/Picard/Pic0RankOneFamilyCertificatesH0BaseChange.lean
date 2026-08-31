/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.RankOneFamilyCertificates
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0
import AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange

/-!
# Tower coherence for rank-one family certificates

The certificate package uses the canonical datum H0 base-change equivalence.  This file proves
that its underlying comparison of glued sections is transitive along arbitrary towers of affine
coefficient rings.  The dependent transport is the equality of the actual base-changed cocycle
datum, not an equality of proof-valued certificate records.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace RankOneFamilyCertificates

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
  [IsScalarTower k R R']
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

private lemma appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {U : Y.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h
  rfl

private lemma cast_appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    {U : Y.Opens} {W W' : X.Opens} (hW : W = W')
    (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)) :
    cast (congrArg (fun V : X.Opens => ↑(Γ(X, V))) hW) ((f.appLE U W e).hom s) =
      (g.appLE U W' e').hom s := by
  subst hf
  subst hW
  rfl

private lemma cast_gluedSubmodule_eq_of_val_heq
    {S : Type u} [CommRing S] [Algebra k S]
    {D₁ D₂ : BasicOpenCocycleDatum C S pi} {W : (relCurve C S).Opens}
    (hD : D₁ = D₂)
    (x : ↑(gluedSubmodule S D₁.pieces D₁.unit W))
    (y : ↑(gluedSubmodule S D₂.pieces D₂.unit W))
    (hval : HEq x.val y.val) :
    cast (congrArg (fun E : BasicOpenCocycleDatum C S pi =>
      ↑(gluedSubmodule S E.pieces E.unit W)) hD) x = y := by
  subst D₂
  exact Subtype.ext (eq_of_heq hval)

private lemma cast_congrArg_self {A : Sort v} (P : A → Sort w)
    {a : A} (h : a = a) (x : P a) :
    cast (congrArg P h) x = x := by
  cases h
  rfl

private lemma linearEquivZero_mapEquiv_eq_cast
    {S : Type u} [CommRing S] [Algebra k S]
    {D₁ D₂ : BasicOpenCocycleDatum C S pi} (hD : D₁ = D₂)
    (x : Sheaf.HModule D₁.sheaf 0) :
    Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
        isTerminalTop D₂.sheaf
        (Sheaf.HModule.mapEquiv
          (eqToIso (congrArg
            (fun E : BasicOpenCocycleDatum C S pi => E.sheaf) hD)) 0 x) =
      cast (congrArg (fun E : BasicOpenCocycleDatum C S pi =>
        ↑(gluedSubmodule S E.pieces E.unit ⊤)) hD)
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C S : Scheme.{u}) : TopCat))
          isTerminalTop D₁.sheaf x) := by
  cases hD
  rw [show congrArg (fun E : BasicOpenCocycleDatum C S pi => E.sheaf)
      (rfl : D₁ = D₁) = rfl from rfl,
    eqToIso_refl, Sheaf.HModule.mapEquiv_apply, Iso.refl_hom,
    Sheaf.HModule.map_id_apply]
  exact (cast_congrArg_self
    (fun E : BasicOpenCocycleDatum C S pi =>
      ↑(gluedSubmodule S E.pieces E.unit ⊤)) (rfl : D₁ = D₁) _).symm

/-- Comparing glued sections in two stages agrees with direct comparison after transport by the
canonical equality of the two base-changed cocycle data. -/
theorem sectionsMap_tower (D : BasicOpenCocycleDatum C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    {W : (relCurve C R).Opens} {W' : (relCurve C R').Opens}
    {W'' : (relCurve C R'').Opens}
    (hW' : W' ≤ relCurveMap C R R' ⁻¹ᵁ W)
    (hW'' : W'' ≤ relCurveMap C R' R'' ⁻¹ᵁ W')
    (s : ↑(gluedSubmodule R D.pieces D.unit W)) :
    let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
      D.baseChange_baseChange C R R' R''
    let hcomp : W'' ≤ relCurveMap C R R'' ⁻¹ᵁ W := by
      rw [← relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R''),
        Scheme.Hom.comp_preimage]
      exact hW''.trans (Scheme.Hom.preimage_mono _ hW')
    cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
      ↑(gluedSubmodule R'' E.pieces E.unit W'')) hD)
        ((D.baseChange R').sectionsMap R'' hW'' (D.sectionsMap R' hW' s)) =
      D.sectionsMap R'' hcomp s := by
  let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
    D.baseChange_baseChange C R R' R''
  let hcomp : W'' ≤ relCurveMap C R R'' ⁻¹ᵁ W := by
    rw [← relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R''),
      Scheme.Hom.comp_preimage]
    exact hW''.trans (Scheme.Hom.preimage_mono _ hW')
  change cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
      ↑(gluedSubmodule R'' E.pieces E.unit W'')) hD)
        ((D.baseChange R').sectionsMap R'' hW'' (D.sectionsMap R' hW' s)) =
      D.sectionsMap R'' hcomp s
  apply cast_gluedSubmodule_eq_of_val_heq C hD
  apply Function.hfunext rfl
  intro j j' hj
  cases hj
  let hopen : W'' ⊓ ((D.baseChange R').baseChange R'').pieces j =
      W'' ⊓ (D.baseChange R'').pieces j :=
    congrArg (fun V : (relCurve C R'').Opens => W'' ⊓ V)
      (D.toBasicOpenCoverData.pieces_tower C R R' R'' j)
  apply (Equiv.cast_eq_iff_heq
    (congrArg (fun V : (relCurve C R'').Opens => ↑(Γ(relCurve C R'', V))) hopen)).mp
  simp only [BasicOpenCocycleDatum.sectionsMap_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact cast_appLE_congr
    (relCurveMap_comp (C := C) (R := R) (R' := R') (R'' := R'')) hopen _ _ (s.val j)

/-- Global glued-section comparison is transitive along an arbitrary coefficient tower. -/
theorem sectionsMapTop_tower (D : BasicOpenCocycleDatum C R pi)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R'']
    (s : ↑(gluedSubmodule R D.pieces D.unit ⊤)) :
    let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
      D.baseChange_baseChange C R R' R''
    cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
      ↑(gluedSubmodule R'' E.pieces E.unit ⊤)) hD)
        ((D.baseChange R').sectionsMapTop R'' (D.sectionsMapTop R' s)) =
      D.sectionsMapTop R'' s := by
  let hW' : (⊤ : (relCurve C R').Opens) ≤
      relCurveMap C R R' ⁻¹ᵁ (⊤ : (relCurve C R).Opens) := by
    rw [Scheme.Hom.preimage_top]
  let hW'' : (⊤ : (relCurve C R'').Opens) ≤
      relCurveMap C R' R'' ⁻¹ᵁ (⊤ : (relCurve C R').Opens) := by
    rw [Scheme.Hom.preimage_top]
  simpa only [BasicOpenCocycleDatum.sectionsMapTop] using
    sectionsMap_tower C R R' D R'' hW' hW'' s

section PureTensor

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
private lemma h0Equiv_val_h0BaseChange_one_tmul
    (D : BasicOpenCocycleDatum C R pi) (hH1 : Subsingleton (datumPair D).H1)
    (y : Sheaf.HModule D.sheaf 0) :
    (((D.baseChange R').pairData.h0Equiv
      (relCover_isAffineOpen₀ C R' (fiberTwoCover pi))
      (relCover_isAffineOpen₁ C R' (fiberTwoCover pi))
      (relCover_sup C R' (fiberTwoCover pi)))
      (D.datumH0BaseChange R' hH1 ((1 : R') ⊗ₜ[R] y))).val =
    D.datumDomBaseChange R' ((1 : R') ⊗ₜ[R]
      ((D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi))
        (relCover_sup C R (fiberTwoCover pi)) y).val)) := by
  letI := D.projective_sectionsInf
  have hinner : ((datumH0BaseChangeEquiv D hH1 R' ((1 : R') ⊗ₜ[R] y) :
      LinearMap.ker ((datumPair D).diff.baseChange R')) :
        R' ⊗[R] ((D.sheaf.obj.obj
          (op (relCover C R (fiberTwoCover pi)).V₀)) ×
          (D.sheaf.obj.obj (op (relCover C R (fiberTwoCover pi)).V₁)))) =
      (1 : R') ⊗ₜ[R] (((D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi))
        (relCover_sup C R (fiberTwoCover pi)) y).val)) := by
    unfold datumH0BaseChangeEquiv
    rw [Scheme.TwoCoverPairData.h0BaseChangeEquiv, LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul]
    change (((LinearMap.ker (datumPair D).diff).subtype.baseChange R')
      ((1 : R') ⊗ₜ[R] (D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi))
        (relCover_sup C R (fiberTwoCover pi)) y)) : _) = _
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
  let e := (D.baseChange R').pairData.h0Equiv
    (relCover_isAffineOpen₀ C R' (fiberTwoCover pi))
    (relCover_isAffineOpen₁ C R' (fiberTwoCover pi))
    (relCover_sup C R' (fiberTwoCover pi))
  change (e (e.symm ((RigidEngine.kerCongr
      ((datumPair D).diff.baseChange R')
      (datumPair (D.baseChange R')).diff
      (D.datumDomBaseChange R') (D.termBaseChangeInf R')
      (fun x => D.datumDiffBaseChange R' x))
      (datumH0BaseChangeEquiv D hH1 R' ((1 : R') ⊗ₜ[R] y))))).val =
    D.datumDomBaseChange R' ((1 : R') ⊗ₜ[R]
      ((D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C R (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C R (fiberTwoCover pi))
        (relCover_sup C R (fiberTwoCover pi)) y).val))
  rw [e.apply_symm_apply]
  refine (RigidEngine.kerCongr_apply_coe _ _ _ _ _ _).trans ?_
  exact congrArg (D.datumDomBaseChange R') hinner

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- On a pure tensor, the certificate's H0 comparison is comparison of the corresponding global
glued section. -/
theorem linearEquivZero_h0BaseChange_one_tmul
    (D : BasicOpenCocycleDatum C R pi) (hH1 : Subsingleton (datumPair D).H1)
    (y : Sheaf.HModule D.sheaf 0) :
    Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C R' : Scheme.{u}) : TopCat))
        isTerminalTop (D.baseChange R').sheaf
        (D.datumH0BaseChange R' hH1 ((1 : R') ⊗ₜ[R] y)) =
      D.sectionsMapTop R'
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y) := by
  let e := Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C R' : Scheme.{u}) : TopCat))
    isTerminalTop (D.baseChange R').sheaf
  apply e.symm.injective
  rw [e.symm_apply_apply]
  apply ((D.baseChange R').pairData.h0Equiv
    (relCover_isAffineOpen₀ C R' (fiberTwoCover pi))
    (relCover_isAffineOpen₁ C R' (fiberTwoCover pi))
    (relCover_sup C R' (fiberTwoCover pi))).injective
  apply Subtype.ext
  unfold e
  rw [h0Equiv_val_h0BaseChange_one_tmul C R R' D hH1 y]
  rw [Scheme.TwoCoverPairData.h0Equiv_val]
  rw [Scheme.TwoCoverPairData.h0Equiv_val]
  rw [LinearEquiv.apply_symm_apply, D.datumDomBaseChange_tmul R',
    D.termBaseChange₀_tmul R', D.termBaseChange₁_tmul R', one_smul]
  rw [one_smul]
  simp only
  apply Prod.ext
  · change D.sectionsMap R'
      (BasicOpenCocycleDatum.le_preimage_chart R' (fiberTwoCover pi).V₀)
        (gluedRes R D.pieces D.unit
          (le_top : (relCover C R (fiberTwoCover pi)).V₀ ≤ ⊤)
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y)) =
      gluedRes R' (D.baseChange R').pieces (D.baseChange R').unit
        (le_top : (relCover C R' (fiberTwoCover pi)).V₀ ≤ ⊤)
        (D.sectionsMapTop R'
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y))
    convert
      (D.gluedRes_sectionsMap R'
        (le_top : (relCover C R (fiberTwoCover pi)).V₀ ≤ ⊤)
        (by rw [Scheme.Hom.preimage_top])
        (BasicOpenCocycleDatum.le_preimage_chart R' (fiberTwoCover pi).V₀)
        (le_top : (relCover C R' (fiberTwoCover pi)).V₀ ≤ ⊤)
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y)).symm using 1
    rfl
  · change D.sectionsMap R'
      (BasicOpenCocycleDatum.le_preimage_chart R' (fiberTwoCover pi).V₁)
        (gluedRes R D.pieces D.unit
          (le_top : (relCover C R (fiberTwoCover pi)).V₁ ≤ ⊤)
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y)) =
      gluedRes R' (D.baseChange R').pieces (D.baseChange R').unit
        (le_top : (relCover C R' (fiberTwoCover pi)).V₁ ≤ ⊤)
        (D.sectionsMapTop R'
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y))
    convert
      (D.gluedRes_sectionsMap R'
        (le_top : (relCover C R (fiberTwoCover pi)).V₁ ≤ ⊤)
        (by rw [Scheme.Hom.preimage_top])
        (BasicOpenCocycleDatum.le_preimage_chart R' (fiberTwoCover pi).V₁)
        (le_top : (relCover C R' (fiberTwoCover pi)).V₁ ≤ ⊤)
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y)).symm using 1
    rfl

end PureTensor

/-! ## Coherence of the H0 equivalence -/

/-- The canonical two-step H0 comparison, including reassociation of tensor products and
transport along the canonical equality of the two base-changed cocycle data. -/
noncomputable def h0BaseChangeTwoStep
    (D : BasicOpenCocycleDatum C R pi) (P : RankOneFamilyCertificates D)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R''] :
    R'' ⊗[R] Sheaf.HModule D.sheaf 0 ≃ₗ[R'']
      Sheaf.HModule (D.baseChange R'').sheaf 0 :=
  let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
    D.baseChange_baseChange C R R' R''
  ((((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R'' R''
      (Sheaf.HModule D.sheaf 0)).symm.trans
      (LinearEquiv.baseChange R' R'' _ _ (P.h0BaseChange R'))).trans
      ((P.scalarExtension R').h0BaseChange R'')).trans
      (Sheaf.HModule.mapEquiv
        (eqToIso (congrArg
          (fun E : BasicOpenCocycleDatum C R'' pi => E.sheaf) hD)) 0))

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- Direct and iterated canonical H0 base change agree along every affine coefficient tower. -/
theorem h0BaseChange_tower
    (D : BasicOpenCocycleDatum C R pi) (P : RankOneFamilyCertificates D)
    (R'' : Type u) [CommRing R''] [Algebra k R''] [Algebra R R''] [Algebra R' R'']
    [IsScalarTower k R R''] [IsScalarTower k R' R''] [IsScalarTower R R' R''] :
    P.h0BaseChange R'' = h0BaseChangeTwoStep C R R' D P R'' := by
  letI : Module R (Sheaf.HModule (D.baseChange R'').sheaf 0) :=
    Module.compHom _ (algebraMap R R'')
  letI : IsScalarTower R R'' (Sheaf.HModule (D.baseChange R'').sheaf 0) :=
    IsScalarTower.of_compHom R R'' _
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro r'' y
  have hone : P.h0BaseChange R'' ((1 : R'') ⊗ₜ[R] y) =
      h0BaseChangeTwoStep C R R' D P R'' ((1 : R'') ⊗ₜ[R] y) := by
    let hD : (D.baseChange R').baseChange R'' = D.baseChange R'' :=
      D.baseChange_baseChange C R R' R''
    let hH1 := (subsingleton_datumPair_h1_iff D).mpr P.h1_vanishing
    let hH1' := (subsingleton_datumPair_h1_iff (D.baseChange R')).mpr
      (P.scalarExtension R').h1_vanishing
    simp only [h0BaseChangeTwoStep, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    symm
    change Sheaf.HModule.mapEquiv
          (eqToIso (congrArg
            (fun E : BasicOpenCocycleDatum C R'' pi => E.sheaf) hD)) 0
          ((P.scalarExtension R').h0BaseChange R''
            (LinearEquiv.baseChange R' R'' _ _ (P.h0BaseChange R')
              ((1 : R'') ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] y)))) =
        P.h0BaseChange R'' ((1 : R'') ⊗ₜ[R] y)
    apply (Sheaf.HModule.linearEquiv₀
      (Opens.grothendieckTopology ((relCurve C R'' : Scheme.{u}) : TopCat))
      isTerminalTop (D.baseChange R'').sheaf).injective
    rw [linearEquivZero_mapEquiv_eq_cast C hD]
    rw [LinearEquiv.baseChange_tmul]
    change cast (congrArg (fun E : BasicOpenCocycleDatum C R'' pi =>
        ↑(gluedSubmodule R'' E.pieces E.unit ⊤)) hD)
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C R'' : Scheme.{u}) : TopCat))
          isTerminalTop ((D.baseChange R').baseChange R'').sheaf
          ((D.baseChange R').datumH0BaseChange R'' hH1'
            ((1 : R'') ⊗ₜ[R'] (D.datumH0BaseChange R' hH1
              ((1 : R') ⊗ₜ[R] y))))) =
      Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C R'' : Scheme.{u}) : TopCat))
        isTerminalTop (D.baseChange R'').sheaf
        (D.datumH0BaseChange R'' hH1 ((1 : R'') ⊗ₜ[R] y))
    rw [linearEquivZero_h0BaseChange_one_tmul C R' R'' (D.baseChange R') hH1']
    rw [linearEquivZero_h0BaseChange_one_tmul C R R' D hH1]
    rw [linearEquivZero_h0BaseChange_one_tmul C R R'' D hH1]
    exact sectionsMapTop_tower C R R' D R''
      (Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C R : Scheme.{u}) : TopCat))
        isTerminalTop D.sheaf y)
  have hr : (r'' ⊗ₜ[R] y : R'' ⊗[R] Sheaf.HModule D.sheaf 0) =
      r'' • ((1 : R'') ⊗ₜ[R] y) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hr]
  simp only [LinearMap.coe_restrictScalars, map_smul]
  exact congrArg (r'' • ·) hone

end RankOneFamilyCertificates

end AlgebraicGeometry
