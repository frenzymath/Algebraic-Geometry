/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0
import AlgebraicJacobian.Picard.DivisorFamilyWindowBaseChange
import AlgebraicJacobian.Picard.Pic0RankOneCocycleBaseChange
import AlgebraicJacobian.Picard.Pic0RankOneFamilyCertificatesH0BaseChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
  [IsScalarTower k B B']
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

set_option maxHeartbeats 2000000 in
-- The two-cover H0 equivalences unfold through several dependent section rings.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- The two-cover carrier of datum H0 base change on a pure tensor. -/
private lemma h0Equiv_val_datumH0BaseChange_one_tmul
    (D : BasicOpenCocycleDatum C B pi) (hH1 : Subsingleton (datumPair D).H1)
    (y : Sheaf.HModule D.sheaf 0) :
    (((D.baseChange B').pairData.h0Equiv
      (relCover_isAffineOpen₀ C B' (fiberTwoCover pi))
      (relCover_isAffineOpen₁ C B' (fiberTwoCover pi))
      (relCover_sup C B' (fiberTwoCover pi)))
      (D.datumH0BaseChange B' hH1 ((1 : B') ⊗ₜ[B] y))).val =
    D.datumDomBaseChange B' ((1 : B') ⊗ₜ[B]
      ((D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C B (fiberTwoCover pi))
        (relCover_sup C B (fiberTwoCover pi)) y).val)) := by
  letI := D.projective_sectionsInf
  have hinner : ((datumH0BaseChangeEquiv D hH1 B' ((1 : B') ⊗ₜ[B] y) :
      LinearMap.ker ((datumPair D).diff.baseChange B')) :
        B' ⊗[B] ((D.sheaf.obj.obj
          (op (relCover C B (fiberTwoCover pi)).V₀)) ×
          (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover pi)).V₁)))) =
      (1 : B') ⊗ₜ[B] (((D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C B (fiberTwoCover pi))
        (relCover_sup C B (fiberTwoCover pi)) y).val)) := by
    unfold datumH0BaseChangeEquiv
    rw [Scheme.TwoCoverPairData.h0BaseChangeEquiv, LinearEquiv.trans_apply,
      LinearEquiv.baseChange_tmul]
    change (((LinearMap.ker (datumPair D).diff).subtype.baseChange B')
      ((1 : B') ⊗ₜ[B] (D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C B (fiberTwoCover pi))
        (relCover_sup C B (fiberTwoCover pi)) y)) : _) = _
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
  let e := (D.baseChange B').pairData.h0Equiv
    (relCover_isAffineOpen₀ C B' (fiberTwoCover pi))
    (relCover_isAffineOpen₁ C B' (fiberTwoCover pi))
    (relCover_sup C B' (fiberTwoCover pi))
  change (e (e.symm ((RigidEngine.kerCongr
      ((datumPair D).diff.baseChange B')
      (datumPair (D.baseChange B')).diff
      (D.datumDomBaseChange B') (D.termBaseChangeInf B')
      (fun x => D.datumDiffBaseChange B' x))
      (datumH0BaseChangeEquiv D hH1 B' ((1 : B') ⊗ₜ[B] y))))).val =
    D.datumDomBaseChange B' ((1 : B') ⊗ₜ[B]
      ((D.pairData.h0Equiv
        (relCover_isAffineOpen₀ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C B (fiberTwoCover pi))
        (relCover_sup C B (fiberTwoCover pi)) y).val))
  rw [e.apply_symm_apply]
  refine (RigidEngine.kerCongr_apply_coe _ _ _ _ _ _).trans ?_
  exact congrArg (D.datumDomBaseChange B') hinner

set_option maxHeartbeats 2000000 in
-- Comparing the two chart restrictions requires the same dependent H0 unfoldings.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- On a pure tensor, datum H0 base change is the comparison of the corresponding
global cocycle-glued section. -/
theorem linearEquiv₀_datumH0BaseChange_one_tmul
    (D : BasicOpenCocycleDatum C B pi) (hH1 : Subsingleton (datumPair D).H1)
    (y : Sheaf.HModule D.sheaf 0) :
    Sheaf.HModule.linearEquiv₀
        (Opens.grothendieckTopology ((relCurve C B' : Scheme.{u}) : TopCat))
        isTerminalTop (D.baseChange B').sheaf
        (D.datumH0BaseChange B' hH1 ((1 : B') ⊗ₜ[B] y)) =
      D.sectionsMapTop B'
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y) := by
  let e := Sheaf.HModule.linearEquiv₀
    (Opens.grothendieckTopology ((relCurve C B' : Scheme.{u}) : TopCat))
    isTerminalTop (D.baseChange B').sheaf
  apply e.symm.injective
  rw [e.symm_apply_apply]
  apply ((D.baseChange B').pairData.h0Equiv
    (relCover_isAffineOpen₀ C B' (fiberTwoCover pi))
    (relCover_isAffineOpen₁ C B' (fiberTwoCover pi))
    (relCover_sup C B' (fiberTwoCover pi))).injective
  apply Subtype.ext
  unfold e
  rw [h0Equiv_val_datumH0BaseChange_one_tmul B' D hH1 y]
  rw [Scheme.TwoCoverPairData.h0Equiv_val]
  rw [Scheme.TwoCoverPairData.h0Equiv_val]
  rw [LinearEquiv.apply_symm_apply, D.datumDomBaseChange_tmul B',
    D.termBaseChange₀_tmul B', D.termBaseChange₁_tmul B', one_smul]
  rw [one_smul]
  simp only
  apply Prod.ext
  · change D.sectionsMap B' (le_preimage_chart B' (fiberTwoCover pi).V₀)
        (gluedRes B D.pieces D.unit
          (le_top : (relCover C B (fiberTwoCover pi)).V₀ ≤ ⊤)
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y)) =
      gluedRes B' (D.baseChange B').pieces (D.baseChange B').unit
        (le_top : (relCover C B' (fiberTwoCover pi)).V₀ ≤ ⊤)
        (D.sectionsMapTop B'
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y))
    convert
      (D.gluedRes_sectionsMap B'
        (le_top : (relCover C B (fiberTwoCover pi)).V₀ ≤ ⊤)
        (by rw [Scheme.Hom.preimage_top])
        (le_preimage_chart B' (fiberTwoCover pi).V₀)
        (le_top : (relCover C B' (fiberTwoCover pi)).V₀ ≤ ⊤)
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y)).symm using 1
    rfl
  · change D.sectionsMap B' (le_preimage_chart B' (fiberTwoCover pi).V₁)
        (gluedRes B D.pieces D.unit
          (le_top : (relCover C B (fiberTwoCover pi)).V₁ ≤ ⊤)
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y)) =
      gluedRes B' (D.baseChange B').pieces (D.baseChange B').unit
        (le_top : (relCover C B' (fiberTwoCover pi)).V₁ ≤ ⊤)
        (D.sectionsMapTop B'
          (Sheaf.HModule.linearEquiv₀
            (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
            isTerminalTop D.sheaf y))
    convert
      (D.gluedRes_sectionsMap B'
        (le_top : (relCover C B (fiberTwoCover pi)).V₁ ≤ ⊤)
        (by rw [Scheme.Hom.preimage_top])
        (le_preimage_chart B' (fiberTwoCover pi).V₁)
        (le_top : (relCover C B' (fiberTwoCover pi)).V₁ ≤ ⊤)
        (Sheaf.HModule.linearEquiv₀
          (Opens.grothendieckTopology ((relCurve C B : Scheme.{u}) : TopCat))
          isTerminalTop D.sheaf y)).symm using 1
    rfl

end BasicOpenCocycleDatum

end AlgebraicGeometry
