/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyIntrinsicIdealSheaf
import AlgebraicJacobian.Picard.DivisorFamilyAffFace
import AlgebraicJacobian.Picard.IdealSheafAffineComap

/-!
# Base change of intrinsic divisor-family ideal sheaves

This file identifies the intrinsic ideal sheaf attached to a widened affine divisor family
with the pullback of that ideal sheaf under scalar extension.  The representative statement
uses an explicit regularity witness; the quotient and explicit-algebra-map statements then
follow from the established `DivFamZarAff` base-change API.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
  [IsScalarTower k R R']

namespace Scheme.LocalEquations

/-- Pulling a local-equation divisor along a relative-curve scalar extension pulls back its
intrinsic Cartier ideal sheaf.  Regularity is supplied in exactly the form required by
`Scheme.LocalEquations.pullback`; no certificate or projectivity hypothesis is used. -/
theorem cartierIdealData_pullback_relCurveMap (d : (relCurve C R).LocalEquations)
    (hreg : ∀ (y z : relCurve C R')
      (hz : z ∈ (d.cover.pullback (relCurveMap C R R')).opens y),
      ((relCurve C R').presheaf.germ
        ((d.cover.pullback (relCurveMap C R R')).opens y) z hz).hom
          (pullbackEqn (relCurveMap C R R') d y)
        ∈ nonZeroDivisors ((relCurve C R').presheaf.stalk z)) :
    (d.pullback (relCurveMap C R R') hreg).cartierIdealData =
      d.cartierIdealData.comap (relCurveMap C R R') := by
  letI : IsAffineHom (relCurveMap C R R') := Over.isAffineHom_cg C
  obtain ⟨D, ⟨A⟩⟩ := exists_affAdaptation_of_isProper C R d
  rw [(A.pullbackOfHreg R' hreg).cartierIdealData_eq_cartierIdeal,
    A.cartierIdealData_eq_cartierIdeal]
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : D.index =>
      ⟨(D.baseChange R').pieces j, (D.baseChange R').isAffineOpen j⟩)
    (D.baseChange R').cover
  intro j
  rw [(A.pullbackOfHreg R' hreg).cartierIdeal_ideal_eq_span_eqn j]
  change Ideal.span {(A.pullbackOfHreg R' hreg).eqn j} =
    (A.cartierIdeal.comap (relCurveMap C R R')).ideal
      ⟨relCurveMap C R R' ⁻¹ᵁ D.pieces j,
        (D.isAffineOpen j).preimage (relCurveMap C R R')⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isAffineHom A.cartierIdeal
      (relCurveMap C R R') ⟨D.pieces j, D.isAffineOpen j⟩,
    A.cartierIdeal_ideal_eq_span_eqn j, Ideal.map_span, Set.image_singleton,
    A.pullbackOfHreg_eqn]
  change Ideal.span {((relCurveMap C R R').appLE (D.pieces j)
      (relCurveMap C R R' ⁻¹ᵁ D.pieces j) le_rfl).hom (A.eqn j)} =
    Ideal.span {((relCurveMap C R R').app ⟨D.pieces j, D.isAffineOpen j⟩).hom
      (A.eqn j)}
  rw [Scheme.Hom.appLE_eq_app]

end Scheme.LocalEquations

namespace DivFamZarAff

variable {n : ℕ}

/-- The intrinsic Cartier ideal sheaf of a widened divisor-family class commutes with scalar
extension along an algebra tower. -/
theorem cartierIdealData_mapAlg (F : DivFamZarAff C R n) :
    (mapAlg R' n F).cartierIdealData =
      F.cartierIdealData.comap (relCurveMap C R R') := by
  refine Quotient.inductionOn F ?_
  rintro ⟨d, hd⟩
  change (mapAlg R' n (mk d hd)).cartierIdealData =
    (mk d hd).cartierIdealData.comap (relCurveMap C R R')
  rw [mapAlg_mk, cartierIdealData_mk, cartierIdealData_mk]
  exact d.cartierIdealData_pullback_relCurveMap R'
    (hd.germ_pullbackEqn_mem_nonZeroDivisors R' n)

/-- The explicit algebra-map form of intrinsic Cartier ideal-sheaf base change. -/
theorem cartierIdealData_mapAlgHom
    {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (φ : A →ₐ[k] A') (F : DivFamZarAff C A n) :
    (mapAlgHom φ F).cartierIdealData =
      letI : Algebra A A' := φ.toRingHom.toAlgebra
      haveI : IsScalarTower k A A' :=
        .of_algebraMap_eq fun a => (φ.commutes a).symm
      F.cartierIdealData.comap (relCurveMap C A A') := by
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A A' :=
    .of_algebraMap_eq fun a => (φ.commutes a).symm
  rw [mapAlgHom_eq_mapAlg φ (fun _ => rfl)]
  exact cartierIdealData_mapAlg A' F

end DivFamZarAff

end AlgebraicGeometry
