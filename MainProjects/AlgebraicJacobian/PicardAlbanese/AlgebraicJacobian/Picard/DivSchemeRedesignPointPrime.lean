/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeFibrePointRead
import AlgebraicJacobian.Picard.DivSchemeRedesignKappaZFibre

/-!
# DD-4 redesign: transport of the pointwise prime condition

The fibre achiever gives divisibility in the DVR at the residue-field point.  This
file transports that divisibility through the local stalk map and records the
resulting total-space prime-membership statement.  It is deliberately separated
from the purity step: prime membership alone does not imply that the colength
module has zero tensor fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace MonoidalCategory CartesianMonoidalCategory
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (K : Type u) [Field K] [Algebra k K] [Algebra R K]
  [IsScalarTower k R K]
variable {π : C.left ⟶ P1 k} [IsFinite π]

variable [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

noncomputable local instance instIsIntegralRelCurvePointPrime (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointPrime (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointPrime (L : Type u) [Field L]
    [Algebra k L] [IsProper C.hom] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- Fibre-germ divisibility of two compared window vectors implies prime
membership of their total chart readings at the corresponding point. -/
theorem mem_prime_of_windowEquiv_fibre_dvd
    (b : Bool) {z : relCurve C R}
    (hz : z ∈ relPinnedChart C R π b)
    {xsec xψ : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)}
    (hsec : relThetaResSide a b le_rfl
        (relThetaWindowEquiv C R π a hH1 xsec) ∈
      ((isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩).asIdeal)
    (hdiv :
      ((relCurve C (relCurveBasePoint C R z).asIdeal.ResidueField).presheaf.germ
        (relPinnedChart C (relCurveBasePoint C R z).asIdeal.ResidueField π b)
        (relCurveResiduePoint C R z)
        (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom
        (relThetaResSide a b le_rfl
          (relThetaWindowEquiv C (relCurveBasePoint C R z).asIdeal.ResidueField π a hH1
            (windowCompare R (relCurveBasePoint C R z).asIdeal.ResidueField xψ))) ∈
      Ideal.span {
        ((relCurve C (relCurveBasePoint C R z).asIdeal.ResidueField).presheaf.germ
          (relPinnedChart C (relCurveBasePoint C R z).asIdeal.ResidueField π b)
          (relCurveResiduePoint C R z)
          (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom
          (relThetaResSide a b le_rfl
            (relThetaWindowEquiv C (relCurveBasePoint C R z).asIdeal.ResidueField π a hH1
              (windowCompare R (relCurveBasePoint C R z).asIdeal.ResidueField xsec)))} ) :
    relThetaResSide a b le_rfl
        (relThetaWindowEquiv C R π a hH1 xψ) ∈
      ((isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩).asIdeal := by
  let Kz := (relCurveBasePoint C R z).asIdeal.ResidueField
  let zK := relCurveResiduePoint C R z
  have hzK : zK ∈ relPinnedChart C Kz π b :=
    relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz
  have hbase : (relCurveMap C R Kz).base zK ∈ relPinnedChart C R π b := by
    rw [relCurveMap_relCurveResiduePoint]
    exact hz
  have hbase_eq : (relCurveMap C R Kz).base zK = z := by
    exact relCurveMap_relCurveResiduePoint C R z
  let zbase : relPinnedChart C R π b :=
    ⟨(relCurveMap C R Kz).base zK, hbase⟩
  have hscomp :=
    stalkMap_germ_relThetaResSide_windowEquiv_at_relCurveResiduePoint
      C R (π := π) a hH1 b hz xsec
  have htcomp :=
    stalkMap_germ_relThetaResSide_windowEquiv_at_relCurveResiduePoint
      C R (π := π) a hH1 b hz xψ
  have hsec' : relThetaResSide a b le_rfl
        (relThetaWindowEquiv C R π a hH1 xsec) ∈
      ((isAffineOpen_relPinnedChart C R π b).primeIdealOf zbase).asIdeal := by
    simpa [zbase, hbase_eq] using hsec
  have hdiv' :
      ((relCurve C Kz).presheaf.germ (relPinnedChart C Kz π b) zK hzK).hom
          (relThetaResSide a b le_rfl
            (relThetaWindowEquiv C Kz π a hH1 (windowCompare R Kz xψ))) ∈
        Ideal.span {
          ((relCurve C Kz).presheaf.germ (relPinnedChart C Kz π b) zK hzK).hom
            (relThetaResSide a b le_rfl
              (relThetaWindowEquiv C Kz π a hH1 (windowCompare R Kz xsec)))} := by
    simpa [Kz, zK] using hdiv
  have hmem := mem_prime_of_stalkMap_germ_mem_span
    (f := relCurveMap C R Kz) (hU := isAffineOpen_relPinnedChart C R π b)
    (hz := hzK) (hzbase := hbase) hscomp htcomp hdiv' hsec'
  simpa [zbase, hbase_eq] using hmem

end AlgebraicGeometry
