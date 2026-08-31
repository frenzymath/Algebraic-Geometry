/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivisorFamilyFieldSurj
import AlgebraicJacobian.Picard.DivisorFamilyPullbackGlued

/-!
# Fibre rank of the Cech difference kernel from divisor degree

The pulled adaptation over a field has glued module equal to the kernel of the pulled
Cech difference.  Delta naturality transports this kernel to the base change of the
original difference map.  The field certificate constructed from divisor degree then
computes its dimension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open Module (finrank)

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {K : Type u} [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R pi d)

omit [Algebra k K] [IsScalarTower k R K] [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- The base-change and algebra-tensor spellings of the Cech difference have the same
kernel. -/
lemma ker_delta_baseChange_eq_ker_lTensor :
    LinearMap.ker ((A.deltaLeft - A.deltaRight).baseChange K) =
      LinearMap.ker (AlgebraTensorModule.lTensor K K (A.deltaLeft - A.deltaRight)) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  rfl

set_option maxHeartbeats 800000 in
-- The proof elaborates the pulled adaptation and both product base-change equivalences.
set_option synthInstance.maxHeartbeats 400000 in
/-- If the pulled local-equation divisor has degree `n`, then the fibre kernel of the
original Cech difference map has dimension `n`.  This is the exact `hdim` shape used by
`DivisorAdaptation.isCertified_of_kernel_spanning`. -/
theorem finrank_ker_delta_baseChange_eq_of_pulled_degree {n : Nat}
    (hproj : forall j : A.index, Module.Projective R (A.colength j))
    (hdeg : Scheme.CurveDivisor.deg K
      (Scheme.presentationDivisor K
        ((A.pulledEquations K hproj).presentation)) = (n : Int)) :
    Module.finrank K
      (LinearMap.ker ((A.deltaLeft - A.deltaRight).baseChange K)) = n := by
  let eMap := Submodule.equivMapOfInjective
    (A.chartProdBaseChange K).toLinearMap
    (A.chartProdBaseChange K).injective
    (LinearMap.ker (AlgebraTensorModule.lTensor K K (A.deltaLeft - A.deltaRight)))
  let e :
      LinearMap.ker ((A.deltaLeft - A.deltaRight).baseChange K) ≃ₗ[K]
        A.pulledGluedSubmodule K :=
    (LinearEquiv.ofEq _ _ (A.ker_delta_baseChange_eq_ker_lTensor (K := K))).trans
      (eMap.trans (LinearEquiv.ofEq _ _ (A.map_ker_lTensor_delta K)))
  have hfr := ((A.pullback K hproj).isCertified_of_deg hdeg).finrank_glued
  change Module.finrank K (A.pulledGluedSubmodule K) = n at hfr
  rw [LinearEquiv.finrank_eq e]
  exact hfr

end DivisorAdaptation

end AlgebraicGeometry
