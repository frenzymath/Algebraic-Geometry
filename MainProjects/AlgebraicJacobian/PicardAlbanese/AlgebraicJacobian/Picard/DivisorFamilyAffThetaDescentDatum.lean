/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCoassoc
import AlgebraicJacobian.Picard.DivisorSubschemeFaithfullyFlat
import AlgebraicJacobian.Descent.InvertibleModule

/-!
# Effectivity of the intrinsic theta descent datum

The descended module of the canonical theta datum is exactly the previously constructed
intrinsic theta equalizer.  Since the chart-product algebra is faithfully flat over the
widened equalizer algebra and the product of local theta quotients is invertible, faithful
flat descent makes the intrinsic equalizer invertible without a swallowing or chart-typing
hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaOverlapQuotientLeftModule thetaOverlapQuotientLeftTower
  thetaOverlapQuotientRightModule thetaOverlapQuotientRightTower
  productOverlapRightAlgebra productOverlapRightTower
  thetaPieceQuotientGluedModule thetaOverlapQuotientGluedModule
  chartProdPieceAlgebra chartProdOverlapAlgebra thetaPieceProdADModule
  thetaPieceProdCPModule thetaPieceProdTower thetaOverlapProdOvlModule
  thetaOverlapQuotientCPModule thetaOverlapProdCPModule thetaOverlapProdADModule
  thetaOverlapProdTower

noncomputable section

variable (A : AffAdaptation D d) (a : ℕ)

set_option maxHeartbeats 1000000 in
-- The proof transports equality through the finite pairwise product comparison.
set_option synthInstance.maxHeartbeats 500000 in
-- The piece and overlap quotient products carry dependent module structures.
/-- The module descended from the intrinsic theta coaction is the intrinsic theta
equalizer already used by the global window construction. -/
theorem IsCertified.thetaDescentDatum_descended_eq {n : ℕ}
    (hc : A.IsCertified n) :
    (hc.thetaDescentDatum A a).descended =
      A.intrinsicThetaGluedOver (π := π) a := by
  apply Submodule.ext
  intro s
  rw [Module.DescentDatum.mem_descended]
  rw [A.intrinsicThetaGluedOver_eq_ker]
  rw [A.mem_intrinsicThetaGluedKernelOver_iff]
  change A.thetaDescentCoaction (π := π) a hc s =
      1 ⊗ₜ[gluedSubalgebra A] s ↔ _
  constructor
  · intro hs p
    have h := congrArg
      (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc) hs
    rw [A.thetaPieceProdBaseChangeToOverlapEquiv_coaction] at h
    rw [A.thetaPieceProdBaseChangeToOverlapEquiv_one_tmul] at h
    exact congrFun h p
  · intro hs
    apply (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc).injective
    rw [A.thetaPieceProdBaseChangeToOverlapEquiv_coaction]
    rw [A.thetaPieceProdBaseChangeToOverlapEquiv_one_tmul]
    funext p
    exact hs p

set_option synthInstance.maxHeartbeats 500000 in
-- Both sides are subtypes of the same dependent piece-product module.
/-- The canonical linear identification between descent effectivity and the intrinsic
theta equalizer. -/
noncomputable def IsCertified.thetaDescendedEquivIntrinsic {n : ℕ}
    (hc : A.IsCertified n) :
    (hc.thetaDescentDatum (π := π) (A := A) (a := a)).descended
        ≃ₗ[gluedSubalgebra A]
      A.IntrinsicThetaGluedOver (π := π) a :=
  LinearEquiv.ofEq
    (hc.thetaDescentDatum (π := π) (A := A) (a := a)).descended
    (A.intrinsicThetaGluedOver (π := π) a)
    (hc.thetaDescentDatum_descended_eq (π := π) A a)

set_option maxHeartbeats 1000000 in
-- Invertibility is transported through faithful-flat descent and the subtype equality.
set_option synthInstance.maxHeartbeats 500000 in
-- The chart-product module and its descended subtype retain dependent product instances.
/-- The intrinsic theta equalizer is invertible over the widened equalizer algebra for
every certified affine adaptation. -/
theorem IsCertified.invertible_intrinsicThetaGluedOver {n : ℕ}
    (hc : A.IsCertified n) :
    Module.Invertible (gluedSubalgebra A)
      (A.IntrinsicThetaGluedOver (π := π) a) := by
  have halgebraMap :
      algebraMap (gluedSubalgebra A) A.chartProd =
        (gluedSubalgebra A).val.toRingHom := by
    ext x i
    rfl
  letI : Module.FaithfullyFlat (gluedSubalgebra A) A.chartProd :=
    RingHom.faithfullyFlat_algebraMap_iff.mp (by
      rw [halgebraMap]
      exact A.faithfullyFlat_gluedSubalgebra_val hc)
  letI : Module.Invertible A.chartProd
      (A.ThetaPieceProd (π := π) a) :=
    A.invertible_thetaPieceProd (π := π) a
  letI : Module.Invertible (gluedSubalgebra A)
      (hc.thetaDescentDatum (π := π) (A := A) (a := a)).descended :=
    (hc.thetaDescentDatum (π := π) (A := A) (a := a)).invertible_descended
  exact Module.Invertible.congr
    (hc.thetaDescendedEquivIntrinsic (π := π) A a)

end


end AffAdaptation

end AlgebraicGeometry
