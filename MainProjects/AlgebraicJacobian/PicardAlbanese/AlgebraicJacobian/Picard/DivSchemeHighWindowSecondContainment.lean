/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeEpsCarve
import AlgebraicJacobian.Picard.DivSchemeHighWindowPointwiseGenerator
import AlgebraicJacobian.Picard.DivSchemeSeedUnivSecondWindowBaseChange

/-!
# The universal second window vanishes along the high-window divisor

The first universal window vanishes along the local equations extracted from any
generator seed whose seed module is `divUniversalSeedK`.  Multiplication preserves this
vanishing, while the universal multiplication span is the entire universal second
window.  This supplies the second-window containment needed by the certificate
constructor, without assuming a certificate.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section UniversalSecondContainment

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowSecondContainment :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS" => ↥(Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)

namespace ThetaGeneratorSeed

set_option maxHeartbeats 2400000 in
-- The proof unfolds the universal seed through both window equivalences.
set_option synthInstance.maxHeartbeats 800000 in
/-- The universal second window is contained in the divisor window extracted from any
generator whose seed submodule is the universal first-window seed. -/
theorem divUniversalSndWindow_le_divisorWindow_of_generator
    (D : ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j))
    (hD : D.IsGenerator)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) :
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule ≤
      divisorWindow (D.localEquations hD)
        (relThetaPairH1_windowMS C pi hpi g) := by
  have hfst :
      (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule ≤
        divisorWindow (D.localEquations hD)
          (relThetaPairH1_windowM C pi hpi g) := by
    have hseed := D.le_vanishingSubmodule hD
    exact Submodule.map_le_iff_le_comap.mp hseed
  rw [← universalMulSpan_eq_divUniversalSndWindow
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb]
  rintro _ ⟨v, rfl⟩
  rw [universalMulMap]
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro t ht
  exact windowShiftMul_mem_divisorWindow C pi hpi g RZ
    (D.localEquations hD) ((Module.finBasis k HS) t) (hfst (v t).2)

set_option maxHeartbeats 2400000 in
-- The proof unfolds the universal seed through both degree-`g` window equivalences.
set_option synthInstance.maxHeartbeats 800000 in
/-- At independent Euler parameter `gamma ≤ g`, the universal second window is
contained in the divisor window extracted from any generator of the universal seed. -/
theorem divUniversalSndWindow_le_divisorWindow_of_generator_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (D : ThetaGeneratorSeed C RZ pi (windowM_choice pi hpi g)
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j))
    (hD : D.IsGenerator)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule ≤
      divisorWindow (D.localEquations hD)
        (relThetaPairH1_windowMS C pi hpi g) := by
  have hfst :
      (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule ≤
        divisorWindow (D.localEquations hD)
          (relThetaPairH1_windowM C pi hpi g) := by
    have hseed := D.le_vanishingSubmodule hD
    exact Submodule.map_le_iff_le_comap.mp hseed
  rw [← universalMulSpan_eq_divUniversalSndWindow_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchiGamma]
  rintro _ ⟨v, rfl⟩
  rw [universalMulMap]
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro t ht
  exact windowShiftMul_mem_divisorWindow C pi hpi g RZ
    (D.localEquations hD) ((Module.finBasis k HS) t) (hfst (v t).2)

end ThetaGeneratorSeed

namespace PointwiseAchiever

set_option maxHeartbeats 2400000 in
-- The specialization elaborates the all-stage pointwise generator and its equations.
set_option synthInstance.maxHeartbeats 800000 in
/-- The all-stage high-window generator satisfies the universal second-window
containment required by `ThetaGeneratorSeed.divFamEps_certifiedFamily`. -/
theorem divUniversalSndWindow_le_highWindow_divisorWindow
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) :
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule ≤
      divisorWindow
        ((highWindowPointwiseGeneratorSeed
          C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
            (isGenerator_highWindowPointwiseGeneratorSeed
              C hpi g r1 r2 b1 b2 i j hO hchi hb))
        (relThetaPairH1_windowMS C pi hpi g) :=
  ThetaGeneratorSeed.divUniversalSndWindow_le_divisorWindow_of_generator
    C hpi g r1 r2 b1 b2 i j
    (highWindowPointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)
    (isGenerator_highWindowPointwiseGeneratorSeed
      C hpi g r1 r2 b1 b2 i j hO hchi hb) hO hchi hb

set_option maxHeartbeats 2400000 in
-- The specialization elaborates the decoupled pointwise generator and its equations.
set_option synthInstance.maxHeartbeats 800000 in
/-- At independent Euler parameter `gamma ≤ g`, the all-stage high-window generator
satisfies the universal second-window containment required by the certificate. -/
theorem divUniversalSndWindow_le_highWindow_divisorWindow_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule ≤
      divisorWindow
        ((highWindowPointwiseGeneratorSeed_at
          C hpi g r1 r2 b1 b2 i j hgamma hchiGamma).localEquations
            (isGenerator_highWindowPointwiseGeneratorSeed_at
              C hpi g r1 r2 b1 b2 i j hgamma hchiGamma))
        (relThetaPairH1_windowMS C pi hpi g) :=
  ThetaGeneratorSeed.divUniversalSndWindow_le_divisorWindow_of_generator_at
    C hpi g r1 r2 b1 b2 i j hgamma
    (highWindowPointwiseGeneratorSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)
    (isGenerator_highWindowPointwiseGeneratorSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma) hchiGamma

end PointwiseAchiever

end UniversalSecondContainment

end AlgebraicGeometry
