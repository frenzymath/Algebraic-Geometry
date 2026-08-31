/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreNormalization

/-!
# Canonical divisor submodules inside normalized high-window ambients

The closed normalization identifies a scalar-extended high-window ambient with
`H^0(N + nS)`.  The divisor reconstructed from the carve point cuts out a
canonical subspace `H^0(N + nS - D)` inside that ambient.  This file packages
the inclusion and the resulting submodule of the normalized ambient.  The
nested-subtype equivalence is kept in `DivSchemeHighWindowFibreWindowEquiv`.

No base case or persistence recurrence is proved here.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowFibreWindow

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreWindow :
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

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowFibreWindow :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowFibreWindow :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowFibreWindow :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowFibreWindow :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowFibreWindow :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowFibreWindow :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

/-! ## The canonical fibre window inside the closed ambient -/

set_option maxHeartbeats 1600000 in
-- Expanding the reconstructed divisor and its high-window section module is expensive.
/-- The divisor fibre window `H^0(N+nS-D)` is contained in the closed ambient
`H^0(N+nS)`. -/
theorem divUniversalFibreHighWindow_le_closedAmbient (n : Nat) :
    divUniversalFibreHighWindow
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n ≤
      Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤ := by
  rw [divUniversalFibreHighWindow]
  refine Scheme.divisorSections_mono K ?_ ⊤
  refine Scheme.CurveDivisor.le_iff_coeffAt.mpr fun x hx => ?_
  rw [Scheme.CurveDivisor.coeffAt_sub]
  have hDx := Scheme.CurveDivisor.le_iff_coeffAt.mp
    (divUniversalFibreDivisor_spec
      C hpi g r1 r2 b1 b2 i j K hO hchi hker).1 x hx
  rw [Scheme.CurveDivisor.coeffAt_zero] at hDx
  omega

set_option maxHeartbeats 1600000 in
-- The comap target contains the full closed-normalization campaign parameters.
/-- The canonical divisor fibre window, regarded as a submodule of its closed
high-window ambient rather than of the whole function field. -/
noncomputable def divUniversalFibreHighWindowInAmbient (n : Nat) :
    Submodule K
      ↥(Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤) :=
  (divUniversalFibreHighWindow
    C hpi g r1 r2 b1 b2 i j K hO hchi hker n).comap
      (Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤).subtype

/-! ## The decoupled canonical fibre window -/

set_option maxHeartbeats 1600000 in
/-- The degree-`g` divisor fibre window at curve parameter `gamma ≤ g` is
contained in the degree-`g` closed ambient. -/
theorem divUniversalFibreHighWindow_le_closedAmbient_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j ≤
          RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) :
    divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n ≤
      Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤ := by
  rw [divUniversalFibreHighWindow_at]
  refine Scheme.divisorSections_mono K ?_ ⊤
  refine Scheme.CurveDivisor.le_iff_coeffAt.mpr fun x hx => ?_
  rw [Scheme.CurveDivisor.coeffAt_sub]
  have hDx := Scheme.CurveDivisor.le_iff_coeffAt.mp
    (divUniversalFibreDivisor_spec_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma).1 x hx
  rw [Scheme.CurveDivisor.coeffAt_zero] at hDx
  omega

set_option maxHeartbeats 1600000 in
/-- The decoupled canonical divisor fibre window, regarded as a submodule of
its degree-`g` closed high-window ambient. -/
noncomputable def divUniversalFibreHighWindowInAmbient_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j ≤
          RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) :
    Submodule K
      ↥(Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤) :=
  (divUniversalFibreHighWindow_at
    C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n).comap
      (Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤).subtype

end HighWindowFibreWindow

end AlgebraicGeometry
