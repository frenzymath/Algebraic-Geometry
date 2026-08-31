/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa
import AlgebraicJacobian.Picard.DivSchemeSeedUnivSndRes

/-!
# The second fibre-window span seam

This is the target-side mirror of `divUniversalFibreKM_eq_span`.  It records the
second fibre window as the span of the readings of the compared second universal
window.  The statement is used to transport the relative multiplication map to a
residue field without choosing generators of the fibre window.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section Campaign

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftSeedFibreSndRes :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]
  [Algebra (DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j) K]
  [IsScalarTower k (DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j) K]
  [IsScalarTower (PairChartRing k g r1 g r2 i j)
    (DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j) K]

noncomputable local instance instIsIntegralRelCurveFibreSndRes (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveFibreSndRes (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveFibreSndRes (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveFibreSndRes (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

set_option maxHeartbeats 1200000 in
-- The transported second-window dictionaries re-elaborate the three-stage scalar tower.
set_option synthInstance.maxHeartbeats 500000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- The second fibre window is the span of the coherent `Phi`-readings of the
compared second universal window. -/
theorem divUniversalFibreK'_eq_span :
    divUniversalFibreK' C hpi g r1 r2 b2 i j K
      = Submodule.span K
          ((fun x =>
              Scheme.mulLinear K ((msCoherenceUnit C K hpi g :
                (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)
                (divFamPhi C K pi (windowM_choice pi hpi g + windowS_choice pi hpi g)
                  (relThetaPairH1_windowMS C pi hpi g)
                  (windowCompare
                    (DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
                      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j)
                    K x))) ''
            ((divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule :
              Set (TensorProduct k
                (DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
                  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j)
                ↥(Scheme.divisorSections k
                  ((windowM_choice pi hpi g + windowS_choice pi hpi g)
                    • fiberWeilDivisor pi) ⊤)))) := by
  rw [divUniversalSndWindow_toSubmodule_eq_span (C := C) (π := pi) hpi g r1 r2 b1 b2 i j,
    span_image_span_of_algebraMap_smul
      (F := fun x =>
        Scheme.mulLinear K ((msCoherenceUnit C K hpi g :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)
          (divFamPhi C K pi (windowM_choice pi hpi g + windowS_choice pi hpi g)
            (relThetaPairH1_windowMS C pi hpi g)
            (windowCompare
              (DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
                (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j)
              K x)))
      (by simp)
      (fun x y => by
        simp only [map_add, Scheme.mulLinear_apply])
      (fun r y => by
        rw [windowCompare_smul, map_smul, map_smul])
      _,
    ← Set.image_comp]
  rw [divUniversalFibreK',
    Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare
      (pairTautSnd k g r1 r2 i j).toSubmodule K,
    Submodule.map_span, Submodule.map_span, Submodule.map_span,
    ← Set.image_comp, ← Set.image_comp, ← Set.image_comp]
  refine congrArg (Submodule.span K) (Set.image_congr fun n _ => ?_)
  simp only [Function.comp_apply]
  rw [baseChange_linearEquiv_apply, windowCompare_baseChange,
    windowCompare_windowCompare]

end Campaign

end AlgebraicGeometry
