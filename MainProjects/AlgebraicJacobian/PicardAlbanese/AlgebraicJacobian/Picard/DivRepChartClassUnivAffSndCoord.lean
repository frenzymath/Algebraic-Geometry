/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffSndBasis

/-! # Second-coordinate compatibility for the universal divisor chart -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Grassmannian Scheme ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section UniversalAffSndCoord

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffSndCoord :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "b2c" => b2.map (windowShiftEquiv hpi g).symm
local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j

set_option maxHeartbeats 1200000 in
-- Normalizing the mapped universal window crosses the Grassmannian coordinate equivalences.
set_option synthInstance.maxHeartbeats 800000 in
/-- The second universal window is the pullback of the second tautological pair-chart point. -/
theorem map_divUniversalSndWindow_eq_map_pairTautSnd
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {T : Type u} [CommRing T] [Algebra k T]
    (alpha : ChartRing i0 j0 →ₐ[k] T) :
    congrAmbient b2.equivFun
        (Module.Grassmannian.map alpha
          (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)) =
      Module.Grassmannian.map
        (alpha.comp (divCarveChartMk k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi)
          g r1 r2 b1 b2c i0 j0))
        (pairTautSnd k g r1 r2 i0 j0) := by
  rw [divUniversalSndWindow,
    mappedWindowShiftBasis_symm_trans_seedWindowShiftEquiv C hpi g r2 b2,
    map_congrAmbient,
    congrAmbient_symm_cancel, divUniversalSnd, ← Module.Grassmannian.map_comp]

end UniversalAffSndCoord

end PointwiseAchiever

end AlgebraicGeometry
