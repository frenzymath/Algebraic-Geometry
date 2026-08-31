/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffFst
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffPairMap
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffSnd
import AlgebraicJacobian.Picard.DivRepClassifyZarAffSurj

/-!
# The widened universal classes hit every divisor chart

The universal seed class is only locally certified on the chart ring, but the characterizing
clause tests it against a globally certified widened representative after arbitrary base change.
The universal window inclusions survive that base change.  Projectivity and constant rank of the
test representative's intrinsic window quotients then upgrade both inclusions to equalities, so
its pair-chart frame presents the same morphism as the canonical divisor chart.
-/

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

section UniversalAffRange

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffRange :
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
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))

local notation "b2c" => b2.map (windowShiftEquiv hpi g).symm
local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j
local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2c i j

set_option maxHeartbeats 8000000 in
-- Both universal windows and the arbitrary framed test elaborate through the pulled seed.
set_option synthInstance.maxHeartbeats 800000 in
/-- The universal widened class satisfies the classifier clause at its canonical divisor chart. -/
theorem isDivRepClassifyAff_divFamZarAffUniv
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    (hb : 0 < windowBound pi hpi) :
    IsDivRepClassifyAff hpi g r1 r2 b1 b2
      (divFamZarAffUniv C hpi g r1 r2 b1 b2c i0 j0 hO hchi hb)
      (ChartMap i0 j0) := by
  intro T _ _ _ _ G hG i j w hw
  let alpha : ChartRing i0 j0 →ₐ[k] T :=
    IsScalarTower.toAlgHom k (ChartRing i0 j0) T
  have heps1 : (G.eps hpi g).1 =
      (Module.Grassmannian.map alpha
        (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
    exact universalFstEps_eq_map
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) (hO := hO) (hchi := hchi)
      i0 j0 hb G hG
  have heps2 : (G.eps hpi g).2 =
      (Module.Grassmannian.map alpha
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
    exact universalSndEps_eq_map
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) (hO := hO) (hchi := hchi)
      i0 j0 hb G hG
  exact divCarveChart_classifies_of_eps_eq_universal
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) i0 j0 G i j w hw heps1 heps2

set_option maxHeartbeats 8000000 in
-- Both off-diagonal universal windows elaborate through the pulled seed and framed test.
set_option synthInstance.maxHeartbeats 800000 in
/-- The universal widened class satisfies the classifier clause when the curve parameter
`gamma ≤ g` is independent of the divisor degree. -/
theorem isDivRepClassifyAff_divFamZarAffUniv_at
    (i0 : (glueData k g r1).J) (j0 : (glueData k g r2).J)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    IsDivRepClassifyAff hpi g r1 r2 b1 b2
      (divFamZarAffUniv_at
        C hpi g r1 r2 b1 b2c i0 j0 hgamma hchiGamma)
      (ChartMap i0 j0) := by
  intro T _ _ _ _ G hG i j w hw
  let alpha : ChartRing i0 j0 →ₐ[k] T :=
    IsScalarTower.toAlgHom k (ChartRing i0 j0) T
  have heps1 : (G.eps hpi g).1 =
      (Module.Grassmannian.map alpha
        (divUniversalFstWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
    exact universalFstEps_eq_map_at
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) i0 j0 hgamma hchiGamma G hG
  have heps2 : (G.eps hpi g).2 =
      (Module.Grassmannian.map alpha
        (divUniversalSndWindow C pi hpi g r1 r2 b1 b2c i0 j0)).toSubmodule := by
    exact universalSndEps_eq_map_at
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
      (b1 := b1) (b2 := b2) i0 j0 hgamma hchiGamma G hG
  exact divCarveChart_classifies_of_eps_eq_universal
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) i0 j0 G i j w hw heps1 heps2

end UniversalAffRange

end PointwiseAchiever

end AlgebraicGeometry
