/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreImage
import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreWindowEquiv
import AlgebraicJacobian.Picard.DivSchemeProjectiveFibreModel

/-!
# Projective relation fibres in the canonical high-window model

Projectivity of a relative high-window quotient makes base change of its
relation exact.  Combining the resulting generic projective-quotient fibre
model with `DivUniversalHighWindowFibreImage` identifies the scalar-extended
relation with the canonical divisor window `H^0(N+nS-D)`.
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

section HighWindowRelationFibreEquiv

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowRelationFibreEquiv :
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
local notation "G[" n "]" => divUniversalHighWindowAmbient
  (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n
local notation "Kr[" n "]" => divUniversalHighWindowRelation
  (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j n

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]
  [Algebra (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi)
    g r1 r2 b1 b2 i j) K]
  [IsScalarTower (PairChartRing k g r1 g r2 i j)
    (DivCarveChartRing k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j) K]
  [IsScalarTower k (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi)
    g r1 r2 b1 b2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowRelationFibreEquiv :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowRelationFibreEquiv :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowRelationFibreEquiv :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowRelationFibreEquiv :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowRelationFibreEquiv :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowRelationFibreEquiv :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

set_option maxHeartbeats 2000000 in
-- Projective base change unfolds the dependent relation and normalized ambient types.
set_option synthInstance.maxHeartbeats 800000 in
/-- A projective relative quotient and the fieldwise image equality identify
the scalar extension of the relation itself with the canonical divisor fibre
window. -/
noncomputable def divUniversalHighWindowRelationFibreEquiv (n : Nat)
    [Module.Projective RZ (G[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
    K ⊗[RZ] ↥Kr[n] ≃ₗ[K]
      ↥(divUniversalFibreHighWindow
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :=
  (Grassmannian.projectiveQuotientFibreModelEquiv Kr[n]
    (divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n)
    (divUniversalFibreHighWindowInAmbient
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) himage).trans
    (divUniversalFibreHighWindowInAmbientEquiv
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)

set_option maxHeartbeats 2400000 in
-- Rewriting the composite equivalence through nested function-field coercions is expensive.
set_option synthInstance.maxHeartbeats 800000 in
/-- The relation fibre equivalence is the normalized ambient read after
scalar-extending the relation inclusion. -/
@[simp]
theorem divUniversalHighWindowRelationFibreEquiv_coe (n : Nat)
    [Module.Projective RZ (G[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)
    (x : K ⊗[RZ] ↥Kr[n]) :
    ((divUniversalHighWindowRelationFibreEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n himage x :
      divUniversalFibreHighWindow
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
      (relCurve C K).functionField) =
    ((divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n
      (LinearMap.baseChange K Kr[n].subtype x) :
        Scheme.divisorSections K
          (windowN C K hpi g + n • windowS C K hpi g) ⊤) :
      (relCurve C K).functionField) := by
  rw [divUniversalHighWindowRelationFibreEquiv, LinearEquiv.trans_apply,
    divUniversalFibreHighWindowInAmbientEquiv_coe,
    Grassmannian.projectiveQuotientFibreModelEquiv_coe]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The projective relation fibre equivalence at independent curve parameter
`gamma ≤ g`. -/
noncomputable def divUniversalHighWindowRelationFibreEquiv_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (G[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n) :
    K ⊗[RZ] ↥Kr[n] ≃ₗ[K]
      ↥(divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n) :=
  (Grassmannian.projectiveQuotientFibreModelEquiv Kr[n]
    (divUniversalHighWindowClosedAmbientFibreEquiv
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n)
    (divUniversalFibreHighWindowInAmbient_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n) himage).trans
    (divUniversalFibreHighWindowInAmbientEquiv_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The decoupled relation fibre equivalence reads through the same normalized closed
ambient map. -/
@[simp]
theorem divUniversalHighWindowRelationFibreEquiv_coe_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) [Module.Projective RZ (G[n] ⧸ Kr[n])]
    (himage : DivUniversalHighWindowFibreImage_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n)
    (x : K ⊗[RZ] ↥Kr[n]) :
    ((divUniversalHighWindowRelationFibreEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n himage x :
      divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n) :
      (relCurve C K).functionField) =
    ((divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n
      (LinearMap.baseChange K Kr[n].subtype x) :
        Scheme.divisorSections K
          (windowN C K hpi g + n • windowS C K hpi g) ⊤) :
      (relCurve C K).functionField) := by
  rw [divUniversalHighWindowRelationFibreEquiv_at, LinearEquiv.trans_apply,
    divUniversalFibreHighWindowInAmbientEquiv_coe_at,
    Grassmannian.projectiveQuotientFibreModelEquiv_coe]

end HighWindowRelationFibreEquiv

end AlgebraicGeometry
