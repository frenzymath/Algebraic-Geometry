/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowFibreWindow

/-!
# Equivalence with a canonical high-window fibre submodule

The canonical divisor fibre window is represented in the normalized ambient
as a nested submodule subtype.  Forgetting that ambient wrapper gives a linear
equivalence with the original function-field submodule.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowFibreWindowEquiv

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreWindowEquiv :
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

noncomputable local instance instIsIntegralRelCurveHighWindowFibreWindowEquiv :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowFibreWindowEquiv :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowFibreWindowEquiv :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowFibreWindowEquiv :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j ≤
        RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

set_option maxHeartbeats 1600000 in
-- Elaborating both nested section-submodule subtype structures exceeds the default budget.
/-- Forgetting the closed-ambient wrapper identifies the in-ambient window
with the original function-field submodule. -/
noncomputable def divUniversalFibreHighWindowInAmbientEquiv (n : Nat) :
    ↥(divUniversalFibreHighWindowInAmbient
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n) ≃ₗ[K]
      ↥(divUniversalFibreHighWindow
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :=
  Submodule.comapSubtypeEquivOfLe
    (divUniversalFibreHighWindow_le_closedAmbient
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)

/-- The in-ambient equivalence does not change the underlying function-field
element. -/
@[simp]
theorem divUniversalFibreHighWindowInAmbientEquiv_coe (n : Nat)
    (x : ↥(divUniversalFibreHighWindowInAmbient
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n)) :
    ((divUniversalFibreHighWindowInAmbientEquiv
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n x :
      divUniversalFibreHighWindow
        C hpi g r1 r2 b1 b2 i j K hO hchi hker n) :
      (relCurve C K).functionField) =
      ((x : Scheme.divisorSections K
       (windowN C K hpi g + n • windowS C K hpi g) ⊤) :
      (relCurve C K).functionField) := by
  exact Submodule.comapSubtypeEquivOfLe_apply_coe
    (divUniversalFibreHighWindow_le_closedAmbient
      C hpi g r1 r2 b1 b2 i j K hO hchi hker n) x

/-! ## The decoupled in-ambient equivalence -/

set_option maxHeartbeats 1600000 in
/-- Forgetting the degree-`g` closed-ambient wrapper identifies the decoupled
in-ambient window with its function-field submodule. -/
noncomputable def divUniversalFibreHighWindowInAmbientEquiv_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j ≤
          RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat) :
    ↥(divUniversalFibreHighWindowInAmbient_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n) ≃ₗ[K]
      ↥(divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n) :=
  Submodule.comapSubtypeEquivOfLe
    (divUniversalFibreHighWindow_le_closedAmbient_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n)

/-- The decoupled in-ambient equivalence preserves the underlying
function-field element. -/
@[simp]
theorem divUniversalFibreHighWindowInAmbientEquiv_coe_at {gamma : Nat}
    (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k
        (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi)
        g r1 r2 b1 b2 i j ≤
          RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : Nat)
    (x : ↥(divUniversalFibreHighWindowInAmbient_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n)) :
    ((divUniversalFibreHighWindowInAmbientEquiv_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n x :
      divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n) :
      (relCurve C K).functionField) =
      ((x : Scheme.divisorSections K
       (windowN C K hpi g + n • windowS C K hpi g) ⊤) :
      (relCurve C K).functionField) := by
  exact Submodule.comapSubtypeEquivOfLe_apply_coe
    (divUniversalFibreHighWindow_le_closedAmbient_at
      C hpi g r1 r2 b1 b2 i j K hgamma hchiGamma hkerGamma n) x

end HighWindowFibreWindowEquiv

end AlgebraicGeometry
