/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeMulSpanMap
import AlgebraicJacobian.Picard.DivSchemeSeedUnivSecondWindow

/-!
# The finite field-level universal multiplication map

`divUniversalFibre_mulSpan_eq_of_windowBound_pos` identifies the abstract
function-field multiplication span of the first universal fibre window with
the second fibre window.  This file turns that equality into a concrete
surjective linear map: a finite tuple of first-window vectors, indexed by a
basis of the multiplier window, maps to the sum of their products.

The remaining relative step is now isolated to a conjugacy theorem comparing
this map with the residue-field base change of `universalMulMapToSnd`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section SecondWindowMap

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSecondWindowMap :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r₁ g r₂ i j) K]
  [IsScalarTower k (PairChartRing k g r₁ g r₂ i j) K]

noncomputable local instance instIsIntegralRelCurveSecondWindowMap :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveSecondWindowMap :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveSecondWindowMap :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveSecondWindowMap :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSecondWindowMap :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveSecondWindowMap :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
  ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K))

local notation "HS" => Scheme.divisorSections K (windowS C K hπ g) ⊤
local notation "KM" => divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
local notation "KMS" => divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K

set_option maxHeartbeats 1600000 in
-- The transported window types and function-field dictionaries require the campaign budget.
/-- The concrete finite multiplication map onto the second universal fibre
window, under the positive ledger bound. -/
noncomputable def divUniversalFibreMulMap
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K))
    (hb : 0 < windowBound π hπ) :
    (Fin (Module.finrank K ↥HS) → ↥KM) →ₗ[K] ↥KMS :=
  Scheme.finiteMulMapTo (ι := Fin (Module.finrank K ↥HS))
    HS KM KMS (Module.finBasis K ↥HS)
    (divUniversalFibre_mulSpan_eq_of_windowBound_pos
      C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker hb)

set_option maxHeartbeats 1600000 in
-- Re-elaboration of the concrete map repeats the transported window dictionaries.
/-- The finite field-level universal multiplication map is surjective. -/
theorem divUniversalFibreMulMap_surjective
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K))
    (hb : 0 < windowBound π hπ) :
    Function.Surjective
      (divUniversalFibreMulMap C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker hb) :=
  Scheme.finiteMulMapTo_surjective (ι := Fin (Module.finrank K ↥HS))
    HS KM KMS (Module.finBasis K ↥HS)
    (divUniversalFibre_mulSpan_eq_of_windowBound_pos
      C hπ g r₁ r₂ b₁ b₂ i j K hO hχ hker hb)

set_option maxHeartbeats 1600000 in
-- The decoupled persistence proof traverses the transported window dictionaries.
/-- The concrete degree-`g` multiplication map with Euler characteristic
normalized by an independent parameter `gamma ≤ g`. -/
noncomputable def divUniversalFibreMulMap_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K)) :
    (Fin (Module.finrank K ↥HS) → ↥KM) →ₗ[K] ↥KMS :=
  Scheme.finiteMulMapTo (ι := Fin (Module.finrank K ↥HS))
    HS KM KMS (Module.finBasis K ↥HS)
    (divUniversalFibre_mulSpan_eq_of_windowBound_pos_at
      C hπ g r₁ r₂ b₁ b₂ i j K hker hgamma hχgamma (windowBound_pos π hπ))

set_option maxHeartbeats 1600000 in
-- Surjectivity re-elaborates the same transported window dictionaries.
/-- The decoupled finite field-level universal multiplication map is surjective. -/
theorem divUniversalFibreMulMap_surjective_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r₁ g r₂ i j) K)) :
    Function.Surjective
      (divUniversalFibreMulMap_at C hπ g r₁ r₂ b₁ b₂ i j K
        hgamma hχgamma hker) :=
  Scheme.finiteMulMapTo_surjective (ι := Fin (Module.finrank K ↥HS))
    HS KM KMS (Module.finBasis K ↥HS)
    (divUniversalFibre_mulSpan_eq_of_windowBound_pos_at
      C hπ g r₁ r₂ b₁ b₂ i j K hker hgamma hχgamma (windowBound_pos π hπ))

end SecondWindowMap

end AlgebraicGeometry
