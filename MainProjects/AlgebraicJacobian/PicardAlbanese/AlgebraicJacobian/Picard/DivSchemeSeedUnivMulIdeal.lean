/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivSecondWindowBaseChange
import AlgebraicJacobian.Picard.DivSchemeMulIdealFinite
import AlgebraicJacobian.Picard.DivSchemeRedesignChartReadIdeal
import AlgebraicJacobian.Picard.DivisorFamilyWindowUnitGeneration

/-!
# Universal multiplication and the genuine chart-reading ideals

The universal multiplication map is presented as a finite sum indexed by a
basis of the multiplier window.  This file records its compatibility with the
two pinned-chart readings and the resulting inclusion of the genuine
second-window reading ideal in the first-window reading ideal.

This is the finite-component form of `IdealPurity.span_range_read_le_of_surjective_mul`.
The reverse inclusion is exposed through an explicit finite unit-generation
condition, discharged below by the canonical theta sections; no flatness
hypothesis is used here.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

private theorem span_range_comp_linearEquiv_eq
    {R B M M' : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M' →ₗ[R] B) (e : M ≃ₗ[R] M') :
    Ideal.span (Set.range (f.comp e.toLinearMap)) = Ideal.span (Set.range f) := by
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨e.symm x, ?_⟩
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]

section Campaign

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftMulIdeal :
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

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS" => ↥(Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "N1" =>
  (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule
local notation "N2" =>
  (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule

noncomputable def divUniversalFstWindowChartRead (b : Bool) :
    N1 →ₗ[RZ] Γ(relCurve C RZ, relPinnedChart C RZ pi b) :=
  (ThetaGeneratorSeed.chartReadMap
      (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b).comp
    (divUniversalSeedKEquiv C pi hpi g r1 r2 b1 b2 i j).toLinearMap

noncomputable def divUniversalSndWindowChartRead (b : Bool) :
    N2 →ₗ[RZ] Γ(relCurve C RZ, relPinnedChart C RZ pi b) :=
  (ThetaGeneratorSeed.chartReadMap
      (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b).comp
    (divUniversalSeedK'Equiv C pi hpi g r1 r2 b1 b2 i j).toLinearMap

noncomputable def divUniversalMultiplierChartRead (b : Bool) (a : HS) :
    Γ(relCurve C RZ, relPinnedChart C RZ pi b) :=
  match b with
  | false => windowShiftTheta₀ C pi hpi g RZ a
  | true => windowShiftTheta₁ C pi hpi g RZ a

-- This identity is valid over the chart ring itself; the field-only assembly
-- wrapper is intentionally not used here.
set_option maxHeartbeats 1000000 in
-- The chart-ring window equivalence requires a deeper dependent reduction.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
private theorem divUniversalMultiplierChartRead_false_eq (a : HS) :
    divUniversalMultiplierChartRead C hpi g r1 r2 b1 b2 i j false a =
      relThetaWindowChartRead C RZ pi (windowS_choice pi hpi g)
        (relThetaPairH1_windowS C hpi g) false (1 ⊗ₜ a) := by
  rw [divUniversalMultiplierChartRead, relThetaWindowChartRead,
    LinearMap.comp_apply, relThetaResSide_false]
  exact (resHom_relThetaWindowEquiv_one_tmul_fst C pi RZ
    (windowS_choice pi hpi g) (relThetaPairH1_windowS C hpi g) a).symm

set_option maxHeartbeats 1000000 in
-- The shifted chart has the same dependent reduction cost.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
private theorem divUniversalMultiplierChartRead_true_eq (a : HS) :
    divUniversalMultiplierChartRead C hpi g r1 r2 b1 b2 i j true a =
      relThetaWindowChartRead C RZ pi (windowS_choice pi hpi g)
        (relThetaPairH1_windowS C hpi g) true (1 ⊗ₜ a) := by
  rw [divUniversalMultiplierChartRead, relThetaWindowChartRead,
    LinearMap.comp_apply, relThetaResSide_true]
  exact (resHom_relThetaWindowEquiv_one_tmul_snd C pi RZ
    (windowS_choice pi hpi g) (relThetaPairH1_windowS C hpi g) a).symm

-- Unfolding both transported window equivalences exceeds the project defaults.
set_option maxHeartbeats 1600000 in
-- The chart readings contain two transported subtype equivalences.
set_option synthInstance.maxHeartbeats 600000 in
set_option linter.unusedSectionVars false in
set_option maxRecDepth 8000 in
theorem divUniversalMulComponentToSnd_chartRead
    (b : Bool) (t : Fin (Module.finrank k HS)) (x : N1) :
    divUniversalSndWindowChartRead C hpi g r1 r2 b1 b2 i j b
        (universalMulComponentToSnd (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j t x) =
      divUniversalMultiplierChartRead C hpi g r1 r2 b1 b2 i j b
          ((Module.finBasis k HS) t) *
        divUniversalFstWindowChartRead C hpi g r1 r2 b1 b2 i j b x := by
  cases b
  · change
      (relCurve C RZ).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C RZ pi
              (windowM_choice pi hpi g + windowS_choice pi hpi g)
              (relThetaPairH1_windowMS C pi hpi g)
              (LinearMap.baseChange RZ
                (windowShiftMul hpi g ((Module.finBasis k HS) t)) x.1)).val.1) =
        windowShiftTheta₀ C pi hpi g RZ ((Module.finBasis k HS) t) *
          (relCurve C RZ).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C RZ pi (windowM_choice pi hpi g)
                (relThetaPairH1_windowM C pi hpi g) x.1).val.1)
    exact relThetaWindowEquiv_sectionMul_fst C pi hpi g RZ
      ((Module.finBasis k HS) t) (relThetaPairH1_windowM C pi hpi g)
      (relThetaPairH1_windowMS C pi hpi g) x.1
  · change
      (relCurve C RZ).resHom (le_inf le_top le_rfl)
          ((relThetaWindowEquiv C RZ pi
              (windowM_choice pi hpi g + windowS_choice pi hpi g)
              (relThetaPairH1_windowMS C pi hpi g)
              (LinearMap.baseChange RZ
                (windowShiftMul hpi g ((Module.finBasis k HS) t)) x.1)).val.2) =
        windowShiftTheta₁ C pi hpi g RZ ((Module.finBasis k HS) t) *
          (relCurve C RZ).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C RZ pi (windowM_choice pi hpi g)
                (relThetaPairH1_windowM C pi hpi g) x.1).val.2)
    exact relThetaWindowEquiv_sectionMul_snd C pi hpi g RZ
      ((Module.finBasis k HS) t) (relThetaPairH1_windowM C pi hpi g)
      (relThetaPairH1_windowMS C pi hpi g) x.1

-- Rewriting the finite component sum repeats the transported chart-reading types.
set_option maxHeartbeats 1600000 in
-- The finite sum expands the same dependent chart-reading types componentwise.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
theorem divUniversalMulMapToSnd_chartRead
    (b : Bool)
    (x : universalMulSource (C := C) (π := pi) (hπ := hpi)
      g r1 r2 b1 b2 i j) :
    divUniversalSndWindowChartRead C hpi g r1 r2 b1 b2 i j b
        (universalMulMapToSnd (C := C) (π := pi)
          hpi g r1 r2 b1 b2 i j x) =
      ∑ t, divUniversalMultiplierChartRead C hpi g r1 r2 b1 b2 i j b
          ((Module.finBasis k HS) t) *
        divUniversalFstWindowChartRead C hpi g r1 r2 b1 b2 i j b (x t) := by
  rw [universalMulMapToSnd_eq_finiteComponentSum
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j]
  simp only [finiteComponentSum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact divUniversalMulComponentToSnd_chartRead
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b t (x t)

-- The concrete universal seed and pinned-chart rings require extra elaboration budget.
set_option maxHeartbeats 1600000 in
-- The concrete chart-ring maps are large dependent objects.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- Surjectivity of the relative second-window multiplication map gives the
inclusion of its chart-reading ideal in the first-window chart-reading ideal. -/
theorem span_range_divUniversalSndWindowChartRead_le_fst
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) (b : Bool) :
    Ideal.span (Set.range
        (divUniversalSndWindowChartRead C hpi g r1 r2 b1 b2 i j b)) ≤
      Ideal.span (Set.range
        (divUniversalFstWindowChartRead C hpi g r1 r2 b1 b2 i j b)) := by
  classical
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := universalMulMapToSnd_surjective
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb y
  rw [divUniversalMulMapToSnd_chartRead
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b]
  exact Ideal.sum_mem _ fun t _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x t, rfl⟩)

-- Transport through both universal seed equivalences exceeds the project defaults.
set_option maxHeartbeats 1600000 in
-- The span transport unfolds both seed equivalences.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The genuine second-window chart-reading ideal is contained in the genuine
first-window ideal.  This is the ideal-level output of second-window
persistence; it assumes neither quotient flatness nor purity. -/
theorem chartReadIdeal_divUniversalSeedK'_le_divUniversalSeedK
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) (b : Bool) :
    ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b ≤
      ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b := by
  rw [ThetaGeneratorSeed.chartReadIdeal, ThetaGeneratorSeed.chartReadIdeal]
  calc
    Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)) =
        Ideal.span (Set.range (divUniversalSndWindowChartRead
          C hpi g r1 r2 b1 b2 i j b)) := by
      simpa only [divUniversalSndWindowChartRead] using
        (span_range_comp_linearEquiv_eq
          (ThetaGeneratorSeed.chartReadMap
            (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)
          (divUniversalSeedK'Equiv C pi hpi g r1 r2 b1 b2 i j)).symm
    _ ≤ Ideal.span (Set.range (divUniversalFstWindowChartRead
        C hpi g r1 r2 b1 b2 i j b)) :=
      span_range_divUniversalSndWindowChartRead_le_fst
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb b
    _ = Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)) := by
      simpa only [divUniversalFstWindowChartRead] using
        span_range_comp_linearEquiv_eq
          (ThetaGeneratorSeed.chartReadMap
            (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)
          (divUniversalSeedKEquiv C pi hpi g r1 r2 b1 b2 i j)

/-- The finite unit-generation condition used by the reverse ideal bridge. -/
def DivUniversalMultiplierChartUnitGeneration (b : Bool) : Prop :=
  ∃ c : Fin (Module.finrank k HS) →
      Γ(relCurve C RZ, relPinnedChart C RZ pi b),
    ∑ t, c t * divUniversalMultiplierChartRead
      C hpi g r1 r2 b1 b2 i j b ((Module.finBasis k HS) t) = 1

-- Rewriting the canonical theta sections through the relative window equivalence is expensive.
set_option maxHeartbeats 1600000 in
-- The base-change window comparison is a large dependent equality.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The canonical theta sections discharge the finite unit-generation condition
on either pinned chart. -/
theorem divUniversalMultiplierChartUnitGeneration (b : Bool) :
    DivUniversalMultiplierChartUnitGeneration C hpi g r1 r2 b1 b2 i j b := by
  obtain ⟨c, hc⟩ :=
    exists_basis_relThetaWindowChartRead_mul_eq_one C RZ pi
      (windowS_choice pi hpi g) (Module.finBasis k HS)
      (relThetaPairH1_windowS C hpi g) b
  refine ⟨c, ?_⟩
  cases b
  · simpa only [divUniversalMultiplierChartRead_false_eq (C := C) (pi := pi)
      (hpi := hpi) (g := g)] using hc
  · simpa only [divUniversalMultiplierChartRead_true_eq (C := C) (pi := pi)
      (hpi := hpi) (g := g)] using hc

-- The concrete finite multiplication presentation has large dependent ring types.
set_option maxHeartbeats 1600000 in
-- The finite-unit argument repeats the concrete chart-ring multiplication map.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
theorem span_range_divUniversalFstWindowChartRead_le_snd_of_unitGeneration
    (b : Bool)
    (hunit : DivUniversalMultiplierChartUnitGeneration
      C hpi g r1 r2 b1 b2 i j b) :
    Ideal.span (Set.range
        (divUniversalFstWindowChartRead C hpi g r1 r2 b1 b2 i j b)) ≤
      Ideal.span (Set.range
        (divUniversalSndWindowChartRead C hpi g r1 r2 b1 b2 i j b)) := by
  classical
  obtain ⟨c, hc⟩ := hunit
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨x, rfl⟩
  rw [← one_mul (divUniversalFstWindowChartRead
    C hpi g r1 r2 b1 b2 i j b x), ← hc, Finset.sum_mul]
  apply Ideal.sum_mem
  intro t _
  have hsingle :
      divUniversalSndWindowChartRead C hpi g r1 r2 b1 b2 i j b
          (universalMulMapToSnd (C := C) (π := pi)
            hpi g r1 r2 b1 b2 i j (Pi.single t x)) =
        divUniversalMultiplierChartRead C hpi g r1 r2 b1 b2 i j b
            ((Module.finBasis k HS) t) *
          divUniversalFstWindowChartRead C hpi g r1 r2 b1 b2 i j b x := by
    rw [divUniversalMulMapToSnd_chartRead
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b]
    rw [Finset.sum_eq_single t
      (fun t' _ htt' => by simp [htt'])
      (fun ht => absurd (Finset.mem_univ t) ht)]
    simp
  rw [mul_assoc, ← hsingle]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span
    ⟨universalMulMapToSnd (C := C) (π := pi)
      hpi g r1 r2 b1 b2 i j (Pi.single t x), rfl⟩)

-- Equality transports through both seed equivalences and the finite presentation.
set_option maxHeartbeats 1600000 in
-- The equality combines both transported span calculations.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- Under explicit unit generation by the multiplier readings, the two
genuine universal chart-reading ideals agree. -/
theorem chartReadIdeal_divUniversalSeedK'_eq_divUniversalSeedK_of_unitGeneration
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) (b : Bool)
    (hunit : DivUniversalMultiplierChartUnitGeneration
      C hpi g r1 r2 b1 b2 i j b) :
    ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b =
      ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b := by
  apply le_antisymm
  · exact chartReadIdeal_divUniversalSeedK'_le_divUniversalSeedK
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb b
  · rw [ThetaGeneratorSeed.chartReadIdeal, ThetaGeneratorSeed.chartReadIdeal]
    calc
      Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
          (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)) =
          Ideal.span (Set.range (divUniversalFstWindowChartRead
            C hpi g r1 r2 b1 b2 i j b)) := by
        simpa only [divUniversalFstWindowChartRead] using
          (span_range_comp_linearEquiv_eq
            (ThetaGeneratorSeed.chartReadMap
              (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)
            (divUniversalSeedKEquiv C pi hpi g r1 r2 b1 b2 i j)).symm
      _ ≤ Ideal.span (Set.range (divUniversalSndWindowChartRead
          C hpi g r1 r2 b1 b2 i j b)) :=
        span_range_divUniversalFstWindowChartRead_le_snd_of_unitGeneration
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b hunit
      _ = Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
          (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)) := by
        simpa only [divUniversalSndWindowChartRead] using
          span_range_comp_linearEquiv_eq
            (ThetaGeneratorSeed.chartReadMap
              (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)
            (divUniversalSeedK'Equiv C pi hpi g r1 r2 b1 b2 i j)

-- The canonical theta sections discharge unit generation on both pinned charts.
set_option maxHeartbeats 1600000 in
-- The final wrapper re-elaborates the transported equality at the chart ring.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
theorem chartReadIdeal_divUniversalSeedK'_eq_divUniversalSeedK
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) (b : Bool) :
    ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b =
      ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b :=
  chartReadIdeal_divUniversalSeedK'_eq_divUniversalSeedK_of_unitGeneration
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb b
    (divUniversalMultiplierChartUnitGeneration
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b)

/-! ## Decoupled Euler-characteristic parameter -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The degree-`g` second-window chart-reading span is contained in the first
one when Riemann--Roch is normalized by `gamma ≤ g`. -/
theorem span_range_divUniversalSndWindowChartRead_le_fst_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (b : Bool) :
    Ideal.span (Set.range
        (divUniversalSndWindowChartRead C hpi g r1 r2 b1 b2 i j b)) ≤
      Ideal.span (Set.range
        (divUniversalFstWindowChartRead C hpi g r1 r2 b1 b2 i j b)) := by
  classical
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := universalMulMapToSnd_surjective_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi y
  rw [divUniversalMulMapToSnd_chartRead
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b]
  exact Ideal.sum_mem _ fun t _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x t, rfl⟩)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The genuine degree-`g` second-window chart-reading ideal is contained in
the first-window ideal at independent Euler parameter `gamma ≤ g`. -/
theorem chartReadIdeal_divUniversalSeedK'_le_divUniversalSeedK_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (b : Bool) :
    ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b ≤
      ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b := by
  rw [ThetaGeneratorSeed.chartReadIdeal, ThetaGeneratorSeed.chartReadIdeal]
  calc
    Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)) =
        Ideal.span (Set.range (divUniversalSndWindowChartRead
          C hpi g r1 r2 b1 b2 i j b)) := by
      simpa only [divUniversalSndWindowChartRead] using
        (span_range_comp_linearEquiv_eq
          (ThetaGeneratorSeed.chartReadMap
            (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)
          (divUniversalSeedK'Equiv C pi hpi g r1 r2 b1 b2 i j)).symm
    _ ≤ Ideal.span (Set.range (divUniversalFstWindowChartRead
        C hpi g r1 r2 b1 b2 i j b)) :=
      span_range_divUniversalSndWindowChartRead_le_fst_at
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi b
    _ = Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)) := by
      simpa only [divUniversalFstWindowChartRead] using
        span_range_comp_linearEquiv_eq
          (ThetaGeneratorSeed.chartReadMap
            (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)
          (divUniversalSeedKEquiv C pi hpi g r1 r2 b1 b2 i j)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- Under explicit multiplier unit generation, the two genuine degree-`g`
chart-reading ideals agree at independent Euler parameter `gamma ≤ g`. -/
theorem chartReadIdeal_divUniversalSeedK'_eq_divUniversalSeedK_of_unitGeneration_at
    {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (b : Bool)
    (hunit : DivUniversalMultiplierChartUnitGeneration
      C hpi g r1 r2 b1 b2 i j b) :
    ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b =
      ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b := by
  apply le_antisymm
  · exact chartReadIdeal_divUniversalSeedK'_le_divUniversalSeedK_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi b
  · rw [ThetaGeneratorSeed.chartReadIdeal, ThetaGeneratorSeed.chartReadIdeal]
    calc
      Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
          (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)) =
          Ideal.span (Set.range (divUniversalFstWindowChartRead
            C hpi g r1 r2 b1 b2 i j b)) := by
        simpa only [divUniversalFstWindowChartRead] using
          (span_range_comp_linearEquiv_eq
            (ThetaGeneratorSeed.chartReadMap
              (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b)
            (divUniversalSeedKEquiv C pi hpi g r1 r2 b1 b2 i j)).symm
      _ ≤ Ideal.span (Set.range (divUniversalSndWindowChartRead
          C hpi g r1 r2 b1 b2 i j b)) :=
        span_range_divUniversalFstWindowChartRead_le_snd_of_unitGeneration
          (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b hunit
      _ = Ideal.span (Set.range (ThetaGeneratorSeed.chartReadMap
          (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)) := by
        simpa only [divUniversalSndWindowChartRead] using
          span_range_comp_linearEquiv_eq
            (ThetaGeneratorSeed.chartReadMap
              (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b)
            (divUniversalSeedK'Equiv C pi hpi g r1 r2 b1 b2 i j)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The canonical theta sections identify the two genuine degree-`g`
chart-reading ideals at independent Euler parameter `gamma ≤ g`. -/
theorem chartReadIdeal_divUniversalSeedK'_eq_divUniversalSeedK_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (b : Bool) :
    ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK' C pi hpi g r1 r2 b1 b2 i j) b =
      ThetaGeneratorSeed.chartReadIdeal
        (divUniversalSeedK C pi hpi g r1 r2 b1 b2 i j) b :=
  chartReadIdeal_divUniversalSeedK'_eq_divUniversalSeedK_of_unitGeneration_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi b
    (divUniversalMultiplierChartUnitGeneration
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j b)

end Campaign

end AlgebraicGeometry
