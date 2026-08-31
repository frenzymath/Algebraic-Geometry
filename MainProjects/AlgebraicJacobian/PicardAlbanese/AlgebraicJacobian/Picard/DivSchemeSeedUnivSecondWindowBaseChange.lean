/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivFibreEquiv
import AlgebraicJacobian.Picard.DivSchemeMulSpanMap
import AlgebraicJacobian.Picard.DivSchemeSeedUnivSecondWindow
import AlgebraicJacobian.Picard.DivSchemeSeedUnivMulSpanClose

/-!
# Residue-field surjectivity of the universal multiplication map

The two cancelled fibre-reading equivalences conjugate the scalar extension of
each relative multiplication component to multiplication in the function field.
Using the scalar-extended multiplier basis, the finite component sum is therefore
the concrete field-level multiplication map onto the second fibre window.
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
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section Campaign

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftSecondWindowBaseChange :
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

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS0" => ↥( Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HM0" => ↥( Scheme.divisorSections k
  (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HMS0" => ↥( Scheme.divisorSections k
  ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤)
local notation "HS" => Scheme.divisorSections K (windowS C K hpi g) ⊤
local notation "N1" => (divUniversalFstWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule
local notation "N2" => (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule
local notation "KM" => divUniversalFibreKM C hpi g r1 r2 b1 i j K
local notation "KMS" => divUniversalFibreK' C hpi g r1 r2 b2 i j K

noncomputable local instance instIsIntegralRelCurveSecondWindowBaseChange :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveSecondWindowBaseChange :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveSecondWindowBaseChange :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTSecondWindowBaseChange :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSecondWindowBaseChange :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveSecondWindowBaseChange :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

/-! ## Relative components -/

set_option maxHeartbeats 1600000 in
-- Elaborating the two transported universal windows exceeds the project default.
/-- One multiplier-basis component of the universal multiplication map,
corestricted to the universal second window. -/
noncomputable def universalMulComponentToSnd
    (t : Fin (Module.finrank k HS0)) : N1 →ₗ[RZ] N2 :=
  ((LinearMap.baseChange RZ (windowShiftMul hpi g ((Module.finBasis k HS0) t))).comp
      (N1).subtype).codRestrict N2 fun x => by
    have hcarve := (carvePairArrow_eq_zero_iff (R := RZ)
      (windowShiftMul hpi g ((Module.finBasis k HS0) t)) N1 N2).mp
      (universal_window_carve (C := C) (π := pi) (hπ := hpi)
        g r1 r2 b1 b2 i j ((Module.finBasis k HS0) t))
    exact hcarve x.1 x.2

set_option maxHeartbeats 1600000 in
-- Unfolding the corestricted finite sum repeats both transported window types.
set_option linter.unusedSectionVars false in
theorem universalMulMapToSnd_eq_finiteComponentSum :
    universalMulMapToSnd (C := C) (π := pi) hpi g r1 r2 b1 b2 i j =
      finiteComponentSum (fun t =>
        universalMulComponentToSnd (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j t) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [universalMulMapToSnd, universalMulMap, finiteComponentSum,
    universalMulComponentToSnd, LinearMap.codRestrict_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply,
    Submodule.coe_sum]

/-! ## Fibre conjugacy -/

/-- The scalar extension of the fixed multiplier basis, read in the fibre
multiplier window. -/
noncomputable def divUniversalMultiplierFibreBasis :
    Module.Basis (Fin (Module.finrank k HS0)) K ↥HS :=
  ((Module.finBasis k HS0).baseChange K).map
    (divUniversalMultiplierFibreEquiv (π := pi) C hpi g K)

-- Unfolding the multiplier dictionary also traverses the relative window construction.
set_option maxHeartbeats 800000 in
-- The multiplier equivalence unfolds the relative curve window dictionary.
set_option maxRecDepth 8000 in
private theorem coe_divUniversalMultiplierFibreBasis_apply
    (t : Fin (Module.finrank k HS0)) :
    (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
        (relCurve C K).functionField) =
      divFamPhi C K pi (windowS_choice pi hpi g)
        (relThetaPairH1_windowS C hpi g)
        (1 ⊗ₜ (Module.finBasis k HS0) t) := by
  simp only [divUniversalMultiplierFibreBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, divUniversalMultiplierFibreEquiv_apply]

-- The transported reading equivalences and product law require the campaign budget.
set_option maxHeartbeats 4000000 in
-- The fibre reading and multiplication dictionaries cross several dependent base-change towers.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
theorem universalMulComponentToSnd_fibre_conjugacy
    (t : Fin (Module.finrank k HS0))
    (x : K ⊗[RZ] N1) :
    (divUniversalSndFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K
        (LinearMap.baseChange K
          (universalMulComponentToSnd (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j t) x) : (relCurve C K).functionField) =
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
          (relCurve C K).functionField) *
        (divUniversalFstFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K x :
          (relCurve C K).functionField) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Submodule.coe_add, hx, hy, mul_add]
  | tmul c x =>
      have hcore :
          (divUniversalSndFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K
              (LinearMap.baseChange K
                (universalMulComponentToSnd (C := C) (pi := pi)
                  hpi g r1 r2 b1 b2 i j t) (1 ⊗ₜ[RZ] x)) :
                (relCurve C K).functionField) =
            (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
                (relCurve C K).functionField) *
              (divUniversalFstFibreReadEquiv
                (π := pi) C hpi g r1 r2 b1 b2 i j K (1 ⊗ₜ[RZ] x) :
                (relCurve C K).functionField) := by
        rw [LinearMap.baseChange_tmul,
          divUniversalSndFibreReadEquiv_one_tmul,
          coe_divUniversalMultiplierFibreBasis_apply,
          divUniversalFstFibreReadEquiv_one_tmul]
        rw [universalMulComponentToSnd, LinearMap.codRestrict_apply,
          LinearMap.comp_apply, Submodule.subtype_apply, windowCompare_baseChange]
        have hmul :
            divFamPhi C K pi (windowS_choice pi hpi g)
                (relThetaPairH1_windowS C hpi g)
                (1 ⊗ₜ ((Module.finBasis k HS0) t)) *
              divFamPhi C K pi (windowM_choice pi hpi g)
                (relThetaPairH1_windowM C pi hpi g)
                (windowCompare RZ K x.1) =
            ((msCoherenceUnit C K hpi g : (relCurve C K).functionFieldˣ) :
                (relCurve C K).functionField) *
              divFamPhi C K pi (windowM_choice pi hpi g + windowS_choice pi hpi g)
                (relThetaPairH1_windowMS C pi hpi g)
                (LinearMap.baseChange K
                  (windowShiftMul hpi g ((Module.finBasis k HS0) t))
                  (windowCompare RZ K x.1)) :=
          divFamPhi_one_tmul_mul (C := C) (K := K) (π := pi) hpi g
          (relThetaPairH1_windowS C hpi g)
          (relThetaPairH1_windowM C pi hpi g)
          (relThetaPairH1_windowMS C pi hpi g)
          ((Module.finBasis k HS0) t) (windowCompare RZ K x.1)
        exact hmul.symm
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul,
        LinearEquiv.map_smul, Submodule.coe_smul,
        Scheme.functionFieldOverModule_smul_def, hcore,
        Submodule.coe_smul, Scheme.functionFieldOverModule_smul_def]
      ring

/-! ## Surjectivity -/

/-- The field-level multiplication map indexed by the scalar extension of the
fixed base-field multiplier basis. -/
noncomputable def divUniversalTransportedFibreMulMap
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (hb : 0 < windowBound pi hpi) :
    (Fin (Module.finrank k HS0) → ↥KM) →ₗ[K] ↥KMS :=
  Scheme.finiteMulMapTo HS KM KMS
    (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
    (divUniversalFibre_mulSpan_eq_of_windowBound_pos
      C hpi g r1 r2 b1 b2 i j K hO hchi hker hb)

-- The finite multiplication presentation is used only through its underlying
-- function-field sum; exposing that equation avoids unfolding the chart map later.
set_option maxHeartbeats 1600000 in
-- The finite multiplication map carries the transported function-field subtypes.
set_option maxRecDepth 12000 in
set_option linter.unusedSectionVars false in
private theorem divUniversalTransportedFibreMulMap_apply_coe
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (hb : 0 < windowBound pi hpi)
    (v : Fin (Module.finrank k HS0) → ↥KM) :
    (divUniversalTransportedFibreMulMap (pi := pi)
      C hpi g r1 r2 b1 b2 i j K hO hchi hker hb v :
        (relCurve C K).functionField) =
      ∑ t, (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
        (relCurve C K).functionField) * (v t : (relCurve C K).functionField) := by
  change (Scheme.finiteMulMap HS KM
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K) v :
        (relCurve C K).functionField) = _
  rw [Scheme.finiteMulMap_apply]

-- Rewriting the finite component sum through both fibre equivalences is similarly expensive.
set_option maxHeartbeats 4000000 in
-- The componentwise conjugacy traverses both cancelled fibre equivalences.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
private theorem fibreComponentSum_conjugacy
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (hb : 0 < windowBound pi hpi)
    (x : Fin (Module.finrank k HS0) → (K ⊗[RZ] N1)) :
    divUniversalSndFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K
        (∑ t, LinearMap.baseChange K
          (universalMulComponentToSnd (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j t) (x t)) =
      divUniversalTransportedFibreMulMap (pi := pi)
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb
        (fun t => divUniversalFstFibreReadEquiv
          (π := pi) C hpi g r1 r2 b1 b2 i j K (x t)) := by
  apply Subtype.ext
  rw [divUniversalTransportedFibreMulMap_apply_coe
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hO hchi hker hb]
  rw [map_sum, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact universalMulComponentToSnd_fibre_conjugacy
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K t (x t)

-- The final surjectivity transport repeats the fibre-window dictionary elaboration.
set_option maxHeartbeats 1600000 in
-- Surjectivity re-elaborates the finite multiplication and fibre-reading dictionaries.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The scalar extension of the universal multiplication map to the second
window is surjective at every field-valued point satisfying the carve equations. -/
theorem universalMulMapToSnd_baseChange_surjective
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (hb : 0 < windowBound pi hpi) :
    Function.Surjective
      (LinearMap.baseChange K
        (universalMulMapToSnd (C := C) (π := pi)
          hpi g r1 r2 b1 b2 i j)) := by
  rw [universalMulMapToSnd_eq_finiteComponentSum
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j]
  apply surjective_baseChange_finiteComponentSum
  intro y
  have hsurj : Function.Surjective
      (divUniversalTransportedFibreMulMap (pi := pi)
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb) :=
    Scheme.finiteMulMapTo_surjective HS KM KMS
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
      (divUniversalFibre_mulSpan_eq_of_windowBound_pos
        C hpi g r1 r2 b1 b2 i j K hO hchi hker hb)
  obtain ⟨z, hz⟩ := hsurj
    (divUniversalSndFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K y)
  let x : Fin (Module.finrank k HS0) → (K ⊗[RZ] N1) := fun t =>
    (divUniversalFstFibreReadEquiv
      (π := pi) C hpi g r1 r2 b1 b2 i j K).symm (z t)
  refine ⟨x, ?_⟩
  apply (divUniversalSndFibreReadEquiv
    (π := pi) C hpi g r1 r2 b1 b2 i j K).injective
  have hconj := fibreComponentSum_conjugacy (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j K hO hchi hker hb x
  have hz' :
      divUniversalTransportedFibreMulMap (pi := pi)
          C hpi g r1 r2 b1 b2 i j K hO hchi hker hb
          (fun t => divUniversalFstFibreReadEquiv
            (π := pi) C hpi g r1 r2 b1 b2 i j K (x t)) =
        divUniversalSndFibreReadEquiv
          (π := pi) C hpi g r1 r2 b1 b2 i j K y := by
    simpa only [x, LinearEquiv.apply_symm_apply] using hz
  simpa only [Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] using
    hconj.trans hz'

/-! ## Residue-field and relative corollaries -/

-- Residue-field towers through the chart quotient exceed the default synthesis depth.
set_option maxHeartbeats 800000 in
-- The residue-field chart quotient requires the larger local synthesis budget.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxSynthPendingDepth 8 in
theorem universalMulMapToSnd_rTensor_residueField_surjective
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi)
    (p : PrimeSpectrum RZ) :
    Function.Surjective
      ((universalMulMapToSnd (C := C) (π := pi)
        hpi g r1 r2 b1 b2 i j).rTensor p.asIdeal.ResidueField) := by
  rw [universalMulMapToSnd_rTensor_surjective_iff_baseChange
    (C := C) (π := pi) hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField]
  exact universalMulMapToSnd_baseChange_surjective
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
    p.asIdeal.ResidueField hO hchi
    (divCarveIdeal_le_ker_of_tower k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j p.asIdeal.ResidueField) hb

-- The finite-module Nakayama wrapper uses the same canonical residue-field tower.
set_option maxHeartbeats 800000 in
-- The finite-module fibre criterion re-synthesizes the residue-field tower.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxSynthPendingDepth 8 in
theorem universalMulMapToSnd_surjective
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) :
    Function.Surjective
      (universalMulMapToSnd (C := C) (π := pi)
        hpi g r1 r2 b1 b2 i j) :=
  universalMulMapToSnd_surjective_of_forall_fibre
    (C := C) (π := pi) hpi g r1 r2 b1 b2 i j
    (fun p => universalMulMapToSnd_rTensor_residueField_surjective
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb p)

-- The span equality packages the residue-field result through the chart tower.
set_option maxHeartbeats 800000 in
-- The relative span closure carries the same chart and residue-field instances.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxSynthPendingDepth 8 in
theorem universalMulSpan_eq_divUniversalSndWindow
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (hb : 0 < windowBound pi hpi) :
    universalMulSpan (C := C) (π := pi) hpi g r1 r2 b1 b2 i j =
      (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule :=
  universalMulSpan_eq_divUniversalSndWindow_of_forall_fibre
    (C := C) (π := pi) hpi g r1 r2 b1 b2 i j
    (fun p => universalMulMapToSnd_rTensor_residueField_surjective
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hO hchi hb p)

/-! ## Decoupled Euler-characteristic parameter -/

/-- The field-level multiplication map for degree `g`, with Riemann--Roch
normalized by an independent `gamma ≤ g`. -/
noncomputable def divUniversalTransportedFibreMulMap_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K)) :
    (Fin (Module.finrank k HS0) → ↥KM) →ₗ[K] ↥KMS :=
  Scheme.finiteMulMapTo HS KM KMS
    (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
    (divUniversalFibre_mulSpan_eq_of_windowBound_pos_at
      C hpi g r1 r2 b1 b2 i j K hker hgamma hchi (windowBound_pos pi hpi))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 12000 in
set_option linter.unusedSectionVars false in
private theorem divUniversalTransportedFibreMulMap_apply_coe_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (v : Fin (Module.finrank k HS0) → ↥KM) :
    (divUniversalTransportedFibreMulMap_at (pi := pi)
      C hpi g r1 r2 b1 b2 i j K hgamma hchi hker v :
        (relCurve C K).functionField) =
      ∑ t, (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K t :
        (relCurve C K).functionField) * (v t : (relCurve C K).functionField) := by
  change (Scheme.finiteMulMap HS KM
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K) v :
        (relCurve C K).functionField) = _
  rw [Scheme.finiteMulMap_apply]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
private theorem fibreComponentSum_conjugacy_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (x : Fin (Module.finrank k HS0) → (K ⊗[RZ] N1)) :
    divUniversalSndFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K
        (∑ t, LinearMap.baseChange K
          (universalMulComponentToSnd (C := C) (pi := pi)
            hpi g r1 r2 b1 b2 i j t) (x t)) =
      divUniversalTransportedFibreMulMap_at (pi := pi)
        C hpi g r1 r2 b1 b2 i j K hgamma hchi hker
        (fun t => divUniversalFstFibreReadEquiv
          (π := pi) C hpi g r1 r2 b1 b2 i j K (x t)) := by
  apply Subtype.ext
  rw [divUniversalTransportedFibreMulMap_apply_coe_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K hgamma hchi hker]
  rw [map_sum, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact universalMulComponentToSnd_fibre_conjugacy
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K t (x t)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- The scalar extension of the degree-`g` universal multiplication map is
surjective when the curve Euler characteristic is normalized at `gamma ≤ g`. -/
theorem universalMulMapToSnd_baseChange_surjective_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K)) :
    Function.Surjective
      (LinearMap.baseChange K
        (universalMulMapToSnd (C := C) (π := pi)
          hpi g r1 r2 b1 b2 i j)) := by
  rw [universalMulMapToSnd_eq_finiteComponentSum
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j]
  apply surjective_baseChange_finiteComponentSum
  intro y
  have hsurj : Function.Surjective
      (divUniversalTransportedFibreMulMap_at (pi := pi)
        C hpi g r1 r2 b1 b2 i j K hgamma hchi hker) :=
    Scheme.finiteMulMapTo_surjective HS KM KMS
      (divUniversalMultiplierFibreBasis (pi := pi) C hpi g K)
      (divUniversalFibre_mulSpan_eq_of_windowBound_pos_at
        C hpi g r1 r2 b1 b2 i j K hker hgamma hchi (windowBound_pos pi hpi))
  obtain ⟨z, hz⟩ := hsurj
    (divUniversalSndFibreReadEquiv (π := pi) C hpi g r1 r2 b1 b2 i j K y)
  let x : Fin (Module.finrank k HS0) → (K ⊗[RZ] N1) := fun t =>
    (divUniversalFstFibreReadEquiv
      (π := pi) C hpi g r1 r2 b1 b2 i j K).symm (z t)
  refine ⟨x, ?_⟩
  apply (divUniversalSndFibreReadEquiv
    (π := pi) C hpi g r1 r2 b1 b2 i j K).injective
  have hconj := fibreComponentSum_conjugacy_at (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j K hgamma hchi hker x
  have hz' :
      divUniversalTransportedFibreMulMap_at (pi := pi)
          C hpi g r1 r2 b1 b2 i j K hgamma hchi hker
          (fun t => divUniversalFstFibreReadEquiv
            (π := pi) C hpi g r1 r2 b1 b2 i j K (x t)) =
        divUniversalSndFibreReadEquiv
          (π := pi) C hpi g r1 r2 b1 b2 i j K y := by
    simpa only [x, LinearEquiv.apply_symm_apply] using hz
  simpa only [Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] using
    hconj.trans hz'

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxSynthPendingDepth 8 in
/-- Residue-field surjectivity at independent Euler parameter `gamma ≤ g`. -/
theorem universalMulMapToSnd_rTensor_residueField_surjective_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum RZ) :
    Function.Surjective
      ((universalMulMapToSnd (C := C) (π := pi)
        hpi g r1 r2 b1 b2 i j).rTensor p.asIdeal.ResidueField) := by
  rw [universalMulMapToSnd_rTensor_surjective_iff_baseChange
    (C := C) (π := pi) hpi g r1 r2 b1 b2 i j p.asIdeal.ResidueField]
  exact universalMulMapToSnd_baseChange_surjective_at
    (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j
    p.asIdeal.ResidueField hgamma hchi
    (divCarveIdeal_le_ker_of_tower k
      (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi)
      g r1 r2 b1 b2 i j p.asIdeal.ResidueField)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxSynthPendingDepth 8 in
/-- Relative surjectivity of the degree-`g` universal multiplication map at
independent Euler parameter `gamma ≤ g`. -/
theorem universalMulMapToSnd_surjective_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    Function.Surjective
      (universalMulMapToSnd (C := C) (π := pi)
        hpi g r1 r2 b1 b2 i j) :=
  universalMulMapToSnd_surjective_of_forall_fibre
    (C := C) (π := pi) hpi g r1 r2 b1 b2 i j
    (fun p => universalMulMapToSnd_rTensor_residueField_surjective_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi p)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxSynthPendingDepth 8 in
/-- The universal multiplication span equals the degree-`g` second window at
independent Euler parameter `gamma ≤ g`. -/
theorem universalMulSpan_eq_divUniversalSndWindow_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    universalMulSpan (C := C) (π := pi) hpi g r1 r2 b1 b2 i j =
      (divUniversalSndWindow C pi hpi g r1 r2 b1 b2 i j).toSubmodule :=
  universalMulSpan_eq_divUniversalSndWindow_of_forall_fibre
    (C := C) (π := pi) hpi g r1 r2 b1 b2 i j
    (fun p => universalMulMapToSnd_rTensor_residueField_surjective_at
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j hgamma hchi p)

end Campaign

end AlgebraicGeometry
