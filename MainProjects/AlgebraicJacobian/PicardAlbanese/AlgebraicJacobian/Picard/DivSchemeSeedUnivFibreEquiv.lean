/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/

import AlgebraicJacobian.Picard.DivSchemeProjectiveBaseChange
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFibreSndRes

/-!
# Fibre reading equivalences for the universal windows

The relative universal windows are projective-quotient submodules.  After a field
base change, the cancelled tensor product identifies them with the corresponding
Grassmannian fibre kernels; the `divFamPhi` dictionary then identifies those kernels
with the function-field windows.  These equivalences are the transport layer for the
DD-R multiplication map.
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
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftFibreEquiv :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
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
  [Algebra (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower k (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower (PairChartRing k g r₁ g r₂ i j)
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]

local notation "RZ" => DivCarveChartRing k
  (windowS_choice π hπ g • fiberWeilDivisor π)
  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
local notation "HS" => ↥(Scheme.divisorSections k
  (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)
local notation "HM" => ↥(Scheme.divisorSections k
  (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)
local notation "HMS" => ↥(Scheme.divisorSections k
  ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)
local notation "N₁" => (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
local notation "N₂" => (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
local notation "KM" => ↥(divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K)
local notation "KMS" => ↥(divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K)

noncomputable local instance instIsIntegralRelCurveFibreEquiv (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveFibreEquiv (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveFibreEquiv (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveFibreEquiv (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

/-! ## The full multiplier dictionary -/

set_option maxHeartbeats 600000 in
-- The full-window dictionary carries the relative-curve base-change instance tower.
set_option synthInstance.maxHeartbeats 300000 in
/-- The `Phi` dictionary identifies the scalar extension of the multiplier window
with the transported fibre multiplier window. -/
noncomputable def divUniversalMultiplierFibreEquiv :
    K ⊗[k] HS ≃ₗ[K] ↥(Scheme.divisorSections K (windowS C K hπ g) ⊤) := by
  let f := (divFamPhi C K π (windowS_choice π hπ g)
      (relThetaPairH1_windowS C hπ g)).codRestrict
      (Scheme.divisorSections K (windowS C K hπ g) ⊤) (fun x => by
        exact divFamPhi_apply_mem C K π (windowS_choice π hπ g)
          (relThetaPairH1_windowS C hπ g) x)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply divFamPhi_injective C K π (windowS_choice π hπ g)
      (relThetaPairH1_windowS C hπ g)
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := exists_divFamPhi_eq C K π (windowS_choice π hπ g)
      (relThetaPairH1_windowS C hπ g) y.property
    exact ⟨x, Subtype.ext hx⟩

@[simp]
theorem divUniversalMultiplierFibreEquiv_apply (x : K ⊗[k] HS) :
    (divUniversalMultiplierFibreEquiv (π := π) C hπ g K x :
        (relCurve C K).functionField) =
      divFamPhi C K π (windowS_choice π hπ g)
        (relThetaPairH1_windowS C hπ g) x :=
  rfl

/-! ## Image equalities for the two fibre windows -/

set_option maxHeartbeats 1000000 in
-- Comparing the universal kernel span with its function-field image is elaboration-heavy.
set_option synthInstance.maxHeartbeats 500000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
theorem map_divFamPhi_fstKernel_eq_fibreWindow :
    Submodule.map
        (divFamPhi C K π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g))
        (LinearMap.ker (Module.Grassmannian.baseChangeMkQ K N₁))
      = divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K := by
  rw [Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare N₁ K,
    Submodule.map_span, ← Set.image_comp]
  simpa only [Function.comp_apply] using
    (divUniversalFibreKM_eq_span C hπ g r₁ r₂ b₁ b₂ i j K).symm

noncomputable def divUniversalSndFibreRead :
    (K ⊗[k] HMS) →ₗ[K] (relCurve C K).functionField :=
  (Scheme.mulLinear K ((msCoherenceUnit C K hπ g :
      (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)).comp
    (divFamPhi C K π (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g))

set_option maxHeartbeats 1200000 in
-- The second-window comparison also unfolds the coherence-unit translation.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
theorem map_divUniversalSndFibreRead_sndKernel_eq_fibreWindow :
    Submodule.map (divUniversalSndFibreRead (π := π) C hπ g K)
        (LinearMap.ker (Module.Grassmannian.baseChangeMkQ K N₂))
      = divUniversalFibreK' C hπ g r₁ r₂ b₂ i j K := by
  rw [Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare N₂ K,
    Submodule.map_span, ← Set.image_comp]
  simpa only [divUniversalSndFibreRead, Function.comp_apply, LinearMap.comp_apply]
    using (divUniversalFibreK'_eq_span C hπ g r₁ r₂ b₁ b₂ i j K).symm

/-! ## The two cancelled fibre-reading equivalences -/

set_option maxHeartbeats 900000 in
-- The composed projective-quotient and window dictionaries need the campaign budget.
set_option synthInstance.maxHeartbeats 500000 in
set_option maxRecDepth 8000 in
noncomputable def divUniversalFstFibreReadEquiv :
    K ⊗[RZ] N₁ ≃ₗ[K] KM := by
  let e0 := Grassmannian.projectiveQuotientWindowFibreEquiv
    (k := k) (R := RZ) (K := K) (N := N₁)
  let e1 := Submodule.equivMapOfInjective
    (divFamPhi C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g))
    (divFamPhi_injective C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g))
    (LinearMap.ker (Module.Grassmannian.baseChangeMkQ K N₁))
  exact e0.trans (e1.trans (LinearEquiv.ofEq _ _
    (map_divFamPhi_fstKernel_eq_fibreWindow
      (π := π) C hπ g r₁ r₂ b₁ b₂ i j K)))

set_option maxHeartbeats 4000000 in
-- Unfolding the cancelled projective-quotient transport on a pure tensor is expensive.
set_option maxRecDepth 20000 in
@[simp]
theorem divUniversalFstFibreReadEquiv_one_tmul (x : N₁) :
    (divUniversalFstFibreReadEquiv (π := π) C hπ g r₁ r₂ b₁ b₂ i j K
        (1 ⊗ₜ[RZ] x) : (relCurve C K).functionField) =
      divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g) (windowCompare RZ K x.1) := by
  rw [windowCompare_eq_cancelBaseChange (k := k) (H := HM) RZ K x.1]
  rfl

set_option maxHeartbeats 1000000 in
-- The target equivalence includes the shifted-window and coherence-unit dictionaries.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
noncomputable def divUniversalSndFibreReadEquiv :
    K ⊗[RZ] N₂ ≃ₗ[K] KMS := by
  let e0 := Grassmannian.projectiveQuotientWindowFibreEquiv
    (k := k) (R := RZ) (K := K) (N := N₂)
  let read := divUniversalSndFibreRead (π := π) C hπ g K
  have hinj : Function.Injective read := by
    intro x y hxy
    apply divFamPhi_injective C K π
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g)
    exact mul_left_cancel₀ (Units.ne_zero (msCoherenceUnit C K hπ g)) hxy
  let e1 := Submodule.equivMapOfInjective read hinj
    (LinearMap.ker (Module.Grassmannian.baseChangeMkQ K N₂))
  exact e0.trans (e1.trans (LinearEquiv.ofEq _ _
    (map_divUniversalSndFibreRead_sndKernel_eq_fibreWindow
      (π := π) C hπ g r₁ r₂ b₁ b₂ i j K)))

set_option maxHeartbeats 4000000 in
-- The shifted-window transport additionally unfolds the coherence-unit dictionary.
set_option maxRecDepth 20000 in
@[simp]
theorem divUniversalSndFibreReadEquiv_one_tmul (x : N₂) :
    (divUniversalSndFibreReadEquiv (π := π) C hπ g r₁ r₂ b₁ b₂ i j K
        (1 ⊗ₜ[RZ] x) : (relCurve C K).functionField) =
      ((msCoherenceUnit C K hπ g : (relCurve C K).functionFieldˣ) :
          (relCurve C K).functionField) *
        divFamPhi C K π (windowM_choice π hπ g + windowS_choice π hπ g)
          (relThetaPairH1_windowMS C π hπ g) (windowCompare RZ K x.1) := by
  rw [windowCompare_eq_cancelBaseChange (k := k) (H := HMS) RZ K x.1]
  rfl

end Campaign

end AlgebraicGeometry
