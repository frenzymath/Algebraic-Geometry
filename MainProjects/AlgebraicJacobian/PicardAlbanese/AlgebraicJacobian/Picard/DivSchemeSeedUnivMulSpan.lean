/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUniv
import AlgebraicJacobian.Picard.DivSchemeClassify

/-!
# The universal multiplication span

This file records the relative product map from the multiplier window and the
universal first window into the universal shifted window.  The map is written
using a finite basis of the multiplier space; its range is therefore the
finite `R_Z`-linear multiplication span.  The carve containment is proved in
the companion theorem below.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftMulSpan :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
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

local notation "RZ" => DivCarveChartRing k
  (windowS_choice π hπ g • fiberWeilDivisor π)
  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
local notation "HS" => ↥(Scheme.divisorSections k
  (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)
local notation "HM" => ↥(Scheme.divisorSections k
  (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)
local notation "HMS" => ↥(Scheme.divisorSections k
  ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)
local notation "K₁" => ↥(divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
local notation "K₂" => ↥(divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule

/-! ## The finite source and its multiplication map -/

/-- A finite free-indexed source for the universal multiplication span. -/
noncomputable abbrev universalMulSource : Type u := Fin (Module.finrank k HS) → K₁

/-- The sum of all multiplier-basis translates of the first universal window. -/
noncomputable def universalMulMap :
    universalMulSource (hπ := hπ) g r₁ r₂ b₁ b₂ i j →ₗ[RZ]
    RZ ⊗[k] HMS :=
  ∑ t : Fin (Module.finrank k HS),
    (LinearMap.baseChange RZ (windowShiftMul hπ g ((Module.finBasis k HS) t))).comp
      ((divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule.subtype.comp
        (LinearMap.proj t))

/-- The relative submodule spanned by all products of a multiplier-window
basis vector with the universal first window. -/
noncomputable def universalMulSpan : Submodule RZ (RZ ⊗[k] HMS) :=
  LinearMap.range (universalMulMap (hπ := hπ) g r₁ r₂ b₁ b₂ i j)

theorem finite_universalMulSource :
    Module.Finite RZ
      (universalMulSource (hπ := hπ) g r₁ r₂ b₁ b₂ i j) := by
  letI := (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).finite_quotient
  letI := (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).projective_quotient
  letI : Module.Finite RZ K₁ :=
    finite_submodule_of_projective_quotient
      (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
  infer_instance

/-! ## Carve containment -/

/-- The coordinate universal pair satisfies the carve over its chart ring. -/
private theorem universal_coordinate_carve (a : HS) :
    carvePairArrow
        (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂ a)
        (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule
        (divUniversalSnd k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule = 0 := by
  change carvePairArrow
      (divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂ a)
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ RZ
        (pairTautFst k g r₁ r₂ i j).toSubmodule))
      (LinearMap.ker (Module.Grassmannian.baseChangeMkQ RZ
        (pairTautSnd k g r₁ r₂ i j).toSubmodule)) = 0
  exact divUniversal_carve k
    (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j RZ a

/-- The universal pair in the transported window ambients satisfies the
`windowShiftMul` carve. -/
theorem universal_window_carve (a : HS) :
    carvePairArrow (windowShiftMul hπ g a)
      (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
      (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule = 0 := by
  let e₁ : (Fin r₁ → k) ≃ₗ[k] HM := b₁.equivFun.symm
  let e₂ : (Fin r₂ → k) ≃ₗ[k] HMS :=
    b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g)
  let μ : (Fin r₁ → k) →ₗ[k] (Fin r₂ → k) :=
    divCarveMul k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) r₁ r₂ b₁ b₂ a
  have hμ : e₂.toLinearMap ∘ₗ μ ∘ₗ e₁.symm.toLinearMap = windowShiftMul hπ g a := by
    refine LinearMap.ext fun v => ?_
    simp [e₁, e₂, μ, divCarveMul, windowShiftMul, LinearMap.comp_apply]
    apply Subtype.ext
    rfl
  have hcoord := universal_coordinate_carve
    (C := C) (π := π) (hπ := hπ) g r₁ r₂ b₁ b₂ i j a
  have htransport :=
    (Grassmannian.carvePairArrow_map_baseChange_eq_zero_iff e₁ e₂ μ
      (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule
      (divUniversalSnd k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule).mpr hcoord
  rw [hμ] at htransport
  exact htransport

/-! ## The span containment -/

theorem universalMulMap_range_le :
    LinearMap.range
        (universalMulMap (hπ := hπ) g r₁ r₂ b₁ b₂ i j) ≤
      (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule := by
  rintro _ ⟨v, rfl⟩
  rw [universalMulMap]
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro t ht
  have hcarve := carvePairArrow_eq_zero_iff (R := RZ)
    (windowShiftMul hπ g ((Module.finBasis k HS) t))
    (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
    (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule |>.mp
    (universal_window_carve
      (C := C) (π := π) (hπ := hπ) g r₁ r₂ b₁ b₂ i j ((Module.finBasis k HS) t))
  exact hcarve (v t).1 (v t).2

theorem universalMulSpan_le :
    universalMulSpan (hπ := hπ) g r₁ r₂ b₁ b₂ i j ≤
      (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule := by
  exact universalMulMap_range_le (hπ := hπ) g r₁ r₂ b₁ b₂ i j

/-- The product map corestricted to the universal second window.  Its residue-
field surjectivity is the only remaining input needed by
`RigidEngine.surjective_of_forall_rTensor_residueField_surjective`. -/
noncomputable def universalMulMapToSnd :
    universalMulSource (hπ := hπ) g r₁ r₂ b₁ b₂ i j →ₗ[RZ] K₂ :=
  (universalMulMap (hπ := hπ) g r₁ r₂ b₁ b₂ i j).codRestrict _ fun v =>
    universalMulMap_range_le (hπ := hπ) g r₁ r₂ b₁ b₂ i j
      (LinearMap.mem_range_self _ v)

theorem finite_universalMulSpan :
    Module.Finite RZ
      ↥(universalMulSpan (hπ := hπ) g r₁ r₂ b₁ b₂ i j) := by
  letI := finite_universalMulSource (hπ := hπ) g r₁ r₂ b₁ b₂ i j
  infer_instance

end AlgebraicGeometry
