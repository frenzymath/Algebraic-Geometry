/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.FibreSurjective
import AlgebraicJacobian.Picard.DivSchemeSeedUnivMulSpan

/-!
# Fibre-to-relative persistence for the universal multiplication span

The only geometric input left implicit here is surjectivity of the universal
product map on every residue-field fibre.  Finite-module Nakayama then makes
the map relatively surjective, equivalently identifies its range with the
universal second window.
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

noncomputable local instance instOverCleftMulSpanClose :
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
local notation "K₂" => ↥(divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule

/-- The residue-fibre premise can equivalently be written with the usual
`baseChange` (left-tensor) orientation. -/
theorem universalMulMapToSnd_rTensor_surjective_iff_baseChange
    (K : Type u) [CommRing K] [Algebra RZ K] :
    Function.Surjective
        ((universalMulMapToSnd (hπ := hπ) g r₁ r₂ b₁ b₂ i j).rTensor K) ↔
      Function.Surjective
        ((universalMulMapToSnd (hπ := hπ) g r₁ r₂ b₁ b₂ i j).baseChange K) := by
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_surj_iff_rTensor_surj]

/-- Residue-field surjectivity of the universal product map persists over the
whole carve-chart ring. -/
theorem universalMulMapToSnd_surjective_of_forall_fibre
    (hfib : ∀ p : PrimeSpectrum RZ,
      Function.Surjective
        ((universalMulMapToSnd (hπ := hπ) g r₁ r₂ b₁ b₂ i j).rTensor
          p.asIdeal.ResidueField)) :
    Function.Surjective (universalMulMapToSnd (hπ := hπ) g r₁ r₂ b₁ b₂ i j) := by
  letI := finite_universalMulSource (hπ := hπ) g r₁ r₂ b₁ b₂ i j
  letI := (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).finite_quotient
  letI := (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).projective_quotient
  letI : Module.Finite RZ K₂ :=
    finite_submodule_of_projective_quotient
      (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
  exact AlgebraicJacobian.RigidEngine.surjective_of_forall_rTensor_residueField_surjective
    (universalMulMapToSnd (hπ := hπ) g r₁ r₂ b₁ b₂ i j) hfib

/-- The relative persistence conclusion: fibrewise spanning makes the finite
universal multiplication span equal the universal second window. -/
theorem universalMulSpan_eq_divUniversalSndWindow_of_forall_fibre
    (hfib : ∀ p : PrimeSpectrum RZ,
      Function.Surjective
        ((universalMulMapToSnd (hπ := hπ) g r₁ r₂ b₁ b₂ i j).rTensor
          p.asIdeal.ResidueField)) :
    universalMulSpan (hπ := hπ) g r₁ r₂ b₁ b₂ i j
      = (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule := by
  refine le_antisymm (universalMulSpan_le (hπ := hπ) g r₁ r₂ b₁ b₂ i j) ?_
  intro x hx
  obtain ⟨v, hv⟩ :=
    universalMulMapToSnd_surjective_of_forall_fibre (hπ := hπ) g r₁ r₂ b₁ b₂ i j hfib
      ⟨x, hx⟩
  rw [universalMulSpan]
  exact LinearMap.mem_range.mpr ⟨v, congrArg Subtype.val hv⟩

end AlgebraicGeometry
