/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeMulIdealBridge

/-!
# Ideal spans from a finite multiplication presentation

`DivSchemeMulIdealBridge` uses a tensor-product source.  The universal
construction in the representability campaign is instead presented by a finite
component map `ι → K`.  These lemmas are the same ideal argument in that
source shape.  They prove the one-sided inclusion without any flatness or
purity assumption, and expose the exact finite unit-generation hypothesis for
the reverse inclusion.
-/

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

namespace IdealPurity

variable {R B K K' : Type u} {ι : Type v}
variable [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup K'] [Module R K']
variable [Fintype ι]

private theorem finite_mul_read_mem_span
    (m : ι → B) (r : K →ₗ[R] B) (x : ι → K) :
    (∑ t, m t * r (x t)) ∈ Ideal.span (Set.range r) := by
  classical
  exact Ideal.sum_mem _ fun t _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x t, rfl⟩)

/-- A surjective finite-component multiplication presentation gives the
second-reading ideal inclusion. -/
theorem span_range_read_le_of_surjective_finite_mul
    (m : ι → B) (r : K →ₗ[R] B) (r' : K' →ₗ[R] B)
    (μ : (ι → K) →ₗ[R] K')
    (hsurj : Function.Surjective μ)
    (hread : ∀ x, r' (μ x) = ∑ t, m t * r (x t)) :
    Ideal.span (Set.range r') ≤ Ideal.span (Set.range r) := by
  classical
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := hsurj y
  rw [hread]
  exact finite_mul_read_mem_span (R := R) m r x

/-- If the multiplier readings generate `1` by a finite coefficient
combination, every first-window reading is in the second-reading ideal. -/
theorem span_range_read_le_of_finite_unit_generation
    (m : ι → B) (r : K →ₗ[R] B) (r' : K' →ₗ[R] B)
    (μ : (ι → K) →ₗ[R] K')
    (hread : ∀ x, r' (μ x) = ∑ t, m t * r (x t))
    (hunit : ∃ c : ι → B, ∑ t, c t * m t = 1) :
    Ideal.span (Set.range r) ≤ Ideal.span (Set.range r') := by
  classical
  obtain ⟨c, hc⟩ := hunit
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  rw [← one_mul (r k), ← hc, Finset.sum_mul]
  apply Ideal.sum_mem
  intro t _
  have hsingle : r' (μ (Pi.single t k)) = m t * r k := by
    rw [hread]
    rw [Finset.sum_eq_single t
      (fun x _ hxt => by simp [hxt])
      (fun h => absurd (Finset.mem_univ t) h)]
    simp
  rw [mul_assoc, ← hsingle]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span
    ⟨μ (Pi.single t k), rfl⟩)

/-- Equality of the two genuine reading ideals from surjective finite
multiplication and explicit unit generation by the multiplier readings. -/
theorem span_range_read_eq_of_surjective_finite_mul_of_unit
    (m : ι → B) (r : K →ₗ[R] B) (r' : K' →ₗ[R] B)
    (μ : (ι → K) →ₗ[R] K')
    (hsurj : Function.Surjective μ)
    (hread : ∀ x, r' (μ x) = ∑ t, m t * r (x t))
    (hunit : ∃ c : ι → B, ∑ t, c t * m t = 1) :
    Ideal.span (Set.range r') = Ideal.span (Set.range r) := by
  apply le_antisymm
  · exact span_range_read_le_of_surjective_finite_mul
      (R := R) m r r' μ hsurj hread
  · exact span_range_read_le_of_finite_unit_generation
      (R := R) m r r' μ hread hunit

end IdealPurity

end AlgebraicGeometry
