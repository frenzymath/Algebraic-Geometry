/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 as described in the LICENSE file.
-/

import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change of a finite component sum

This is the small algebraic tensor identity used by the universal multiplication
span.  Keeping it independent of the large window types prevents elaboration of
the geometric source from obscuring the actual finite-product calculation.
-/

set_option autoImplicit false
set_option quotPrecheck false

universe u v

open scoped TensorProduct

namespace AlgebraicGeometry

variable {R K M N : Type u} [CommRing R] [CommRing K] [Algebra R K]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable {ι : Type v} [Fintype ι]

/-- The sum of component maps on a finite product. -/
noncomputable def finiteComponentSum (f : ι → M →ₗ[R] N) :
    (ι → M) →ₗ[R] N := by
  classical
  exact ∑ t : ι, (f t).comp (LinearMap.proj t)

/-- A finite component sum evaluated on a vector supported in one coordinate
is that component map. -/
@[simp]
theorem finiteComponentSum_piSingle [DecidableEq ι]
    (f : ι → M →ₗ[R] N) (i : ι) (x : M) :
    finiteComponentSum f (Pi.single i x) = f i x := by
  classical
  rw [finiteComponentSum, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Base change commutes with a finite component sum, after tensoring the
product source into its component fibres with `TensorProduct.piRightHom`. -/
theorem baseChange_finiteComponentSum (f : ι → M →ₗ[R] N) :
    LinearMap.baseChange K (finiteComponentSum f) =
      (∑ t : ι,
        (LinearMap.baseChange K (f t)).comp
          ((LinearMap.proj t) :
            (ι → (K ⊗[R] M)) →ₗ[K] (K ⊗[R] M))) ∘ₗ
        TensorProduct.piRightHom R K K (fun _ : ι => M) := by
  classical
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, Finset.sum_add_distrib]
  | tmul a v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.piRightHom_tmul,
        finiteComponentSum, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply]
      rw [TensorProduct.tmul_sum]

/-- Surjectivity of the component sum implies surjectivity of the base-changed
sum.  The finite-product equivalence supplies the preimage in the tensor
product source. -/
theorem surjective_baseChange_finiteComponentSum
    (f : ι → M →ₗ[R] N)
    (hsurj : Function.Surjective
      (∑ t : ι,
        (LinearMap.baseChange K (f t)).comp
          ((LinearMap.proj t) :
            (ι → (K ⊗[R] M)) →ₗ[K] (K ⊗[R] M)))) :
    Function.Surjective (LinearMap.baseChange K (finiteComponentSum f)) := by
  classical
  intro y
  obtain ⟨w, hw⟩ := hsurj y
  let e := TensorProduct.piRight R K K (fun _ : ι => M)
  refine ⟨e.symm w, ?_⟩
  rw [baseChange_finiteComponentSum]
  change
    (∑ t : ι,
      (LinearMap.baseChange K (f t)).comp
        ((LinearMap.proj t) :
          (ι → (K ⊗[R] M)) →ₗ[K] (K ⊗[R] M)))
      (TensorProduct.piRightHom R K K (fun _ : ι => M) (e.symm w)) = y
  have he : TensorProduct.piRightHom R K K (fun _ : ι => M) (e.symm w) = w := by
    change e (e.symm w) = w
    exact e.apply_symm_apply w
  rw [he]
  simpa only [LinearMap.coe_sum, LinearMap.coe_comp, Function.comp_apply] using hw

end AlgebraicGeometry
