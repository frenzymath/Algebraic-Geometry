/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Image transport through a scalar-extension equivalence

This file contains the small linear-algebra bridge used by the high-window
fibre model.  An equivalence on the scalar-extended source and target, together
with a commuting square for a map and its base change, transports the image
submodule.  No geometry, finite-dimensionality, or flatness is involved.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

section ImageTransfer

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-! ## The range of a base-changed map -/

/-- Base change commutes with taking the range of a linear map.

The statement is proved here rather than imported from a geometry-specific
module so that the image-conjugacy theorem below remains inexpensive to use.
-/
theorem range_baseChange_linear (f : M →ₗ[R] N) :
    LinearMap.range (LinearMap.baseChange S f) =
      Submodule.baseChange S (LinearMap.range f) := by
  apply le_antisymm
  · rw [LinearMap.range_le_iff_comap, eq_top_iff]
    rintro z -
    induction z with
    | zero => simp
    | tmul a m =>
        rw [Submodule.mem_comap, LinearMap.baseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a
          (LinearMap.mem_range_self f m)
    | add x y hx hy =>
        rw [Submodule.mem_comap, map_add]
        exact Submodule.add_mem _ (Submodule.mem_comap.1 hx)
          (Submodule.mem_comap.1 hy)
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, rfl⟩ := hy
    exact ⟨(1 : S) ⊗ₜ[R] m, by
      rw [LinearMap.baseChange_tmul, TensorProduct.mk_apply]⟩

/-! ## Transport through a conjugacy square -/

/-- The image of `f` after scalar extension, transported through equivalences
on source and target, is exactly the image of the conjugate map `f'`.

The hypothesis is pointwise so callers can discharge it with the naturality
lemma for their chosen fibre equivalences. -/
theorem map_baseChange_range_eq_range_of_conjugate
    (f : M →ₗ[R] N)
    {M' N' : Type u} [AddCommGroup M'] [Module S M']
      [AddCommGroup N'] [Module S N']
    (f' : M' →ₗ[S] N')
    (eM : (S ⊗[R] M) ≃ₗ[S] M')
    (eN : (S ⊗[R] N) ≃ₗ[S] N')
    (hconj : ∀ x : S ⊗[R] M,
      eN (LinearMap.baseChange S f x) = f' (eM x)) :
    Submodule.map eN.toLinearMap
        (Submodule.baseChange S (LinearMap.range f)) =
      LinearMap.range f' := by
  rw [← range_baseChange_linear (S := S) f]
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hy
    change eN (LinearMap.baseChange S f x) ∈ LinearMap.range f'
    rw [hconj]
    exact LinearMap.mem_range_self f' (eM x)
  · rintro z ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := eM.surjective x
    refine ⟨LinearMap.baseChange S f y, ?_, hconj y⟩
    exact LinearMap.mem_range_self (LinearMap.baseChange S f) y

end ImageTransfer

end AlgebraicGeometry
