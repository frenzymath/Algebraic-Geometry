/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowSyzygy

/-!
# Conjugacy transfer for a fibre syzygy presentation

This file is deliberately independent of the high-window geometry.  It packages the
linear algebra used after a fibre model has been constructed: kernel containment for
the field presentation transfers through three base-change equivalences to the
corresponding relative presentation.  The final corollary feeds that containment into
the `liftQ` injectivity criterion from `DivSchemeHighWindowSyzygy`.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

section Conjugacy

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {P M N : Type u}
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {P' M' N' : Type u}
variable [AddCommGroup P'] [Module S P']
variable [AddCommGroup M'] [Module S M']
variable [AddCommGroup N'] [Module S N']

/-- Kernel containment transfers through equivalences conjugating a pair of maps
and their base changes.  The equivalences need not arise from tensor products;
the statement only uses their bijectivity and the two displayed naturality laws.

`hf` conjugates `baseChange S f` to `f'`, while `hd` conjugates `baseChange S d`
to `d'`.  Thus a witness in the fibre range can be pulled back through the
source equivalence and gives a witness in the relative base-change range.
-/
theorem ker_baseChange_le_range_baseChange_of_conjugate
    (f : M →ₗ[R] N) (d : P →ₗ[R] M)
    (f' : M' →ₗ[S] N') (d' : P' →ₗ[S] M')
    (eM : (S ⊗[R] M) ≃ₗ[S] M')
    (eN : (S ⊗[R] N) →ₗ[S] N')
    (eP : (S ⊗[R] P) ≃ₗ[S] P')
    (hf : ∀ x : S ⊗[R] M,
      eN (LinearMap.baseChange S f x) = f' (eM x))
    (hd : ∀ y : S ⊗[R] P,
      eM (LinearMap.baseChange S d y) = d' (eP y))
    (hker : LinearMap.ker f' ≤ LinearMap.range d') :
    LinearMap.ker (LinearMap.baseChange S f) ≤
      LinearMap.range (LinearMap.baseChange S d) := by
  intro x hx
  have hfx' : f' (eM x) = 0 := by
    rw [← hf x, LinearMap.mem_ker.mp hx, map_zero]
  obtain ⟨z, hz⟩ := hker (LinearMap.mem_ker.mpr hfx')
  obtain ⟨y, rfl⟩ := eP.surjective z
  refine ⟨y, ?_⟩
  apply eM.injective
  rw [hd y, hz]

/-- The same transfer followed by the relative `liftQ` criterion.  This is the
generic shape consumed by the high-window relation induction: an independent
fibre boundary presentation proves injectivity of the base-changed
injectivization, without assuming flatness of its target quotient.
-/
theorem liftQ_baseChange_injective_of_conjugate_boundary
    (f : M →ₗ[R] N) (d : P →ₗ[R] M) (hfd : f.comp d = 0)
    (f' : M' →ₗ[S] N') (d' : P' →ₗ[S] M')
    (eM : (S ⊗[R] M) ≃ₗ[S] M')
    (eN : (S ⊗[R] N) →ₗ[S] N')
    (eP : (S ⊗[R] P) ≃ₗ[S] P')
    (hf : ∀ x : S ⊗[R] M,
      eN (LinearMap.baseChange S f x) = f' (eM x))
    (hd : ∀ y : S ⊗[R] P,
      eM (LinearMap.baseChange S d y) = d' (eP y))
    (hker : LinearMap.ker f' ≤ LinearMap.range d') :
    Function.Injective
      (LinearMap.baseChange S ((LinearMap.ker f).liftQ f le_rfl)) := by
  exact liftQ_baseChange_injective_of_boundary f d hfd S
    (ker_baseChange_le_range_baseChange_of_conjugate
      f d f' d' eM eN eP hf hd hker)

/-- The conjugate-boundary criterion in the right-tensor spelling used by the
high-window syzygy predicate. -/
theorem liftQ_rTensor_injective_of_conjugate_boundary
    (f : M →ₗ[R] N) (d : P →ₗ[R] M) (hfd : f.comp d = 0)
    (f' : M' →ₗ[S] N') (d' : P' →ₗ[S] M')
    (eM : (S ⊗[R] M) ≃ₗ[S] M')
    (eN : (S ⊗[R] N) →ₗ[S] N')
    (eP : (S ⊗[R] P) ≃ₗ[S] P')
    (hf : ∀ x : S ⊗[R] M,
      eN (LinearMap.baseChange S f x) = f' (eM x))
    (hd : ∀ y : S ⊗[R] P,
      eM (LinearMap.baseChange S d y) = d' (eP y))
    (hker : LinearMap.ker f' ≤ LinearMap.range d') :
    Function.Injective
      (((LinearMap.ker f).liftQ f le_rfl).rTensor S) := by
  apply (LinearMap.lTensor_inj_iff_rTensor_inj
    (M := S) (f := (LinearMap.ker f).liftQ f le_rfl)).mp
  rw [← LinearMap.baseChange_eq_ltensor]
  exact liftQ_baseChange_injective_of_conjugate_boundary
    f d hfd f' d' eM eN eP hf hd hker

end Conjugacy

end AlgebraicGeometry
