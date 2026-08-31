/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import AlgebraicJacobian.Picard.DivSchemeProjectiveBaseChange

/-!
# Projective-quotient fibre models in an arbitrary ambient module

A submodule with projective quotient base-changes without a flatness hypothesis.
After choosing an equivalence from the base-changed ambient module to a concrete
fibre model, this file packages the induced equivalence onto the corresponding
image submodule and records its compatibility with the ambient inclusion.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry.Grassmannian

variable {R S M V : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup V] [Module S V]

/-- Transport the scalar extension of a projective-quotient submodule through an
equivalence of ambient modules. -/
noncomputable def projectiveQuotientFibreModelEquiv (N : Submodule R M)
    [Module.Projective R (M ⧸ N)] (e : S ⊗[R] M ≃ₗ[S] V) (W : Submodule S V)
    (hW : Submodule.map e.toLinearMap (N.baseChange S) = W) :
    S ⊗[R] N ≃ₗ[S] W :=
  (projectiveQuotientBaseChangeEquiv (S := S) N).trans
    ((Submodule.equivMapOfInjective e.toLinearMap e.injective (N.baseChange S)).trans
      (LinearEquiv.ofEq _ _ hW))

/-- The fibre-model equivalence is the restriction of the chosen ambient
equivalence after scalar-extending the inclusion of `N`. -/
@[simp]
theorem projectiveQuotientFibreModelEquiv_coe (N : Submodule R M)
    [Module.Projective R (M ⧸ N)] (e : S ⊗[R] M ≃ₗ[S] V) (W : Submodule S V)
    (hW : Submodule.map e.toLinearMap (N.baseChange S) = W) (x : S ⊗[R] N) :
    ((projectiveQuotientFibreModelEquiv N e W hW x : W) : V) =
      e (LinearMap.baseChange S N.subtype x) :=
  rfl

end AlgebraicGeometry.Grassmannian
