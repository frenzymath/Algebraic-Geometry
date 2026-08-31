/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Rank-one fibre quotients

If a vector `1 ⊗ s` is nonzero in a one-dimensional fibre `K ⊗[B] M`, then it spans that
fibre.  Consequently, every surjective image of `M` that kills `s` has zero `K`-fibre.

The mapped-submodule form is tailored to an ideal `J ≤ B`: if the fibre of `J` has rank one,
`s ∈ J` survives in that fibre, and a quotient map kills `s`, then the image of `J` in the
quotient has zero residue-field fibre.  This is purely right exactness of tensor product;
neither flatness nor finite generation over `B` is needed at this step.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

namespace RankOneFibre

/-- A surjective image has zero field fibre when every source-fibre vector is a scalar multiple
of `1 ⊗ s`, and the image kills `s`.  The spanning hypothesis also covers the zero-fibre case;
no dimension or nonzero-vector assumption is required. -/
theorem subsingleton_tensor_of_surjective_of_span_singleton
    {B K M N : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (hf : Function.Surjective f) (s : M)
    (hspan : ∀ v : K ⊗[B] M, ∃ c : K, c • ((1 : K) ⊗ₜ[B] s) = v)
    (hfs : f s = 0) :
    Subsingleton (N ⊗[B] K) := by
  have hft : Function.Surjective (f.lTensor K) :=
    LinearMap.lTensor_surjective K hf
  have hzero : ∀ v : K ⊗[B] M, (f.lTensor K) v = 0 := by
    intro v
    obtain ⟨c, hc⟩ := hspan v
    rw [← hc, ← TensorProduct.tmul_eq_smul_one_tmul c s,
      LinearMap.lTensor_tmul, hfs]
    simp
  have hsub : Subsingleton (K ⊗[B] N) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := hft x
    obtain ⟨y', rfl⟩ := hft y
    rw [hzero x', hzero y']
  exact (TensorProduct.comm B N K).toEquiv.subsingleton

/-- A surjective image of a module has zero field fibre if it kills a nonzero vector spanning
the one-dimensional source fibre. -/
theorem subsingleton_tensor_of_surjective_of_finrank_eq_one
    {B K M N : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (hf : Function.Surjective f) (s : M)
    (hfin : Module.finrank K (K ⊗[B] M) = 1)
    (hs : (1 : K) ⊗ₜ[B] s ≠ 0) (hfs : f s = 0) :
    Subsingleton (N ⊗[B] K) := by
  apply subsingleton_tensor_of_surjective_of_span_singleton f hf s
  · intro v
    exact exists_smul_eq_of_finrank_eq_one hfin hs v
  · exact hfs

/-- If a linear map kills a generator of a one-dimensional source fibre, the fibre of its
range is zero. -/
theorem subsingleton_range_tensor_of_finrank_eq_one
    {B K M N : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (s : M)
    (hfin : Module.finrank K (K ⊗[B] M) = 1)
    (hs : (1 : K) ⊗ₜ[B] s ≠ 0) (hfs : f s = 0) :
    Subsingleton ((LinearMap.range f) ⊗[B] K) := by
  apply subsingleton_tensor_of_surjective_of_finrank_eq_one f.rangeRestrict
    (LinearMap.surjective_rangeRestrict f) s hfin hs
  apply Subtype.ext
  exact hfs

/-- Range specialization of `subsingleton_tensor_of_surjective_of_span_singleton`. -/
theorem subsingleton_range_tensor_of_span_singleton
    {B K M N : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (f : M →ₗ[B] N) (s : M)
    (hspan : ∀ v : K ⊗[B] M, ∃ c : K, c • ((1 : K) ⊗ₜ[B] s) = v)
    (hfs : f s = 0) :
    Subsingleton ((LinearMap.range f) ⊗[B] K) := by
  apply subsingleton_tensor_of_surjective_of_span_singleton f.rangeRestrict
    (LinearMap.surjective_rangeRestrict f) s hspan
  apply Subtype.ext
  exact hfs

/-- Let `P` be a submodule whose field fibre is one-dimensional.  If `s ∈ P` survives in
that fibre and `f s = 0`, then the fibre of the image `f(P)` is zero.

For a chart ideal `J` and the quotient map `B → B/(s)`, the conclusion is precisely the
vanishing of the fibre of the image of `J` in `B/(s)`. -/
theorem subsingleton_map_tensor_of_finrank_eq_one
    {B K M N : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (P : Submodule B M) (f : M →ₗ[B] N) (s : M) (hsP : s ∈ P)
    (hfin : Module.finrank K (K ⊗[B] P) = 1)
    (hs : (1 : K) ⊗ₜ[B] (⟨s, hsP⟩ : P) ≠ 0) (hfs : f s = 0) :
    Subsingleton ((P.map f) ⊗[B] K) := by
  rw [← LinearMap.range_domRestrict P f]
  apply subsingleton_range_tensor_of_finrank_eq_one
    (f.domRestrict P) (⟨s, hsP⟩ : P) hfin hs
  simpa using hfs

/-- Mapped-submodule specialization of `subsingleton_tensor_of_surjective_of_span_singleton`.
This is useful when the source ideal fibre may itself be zero. -/
theorem subsingleton_map_tensor_of_span_singleton
    {B K M N : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (P : Submodule B M) (f : M →ₗ[B] N) (s : M) (hsP : s ∈ P)
    (hspan : ∀ v : K ⊗[B] P, ∃ c : K,
      c • ((1 : K) ⊗ₜ[B] (⟨s, hsP⟩ : P)) = v) (hfs : f s = 0) :
    Subsingleton ((P.map f) ⊗[B] K) := by
  rw [← LinearMap.range_domRestrict P f]
  apply subsingleton_range_tensor_of_span_singleton
    (f.domRestrict P) (⟨s, hsP⟩ : P) hspan
  simpa using hfs

/-- Quotienting by a vector that survives and spans a one-dimensional field fibre produces
a quotient with zero field fibre. -/
theorem subsingleton_quotient_span_tensor_of_finrank_eq_one
    {B K M : Type u} [CommRing B] [Field K] [Algebra B K]
    [AddCommGroup M] [Module B M]
    (s : M) (hfin : Module.finrank K (K ⊗[B] M) = 1)
    (hs : (1 : K) ⊗ₜ[B] s ≠ 0) :
    Subsingleton ((M ⧸ Submodule.span B ({s} : Set M)) ⊗[B] K) := by
  apply subsingleton_tensor_of_surjective_of_finrank_eq_one
    (Submodule.span B ({s} : Set M)).mkQ
    (Submodule.mkQ_surjective _) s hfin hs
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_span_singleton_self s

end RankOneFibre

end AlgebraicGeometry
