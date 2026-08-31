/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The entries ideal of a map into a finite projective module (DD-3, stage 3e)

The reusable **universal vanishing-locus gift** of the DD-3 port
(`informal/spec-dd-3.md` §2; worksheet §3.1): for an `R`-linear map `φ : M →ₗ[R] N`
with `M` finite and `N` finite projective, the ideal of "matrix entries" of `φ` —
the coordinates, through a chosen split embedding `N ↪ R^n`, of the images of chosen
generators of `M` — represents the vanishing of `φ` under base change:

`φ ⊗ S = 0  ↔  entriesIdeal φ ≤ ker (R → S)`,

for every `R`-algebra `S`.  DD-R's `(♦)` two-window multiplication carve consumes this
with `M := H_s ⊗ K` and `N := (H_{M+s} ⊗ R)/K'` over the chart rings of the
Grassmannian pair; the closed-subscheme wrapper is `Picard/VanishingLocus.lean`.

The carrier is module-algebra only (worksheet §1.1 discipline): no scheme appears in
this file.

* `AlgebraicGeometry.Grassmannian.entriesIdeal`: the ideal.
* `AlgebraicGeometry.Grassmannian.baseChange_eq_zero_iff`: **the universal property**.
* `AlgebraicGeometry.Grassmannian.baseChange_entriesIdeal_quotient_eq_zero`: `φ`
  vanishes after base change to `R ⧸ entriesIdeal φ` (the universal witness).
-/

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.Grassmannian

variable {R : Type u} [CommRing R]

section Split

variable (R : Type u) [CommRing R] (N : Type u) [AddCommGroup N] [Module R N]
variable [Module.Finite R N] [Module.Projective R N]

/-- The rank of a chosen finite free module through which the finite projective `N`
splits. -/
noncomputable def splitRank : ℕ :=
  (Module.Finite.exists_comp_eq_id_of_projective R N).choose

/-- The chosen surjection `R^n ↠ N` of the splitting. -/
noncomputable def splitSurj : (Fin (splitRank R N) → R) →ₗ[R] N :=
  (Module.Finite.exists_comp_eq_id_of_projective R N).choose_spec.choose

/-- The chosen section `N ↪ R^n` of the splitting. -/
noncomputable def splitSect : N →ₗ[R] (Fin (splitRank R N) → R) :=
  (Module.Finite.exists_comp_eq_id_of_projective R N).choose_spec.choose_spec.choose

lemma splitSurj_comp_splitSect : splitSurj R N ∘ₗ splitSect R N = LinearMap.id :=
  (Module.Finite.exists_comp_eq_id_of_projective
    R N).choose_spec.choose_spec.choose_spec.2.2

lemma splitSurj_splitSect (y : N) : splitSurj R N (splitSect R N y) = y :=
  LinearMap.congr_fun (splitSurj_comp_splitSect R N) y

variable {N} (S : Type u) [CommRing S] [Algebra R S]

/-- The one-tensor vanishing test through the chosen splitting: `1 ⊗ y` dies in
`S ⊗[R] N` iff every coordinate of the split embedding of `y` dies in `S`. -/
lemma one_tmul_eq_zero_iff (y : N) :
    (1 : S) ⊗ₜ[R] y = (0 : S ⊗[R] N) ↔
      ∀ j, algebraMap R S (splitSect R N y j) = 0 := by
  constructor
  · intro h j
    have h2 : (1 : S) ⊗ₜ[R] (splitSect R N y) = (0 : S ⊗[R] (Fin (splitRank R N) → R)) := by
      have h1 := congrArg (LinearMap.baseChange S (splitSect R N)) h
      rw [LinearMap.baseChange_tmul, map_zero] at h1
      exact h1
    have h3 := congrArg (TensorProduct.piScalarRightHom R S S (Fin (splitRank R N))) h2
    rw [map_zero, TensorProduct.piScalarRightHom_tmul] at h3
    have h4 := congrFun h3 j
    rw [Algebra.smul_def, mul_one] at h4
    exact h4
  · intro h
    have h2 : (1 : S) ⊗ₜ[R] (splitSect R N y)
        = (0 : S ⊗[R] (Fin (splitRank R N) → R)) := by
      apply (TensorProduct.piScalarRight R S S (Fin (splitRank R N))).injective
      rw [map_zero, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
      funext j
      rw [Algebra.smul_def, mul_one, Pi.zero_apply]
      exact h j
    have h3 := congrArg (LinearMap.baseChange S (splitSurj R N)) h2
    rw [LinearMap.baseChange_tmul, map_zero, splitSurj_splitSect] at h3
    exact h3

end Split

section Gens

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

/-- The number of chosen generators of the finite module `M`. -/
noncomputable def genCard : ℕ :=
  (Module.Finite.exists_fin (R := R) (M := M)).choose

/-- The chosen generators of the finite module `M`. -/
noncomputable def gen : Fin (genCard R M) → M :=
  (Module.Finite.exists_fin (R := R) (M := M)).choose_spec.choose

lemma span_range_gen : Submodule.span R (Set.range (gen R M)) = ⊤ :=
  (Module.Finite.exists_fin (R := R) (M := M)).choose_spec.choose_spec

variable {M} {N : Type u} [AddCommGroup N] [Module R N]
variable (S : Type u) [CommRing S] [Algebra R S]

/-- Vanishing of the base change of `φ` is a condition on the chosen generators. -/
lemma baseChange_eq_zero_iff_forall_gen (φ : M →ₗ[R] N) :
    LinearMap.baseChange S φ = 0 ↔
      ∀ i, (1 : S) ⊗ₜ[R] φ (gen R M i) = (0 : S ⊗[R] N) := by
  constructor
  · intro h i
    have h1 := LinearMap.congr_fun h ((1 : S) ⊗ₜ[R] gen R M i)
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply] at h1
    exact h1
  · intro h
    have hall : ∀ m : M, (1 : S) ⊗ₜ[R] φ m = (0 : S ⊗[R] N) := by
      intro m
      have hmem : m ∈ Submodule.span R (Set.range (gen R M)) := by
        rw [span_range_gen]; trivial
      induction hmem using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h i
      | zero => rw [map_zero, TensorProduct.tmul_zero]
      | add x y _ _ hx' hy' => rw [map_add, TensorProduct.tmul_add, hx', hy', add_zero]
      | smul r x _ hx' => rw [map_smul, TensorProduct.tmul_smul, hx', smul_zero]
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, LinearMap.zero_apply]
    | tmul s m =>
      rw [LinearMap.baseChange_tmul, LinearMap.zero_apply,
        show s ⊗ₜ[R] φ m = s • ((1 : S) ⊗ₜ[R] φ m) from by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        hall, smul_zero]
    | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

end Gens

section EntriesIdeal

variable {R : Type u} [CommRing R] {M N : Type u}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]

/-- **The entries ideal** of `φ : M →ₗ[R] N` (`M` finite, `N` finite projective): the
ideal generated by the coordinates, through the chosen split embedding `N ↪ R^n`, of
the images of the chosen generators of `M`.  Its quotient represents the vanishing of
`φ` under base change (`baseChange_eq_zero_iff`). -/
noncomputable def entriesIdeal (φ : M →ₗ[R] N) : Ideal R :=
  Ideal.span {x : R | ∃ (i : Fin (genCard R M)) (j : Fin (splitRank R N)),
    x = splitSect R N (φ (gen R M i)) j}

/-- **The universal property of the entries ideal**: for every `R`-algebra `S`, the
base change `φ ⊗ S` vanishes iff `S` kills the entries ideal. -/
theorem baseChange_eq_zero_iff (φ : M →ₗ[R] N) (S : Type u) [CommRing S] [Algebra R S] :
    LinearMap.baseChange S φ = 0 ↔ entriesIdeal φ ≤ RingHom.ker (algebraMap R S) := by
  rw [baseChange_eq_zero_iff_forall_gen]
  constructor
  · intro h
    rw [entriesIdeal, Ideal.span_le]
    rintro x ⟨i, j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact (one_tmul_eq_zero_iff R S _).mp (h i) j
  · intro h i
    rw [one_tmul_eq_zero_iff R S]
    intro j
    have hmem : splitSect R N (φ (gen R M i)) j ∈ entriesIdeal φ :=
      Ideal.subset_span ⟨i, j, rfl⟩
    exact RingHom.mem_ker.mp (h hmem)

/-- The universal witness: `φ` vanishes after base change to `R ⧸ entriesIdeal φ`. -/
theorem baseChange_entriesIdeal_quotient_eq_zero (φ : M →ₗ[R] N) :
    LinearMap.baseChange (R ⧸ entriesIdeal φ) φ = 0 := by
  rw [baseChange_eq_zero_iff]
  intro x hx
  rw [RingHom.mem_ker, Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

end EntriesIdeal

end AlgebraicGeometry.Grassmannian
