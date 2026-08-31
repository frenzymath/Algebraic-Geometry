/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Finite products of localizations of a commutative ring

For a commutative ring `A` and a finite covering family of basic opens — elements
`f i : A` with `Ideal.span (Set.range f) = ⊤` — the product `∀ i, S i` of localizations
`S i := A[1/f i]` is the algebraic incarnation of a finite affine cover of `Spec A`.  This
file provides the toolkit used by the Čech–Picard dictionary
(`AlgebraicJacobian.Picard.PicAffine`) to run faithfully flat descent along such covers:

* `AlgHom.ext_of_isLocalization_pi` — **the pi-ext lemma**: two `A`-algebra maps out of a
  finite product of localizations of `A` agreeing on the coordinate idempotents
  `Pi.single i 1` are equal.  This makes every diagram of algebra maps out of such
  products commute by pure bookkeeping, replacing all naturality arguments downstream.
* `Module.FaithfullyFlat.pi_of_span_eq_top` — a finite product of `Away (f i)`
  localizations along a covering family (`span (range f) = ⊤`) is faithfully flat.
* `Algebra.TensorProduct.piRightAlgEquiv`, `piLeftAlgEquiv`, `piPiAlgEquiv` — tensor
  products distribute over finite products of algebras, as `A`-algebra equivalences, with
  pure-tensor `simp` formulas.
* `IsLocalization.Away.algHomOfDvd` — the canonical map `A[1/f] →ₐ[A] A[1/g]` for `f ∣ g`
  (any two such maps are equal: `IsLocalization.algHom_subsingleton`).
* `IsLocalization.Away.tensor`, `IsLocalization.Away.tensorEquiv` — the tensor product of
  `Away f` and `Away g` localizations is an `Away (f * g)` localization, hence canonically
  isomorphic to any other model of it.

Everything is elementary commutative algebra; the file is deliberately scheme-free and
shaped for mathlib.
-/

universe u v w u₂

open TensorProduct

section PiExt

variable {A : Type u} [CommRing A] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
variable {C : Type u} [CommRing C] [Algebra A C]

/-- **The pi-ext lemma.**  Two `A`-algebra maps out of a finite product of localizations
of `A` that agree on the coordinate idempotents `Pi.single i 1` are equal.

Proof sketch: fix `i` and let `ε := φ (Pi.single i 1)`, an idempotent with the same value
for `ψ`.  The map `y ↦ φ (Pi.single i y)`, corestricted to the quotient
`C ⧸ Ideal.span {1 - ε}`, is a *unital* `A`-algebra map out of the localization `S i`
(unitality is `φ (single i 1) = ε ↦ 1`), hence agrees with the one for `ψ` by
`IsLocalization.ringHom_ext`.  Therefore `φ (single i y) - ψ (single i y) ∈ span {1 - ε}`;
multiplying by `ε` and using `φ (single i y) * ε = φ (single i y)` (from
`single i y * single i 1 = single i y`) gives `φ (single i y) = ψ (single i y)`.  Conclude
by `x = ∑ i, Pi.single i (x i)` (`Finset.univ_sum_single`). -/
theorem AlgHom.ext_of_isLocalization_pi (M : ι → Submonoid A)
    [∀ i, IsLocalization (M i) (S i)] {φ ψ : (∀ i, S i) →ₐ[A] C}
    (h : ∀ i, φ (Pi.single i 1) = ψ (Pi.single i 1)) : φ = ψ := by
  have key : ∀ (i : ι) (y : S i), φ (Pi.single i y) = ψ (Pi.single i y) := by
    intro i y
    set ε : C := φ (Pi.single i 1) with hε
    have hψε : ψ (Pi.single i 1) = ε := (h i).symm
    have hidem : ε * ε = ε := by
      rw [hε, ← map_mul, ← Pi.single_mul, one_mul]
    -- the class of `ε` in `C ⧸ (1 - ε)` is `1`
    have hmkε : Ideal.Quotient.mk (Ideal.span {1 - ε}) ε = 1 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - ε})), Ideal.Quotient.eq]
      simpa using (Ideal.span {1 - ε}).neg_mem (Ideal.subset_span (Set.mem_singleton _))
    -- `y ↦ mk (φ (Pi.single i y))` is a *unital* ring hom out of the localization `S i`
    let Φ : S i →+* C ⧸ Ideal.span {1 - ε} :=
      { toFun := fun z => Ideal.Quotient.mk (Ideal.span {1 - ε}) (φ (Pi.single i z))
        map_one' := by rw [← hε]; exact hmkε
        map_mul' := fun z w => by
          rw [← map_mul (Ideal.Quotient.mk (Ideal.span {1 - ε})), ← map_mul φ, ← Pi.single_mul]
        map_zero' := by simp
        map_add' := fun z w => by
          rw [← map_add (Ideal.Quotient.mk (Ideal.span {1 - ε})), ← map_add φ, ← Pi.single_add] }
    let Ψ : S i →+* C ⧸ Ideal.span {1 - ε} :=
      { toFun := fun z => Ideal.Quotient.mk (Ideal.span {1 - ε}) (ψ (Pi.single i z))
        map_one' := by rw [hψε]; exact hmkε
        map_mul' := fun z w => by
          rw [← map_mul (Ideal.Quotient.mk (Ideal.span {1 - ε})), ← map_mul ψ, ← Pi.single_mul]
        map_zero' := by simp
        map_add' := fun z w => by
          rw [← map_add (Ideal.Quotient.mk (Ideal.span {1 - ε})), ← map_add ψ, ← Pi.single_add] }
    -- they agree on `A`, hence on all of the localization `S i`
    have hcomp : Φ.comp (algebraMap A (S i)) = Ψ.comp (algebraMap A (S i)) := by
      ext a
      change Ideal.Quotient.mk (Ideal.span {1 - ε}) (φ (Pi.single i (algebraMap A (S i) a)))
        = Ideal.Quotient.mk (Ideal.span {1 - ε}) (ψ (Pi.single i (algebraMap A (S i) a)))
      have hsa : (Pi.single i (algebraMap A (S i) a) : ∀ j, S j)
          = algebraMap A (∀ j, S j) a * Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      rw [hsa, map_mul φ, map_mul ψ, AlgHom.commutes, AlgHom.commutes, ← hε, hψε]
    have hΦΨ : Φ = Ψ := IsLocalization.ringHom_ext (M := M i) hcomp
    have hmem : φ (Pi.single i y) - ψ (Pi.single i y) ∈ Ideal.span {1 - ε} :=
      Ideal.Quotient.eq.mp (DFunLike.congr_fun hΦΨ y)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    -- multiply the membership witness by `ε` and use `φ (single i y) * ε = φ (single i y)`
    have hφy : φ (Pi.single i y) * ε = φ (Pi.single i y) := by
      rw [hε, ← map_mul, ← Pi.single_mul, mul_one]
    have hψy : ψ (Pi.single i y) * ε = ψ (Pi.single i y) := by
      rw [← hψε, ← map_mul, ← Pi.single_mul, mul_one]
    have hzero : (φ (Pi.single i y) - ψ (Pi.single i y)) * ε = 0 := by
      rw [← hc, mul_assoc, sub_mul, one_mul, hidem, sub_self, mul_zero]
    rw [sub_mul, hφy, hψy] at hzero
    exact sub_eq_zero.mp hzero
  refine AlgHom.ext fun x => ?_
  calc φ x = φ (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, φ (Pi.single i (x i)) := map_sum φ _ Finset.univ
    _ = ∑ i, ψ (Pi.single i (x i)) := Finset.sum_congr rfl fun i _ => key i (x i)
    _ = ψ (∑ i, Pi.single i (x i)) := (map_sum ψ _ Finset.univ).symm
    _ = ψ x := by rw [Finset.univ_sum_single]

end PiExt

section FaithfullyFlat

variable {A : Type u} [CommRing A] {ι : Type v} [Fintype ι]
variable {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]

/-- A finite product of flat modules is flat. -/
theorem Module.Flat.pi_of_finite [∀ i, Module.Flat A (S i)] :
    Module.Flat A (∀ i, S i) :=
  -- transport `Module.Flat.dfinsupp` along `DFinsupp.linearEquivFunOnFintype`
  letI := Classical.decEq ι
  Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A) (M := S)).symm

/-- **A finite product of localizations along a covering family is faithfully flat**:
if `Ideal.span (Set.range f) = ⊤`, then `∀ i, A[1/f i]` is a faithfully flat `A`-algebra.

Proof sketch: flatness is `IsLocalization.flat` plus `Module.Flat.pi_of_finite`.  For
faithfulness use `Module.FaithfullyFlat.iff_flat_and_proper_ideal`: a proper ideal `I`
lies in a maximal `m`, and since `span (range f) = ⊤` some `f i ∉ m`.  If
`I • (⊤ : Submodule A (∀ i, S i)) = ⊤` then, applying the (surjective) coordinate
projection and `Submodule.map_smul''`, also `I • (⊤ : Submodule A (S i)) = ⊤`, hence
`m • ⊤ = ⊤`.  Map along the ring map `χ : S i →+* A ⧸ m` obtained from
`IsLocalization.Away.lift` (the class of `f i` in the field `A ⧸ m` is nonzero, hence
invertible): the equation `1 = ∑ aₖ • sₖ` with `aₖ ∈ m` maps to `1 = 0`, a
contradiction. -/
theorem Module.FaithfullyFlat.pi_of_span_eq_top (f : ι → A)
    [∀ i, IsLocalization.Away (f i) (S i)] (hspan : Ideal.span (Set.range f) = ⊤) :
    Module.FaithfullyFlat A (∀ i, S i) := by
  haveI : ∀ i, Module.Flat A (S i) := fun i =>
    IsLocalization.flat (S i) (Submonoid.powers (f i))
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨Module.Flat.pi_of_finite, fun I hI hIT => ?_⟩
  obtain ⟨m, hmax, hIm⟩ := Ideal.exists_le_maximal I hI
  -- since `span (range f) = ⊤`, some `f i` avoids the maximal ideal `m`
  obtain ⟨i, hfi⟩ : ∃ i, f i ∉ m := by
    by_contra hall
    have hle : Ideal.span (Set.range f) ≤ m :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i =>
        not_not.mp fun hn => hall ⟨i, hn⟩)
    rw [hspan, top_le_iff] at hle
    exact hmax.ne_top hle
  -- push `I • ⊤ = ⊤` through the (surjective) coordinate projection, enlarge `I` to `m`
  have hproj : I • (⊤ : Submodule A (S i)) = ⊤ := by
    have hmap := congrArg
      (Submodule.map (LinearMap.proj i : (∀ j, S j) →ₗ[A] S i)) hIT
    rwa [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] at hmap
  have hm : m • (⊤ : Submodule A (S i)) = ⊤ := by
    have hmono := Submodule.smul_mono_left (N := (⊤ : Submodule A (S i))) hIm
    rw [hproj] at hmono
    exact top_le_iff.mp hmono
  -- the residue-field character `S i →+* A ⧸ m` kills `m • ⊤` but sends `1` to `1`
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have hfm : Ideal.Quotient.mk m (f i) ≠ 0 := fun h0 =>
    hfi (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hunit : ∀ y : Submonoid.powers (f i), IsUnit (Ideal.Quotient.mk m (y : A)) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := hy
    change IsUnit (Ideal.Quotient.mk m (f i ^ n))
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr hfm).pow n
  have hlift : ∀ x ∈ m • (⊤ : Submodule A (S i)),
      IsLocalization.lift (M := Submonoid.powers (f i)) (S := S i) hunit x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun a ha s _ => ?_) (fun u v hu hv => ?_)
    · rw [Algebra.smul_def, map_mul, IsLocalization.lift_eq,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
    · rw [map_add, hu, hv, add_zero]
  have h1 : IsLocalization.lift (M := Submonoid.powers (f i)) (S := S i) hunit (1 : S i) = 0 :=
    hlift 1 (by rw [hm]; exact Submodule.mem_top)
  rw [map_one] at h1
  exact one_ne_zero h1

end FaithfullyFlat

namespace Algebra.TensorProduct

variable (A : Type u) [CommRing A] {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι]
variable (N : Type u₂) [CommRing N] [Algebra A N]
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]

/-- Tensoring distributes over finite products of algebras, on the right: the `A`-algebra
equivalence `N ⊗[A] (∀ i, S i) ≃ₐ[A] ∀ i, N ⊗[A] S i`.  This is
`TensorProduct.piRight` upgraded to algebras. -/
noncomputable def piRightAlgEquiv : (N ⊗[A] ∀ i, S i) ≃ₐ[A] ∀ i, N ⊗[A] S i :=
  -- `map_mul` is checked by two rounds of `TensorProduct.induction_on` (both sides are
  -- bilinear); on pure tensors it is componentwise `tmul_mul_tmul`.
  AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight A A N S)
    (by
      funext i
      simp [Algebra.TensorProduct.one_def])
    (fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
      | tmul a s =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
        | tmul b t =>
          funext i
          simp [Algebra.TensorProduct.tmul_mul_tmul])

@[simp]
lemma piRightAlgEquiv_tmul (x : N) (s : ∀ i, S i) :
    piRightAlgEquiv A N S (x ⊗ₜ s) = fun i => x ⊗ₜ s i :=
  rfl

variable [Fintype κ] [DecidableEq κ] (T : κ → Type u) [∀ j, CommRing (T j)]
  [∀ j, Algebra A (T j)]

/-- Tensoring distributes over finite products of algebras, on the left. -/
noncomputable def piLeftAlgEquiv : ((∀ i, S i) ⊗[A] N) ≃ₐ[A] ∀ i, S i ⊗[A] N :=
  -- `comm`, then `piRightAlgEquiv`, then componentwise `comm`.
  (Algebra.TensorProduct.comm A _ _).trans
    ((piRightAlgEquiv A N S).trans
      (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.comm A _ _))

@[simp]
lemma piLeftAlgEquiv_tmul (s : ∀ i, S i) (x : N) :
    piLeftAlgEquiv A N S (s ⊗ₜ x) = fun i => s i ⊗ₜ x :=
  rfl

/-- Uncurrying a doubly-indexed family of `A`-algebras, as an `A`-algebra equivalence
(implementation helper for `piPiAlgEquiv`). -/
private def piProdAlgEquiv (R : ι → κ → Type u) [∀ i j, CommRing (R i j)]
    [∀ i j, Algebra A (R i j)] : (∀ i, ∀ j, R i j) ≃ₐ[A] ∀ p : ι × κ, R p.1 p.2 where
  toFun x p := x p.1 p.2
  invFun x i j := x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The tensor product of two finite products of `A`-algebras is the finite product of
the pairwise tensor products, as an `A`-algebra equivalence. -/
noncomputable def piPiAlgEquiv :
    ((∀ i, S i) ⊗[A] ∀ j, T j) ≃ₐ[A] ∀ p : ι × κ, S p.1 ⊗[A] T p.2 :=
  -- `piLeftAlgEquiv`, then componentwise `piRightAlgEquiv`, then uncurry.
  (piLeftAlgEquiv A (∀ j, T j) S).trans
    ((AlgEquiv.piCongrRight fun i => piRightAlgEquiv A (S i) T).trans
      (piProdAlgEquiv A fun i j => S i ⊗[A] T j))

@[simp]
lemma piPiAlgEquiv_tmul (s : ∀ i, S i) (t : ∀ j, T j) :
    piPiAlgEquiv A S T (s ⊗ₜ t) = fun p : ι × κ => s p.1 ⊗ₜ t p.2 :=
  rfl

end Algebra.TensorProduct

namespace IsLocalization.Away

variable {A : Type u} [CommRing A] (f g : A)
variable (S : Type u) [CommRing S] [Algebra A S]
variable (T : Type u) [CommRing T] [Algebra A T]

/-- The canonical `A`-algebra map `A[1/f] →ₐ[A] A[1/g]` when `f ∣ g`.  It is unique with
this type (`IsLocalization.algHom_subsingleton`). -/
noncomputable def algHomOfDvd [IsLocalization.Away f S] [IsLocalization.Away g T]
    (h : f ∣ g) : S →ₐ[A] T :=
  -- `IsLocalization.liftAlgHom` with unit witness `IsLocalization.Away.isUnit_of_dvd`
  -- for powers of `f`.
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := Algebra.ofId A T)
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      have hu : IsUnit (algebraMap A T f) := IsLocalization.Away.isUnit_of_dvd (S := T) g h
      simpa [Algebra.ofId_apply, ← hn, map_pow] using hu.pow n)

/-- The tensor product of an `Away f` and an `Away g` localization of `A` is an
`Away (f * g)` localization of `A`.  (Mathlib's `IsLocalization.Away.tensor` is the
`S`-relative statement; this is the `A`-relative one.)

Proof sketch: mathlib's `IsLocalization.Away.tensor` instance exhibits `S ⊗[A] T` as the
localization of `S` away from `algebraMap A S g`; conclude with
`IsLocalization.Away.mul'` along the tower `A → S → S ⊗[A] T`. -/
theorem tensor' [IsLocalization.Away f S] [IsLocalization.Away g T] :
    IsLocalization.Away (f * g) (S ⊗[A] T) := by
  -- mathlib's `IsLocalization.Away.tensor` exhibits `S ⊗[A] T` as the localization of `S`
  -- away from `algebraMap A S g`; conclude along the tower `A → S → S ⊗[A] T`.
  haveI : IsLocalization.Away (algebraMap A S g) (S ⊗[A] T) :=
    IsLocalization.Away.tensor (R := A) (S := S) (A := T) (r := g)
  exact IsLocalization.Away.mul' S (S ⊗[A] T) f g

/-- The canonical `A`-algebra equivalence from the tensor product of an `Away f` and an
`Away g` localization to any `Away (f * g)` localization. -/
noncomputable def tensorEquiv' (C : Type u) [CommRing C] [Algebra A C]
    [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) C] : (S ⊗[A] T) ≃ₐ[A] C :=
  haveI := tensor' f g S T
  IsLocalization.algEquiv (Submonoid.powers (f * g)) _ _

end IsLocalization.Away
