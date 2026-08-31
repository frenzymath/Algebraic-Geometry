/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.TwoLattice
import AlgebraicJacobian.Cohomology.RigidEngineLattice
import Mathlib.RingTheory.Polynomial.Basic

/-!
# RE-1b — the `ℙ¹` line-bundle models as two-lattice pairs

The **family model** `TwoLatticePair.model R ι m` is the two-lattice pair of the direct
sum `⊕ᵢ 𝒪(m i)` of line bundles on the two-chart projective line, relative over an
arbitrary commutative ring `R` (`informal/w4-rigid-engine-worksheet.md` §2.2, "the
models"): the chart lattices are `ι → R[X]` (polynomials in the chart coordinates), the
overlap module is `ι → R[T;T⁻¹]` (Laurent polynomials), and the chart-1 lattice is glued
in through the twist `q ↦ T^(m i) · q(T⁻¹)` componentwise.

Its cohomology is the classical monomial-window computation, relative over any `R`:

* `moduleFinite_h1_model` — `H¹` of the model is a finite `R`-module (the window
  `{T^j : m i < j < 0}`), for **any** commutative `R`: one application of the landed
  monomial-ladder keystone
  `LaurentPolynomial.moduleFinite_quotient_sup_of_exists_pow_smul_mem`
  (`AlgebraicJacobian.Algebra.TwoLattice`) on the componentwise Laurent module.
* `moduleFinite_h0_model` — `H⁰` of the model is a finite `R`-module for Noetherian `R`:
  the first chart component of an `H⁰`-class is trapped in the degree window
  `deg ≤ m i` (`Polynomial.degreeLT`), and determines the class.

The model exists to receive the **model surjection** (worksheet §2.2, built in
`AlgebraicJacobian.Cohomology.RigidEngineLatticeModelHom`): every finite two-lattice pair
is a quotient of a family model, which is what makes the coherence theorems COH-1/COH-0
one-step (no induction on twists).
-/

set_option autoImplicit false

universe u v

open Polynomial LaurentPolynomial

namespace TwoLatticePair

variable (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] (m : ι → ℤ)

/-! ### Laurent coefficient bookkeeping -/

private lemma toLaurent_apply_coe (p : R[X]) (n : ℕ) :
    (Polynomial.toLaurent p) ((n : ℤ)) = p.coeff n := by
  rw [Polynomial.toLaurent_apply, Finsupp.mapDomain_apply Nat.cast_injective,
    Polynomial.toFinsupp_apply]

private lemma toLaurent_apply_neg (p : R[X]) {k : ℤ} (hk : k < 0) :
    (Polynomial.toLaurent p) k = 0 := by
  rw [Polynomial.toLaurent_apply]
  refine Finsupp.mapDomain_notin_range _ _ ?_
  rintro ⟨nn, rfl⟩
  omega

/-! ### The components of the model -/

/-- (Implementation) The chart coordinate action of the model: componentwise
multiplication by `X`. -/
private noncomputable def modelT : Module.End R (ι → R[X]) :=
  Algebra.lsmul R R (ι → R[X]) (X : R[X])

omit [Fintype ι] in
private lemma modelT_apply (p : ι → R[X]) (i : ι) : modelT R ι p i = X * p i := rfl

/-- (Implementation) The invertible overlap action of the model: componentwise
multiplication by `T`, with inverse multiplication by `T⁻¹`. -/
private noncomputable def modelTN : (Module.End R (ι → R[T;T⁻¹]))ˣ where
  val := Algebra.lsmul R R (ι → R[T;T⁻¹]) (T 1 : R[T;T⁻¹])
  inv := Algebra.lsmul R R (ι → R[T;T⁻¹]) (T (-1) : R[T;T⁻¹])
  val_inv := by rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  inv_val := by rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]

omit [Fintype ι] in
private lemma modelTN_val_apply (n : ι → R[T;T⁻¹]) (i : ι) :
    (modelTN R ι).val n i = T 1 * n i := rfl

omit [Fintype ι] in
private lemma modelTN_inv_apply (n : ι → R[T;T⁻¹]) (i : ι) :
    (modelTN R ι).inv n i = T (-1) * n i := rfl

omit [Fintype ι] in
private lemma modelTN_val_pow_apply (M : ℕ) (n : ι → R[T;T⁻¹]) (i : ι) :
    (((modelTN R ι).val ^ M) n) i = (T (M : ℤ) : R[T;T⁻¹]) * n i := by
  have hval : (modelTN R ι).val = Algebra.lsmul R R (ι → R[T;T⁻¹]) (T 1 : R[T;T⁻¹]) := rfl
  rw [hval, ← map_pow, T_pow, mul_one]
  rfl

omit [Fintype ι] in
private lemma modelTN_inv_pow_apply (M : ℕ) (n : ι → R[T;T⁻¹]) (i : ι) :
    (((modelTN R ι).inv ^ M) n) i = (T (-(M : ℤ)) : R[T;T⁻¹]) * n i := by
  have hinv : (modelTN R ι).inv = Algebra.lsmul R R (ι → R[T;T⁻¹]) (T (-1) : R[T;T⁻¹]) := rfl
  rw [hinv, ← map_pow, T_pow, mul_neg_one]
  rfl

/-- (Implementation) The chart-0 localization map of the model: componentwise
`toLaurent`. -/
private noncomputable def modelI0 : (ι → R[X]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  LinearMap.pi fun i => Polynomial.toLaurentAlg.toLinearMap ∘ₗ LinearMap.proj i

omit [Fintype ι] in
private lemma modelI0_apply (p : ι → R[X]) (i : ι) :
    modelI0 R ι p i = Polynomial.toLaurent (p i) := rfl

/-- (Implementation) The chart-1 localization map of the model: componentwise
`q ↦ T^(m i) · q(T⁻¹)`, the twisted gluing. -/
private noncomputable def modelI1 : (ι → R[X]) →ₗ[R] (ι → R[T;T⁻¹]) :=
  LinearMap.pi fun i =>
    Algebra.lsmul R R R[T;T⁻¹] ((T (m i) : R[T;T⁻¹])) ∘ₗ (invert (R := R)).toLinearMap ∘ₗ
      Polynomial.toLaurentAlg.toLinearMap ∘ₗ LinearMap.proj i

omit [Fintype ι] in
private lemma modelI1_apply (q : ι → R[X]) (i : ι) :
    modelI1 R ι m q i = T (m i) * invert (Polynomial.toLaurent (q i)) := rfl

/-! ### The model pair -/

/-- **The family line-bundle model** `⊕_{i : ι} 𝒪(m i)` on the two-chart projective
line, as a two-lattice pair over `R`: chart lattices `ι → R[X]`, overlap module
`ι → R[T;T⁻¹]`, componentwise coordinate actions, chart-0 gluing `toLaurent` and chart-1
gluing `q ↦ T^(m i) · q(T⁻¹)`. -/
noncomputable def model : TwoLatticePair R (ι → R[X]) (ι → R[X]) (ι → R[T;T⁻¹]) where
  t₀ := modelT R ι
  t₁ := modelT R ι
  tN := modelTN R ι
  ι₀ := modelI0 R ι
  ι₁ := modelI1 R ι m
  ι₀_comm := fun p => by
    funext i
    simp only [modelI0_apply, modelT_apply, modelTN_val_apply, map_mul,
      Polynomial.toLaurent_X]
  ι₁_comm := fun q => by
    funext i
    simp only [modelI1_apply, modelT_apply, modelTN_inv_apply, map_mul,
      Polynomial.toLaurent_X, invert_T]
    ring
  denom₀ := fun n => by
    classical
    choose k f hf using fun i => (n i).exists_T_pow
    set M : ℕ := Finset.univ.sup k with hM
    refine ⟨M, fun i => X ^ (M - k i) * f i, ?_⟩
    funext i
    have hle : k i ≤ M := hM ▸ Finset.le_sup (Finset.mem_univ i)
    simp only [modelTN_val_pow_apply, modelI0_apply, map_mul, Polynomial.toLaurent_X_pow,
      hf i]
    rw [show ((M : ℕ) : ℤ) = ((M - k i : ℕ) : ℤ) + ((k i : ℕ) : ℤ) from by omega, T_add]
    ring
  denom₁ := fun n => by
    classical
    choose k g hg using fun i => (invert (R := R) (n i)).exists_T_pow
    set M : ℕ := Finset.univ.sup fun i => (k i - m i).toNat with hM
    refine ⟨M, fun i => X ^ ((M : ℤ) + m i - k i).toNat * g i, ?_⟩
    funext i
    have hle : k i - m i ≤ (M : ℤ) := by
      refine le_trans (Int.self_le_toNat _) ?_
      exact_mod_cast hM ▸ Finset.le_sup (Finset.mem_univ i)
    have he : (((M : ℤ) + m i - k i).toNat : ℤ) = (M : ℤ) + m i - k i :=
      Int.toNat_of_nonneg (by omega)
    simp only [modelTN_inv_pow_apply, modelI1_apply]
    rw [map_mul, Polynomial.toLaurent_X_pow, hg i, map_mul, map_mul, invert_T,
      LaurentPolynomial.involutive_invert (n i), he,
      show (-(M : ℤ)) = m i + (-((M : ℤ) + m i - k i)) + (-(k i)) from by ring,
      T_add, T_add]
    simp only [invert_T]
    ring
  ann₀ := fun p hp => ⟨0, by
    funext i
    have h := congrFun hp i
    rw [modelI0_apply, Pi.zero_apply] at h
    have hz := Polynomial.toLaurent_eq_zero.mp h
    simp [hz]⟩
  ann₁ := fun q hq => ⟨0, by
    funext i
    have h := congrFun hq i
    rw [modelI1_apply, Pi.zero_apply] at h
    have h2 : invert (R := R) (Polynomial.toLaurent (q i)) = 0 :=
      ((isUnit_T (m i)).mul_right_eq_zero).mp h
    have h3 : Polynomial.toLaurent (q i) = 0 := by
      have h4 := congrArg (invert (R := R)) h2
      rwa [LaurentPolynomial.involutive_invert, map_zero] at h4
    have hz := Polynomial.toLaurent_eq_zero.mp h3
    simp [hz]⟩

/-! ### The public component interface of the model -/

@[simp] lemma model_t₀_apply (p : ι → R[X]) (i : ι) :
    (model R ι m).t₀ p i = X * p i := rfl

@[simp] lemma model_t₁_apply (q : ι → R[X]) (i : ι) :
    (model R ι m).t₁ q i = X * q i := rfl

@[simp] lemma model_tN_val_apply (n : ι → R[T;T⁻¹]) (i : ι) :
    (model R ι m).tN.val n i = T 1 * n i := rfl

@[simp] lemma model_tN_inv_apply (n : ι → R[T;T⁻¹]) (i : ι) :
    (model R ι m).tN.inv n i = T (-1) * n i := rfl

@[simp] lemma model_ι₀_apply (p : ι → R[X]) (i : ι) :
    (model R ι m).ι₀ p i = Polynomial.toLaurent (p i) := rfl

@[simp] lemma model_ι₁_apply (q : ι → R[X]) (i : ι) :
    (model R ι m).ι₁ q i = T (m i) * invert (Polynomial.toLaurent (q i)) := rfl

lemma model_tN_val_pow_apply (M : ℕ) (n : ι → R[T;T⁻¹]) (i : ι) :
    (((model R ι m).tN.val ^ M) n) i = (T (M : ℤ) : R[T;T⁻¹]) * n i :=
  modelTN_val_pow_apply R ι M n i

lemma model_tN_inv_pow_apply (M : ℕ) (n : ι → R[T;T⁻¹]) (i : ι) :
    (((model R ι m).tN.inv ^ M) n) i = (T (-(M : ℤ)) : R[T;T⁻¹]) * n i :=
  modelTN_inv_pow_apply R ι M n i

/-- The chart-1 localization map of the model is injective. -/
lemma ι₁_model_injective : Function.Injective (model R ι m).ι₁ := by
  intro q q' h
  funext i
  have hc := congrFun h i
  rw [model_ι₁_apply, model_ι₁_apply] at hc
  have h2 := (isUnit_T (R := R) (m i)).mul_left_cancel hc
  exact Polynomial.toLaurent_injective ((invert (R := R)).injective h2)

/-! ### The window computation, degree 1: `H¹` finiteness over any ring -/

/-- **The monomial-window computation for `H¹` of the model, over any commutative
`R`**: `H¹(⊕ᵢ 𝒪(m i))` is a finite `R`-module. One application of the landed two-lattice
monomial ladder on the componentwise Laurent module — no Noetherian hypothesis. -/
theorem moduleFinite_h1_model : Module.Finite R (model R ι m).H1 := by
  have hstab₀ : ∀ x ∈ LinearMap.range (model R ι m).ι₀,
      (T 1 : R[T;T⁻¹]) • x ∈ LinearMap.range (model R ι m).ι₀ := by
    rintro x ⟨p, rfl⟩
    exact ⟨(model R ι m).t₀ p, by rw [(model R ι m).ι₀_comm p]; rfl⟩
  have hstab₁ : ∀ x ∈ LinearMap.range (model R ι m).ι₁,
      (T (-1) : R[T;T⁻¹]) • x ∈ LinearMap.range (model R ι m).ι₁ := by
    rintro x ⟨q, rfl⟩
    exact ⟨(model R ι m).t₁ q, by rw [(model R ι m).ι₁_comm q]; rfl⟩
  have hloc₀ : ∀ n : ι → R[T;T⁻¹], ∃ mm : ℕ,
      ((T 1 : R[T;T⁻¹]) ^ mm) • n ∈ LinearMap.range (model R ι m).ι₀ := by
    intro n
    obtain ⟨mm, x, hx⟩ := (model R ι m).denom₀ n
    refine ⟨mm, x, ?_⟩
    rw [← hx]
    funext i
    rw [model_tN_val_pow_apply]
    change (T (mm : ℤ) : R[T;T⁻¹]) * n i = ((T 1 : R[T;T⁻¹]) ^ mm) * n i
    rw [T_pow, mul_one]
  have hloc₁ : ∀ n : ι → R[T;T⁻¹], ∃ mm : ℕ,
      ((T (-1) : R[T;T⁻¹]) ^ mm) • n ∈ LinearMap.range (model R ι m).ι₁ := by
    intro n
    obtain ⟨mm, y, hy⟩ := (model R ι m).denom₁ n
    refine ⟨mm, y, ?_⟩
    rw [← hy]
    funext i
    rw [model_tN_inv_pow_apply]
    change (T (-(mm : ℤ)) : R[T;T⁻¹]) * n i = ((T (-1) : R[T;T⁻¹]) ^ mm) * n i
    rw [T_pow, mul_neg_one]
  exact LaurentPolynomial.moduleFinite_quotient_sup_of_exists_pow_smul_mem
    hstab₀ hstab₁ hloc₀ hloc₁

/-! ### The window computation, degree 0: `H⁰` finiteness over Noetherian rings -/

/-- **The degree-window computation for `H⁰` of the model, over Noetherian `R`**:
`H⁰(⊕ᵢ 𝒪(m i))` is a finite `R`-module. The first chart component of an `H⁰`-class is
trapped in the finite window `deg ≤ m i` and determines the class. -/
theorem moduleFinite_h0_model [IsNoetherianRing R] :
    Module.Finite R ↥(model R ι m).H0 := by
  classical
  have hmem : ∀ (z : ↥(model R ι m).H0) (i : ι),
      (z : (ι → R[X]) × (ι → R[X])).1 i ∈ Polynomial.degreeLT R ((m i + 1).toNat) := by
    intro z i
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
    intro nn hnn
    have hz := (model R ι m).mem_H0_iff_eq.mp z.prop
    have hcomp := congrFun hz i
    rw [model_ι₀_apply, model_ι₁_apply] at hcomp
    rw [← toLaurent_apply_coe, hcomp,
      show (T (m i) : R[T;T⁻¹]) = AddMonoidAlgebra.single (m i) 1 from rfl,
      AddMonoidAlgebra.single_mul_apply, one_mul, LaurentPolynomial.invert_apply]
    refine toLaurent_apply_neg R _ ?_
    have : m i + 1 ≤ (nn : ℤ) := Int.toNat_le.mp hnn
    omega
  let g : ↥(model R ι m).H0 →ₗ[R] ∀ i, ↥(Polynomial.degreeLT R ((m i + 1).toNat)) :=
    LinearMap.pi fun i => LinearMap.codRestrict (Polynomial.degreeLT R ((m i + 1).toNat))
      (LinearMap.proj i ∘ₗ LinearMap.fst R (ι → R[X]) (ι → R[X]) ∘ₗ Submodule.subtype _)
      fun z => hmem z i
  have hg : Function.Injective g := by
    intro z w hzw
    have h1 : (z : (ι → R[X]) × (ι → R[X])).1 = (w : (ι → R[X]) × (ι → R[X])).1 :=
      funext fun i => congrArg Subtype.val (congrFun hzw i)
    have h2 : (z : (ι → R[X]) × (ι → R[X])).2 = (w : (ι → R[X]) × (ι → R[X])).2 := by
      refine ι₁_model_injective R ι m ?_
      rw [← (model R ι m).mem_H0_iff_eq.mp z.prop, ← (model R ι m).mem_H0_iff_eq.mp w.prop,
        h1]
    exact Subtype.ext (Prod.ext h1 h2)
  haveI : ∀ i, Module.Finite R ↥(Polynomial.degreeLT R ((m i + 1).toNat)) := fun i =>
    Module.Finite.equiv (Polynomial.degreeLTEquiv R ((m i + 1).toNat)).symm
  exact Module.Finite.of_injective g hg

end TwoLatticePair
