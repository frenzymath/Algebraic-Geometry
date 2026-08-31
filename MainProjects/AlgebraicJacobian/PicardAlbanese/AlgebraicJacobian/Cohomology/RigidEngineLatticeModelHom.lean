/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RigidEngineLatticeModel

/-!
# RE-1b — the finite model surjection

Every two-lattice pair with finite chart lattices is a quotient of a family line-bundle
model (`informal/w4-rigid-engine-worksheet.md` §2.2, "the finite surjection onto a
pair"): choosing finite generators of each lattice over the coordinate action and
clearing denominators produces, for each generator, a twist `m i : ℤ` and a map from the
model summand `𝒪(m i)`; the sum is a map of pairs `model R ι m ⟶ P` surjective on both
chart lattices *and* on the overlap module. This is Mumford's "finite free approximation
mapping onto the needed cocycles", terminating because it runs over `R[X]`, not over `R`.

**The finiteness spelling** (worksheet risk 3, lane-owned, pinned here): a chart lattice
`M₀` with coordinate action `t₀` is *finite* when `Module.Finite R[X] (Module.AEval' t₀)`
— mathlib's polynomial-action module `Module.AEval'` puts the `R[X]`-structure through
the endomorphism (`X • x = t₀ x`), so no competing `R[X]`-module structures are ever
placed on the overlap module.

## Main declarations

* `TwoLatticePair.laurentToEnd` — the Laurent-polynomial action `R[T;T⁻¹] →ₐ[R] End R N`
  on the overlap module through the invertible coordinate, with
  `laurentToEnd_toLaurent_ι₀`/`laurentToEnd_invert_toLaurent_ι₁` intertwining it with the
  polynomial actions on the two chart lattices.
* `TwoLatticePair.modelHom` — the map of pairs `model R ι m ⟶ P` determined by target
  generators `a : ι → M₀`, `b : ι → M₁` with `T^(m i)`-twisted matching overlap images.
* `TwoLatticePair.moduleFinite_aeval_model_t₀`/`…_t₁` — the models themselves have
  finite lattices in the pinned spelling.
* `TwoLatticePair.exists_hom_model_surjective` — **the finite model surjection**: a pair
  with finite lattices admits a map from a family model surjective on the chart-0,
  chart-1 and overlap components.

The coherence theorems COH-1/COH-0 fed by this surjection are in
`AlgebraicJacobian.Cohomology.RigidEngineLatticeCoherence`.
-/

set_option autoImplicit false

universe u v

open Polynomial LaurentPolynomial

namespace TwoLatticePair

variable {R : Type u} [CommRing R]
variable {M₀ M₁ N : Type*}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup N]
variable [Module R M₀] [Module R M₁] [Module R N]
variable (P : TwoLatticePair R M₀ M₁ N)

/-! ### The Laurent-polynomial action on the overlap module -/

/-- The Laurent-polynomial action on the overlap module of a two-lattice pair: the
`R`-algebra map `R[T;T⁻¹] →ₐ[R] End R N` sending `T` to the invertible coordinate
action `tN`. -/
noncomputable def laurentToEnd : R[T;T⁻¹] →ₐ[R] Module.End R N :=
  AddMonoidAlgebra.lift R (Module.End R N) ℤ
    ((Units.coeHom (Module.End R N)).comp (zpowersHom (Module.End R N)ˣ P.tN))

lemma laurentToEnd_single (j : ℤ) (r : R) :
    P.laurentToEnd (AddMonoidAlgebra.single j r) =
      r • (((P.tN ^ j : (Module.End R N)ˣ)) : Module.End R N) := by
  unfold laurentToEnd
  rw [AddMonoidAlgebra.lift_single]
  simp

@[simp]
lemma laurentToEnd_T (j : ℤ) :
    P.laurentToEnd (T j) = (((P.tN ^ j : (Module.End R N)ˣ)) : Module.End R N) := by
  have h : (T j : R[T;T⁻¹]) = AddMonoidAlgebra.single j 1 := rfl
  rw [h, laurentToEnd_single, one_smul]

/-- (Implementation) Nonnegative unit powers of the overlap action, in endomorphism
form. -/
private lemma tN_zpow_natCast (k : ℕ) :
    (((P.tN ^ (k : ℤ) : (Module.End R N)ˣ)) : Module.End R N) = P.tN.val ^ k := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val]

/-- (Implementation) Negative unit powers of the overlap action, in endomorphism
form. -/
private lemma tN_zpow_neg_natCast (k : ℕ) :
    (((P.tN ^ (-(k : ℤ)) : (Module.End R N)ˣ)) : Module.End R N) = P.tN.inv ^ k := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  rfl

lemma laurentToEnd_T_natCast (k : ℕ) :
    P.laurentToEnd (T (k : ℤ)) = P.tN.val ^ k := by
  rw [laurentToEnd_T, tN_zpow_natCast]

lemma laurentToEnd_T_neg_natCast (k : ℕ) :
    P.laurentToEnd (T (-(k : ℤ))) = P.tN.inv ^ k := by
  rw [laurentToEnd_T, tN_zpow_neg_natCast]

lemma laurentToEnd_T_one : P.laurentToEnd (T 1) = P.tN.val := by
  rw [laurentToEnd_T, zpow_one]

/-- The Laurent action on the overlap intertwines the chart-0 polynomial action:
`q(T)` acting on `ι₀ x` is `ι₀ (q(t₀) x)`. -/
lemma laurentToEnd_toLaurent_ι₀ (q : R[X]) (x : M₀) :
    P.laurentToEnd (Polynomial.toLaurent q) (P.ι₀ x) =
      P.ι₀ (Polynomial.aeval P.t₀ q x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k r =>
    rw [Polynomial.toLaurent_C_mul_T, ← single_eq_C_mul_T, laurentToEnd_single,
      Polynomial.aeval_monomial, LinearMap.smul_apply, tN_zpow_natCast,
      Module.End.mul_apply, Module.algebraMap_end_apply, ← P.ι₀_pow_comm, ← map_smul]

/-- The Laurent action on the overlap intertwines the chart-1 polynomial action through
the inversion `T ↦ T⁻¹`: `q(T⁻¹)` acting on `ι₁ y` is `ι₁ (q(t₁) y)`. -/
lemma laurentToEnd_invert_toLaurent_ι₁ (q : R[X]) (y : M₁) :
    P.laurentToEnd (invert (Polynomial.toLaurent q)) (P.ι₁ y) =
      P.ι₁ (Polynomial.aeval P.t₁ q y) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k r =>
    rw [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T, ← single_eq_C_mul_T,
      laurentToEnd_single, Polynomial.aeval_monomial, LinearMap.smul_apply,
      tN_zpow_neg_natCast, Module.End.mul_apply, Module.algebraMap_end_apply,
      ← P.ι₁_pow_comm, ← map_smul]

/-! ### The map of pairs out of a family model -/

variable (ι : Type v) [Fintype ι]

/-- (Implementation) The chart component of the model hom: `p ↦ ∑ i, (p i)(t) (a i)`,
the polynomial action of each model coordinate on its target generator. -/
private noncomputable def modelHomChart (t : Module.End R M₀) (a : ι → M₀) :
    (ι → R[X]) →ₗ[R] M₀ :=
  ∑ i : ι, LinearMap.applyₗ (a i) ∘ₗ (Polynomial.aeval t).toLinearMap ∘ₗ LinearMap.proj i

private lemma modelHomChart_apply (t : Module.End R M₀) (a : ι → M₀) (p : ι → R[X]) :
    modelHomChart ι t a p = ∑ i : ι, Polynomial.aeval t (p i) (a i) := by
  simp [modelHomChart]

/-- (Implementation) The overlap component of the model hom:
`n ↦ ∑ i, (n i)(tN) (c i)`, the Laurent action of each model coordinate on the overlap
image of its target generator. -/
private noncomputable def modelHomOverlap (c : ι → N) : (ι → R[T;T⁻¹]) →ₗ[R] N :=
  ∑ i : ι, LinearMap.applyₗ (c i) ∘ₗ P.laurentToEnd.toLinearMap ∘ₗ LinearMap.proj i

private lemma modelHomOverlap_apply (c : ι → N) (n : ι → R[T;T⁻¹]) :
    modelHomOverlap P ι c n = ∑ i : ι, P.laurentToEnd (n i) (c i) := by
  simp [modelHomOverlap]

variable {ι}

/-- **The model hom**: the map of pairs `model R ι m ⟶ P` determined by target
generators `a : ι → M₀` and `b : ι → M₁` whose overlap images match up to the twist:
`T^(m i) · ι₀ (a i) = ι₁ (b i)`. Chart components act by evaluating the model
polynomials at the coordinate actions on the generators; the overlap component acts by
the Laurent action on the `ι₀`-images. -/
noncomputable def modelHom (m : ι → ℤ) (a : ι → M₀) (b : ι → M₁)
    (hab : ∀ i, P.laurentToEnd (T (m i)) (P.ι₀ (a i)) = P.ι₁ (b i)) :
    (model R ι m).Hom P where
  hom₀ := modelHomChart ι P.t₀ a
  hom₁ := modelHomChart ι P.t₁ b
  homN := modelHomOverlap P ι fun i => P.ι₀ (a i)
  comm_t₀ := fun p => by
    rw [modelHomChart_apply, modelHomChart_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [model_t₀_apply, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  comm_t₁ := fun q => by
    rw [modelHomChart_apply, modelHomChart_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [model_t₁_apply, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  comm_tN := fun n => by
    rw [modelHomOverlap_apply, modelHomOverlap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [model_tN_val_apply, map_mul, laurentToEnd_T_one, Module.End.mul_apply]
  comm_ι₀ := fun p => by
    rw [modelHomOverlap_apply, modelHomChart_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [model_ι₀_apply, laurentToEnd_toLaurent_ι₀]
  comm_ι₁ := fun q => by
    rw [modelHomOverlap_apply, modelHomChart_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [model_ι₁_apply, mul_comm ((T (m i) : R[T;T⁻¹])), map_mul, Module.End.mul_apply,
      hab i, laurentToEnd_invert_toLaurent_ι₁]

lemma modelHom_hom₀_apply (m : ι → ℤ) (a : ι → M₀) (b : ι → M₁)
    (hab : ∀ i, P.laurentToEnd (T (m i)) (P.ι₀ (a i)) = P.ι₁ (b i)) (p : ι → R[X]) :
    (P.modelHom m a b hab).hom₀ p = ∑ i : ι, Polynomial.aeval P.t₀ (p i) (a i) :=
  modelHomChart_apply ι P.t₀ a p

lemma modelHom_hom₁_apply (m : ι → ℤ) (a : ι → M₀) (b : ι → M₁)
    (hab : ∀ i, P.laurentToEnd (T (m i)) (P.ι₀ (a i)) = P.ι₁ (b i)) (q : ι → R[X]) :
    (P.modelHom m a b hab).hom₁ q = ∑ i : ι, Polynomial.aeval P.t₁ (q i) (b i) :=
  modelHomChart_apply ι P.t₁ b q

/-! ### The models have finite lattices in the pinned spelling -/

section ModelFinite

variable (R) (ι) (m : ι → ℤ)

/-- The polynomial-action module of the model chart lattice is the free module
`ι → R[X]` itself: `X` acts componentwise as multiplication by `X`. -/
private noncomputable def modelAEvalEquiv :
    Module.AEval' (model R ι m).t₀ ≃ₗ[R[X]] (ι → R[X]) :=
  LinearEquiv.ofAEval (model R ι m).t₀ (LinearEquiv.refl R (ι → R[X])) fun p => by
    funext i
    simp only [LinearEquiv.refl_apply, Pi.smul_apply, smul_eq_mul]
    rw [Module.End.smul_def, model_t₀_apply]

instance moduleFinite_aeval_model_t₀ :
    Module.Finite R[X] (Module.AEval' (model R ι m).t₀) :=
  Module.Finite.equiv (modelAEvalEquiv R ι m).symm

instance moduleFinite_aeval_model_t₁ :
    Module.Finite R[X] (Module.AEval' (model R ι m).t₁) :=
  moduleFinite_aeval_model_t₀ R ι m

end ModelFinite

/-! ### The finite model surjection -/

/-- **The finite model surjection** (worksheet §2.2): a two-lattice pair whose chart
lattices are finite over the coordinate actions (`Module.Finite R[X] (Module.AEval' t)`,
the pinned spelling) admits a map of pairs from a family line-bundle model that is
surjective on the chart-0 lattice, the chart-1 lattice, **and** the overlap module.
Overlap surjectivity follows from chart surjectivity and denominator clearing. -/
theorem exists_hom_model_surjective
    [Module.Finite R[X] (Module.AEval' P.t₀)] [Module.Finite R[X] (Module.AEval' P.t₁)] :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℤ) (f : (model R ι m).Hom P),
      Function.Surjective f.hom₀ ∧ Function.Surjective f.hom₁ ∧
        Function.Surjective f.homN := by
  classical
  obtain ⟨n₀, g₀, hg₀⟩ := Module.Finite.exists_fin (R := R[X]) (M := Module.AEval' P.t₀)
  obtain ⟨n₁, g₁, hg₁⟩ := Module.Finite.exists_fin (R := R[X]) (M := Module.AEval' P.t₁)
  -- The target generators in the two lattices.
  set a₀ : Fin n₀ → M₀ := fun j => (Module.AEval'.of P.t₀).symm (g₀ j) with ha₀
  set b₁ : Fin n₁ → M₁ := fun j => (Module.AEval'.of P.t₁).symm (g₁ j) with hb₁
  -- Clear denominators to produce the twists and the matching opposite-chart data.
  choose k₀ y₀ hk₀ using fun j => P.denom₁ (P.ι₀ (a₀ j))
  choose k₁ x₁ hk₁ using fun j => P.denom₀ (P.ι₁ (b₁ j))
  refine ⟨Fin n₀ ⊕ Fin n₁, inferInstance,
    Sum.elim (fun j => -(k₀ j : ℤ)) (fun j => -(k₁ j : ℤ)), ?_⟩
  set a : Fin n₀ ⊕ Fin n₁ → M₀ := Sum.elim a₀ x₁ with ha
  set b : Fin n₀ ⊕ Fin n₁ → M₁ := Sum.elim y₀ b₁ with hb
  have hab : ∀ i, P.laurentToEnd
      (T (Sum.elim (fun j => -(k₀ j : ℤ)) (fun j => -(k₁ j : ℤ)) i)) (P.ι₀ (a i)) =
        P.ι₁ (b i) := by
    rintro (j | j)
    · simp only [ha, hb, Sum.elim_inl]
      rw [laurentToEnd_T_neg_natCast]
      exact hk₀ j
    · simp only [ha, hb, Sum.elim_inr]
      rw [laurentToEnd_T_neg_natCast, ← hk₁ j, P.tN_inv_pow_val_pow_apply]
  set f := P.modelHom _ a b hab with hf
  -- Chart-0 surjectivity: expand along the chosen `R[X]`-generators.
  have hs₀ : Function.Surjective f.hom₀ := by
    intro x
    have hx : Module.AEval'.of P.t₀ x ∈ Submodule.span R[X] (Set.range g₀) := by
      rw [hg₀]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R[X])).mp hx
    refine ⟨Sum.elim c 0, ?_⟩
    rw [hf, modelHom_hom₀_apply, Fintype.sum_sum_type]
    simp only [ha, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero,
      LinearMap.zero_apply, Finset.sum_const_zero, add_zero]
    have hc' := congrArg (Module.AEval'.of P.t₀).symm hc
    rw [map_sum, LinearEquiv.symm_apply_apply] at hc'
    simpa only [Module.AEval.of_symm_smul, Module.End.smul_def] using hc'
  -- Chart-1 surjectivity, symmetrically.
  have hs₁ : Function.Surjective f.hom₁ := by
    intro y
    have hy : Module.AEval'.of P.t₁ y ∈ Submodule.span R[X] (Set.range g₁) := by
      rw [hg₁]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R[X])).mp hy
    refine ⟨Sum.elim 0 c, ?_⟩
    rw [hf, modelHom_hom₁_apply, Fintype.sum_sum_type]
    simp only [hb, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero,
      LinearMap.zero_apply, Finset.sum_const_zero, zero_add]
    have hc' := congrArg (Module.AEval'.of P.t₁).symm hc
    rw [map_sum, LinearEquiv.symm_apply_apply] at hc'
    simpa only [Module.AEval.of_symm_smul, Module.End.smul_def] using hc'
  -- Overlap surjectivity: chart-0 surjectivity plus denominator clearing.
  have hsN : Function.Surjective f.homN := by
    intro n
    obtain ⟨k, x, hkx⟩ := P.denom₀ n
    obtain ⟨p, hp⟩ := hs₀ x
    refine ⟨((model R (Fin n₀ ⊕ Fin n₁)
      (Sum.elim (fun j => -(k₀ j : ℤ)) (fun j => -(k₁ j : ℤ)))).tN.inv ^ k)
      ((model R (Fin n₀ ⊕ Fin n₁)
        (Sum.elim (fun j => -(k₀ j : ℤ)) (fun j => -(k₁ j : ℤ)))).ι₀ p), ?_⟩
    rw [f.comm_tN_inv_pow, f.comm_ι₀, hp, ← hkx, P.tN_inv_pow_val_pow_apply]
  exact ⟨f, hs₀, hs₁, hsN⟩

end TwoLatticePair
