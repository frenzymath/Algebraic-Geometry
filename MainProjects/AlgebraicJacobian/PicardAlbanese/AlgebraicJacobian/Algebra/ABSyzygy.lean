/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.ABDepthSES

/-!
# Syzygy substrate for the Auslander–Buchsbaum formula

Fourth file of the Auslander–Buchsbaum package: the per-syzygy ingredients the
proof of the formula (`ABFormula`) consumes.

* `RingTheory.Module.exists_minimalSurjection_finite_localRing` — a finite
  module over a local ring admits a surjection `R^n ↠ M` of minimal rank
  `n = dim_κ(κ ⊗_R M)` whose kernel is contained in `𝔪 • ⊤` (Nakayama lift of
  a κ-basis).
* `RingTheory.Module.hasProjectiveDimensionLT_succ_of_projectiveDimension_eq`,
  `…hasProjectiveDimensionLT_ker_of_surjection`,
  `…hasProjectiveDimensionLT_succ_of_hasProjectiveDimensionLT_ker` — the bridge
  from the `projectiveDimension` equation to Mathlib's
  `HasProjectiveDimensionLT`, and syzygy descent/ascent along the kernel SES
  `0 → ker f → R^n → M → 0`.
* `RingTheory.Module.depth_ses_ineqs_of_surjection_finite_localRing` — the two
  Stacks-00LX inequalities on the kernel SES, after identifying
  `depth(R^n) = depth(R)`.
* `RingTheory.Module.exists_ne_zero_ext_of_depth_eq` — a nonzero class in
  `Ext^D(κ, M)` when `depth M = D` (the converse read-off of Stacks 00LW).
* `RingTheory.Module.ext_comp_mk₀_ofHom_eq_zero_of_entries_mem_annihilator` —
  the matrix-collapse on Ext: a map `A : R^m →ₗ R^n` with all entries in
  `Ann_R N` induces the zero postcomposition on `Ext^p(N, -)`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory

namespace RingTheory

namespace Module

/-! ### Minimal surjection substrate

For a finite `R`-module `M` over a local ring `R`, there exists a surjective
`R`-linear map `f : (Fin n → R) →ₗ[R] M` of the **minimal possible rank**
`n = dim_κ (κ ⊗_R M)` (where `κ = R/𝔪` is the residue field) whose **kernel
is contained in `𝔪 • ⊤`**. This is the first step of constructing a *minimal
finite free resolution*: iterating the construction on the kernel (which is
itself finitely generated when `R` is Noetherian) produces successive
syzygies whose differential maps each have image in `𝔪` times their target.

This is the per-step ingredient of Stacks `lemma-add-trivial-complex` used by
`auslander_buchsbaum_formula_succ_pd` in `ABFormula`. It packages the basic
**Nakayama-lift** of a κ-basis of `κ ⊗_R M` to an `R`-spanning family in `M`
and reads off the kernel-containment from linear independence of the basis
combined with the `1 ⊗_R -` evaluation.

Mathlib substrate used:
* `IsLocalRing.span_eq_top_of_tmul_eq_basis` — Nakayama lift of a κ-basis.
* `TensorProduct.mk_surjective` — the `1 ⊗_R -` map is surjective for the
  residue-field tensor.
* `Module.Basis.constr_range` — range of the linear extension equals span of
  the chosen image set.
* `Module.Basis.linearIndependent` — independence of a κ-basis.
* `IsLocalRing.residue_eq_zero_iff` — `r ∈ 𝔪 ↔ residue r = 0`. -/
/-- Provenance: CUSTOM. -/
lemma exists_minimalSurjection_finite_localRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [_root_.Module.Finite R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M),
      Function.Surjective f ∧
      n = _root_.Module.finrank (IsLocalRing.ResidueField R)
        (TensorProduct R (IsLocalRing.ResidueField R) M) ∧
      LinearMap.ker f ≤ (IsLocalRing.maximalIdeal R) • ⊤ := by
  set κ := IsLocalRing.ResidueField R with hκ
  set n := _root_.Module.finrank κ (TensorProduct R κ M) with hn
  -- Pick a κ-basis of `κ ⊗_R M`.
  let b : _root_.Module.Basis (Fin n) κ (TensorProduct R κ M) :=
    _root_.Module.finBasis κ (TensorProduct R κ M)
  -- The canonical map `(1 : κ) ⊗_R -` is surjective.
  have hsurj_mk : Function.Surjective ((TensorProduct.mk R κ M) 1) := by
    apply TensorProduct.mk_surjective
    exact Ideal.Quotient.mk_surjective
  -- Lift each basis element to a representative in M.
  choose lift hlift using hsurj_mk
  let m : Fin n → M := fun i => lift (b i)
  have hm : ∀ i, (1 : κ) ⊗ₜ[R] m i = b i := fun i => hlift (b i)
  -- Define `f` by sending each standard basis vector of `Fin n → R` to `m i`.
  let f : (Fin n → R) →ₗ[R] M := (Pi.basisFun R (Fin n)).constr R m
  -- Evaluation: `f x = Σ x i • m i`.
  have hf_eval : ∀ x : Fin n → R, f x = ∑ i, x i • m i := by
    intro x
    rw [show f x = ((Pi.basisFun R (Fin n)).constr R) m x from rfl,
        _root_.Module.Basis.constr_apply]
    have h : (Pi.basisFun R (Fin n)).repr x = Finsupp.equivFunOnFinite.symm x := by
      ext i; rw [Pi.basisFun_repr]; rfl
    rw [h, Finsupp.sum_fintype _ _ (by intros; simp)]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  -- Range = span of `m`.
  have hf_range : LinearMap.range f = Submodule.span R (Set.range m) :=
    _root_.Module.Basis.constr_range _ _
  -- Nakayama: span of `m i` equals all of `M`.
  have hspan : Submodule.span R (Set.range m) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis m b hm
  refine ⟨n, f, ?_, rfl, ?_⟩
  · exact LinearMap.range_eq_top.mp (by rw [hf_range, hspan])
  · -- Kernel containment in `𝔪 • ⊤`.
    intro x hx
    have hfx : f x = 0 := hx
    rw [hf_eval] at hfx
    -- Apply `(1 : κ) ⊗_R -` to `Σ x i • m i = 0`.
    have h1 : (1 : κ) ⊗ₜ[R] (∑ i, x i • m i) = (0 : TensorProduct R κ M) := by
      rw [hfx]; exact TensorProduct.tmul_zero _ _
    rw [TensorProduct.tmul_sum] at h1
    -- Rewrite each summand: `1 ⊗_R (x i • m i) = residue(x i) • b i`.
    have hrewrite : ∀ i, (1 : κ) ⊗ₜ[R] (x i • m i)
        = (IsLocalRing.residue R (x i) : κ) • b i := by
      intro i
      rw [show ((1 : κ) ⊗ₜ[R] (x i • m i))
          = x i • ((1 : κ) ⊗ₜ[R] m i) from
        (TensorProduct.tmul_smul (R := R) (x i) (1 : κ) (m i))]
      rw [hm i]; rfl
    rw [show (∑ i, (1 : κ) ⊗ₜ[R] (x i • m i))
        = ∑ i, (IsLocalRing.residue R (x i) : κ) • b i from
      Finset.sum_congr rfl (fun i _ => hrewrite i)] at h1
    -- Linear independence of `b` forces each `residue (x i) = 0`.
    have hlin : LinearIndependent κ b := b.linearIndependent
    have hall : ∀ i, (IsLocalRing.residue R (x i) : κ) = 0 := by
      have := Fintype.linearIndependent_iff.mp hlin
        (fun i => IsLocalRing.residue R (x i)) h1
      exact fun i => this i
    -- Convert each component-in-𝔪 to `x ∈ 𝔪 • ⊤` via `Pi.single` decomposition.
    have hx_pi : ∀ i, x i ∈ IsLocalRing.maximalIdeal R := by
      intro i
      have : IsLocalRing.residue R (x i) = 0 := hall i
      rwa [IsLocalRing.residue_eq_zero_iff] at this
    rw [show x = ∑ i, Pi.single i (x i) from (Finset.univ_sum_single x).symm]
    refine Submodule.sum_mem _ ?_
    intro i _
    have hsingle :
        (Pi.single i (x i) : Fin n → R)
          = (x i) • (Pi.single i (1 : R) : Fin n → R) := by
      ext j; by_cases hij : i = j <;> simp [Pi.single, Function.update, hij]
    rw [hsingle]
    exact Submodule.smul_mem_smul (hx_pi i) trivial

/-! ### Bridge from the `projectiveDimension` equation to `HasProjectiveDimensionLT`

Converts the `Module.projectiveDimension R M = ((n : ℕ) : WithBot ℕ∞)` hypothesis
(the carrier used in `auslander_buchsbaum_formula` / `_succ_pd`) to Mathlib's
inductive Ext-vanishing predicate `HasProjectiveDimensionLT (ModuleCat.of R M) (n+1)`.
This single rewrite via `CategoryTheory.projectiveDimension_lt_iff` is the entry
point for the SES-descent path: once we have `HasProjectiveDimensionLT M (n+1)`,
the SES `0 → K → R^n → M → 0` plus
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁` deliver the syzygy descent
(`HasProjectiveDimensionLT K n`) abstractly, with no minimal-resolution carving
required. -/
/-- Provenance: CUSTOM. -/
lemma hasProjectiveDimensionLT_succ_of_projectiveDimension_eq
    {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (hpd : _root_.Module.projectiveDimension R M = ((n : ℕ) : WithBot ℕ∞)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) := by
  apply CategoryTheory.projectiveDimension_lt_iff.mp
  rw [show CategoryTheory.projectiveDimension (ModuleCat.of R M)
        = _root_.Module.projectiveDimension R M from rfl, hpd]
  exact_mod_cast Nat.lt_succ_self n

/-! ### Syzygy descent via `hasProjectiveDimensionLT_X₁`

For a surjection `f : R^n →ₗ M` and a bound `HasProjectiveDimensionLT M (k+2)`
on the projective dimension of `M`, the kernel `K = ker f` satisfies
`HasProjectiveDimensionLT K (k+1)`. This is the **per-syzygy** step: the
Nat-recursion on `pd` happens entirely at the Ext-vanishing-class level via
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`
applied to the SES `0 → K → R^n → M → 0`, with `R^n` projective discharged via
`ModuleCat.projective_of_free` + `projective_iff_hasProjectiveDimensionLT_one`. -/
/-- Provenance: CUSTOM. -/
lemma hasProjectiveDimensionLT_ker_of_surjection
    {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {n : ℕ} (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)
    {k : ℕ}
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 2)) :
    HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f)) (k + 1) := by
  let S := LinearMap.shortComplexKer f
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
  haveI hRn_proj : CategoryTheory.Projective (ModuleCat.of R (Fin n → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R (Fin n))
  haveI hRn_pd : HasProjectiveDimensionLT (ModuleCat.of R (Fin n → R)) (k + 1) :=
    hasProjectiveDimensionLT_of_ge _ 1 (k + 1) (by omega)
  exact hS.hasProjectiveDimensionLT_X₁ (k + 1)
    (by simpa [S] using hRn_pd) (by simpa [S] using hM)

/-! ### Projective-dimension ascent via `hasProjectiveDimensionLT_X₃`

The companion of `hasProjectiveDimensionLT_ker_of_surjection`: from a syzygy
bound `HasProjectiveDimensionLT (ker f) (k+1)` we obtain
`HasProjectiveDimensionLT M (k+2)`. Together with the descent, this gives
a clean way to extract `pd K = k+1` exactly (assuming we know
`pd M ≥ k+2`): the contrapositive form is "if `pd K < k+1` then `pd M < k+2`".
This is the input the inductive closure assembly of
`auslander_buchsbaum_formula_succ_pd` needs to extract `pd K = k` exactly. -/
/-- Provenance: CUSTOM. -/
lemma hasProjectiveDimensionLT_succ_of_hasProjectiveDimensionLT_ker
    {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {n : ℕ} (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)
    {k : ℕ}
    (hK_lt : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 2) := by
  let S := LinearMap.shortComplexKer f
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
  haveI hRn_proj : CategoryTheory.Projective (ModuleCat.of R (Fin n → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R (Fin n))
  haveI hRn_pd : HasProjectiveDimensionLT (ModuleCat.of R (Fin n → R)) (k + 2) :=
    hasProjectiveDimensionLT_of_ge _ 1 (k + 2) (by omega)
  exact hS.hasProjectiveDimensionLT_X₃ (k + 1)
    (by simpa [S] using hK_lt) (by simpa [S] using hRn_pd)

/-! ### Both `depth_of_short_exact` inequalities for the SES `0 → ker f → R^n → M → 0`

Packages parts (2) and (3) of Stacks 00LX applied to the kernel SES of a
surjection `f : R^n ↠ M` from a finite free module of rank `n ≥ 1` over a
Noetherian local ring, after identifying `depth(R^n) = depth(R)` via
`depth_pi_const_eq_depth_of_nonempty`. These are precisely the two inequalities
fed to `enat_ab_inductive_combine` to close the inductive step of the
Auslander–Buchsbaum formula. -/
/-- Provenance: CUSTOM. -/
lemma depth_ses_ineqs_of_surjection_finite_localRing
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [_root_.Module.Finite R M] [Nontrivial M]
    {n : ℕ} (hn : 1 ≤ n) (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)
    [Nontrivial (LinearMap.ker f)] :
    min (depth (IsLocalRing.maximalIdeal R) R)
        (depth (IsLocalRing.maximalIdeal R) (LinearMap.ker f) - 1)
      ≤ depth (IsLocalRing.maximalIdeal R) M
    ∧ min (depth (IsLocalRing.maximalIdeal R) R)
          (depth (IsLocalRing.maximalIdeal R) M + 1)
      ≤ depth (IsLocalRing.maximalIdeal R) (LinearMap.ker f) := by
  haveI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin n) := ⟨default⟩
  haveI : Nontrivial (Fin n → R) := Pi.nontrivial
  haveI : _root_.Module.Finite R (LinearMap.ker f) := Module.IsNoetherian.finite R _
  have hex : Function.Exact (LinearMap.ker f).subtype f :=
    LinearMap.exact_subtype_ker_map f
  have hinj : Function.Injective (LinearMap.ker f).subtype :=
    Subtype.val_injective
  have htriple := depth_of_short_exact (LinearMap.ker f).subtype f hinj hf hex
  have heq : depth (IsLocalRing.maximalIdeal R) (Fin n → R)
      = depth (IsLocalRing.maximalIdeal R) R :=
    depth_pi_const_eq_depth_of_nonempty _
  refine ⟨?_, ?_⟩
  · have h2 := htriple.2.1
    rwa [heq] at h2
  · have h3 := htriple.2.2
    rwa [heq] at h3

/-! ### Nonzero `Ext` at the depth index

The converse read-off of `depth_eq_smallest_ext_index`: for a nonzero finite
module `M` of depth exactly `↑D` over a Noetherian local ring, there is a
nonzero element of `Ext^D_R(κ, M)`. (Below `↑D` all `Ext` vanish; the strict
failure of vanishing at `↑(D+1)` must therefore occur at index `D`.) This is
the input that exhibits a nonzero class in the base case of Auslander–Buchsbaum:
`Ext^{depth R}(κ, R^k) ≠ 0`. -/
/-- Provenance: CUSTOM. -/
lemma exists_ne_zero_ext_of_depth_eq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [_root_.Module.Finite R M]
    [Nontrivial M] {D : ℕ}
    (hD : depth (IsLocalRing.maximalIdeal R) M = (D : ℕ∞)) :
    ∃ e : Abelian.Ext.{u} (ModuleCat.of R (IsLocalRing.ResidueField R))
        (ModuleCat.of R M) D, e ≠ 0 := by
  -- Below `D`, all Ext vanish.
  have hvanish : ∀ i : ℕ, i < D → ∀ e : Abelian.Ext.{u}
      (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of R M) i, e = 0 :=
    (depth_eq_smallest_ext_index (M := M) D).mp (by rw [hD])
  -- `↑(D+1) ≤ depth M` fails, so vanishing below `D+1` fails.
  have hnle : ¬ ((D + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M := by
    rw [hD, Nat.cast_le]; omega
  rw [depth_eq_smallest_ext_index (M := M) (D + 1)] at hnle
  push Not at hnle
  obtain ⟨i, hi, e, he⟩ := hnle
  have hiD : i = D := by
    by_contra hne
    have : i < D := by omega
    exact he (hvanish i this e)
  subst hiD
  exact ⟨e, he⟩

/-! ### Matrix decomposition and matrix-collapse on `Ext`

For an R-linear map `A : R^m →ₗ R^n` between standard free modules over a
commutative ring R, A decomposes as `A = ∑_{(i,j)} A_{i,j} • E_{i,j}` where
`A_{i,j} = (A (Pi.single j 1)) i` is the matrix entry and `E_{i,j}` is the
"elementary" linear map sending `Pi.single j 1 ↦ Pi.single i 1`. From this
decomposition combined with R-bilinearity of `Ext.comp` and the axiom-clean
helper `ext_smul_eq_zero_of_mem_annihilator`, we obtain the matrix-collapse
result: if every entry of A lies in `Ann_R N`, then the induced postcomposition
`Ext^p(N, R^m) → Ext^p(N, R^n)` via `mk₀ (ofHom A)` is the zero map.

This is the key substrate for the base case `pd M = 1` of the
Auslander–Buchsbaum formula: given a minimal surjection `f : R^n ↠ M`
with `ker f` free of positive rank, the inclusion `ker f ≅ R^k ↪ R^n` is an
R-linear map with entries in 𝔪 (by minimality `ker f ≤ 𝔪 • ⊤`); the
matrix-collapse then forces the LES injectivity needed to conclude
`depth M < depth R`. -/

/-- The "elementary matrix" linear map `E_{i,j} : R^m →ₗ R^n` sending
`Pi.single j 1 ↦ Pi.single i 1` and all other standard basis vectors to 0. -/
private def elemMap {R : Type u} [CommRing R] (n m : ℕ) (i : Fin n) (j : Fin m) :
    (Fin m → R) →ₗ[R] (Fin n → R) :=
  (LinearMap.toSpanSingleton R (Fin n → R) (Pi.single i (1 : R) : Fin n → R)) ∘ₗ
    (LinearMap.proj (R := R) (φ := fun _ : Fin m => R) j)

/-- The elementary map `E_{i,j}` evaluated at `x : R^m` gives `Pi.single i (x j)`. -/
private lemma elemMap_apply {R : Type u} [CommRing R] (n m : ℕ)
    (i : Fin n) (j : Fin m) (x : Fin m → R) :
    (elemMap n m i j : (Fin m → R) →ₗ[R] (Fin n → R)) x = Pi.single i (x j) := by
  classical
  change (LinearMap.toSpanSingleton R (Fin n → R)
    (Pi.single i (1 : R) : Fin n → R)) (x j) = Pi.single i (x j)
  rw [LinearMap.toSpanSingleton_apply]
  ext k
  rw [Pi.smul_apply]
  by_cases hk : k = i
  · subst hk; rw [Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, smul_zero]

/-- Matrix decomposition: every R-linear map `A : R^m →ₗ R^n` can be written
as a sum `∑_{(i,j)} A (Pi.single j 1) i • elemMap n m i j` of elementary maps
weighted by matrix entries. -/
private lemma linearMap_finFunR_matrix_decomp {R : Type u} [CommRing R] {n m : ℕ}
    (A : (Fin m → R) →ₗ[R] (Fin n → R)) :
    A = ∑ ij : Fin n × Fin m, (A (Pi.single ij.2 1) ij.1) • elemMap n m ij.1 ij.2 := by
  classical
  refine LinearMap.ext fun (x : Fin m → R) => ?_
  rw [LinearMap.sum_apply]
  rw [show A x = ∑ j : Fin m, ∑ i : Fin n,
      (A (Pi.single j 1) i) • (Pi.single i (x j) : Fin n → R) from ?_]
  · rw [← Finset.univ_product_univ, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, elemMap_apply]
  · have hx_decomp : x = ∑ j : Fin m, (x j) • (Pi.single j (1 : R) : Fin m → R) := by
      ext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    conv_lhs => rw [hx_decomp, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    ext k
    rw [Pi.smul_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, smul_eq_mul, mul_comm]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h

/-- **Matrix-collapse on Ext.** For an R-linear map `A : R^m →ₗ R^n` whose every
matrix entry `A (Pi.single j 1) i` lies in `Ann_R N`, the postcomposition map
`Ext^p(N, R^m) → Ext^p(N, R^n)` induced by `mk₀ (ofHom A)` is the zero map.

Proof: write `A = ∑_{(i,j)} A_{i,j} • E_{i,j}` via `linearMap_finFunR_matrix_decomp`.
Push through `ofHom`, `mk₀`, and `Ext.comp` using `ofHom_sum / mk₀_sum / comp_sum`
plus `ofHom_smul / mk₀_smul / comp_smul`. Each summand becomes
`A_{i,j} • (e.comp (mk₀ (ofHom (elemMap _ _ i j))))`, where the scalar `A_{i,j}`
lies in `Ann_R N`. The existing `ext_smul_eq_zero_of_mem_annihilator` (Stacks
00LW fragment) makes each such scalar action zero. Hence the total sum is zero.
(Non-private: reused by the base case of `ABFormula`.) 





 * Provenance: CUSTOM.
-/
lemma ext_comp_mk₀_ofHom_eq_zero_of_entries_mem_annihilator
    {R : Type u} [CommRing R]
    {N : ModuleCat.{u} R}
    {n m : ℕ}
    (A : (Fin m → R) →ₗ[R] (Fin n → R))
    (hA : ∀ (i : Fin n) (j : Fin m),
        A (Pi.single j 1) i ∈ _root_.Module.annihilator R (N : Type u))
    {p : ℕ} (e : Abelian.Ext.{u} N (ModuleCat.of R (Fin m → R)) p) :
    e.comp (CategoryTheory.Abelian.Ext.mk₀
              (ModuleCat.ofHom A :
                ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R)))
          (add_zero p) = 0 := by
  classical
  rw [linearMap_finFunR_matrix_decomp A]
  rw [show (ModuleCat.ofHom (∑ ij : Fin n × Fin m,
      A (Pi.single ij.2 1) ij.1 • elemMap n m ij.1 ij.2) :
      ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R))
      = ∑ ij : Fin n × Fin m, ModuleCat.ofHom
          (A (Pi.single ij.2 1) ij.1 • elemMap n m ij.1 ij.2) from by
    refine ModuleCat.hom_ext ?_
    rw [ModuleCat.hom_sum]
    rfl]
  rw [CategoryTheory.Abelian.Ext.mk₀_sum]
  rw [CategoryTheory.Abelian.Ext.comp_sum]
  apply Finset.sum_eq_zero
  intro ij _
  rw [show (ModuleCat.ofHom (A (Pi.single ij.2 1) ij.1 • elemMap n m ij.1 ij.2) :
      ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R))
      = A (Pi.single ij.2 1) ij.1 • ModuleCat.ofHom (elemMap n m ij.1 ij.2) from by
    refine ModuleCat.hom_ext ?_; rfl]
  rw [show (CategoryTheory.Abelian.Ext.mk₀
      (A (Pi.single ij.2 1) ij.1 • ModuleCat.ofHom (elemMap n m ij.1 ij.2)) :
        Abelian.Ext.{u} (ModuleCat.of R (Fin m → R)) (ModuleCat.of R (Fin n → R)) 0)
      = A (Pi.single ij.2 1) ij.1 • CategoryTheory.Abelian.Ext.mk₀
          (ModuleCat.ofHom (elemMap n m ij.1 ij.2)) from
      CategoryTheory.Abelian.Ext.mk₀_smul (R := R) _ _]
  rw [CategoryTheory.Abelian.Ext.comp_smul]
  exact ext_smul_eq_zero_of_mem_annihilator _ (hA ij.1 ij.2)


end Module

end RingTheory
