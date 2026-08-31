/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

/-!
# The two-term finite replacement of a flat complex (Mumford AV II §5 Lemma 1)

**The abstract core of the B3 `P¹`-engine and the B5 semicontinuity gate.**
Pure module theory — no schemes, no sheaves.

Let `A` be a noetherian commutative ring and `d : M⁰ →ₗ[A] M¹` a two-term
complex of **flat** `A`-modules whose cohomology `H⁰ = ker d` and
`H¹ = coker d` is finitely generated.  Then `d` admits a *finite
replacement*: a two-term complex `k : K⁰ → K¹` with `K¹` finite **free** and
`K⁰` finitely generated **projective**, together with a quasi-isomorphism
`K• → M•` whose formation commutes with arbitrary base change `A → B`: the
induced maps `H⁰(K• ⊗ B) → H⁰(M• ⊗ B)` and `H¹(K• ⊗ B) → H¹(M• ⊗ B)` are
bijective for *every* commutative `A`-algebra `B`
(`TwoTermFiniteReplacement`, `exists_twoTermFiniteReplacement`).

## Statement audit

* The classically quoted form (Mumford, *Abelian Varieties* II §5 Lemma 1;
  EGA III 6.10.5) produces `Kⁱ` finite free for `i ≥ 1` and `K⁰` finitely
  generated **projective** (= flat + finitely presented); `K⁰` can be chosen
  finite *free* only after localizing.  The finite-free-in-degree-0 form is
  **FALSE** globally: take `A` a Dedekind domain with a nonprincipal ideal
  `I`, `M⁰ := I` (flat, f.g.), `M¹ := 0`, `d := 0`.  For any two-term finite
  free complex `k : A^a → A^b` computing `H⁰ ≅ I`, `H¹ = 0` universally, `k`
  is surjective onto the free `A^b`, hence split, so `H⁰(K•) = ker k` would
  be *stably free*; over a Dedekind domain stably free implies free
  (Steinitz), contradicting `I` nonprincipal.  We therefore pin the
  projective form.  This loses nothing for the consumers: local freeness of
  `H⁰` is checked stalkwise, and finite projective modules are locally free.
* `H¹` base change (`h1_bijective`) holds for **any** complex — cokernels
  commute with the (right-exact) tensor product; the mathematical content of
  the base-change clause is in `H⁰`, where the flatness of `M¹` enters
  through purity of `ker g ↪ M⁰ × K¹` (Stacks 00HL).
* The construction: choose generators of `H¹`, lift them to
  `a1 : A^n → M¹`; set `g := d ∘ fst - a1 ∘ snd : M⁰ × A^n → M¹`
  (surjective by the choice of generators) and `K⁰ := ker g`, the fibre
  product `M⁰ ×_{M¹} A^n`.  Then `K⁰` is f.g. (extension of a submodule of
  `A^n` by `ker d`; noetherianity), flat (pure kernel of a surjection with
  flat cokernel `M¹`), hence finitely presented and projective.

## Main declarations

* `AlgebraicJacobian.TwoTerm.h0Map` / `h1Map` — the maps induced on
  kernels/cokernels by a commuting square of two-term complexes.
* `AlgebraicJacobian.TwoTerm.lTensor_injective_of_exact_of_flat` — Stacks
  00HL: a short exact sequence with flat cokernel stays left-exact after
  tensoring with anything.  One-step wrapper around mathlib's
  `lTensor_injective_of_exact_of_exact_of_rTensor_injective`.  (An
  equivalent statement `Module.Flat.lTensor_injective_of_exact` exists in
  `AlgebraicJacobian.Picard.FlatKernelBase`, but that file imports the
  scheme stack and this brick must stay Mathlib-only, hence the re-derived
  wrapper instead of an import.)
* `AlgebraicJacobian.TwoTerm.flat_prod` — a product of two flat modules is
  flat (not an instance in mathlib).
* `AlgebraicJacobian.TwoTermFiniteReplacement` — the pinned structure.
* `AlgebraicJacobian.exists_twoTermFiniteReplacement` — the existence
  theorem (Mumford AV II §5 Lemma 1, two-term case).
* `AlgebraicJacobian.TwoTerm.cokerBaseChangeEquiv` — `H¹` (top cohomology)
  commutes with arbitrary base change, for any single linear map.
* `AlgebraicJacobian.TwoTerm.subsingleton_of_forall_maximal_le_smul`,
  `surjective_of_baseChange_quotient_surjective` — fibrewise vanishing of
  `H¹` at all maximal ideals forces `H¹ = 0` (f.g. `H¹` + Nakayama).
* `AlgebraicJacobian.TwoTerm.flat_ker_of_surjective`,
  `projective_ker_of_surjective`, `bijective_kerBaseChange_of_surjective` —
  the B3 endgame: once `H¹ = 0`, the kernel `H⁰ = ker d` is finite
  projective (locally free) and its formation commutes with arbitrary base
  change.
* `AlgebraicJacobian.TwoTerm.h0_baseChange_of_fibrewise_h1_vanishing` — the
  bundled consumer corollary: fibrewise `h¹`-vanishing ⟹ `d` surjective,
  `ker d` finite projective, and `B ⊗ ker d ≅ ker (d ⊗ B)` for all `B`.

## References

Mumford, *Abelian Varieties*, II §5 Lemma 1; EGA III 6.10.5;
Stacks 00HL (purity), 0B91 ff. (cohomology and base change);
Nitsure, *Construction of Hilbert and Quot schemes*, §5.
-/

set_option autoImplicit false

universe u v

open TensorProduct LinearMap Function

namespace AlgebraicJacobian

namespace TwoTerm

/-! ## §1. Induced maps on `H⁰` and `H¹` of a commuting square

For a commuting square `d ∘ a0 = a1 ∘ k` of two-term complexes
`k : K0 → K1`, `d : M0 → M1`, the legs `a0, a1` induce maps
`ker k → ker d` (`h0Map`) and `coker k → coker d` (`h1Map`). -/

section InducedMaps

variable {R : Type*} [CommRing R]
variable {K0 K1 M0 M1 : Type*}
  [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
variable (k : K0 →ₗ[R] K1) (d : M0 →ₗ[R] M1) (a0 : K0 →ₗ[R] M0) (a1 : K1 →ₗ[R] M1)

/-- The map induced on `H⁰` (kernels) by a commuting square of two-term
complexes: `a0` restricted to `ker k → ker d`. -/
def h0Map (h : d ∘ₗ a0 = a1 ∘ₗ k) : ker k →ₗ[R] ker d :=
  a0.restrict fun x hx => by
    have hx' := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx'
    simp only [mem_ker] at hx ⊢
    rw [hx', hx, map_zero]

@[simp] lemma h0Map_apply_coe (h : d ∘ₗ a0 = a1 ∘ₗ k) (x : ker k) :
    (h0Map k d a0 a1 h x : M0) = a0 x := rfl

/-- The map induced on `H¹` (cokernels) by a commuting square of two-term
complexes: `a1` descended to `K1 ⧸ range k → M1 ⧸ range d`. -/
def h1Map (h : d ∘ₗ a0 = a1 ∘ₗ k) : (K1 ⧸ range k) →ₗ[R] (M1 ⧸ range d) :=
  Submodule.mapQ _ _ a1 <| by
    rintro x ⟨y, rfl⟩
    have hy := LinearMap.congr_fun h y
    simp only [LinearMap.comp_apply] at hy
    exact ⟨a0 y, hy⟩

@[simp] lemma h1Map_mk (h : d ∘ₗ a0 = a1 ∘ₗ k) (x : K1) :
    h1Map k d a0 a1 h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (a1 x) :=
  rfl

/-- A commuting square whose vertical maps are linear equivalences induces a
linear equivalence on degree-zero cohomology, represented as kernels. -/
noncomputable def h0LinearEquiv
    (k : K0 →ₗ[R] K1) (d : M0 →ₗ[R] M1)
    (e0 : K0 ≃ₗ[R] M0) (e1 : K1 ≃ₗ[R] M1)
    (h : d ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ k) :
    ker k ≃ₗ[R] ker d := by
  have hinv : k ∘ₗ e0.symm.toLinearMap = e1.symm.toLinearMap ∘ₗ d := by
    ext x
    apply e1.injective
    have hx := LinearMap.congr_fun h (e0.symm x)
    simpa using hx.symm
  exact
    { h0Map k d e0.toLinearMap e1.toLinearMap h with
      invFun := h0Map d k e0.symm.toLinearMap e1.symm.toLinearMap hinv
      left_inv := by
        intro x
        apply Subtype.ext
        exact e0.symm_apply_apply x.1
      right_inv := by
        intro x
        apply Subtype.ext
        exact e0.apply_symm_apply x.1 }

/-- A commuting square whose vertical maps are linear equivalences induces a
linear equivalence on degree-one cohomology, represented as quotients by the
ranges of the differentials. -/
noncomputable def h1LinearEquiv
    (k : K0 →ₗ[R] K1) (d : M0 →ₗ[R] M1)
    (e0 : K0 ≃ₗ[R] M0) (e1 : K1 ≃ₗ[R] M1)
    (h : d ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ k) :
    (K1 ⧸ range k) ≃ₗ[R] (M1 ⧸ range d) := by
  have hinv : k ∘ₗ e0.symm.toLinearMap = e1.symm.toLinearMap ∘ₗ d := by
    ext x
    apply e1.injective
    have hx := LinearMap.congr_fun h (e0.symm x)
    simpa using hx.symm
  exact
    { h1Map k d e0.toLinearMap e1.toLinearMap h with
      invFun := h1Map d k e0.symm.toLinearMap e1.symm.toLinearMap hinv
      left_inv := by
        intro x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change Submodule.Quotient.mk (e1.symm (e1 x)) = Submodule.Quotient.mk x
          rw [e1.symm_apply_apply]
      right_inv := by
        intro x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change Submodule.Quotient.mk (e1 (e1.symm x)) = Submodule.Quotient.mk x
          rw [e1.apply_symm_apply] }

end InducedMaps

section BaseChangeSquare

variable {A : Type u} [CommRing A]
variable {K0 K1 M0 M1 : Type u}
  [AddCommGroup K0] [Module A K0] [AddCommGroup K1] [Module A K1]
  [AddCommGroup M0] [Module A M0] [AddCommGroup M1] [Module A M1]
variable (k : K0 →ₗ[A] K1) (d : M0 →ₗ[A] M1) (a0 : K0 →ₗ[A] M0) (a1 : K1 →ₗ[A] M1)

/-- A commuting square of two-term complexes stays commuting after any base
change `A → B`. -/
theorem baseChange_square (B : Type v) [CommRing B] [Algebra A B]
    (h : d ∘ₗ a0 = a1 ∘ₗ k) :
    d.baseChange B ∘ₗ a0.baseChange B = a1.baseChange B ∘ₗ k.baseChange B := by
  rw [← baseChange_comp, ← baseChange_comp, h]

end BaseChangeSquare

/-! ## §2. Purity (Stacks 00HL) and flatness of products -/

section Purity

variable {R : Type*} [CommRing R]

/-- **Stacks 00HL** (purity of a flat-cokernel extension): if
`0 → N → Q → P → 0` is a short exact sequence of `R`-modules with `P` flat,
then `C ⊗ N → C ⊗ Q` is injective for *every* `R`-module `C`.

One-step wrapper around mathlib's 3×3 chase
`lTensor_injective_of_exact_of_exact_of_rTensor_injective`, instantiated at
the free presentation `ker π ↪ (C →₀ R) —π→ C → 0` of `C`.  (A twin
`Module.Flat.lTensor_injective_of_exact` lives in
`AlgebraicJacobian.Picard.FlatKernelBase`; it is deliberately not imported
here because that file depends on the scheme stack and this brick must stay
Mathlib-only.) -/
theorem lTensor_injective_of_exact_of_flat
    {N Q P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P] [Module.Flat R P]
    {ι : N →ₗ[R] Q} {g : Q →ₗ[R] P}
    (hι : Function.Injective ι) (hexact : Function.Exact ι g)
    (hg : Function.Surjective g)
    (C : Type*) [AddCommGroup C] [Module R C] :
    Function.Injective (ι.lTensor C) := by
  classical
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    ((Finsupp.linearCombination R (_root_.id : C → C)).exact_subtype_ker_map)
    (Finsupp.linearCombination_id_surjective R C)
    hexact hg
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))
    (Module.Flat.lTensor_preserves_injective_linearMap _ hι)

/-- Naturality of `TensorProduct.prodRight` in the non-product variable. -/
theorem prodRight_rTensor_apply {M N X Y : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (u : X ⊗[R] (M × N)) :
    TensorProduct.prodRight R R Y M N (f.rTensor (M × N) u)
      = ((f.rTensor M).prodMap (f.rTensor N)) (TensorProduct.prodRight R R X M N u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x mn => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- A product of two flat modules is flat.  (Not an instance in mathlib;
proved via `TensorProduct.prodRight` naturality and the ideal criterion
`Module.Flat.iff_rTensor_injective'`.) -/
theorem flat_prod {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have hM : Function.Injective (I.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
  have hN : Function.Injective (I.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
  intro x y hxy
  apply (TensorProduct.prodRight R R (↥I) M N).injective
  have h2 := congrArg (TensorProduct.prodRight R R R M N) hxy
  rw [prodRight_rTensor_apply I.subtype x, prodRight_rTensor_apply I.subtype y] at h2
  have hinj : Function.Injective ((I.subtype.rTensor M).prodMap (I.subtype.rTensor N)) := by
    rw [LinearMap.coe_prodMap]
    exact hM.prodMap hN
  exact hinj h2

end Purity

/-! ## §3. Base-change plumbing for binary products -/

section ProdBaseChange

variable {A : Type u} [CommRing A]
variable {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable (B : Type v) [CommRing B] [Algebra A B]

/-- The base change of the first projection, through
`TensorProduct.prodRight`. -/
theorem fst_baseChange_apply (u : B ⊗[A] (M × N)) :
    (LinearMap.fst A M N).baseChange B u
      = (TensorProduct.prodRight A B B M N u).1 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul b p => simp
  | add u v hu hv => simp only [map_add, hu, hv, Prod.fst_add]

/-- The base change of the second projection, through
`TensorProduct.prodRight`. -/
theorem snd_baseChange_apply (u : B ⊗[A] (M × N)) :
    (LinearMap.snd A M N).baseChange B u
      = (TensorProduct.prodRight A B B M N u).2 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul b p => simp
  | add u v hu hv => simp only [map_add, hu, hv, Prod.snd_add]

/-- Any pair of tensors is jointly hit by an element of the base-changed
product: surjectivity of `(fst ⊗ B, snd ⊗ B)`. -/
theorem exists_baseChange_prod_pair (p : B ⊗[A] M) (w : B ⊗[A] N) :
    ∃ u : B ⊗[A] (M × N),
      (LinearMap.fst A M N).baseChange B u = p ∧
        (LinearMap.snd A M N).baseChange B u = w := by
  refine ⟨(TensorProduct.prodRight A B B M N).symm (p, w), ?_, ?_⟩
  · rw [fst_baseChange_apply, LinearEquiv.apply_symm_apply]
  · rw [snd_baseChange_apply, LinearEquiv.apply_symm_apply]

end ProdBaseChange

/-! ## §4. `H¹` commutes with arbitrary base change (for any single map) -/

section CokerBaseChange

variable {A : Type u} [CommRing A]
variable {M0 M1 : Type u} [AddCommGroup M0] [Module A M0] [AddCommGroup M1] [Module A M1]

/-- **`H¹` (top cohomology) commutes with arbitrary base change.**  For any
`A`-linear `f : M0 → M1` and any commutative `A`-algebra `B`, the cokernel
of `f ⊗ B` is naturally `B ⊗ coker f`.  Right-exactness of the tensor
product; no flatness and no finiteness.  The forward map descends
`mkQ (range f) ⊗ B`. -/
noncomputable def cokerBaseChangeEquiv (f : M0 →ₗ[A] M1)
    (B : Type v) [CommRing B] [Algebra A B] :
    ((B ⊗[A] M1) ⧸ range (f.baseChange B)) ≃ₗ[B] B ⊗[A] (M1 ⧸ range f) := by
  have hexact : Function.Exact (f.baseChange B) ((range f).mkQ.baseChange B) :=
    lTensor_exact B f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  refine LinearEquiv.ofBijective
    (Submodule.liftQ _ ((range f).mkQ.baseChange B) ?_) ⟨?_, ?_⟩
  · -- `range (f ⊗ B) ≤ ker (mkQ ⊗ B)`
    rintro x ⟨y, rfl⟩
    exact hexact.apply_apply_eq_zero y
  · -- injectivity: `ker (mkQ ⊗ B) = range (f ⊗ B)`
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.liftQ_apply] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hexact y).mp hq
  · -- surjectivity, from surjectivity of `mkQ ⊗ B`
    intro z
    obtain ⟨y, rfl⟩ :=
      LinearMap.baseChange_surjective B (Submodule.mkQ_surjective (range f)) z
    exact ⟨Submodule.Quotient.mk y, Submodule.liftQ_apply _ _ _⟩

end CokerBaseChange

/-! ## §5. Nakayama: fibrewise vanishing at maximal ideals kills a finite module -/

section Nakayama

variable {A : Type u} [CommRing A]

/-- Nakayama over all maximal ideals: a finitely generated module `Q` with
`Q = 𝔪Q` for every maximal ideal `𝔪` is trivial.  (For each `𝔪`, Nakayama
produces `r ≡ 1 mod 𝔪` annihilating `Q`, so the annihilator of `Q` lies in
no maximal ideal.) -/
theorem subsingleton_of_forall_maximal_le_smul
    {Q : Type*} [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (h : ∀ (m : Ideal A), m.IsMaximal → (⊤ : Submodule A Q) ≤ m • ⊤) :
    Subsingleton Q := by
  have hann : (⊤ : Submodule A Q).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr2⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
        (Module.finite_def.mp inferInstance) (h m hm)
    have hrann : r ∈ (⊤ : Submodule A Q).annihilator :=
      Submodule.mem_annihilator.mpr fun q _ => hr2 q trivial
    have hone : (1 : A) ∈ m := by
      have := m.sub_mem (hle hrann) hr1
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr hone)
  refine subsingleton_of_forall_eq 0 fun q => ?_
  have h1 : (1 : A) ∈ (⊤ : Submodule A Q).annihilator := hann ▸ Submodule.mem_top
  simpa using Submodule.mem_annihilator.mp h1 q Submodule.mem_top

variable {M0 M1 : Type u} [AddCommGroup M0] [Module A M0] [AddCommGroup M1] [Module A M1]

/-- **Fibrewise `H¹`-vanishing forces `H¹ = 0`** (no flatness needed): if
`coker d` is finitely generated and `d ⊗ (A ⧸ 𝔪)` is surjective for every
maximal ideal `𝔪` — e.g. if `H¹(M• ⊗ κ(𝔪)) = 0` for all closed fibres —
then `d` is surjective.  Top cohomology commutes with base change
(`cokerBaseChangeEquiv`), so the hypothesis says `(coker d) ⊗ A/𝔪 = 0`, and
Nakayama over all maximal ideals kills the f.g. module `coker d`. -/
theorem surjective_of_baseChange_quotient_surjective {d : M0 →ₗ[A] M1}
    [Module.Finite A (M1 ⧸ range d)]
    (hfib : ∀ (m : Ideal A), m.IsMaximal →
      Function.Surjective (d.baseChange (A ⧸ m))) :
    Function.Surjective d := by
  rw [← range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  apply subsingleton_of_forall_maximal_le_smul (A := A)
  intro m hm
  haveI h1 : Subsingleton (((A ⧸ m) ⊗[A] M1) ⧸ range (d.baseChange (A ⧸ m))) := by
    rw [Submodule.Quotient.subsingleton_iff, range_eq_top]
    exact hfib m hm
  haveI h2 : Subsingleton ((A ⧸ m) ⊗[A] (M1 ⧸ range d)) :=
    (cokerBaseChangeEquiv d (A ⧸ m)).symm.toEquiv.subsingleton
  haveI h3 : Subsingleton
      ((M1 ⧸ range d) ⧸ (m • ⊤ : Submodule A (M1 ⧸ range d))) :=
    (TensorProduct.quotTensorEquivQuotSMul (M1 ⧸ range d) m).symm.toEquiv.subsingleton
  intro q _
  rw [← Submodule.Quotient.mk_eq_zero]
  exact Subsingleton.elim _ _

end Nakayama

/-! ## §6. The B3 endgame: `H¹ = 0` makes `H⁰` finite projective, universally -/

section KerBaseChange

variable {A : Type u} [CommRing A]
variable {M0 M1 : Type u} [AddCommGroup M0] [Module A M0] [AddCommGroup M1] [Module A M1]

/-- The canonical base-change comparison for `H⁰`: the map
`B ⊗ ker d → ker (d ⊗ B)` induced by the inclusion.  An isomorphism whenever
`d` is surjective and `M1` is flat
(`bijective_kerBaseChange_of_surjective`). -/
noncomputable def kerBaseChange (d : M0 →ₗ[A] M1)
    (B : Type v) [CommRing B] [Algebra A B] :
    (B ⊗[A] ↥(ker d)) →ₗ[B] ↥(ker (d.baseChange B)) :=
  LinearMap.codRestrict _ ((ker d).subtype.baseChange B) fun z => by
    have hzero : d ∘ₗ (ker d).subtype = 0 := by
      ext x
      exact x.2
    have h1 : d.baseChange B ∘ₗ (ker d).subtype.baseChange B = 0 := by
      rw [← baseChange_comp, hzero, baseChange_zero]
    rw [mem_ker]
    exact LinearMap.congr_fun h1 z

@[simp] lemma kerBaseChange_apply_coe (d : M0 →ₗ[A] M1)
    (B : Type v) [CommRing B] [Algebra A B] (z : B ⊗[A] ↥(ker d)) :
    (kerBaseChange d B z : B ⊗[A] M0) = (ker d).subtype.baseChange B z := rfl

/-- If `d : M0 → M1` is a surjection with `M1` flat, then `ker d` is a
*pure* submodule of `M0`: the formation of `H⁰ = ker d` commutes with
arbitrary base change.  This is the `H⁰`-half of cohomology-and-base-change
once `H¹` vanishes. -/
theorem bijective_kerBaseChange_of_surjective [Module.Flat A M1]
    {d : M0 →ₗ[A] M1} (hd : Function.Surjective d)
    (B : Type v) [CommRing B] [Algebra A B] :
    Function.Bijective (kerBaseChange d B) := by
  have hexact : Function.Exact (ker d).subtype d := d.exact_subtype_ker_map
  have hinj : Function.Injective ((ker d).subtype.lTensor B) :=
    lTensor_injective_of_exact_of_flat (Submodule.injective_subtype _) hexact hd B
  constructor
  · intro z w hzw
    apply hinj
    exact congrArg Subtype.val hzw
  · intro x
    have hexactB : Function.Exact ((ker d).subtype.baseChange B) (d.baseChange B) :=
      lTensor_exact B hexact hd
    obtain ⟨z, hz⟩ := (hexactB x.1).mp (mem_ker.mp x.2)
    exact ⟨z, Subtype.ext hz⟩

/-- If `d : M0 → M1` is a surjection of flat modules, its kernel is flat.
(Purity of `ker d ↪ M0` + the composite-injectivity trick; no noetherian
hypothesis.) -/
theorem flat_ker_of_surjective [Module.Flat A M0] [Module.Flat A M1]
    {d : M0 →ₗ[A] M1} (hd : Function.Surjective d) :
    Module.Flat A ↥(ker d) := by
  have hexact : Function.Exact (ker d).subtype d := d.exact_subtype_ker_map
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have h1 : Function.Injective (I.subtype.rTensor M0) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
  have h2 : Function.Injective ((ker d).subtype.lTensor ↥I) :=
    lTensor_injective_of_exact_of_flat (Submodule.injective_subtype _) hexact hd ↥I
  have hcomp : ((ker d).subtype.lTensor A).comp (I.subtype.rTensor ↥(ker d))
      = (I.subtype.rTensor M0).comp ((ker d).subtype.lTensor ↥I) := by
    rw [lTensor_comp_rTensor, rTensor_comp_lTensor]
  have h3 : Function.Injective
      ⇑(((ker d).subtype.lTensor A).comp (I.subtype.rTensor ↥(ker d))) := by
    rw [hcomp, coe_comp]
    exact h1.comp h2
  rw [coe_comp] at h3
  exact h3.of_comp

/-- Over a noetherian ring, the kernel of a surjection of flat modules with
finitely generated kernel is finite **projective** (= locally free): the B3
endgame conclusion for `H⁰`. -/
theorem projective_ker_of_surjective [IsNoetherianRing A]
    [Module.Flat A M0] [Module.Flat A M1]
    {d : M0 →ₗ[A] M1} (hd : Function.Surjective d) (hH0 : (ker d).FG) :
    Module.Projective A ↥(ker d) := by
  haveI : Module.Finite A ↥(ker d) := Module.Finite.iff_fg.mpr hH0
  haveI : Module.Flat A ↥(ker d) := flat_ker_of_surjective hd
  haveI : Module.FinitePresentation A ↥(ker d) :=
    Module.finitePresentation_of_finite A ↥(ker d)
  exact Module.Flat.projective_of_finitePresentation

/-- **The bundled B3 endgame** (cohomology and base change for a two-term
complex, Nitsure §5 / Mumford AV II §5): if `d : M0 → M1` is a two-term
complex of flat modules over a noetherian ring with `H⁰ = ker d` and
`H¹ = coker d` finitely generated, and `H¹` vanishes on every closed fibre
(`d ⊗ A/𝔪` surjective for all maximal `𝔪`), then `d` is surjective,
`H⁰ = ker d` is finite projective (locally free), and the formation of `H⁰`
commutes with arbitrary base change. -/
theorem h0_baseChange_of_fibrewise_h1_vanishing [IsNoetherianRing A]
    [Module.Flat A M0] [Module.Flat A M1]
    {d : M0 →ₗ[A] M1} (hH0 : (ker d).FG) [Module.Finite A (M1 ⧸ range d)]
    (hfib : ∀ (m : Ideal A), m.IsMaximal →
      Function.Surjective (d.baseChange (A ⧸ m))) :
    Function.Surjective d ∧ Module.Finite A ↥(ker d) ∧
      Module.Projective A ↥(ker d) ∧
      ∀ (B : Type v) [CommRing B] [Algebra A B],
        Function.Bijective (kerBaseChange d B) := by
  have hd := surjective_of_baseChange_quotient_surjective hfib
  exact ⟨hd, Module.Finite.iff_fg.mpr hH0, projective_ker_of_surjective hd hH0,
    fun B _ _ => bijective_kerBaseChange_of_surjective hd B⟩

/-- Surjectivity of a linear map descends along the self base change
`A ⊗[A] -` (conjugation by `TensorProduct.lid`). -/
theorem surjective_of_baseChange_self {A : Type u} [CommRing A] {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Surjective (f.baseChange A)) :
    Function.Surjective f := by
  have hnat : ∀ w : A ⊗[A] M,
      f (TensorProduct.lid A M w) = TensorProduct.lid A N (f.baseChange A w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp
    | add u v hu hv => simp [map_add, hu, hv]
  intro y
  obtain ⟨u, hu⟩ := hf ((TensorProduct.lid A N).symm y)
  refine ⟨TensorProduct.lid A M u, ?_⟩
  rw [hnat, hu, LinearEquiv.apply_symm_apply]

end KerBaseChange

end TwoTerm

/-! ## §7. The pinned structure and the existence theorem -/

section Replacement

open TwoTerm

variable {A : Type u} [CommRing A]
variable {M0 M1 : Type u} [AddCommGroup M0] [Module A M0] [AddCommGroup M1] [Module A M1]

/-- **A two-term finite replacement** of the complex `d : M0 → M1`
(Mumford AV II §5 Lemma 1; EGA III 6.10.5): a two-term complex
`k : K0 → A^n` with `K0` finite projective and `A^n` finite free, together
with a quasi-isomorphism `(a0, a1) : K• → M•` whose formation commutes with
arbitrary base change: for every commutative `A`-algebra `B` the induced
maps `H⁰(K• ⊗ B) → H⁰(M• ⊗ B)` and `H¹(K• ⊗ B) → H¹(M• ⊗ B)` are bijective.

Audit (see the file docstring): `K0` finite *free* is not achievable
globally — only finite projective — and projectivity is what the consumers
(local freeness of `H⁰`, minor/Fitting loci of `k`) actually use; after
localization `K0` becomes free and `k` a matrix. -/
structure TwoTermFiniteReplacement (d : M0 →ₗ[A] M1) : Type (u + 1) where
  /-- The rank of the degree-1 finite free term `K¹ = A^n`. -/
  n : ℕ
  /-- The degree-0 term of the replacement complex. -/
  K0 : Type u
  [addCommGroup_K0 : AddCommGroup K0]
  [module_K0 : Module A K0]
  /-- The differential `K⁰ → K¹ = A^n` of the replacement complex. -/
  k : K0 →ₗ[A] (Fin n → A)
  /-- The degree-0 leg of the quasi-isomorphism `K• → M•`. -/
  a0 : K0 →ₗ[A] M0
  /-- The degree-1 leg of the quasi-isomorphism `K• → M•`. -/
  a1 : (Fin n → A) →ₗ[A] M1
  /-- `K⁰` is finitely generated. -/
  finite_K0 : Module.Finite A K0
  /-- `K⁰` is projective (finite free is impossible globally; see audit). -/
  projective_K0 : Module.Projective A K0
  /-- `(a0, a1)` is a map of complexes. -/
  comm : d ∘ₗ a0 = a1 ∘ₗ k
  /-- The `H⁰` comparison map is bijective after arbitrary base change. -/
  h0_bijective : ∀ (B : Type u) [CommRing B] [Algebra A B],
    Function.Bijective
      (h0Map (k.baseChange B) (d.baseChange B) (a0.baseChange B) (a1.baseChange B)
        (baseChange_square k d a0 a1 B comm))
  /-- The `H¹` comparison map is bijective after arbitrary base change. -/
  h1_bijective : ∀ (B : Type u) [CommRing B] [Algebra A B],
    Function.Bijective
      (h1Map (k.baseChange B) (d.baseChange B) (a0.baseChange B) (a1.baseChange B)
        (baseChange_square k d a0 a1 B comm))

attribute [instance] TwoTermFiniteReplacement.addCommGroup_K0
  TwoTermFiniteReplacement.module_K0 TwoTermFiniteReplacement.finite_K0
  TwoTermFiniteReplacement.projective_K0

/-- **Existence of the two-term finite replacement** (Mumford AV II §5
Lemma 1, two-term case).  If `A` is noetherian, `M0`, `M1` are flat, and
`H⁰ = ker d`, `H¹ = coker d` are finitely generated, then `d` admits a
two-term finite replacement in the sense of `TwoTermFiniteReplacement`. -/
theorem exists_twoTermFiniteReplacement [IsNoetherianRing A]
    [Module.Flat A M0] [Module.Flat A M1] (d : M0 →ₗ[A] M1)
    (hH0 : (ker d).FG) [hH1 : Module.Finite A (M1 ⧸ range d)] :
    Nonempty (TwoTermFiniteReplacement d) := by
  classical
  -- Step 1: lift generators of `H¹ = coker d` to `a1 : A^n → M1`.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M1 ⧸ range d)
  choose y hy using fun i => Submodule.Quotient.mk_surjective (range d) (s i)
  set a1 : (Fin n → A) →ₗ[A] M1 := Fintype.linearCombination A y with ha1
  have hsurj1 : Function.Surjective ((range d).mkQ ∘ₗ a1) := by
    rw [← range_eq_top, range_comp, ha1, Fintype.range_linearCombination,
      Submodule.map_span, ← Set.range_comp]
    have hys : ((range d).mkQ ∘ y) = s := funext fun i => hy i
    rw [hys, hs]
  have hcover : ∀ z : M1, ∃ v : Fin n → A, z - a1 v ∈ range d := by
    intro z
    obtain ⟨v, hv⟩ := hsurj1 (Submodule.Quotient.mk z)
    refine ⟨v, ?_⟩
    have hv' : Submodule.Quotient.mk (a1 v) = (Submodule.Quotient.mk z : M1 ⧸ range d) := hv
    rw [Submodule.Quotient.eq] at hv'
    rw [← neg_sub]
    exact (range d).neg_mem hv'
  -- Step 2: the surjection `g : M0 × A^n → M1` and its kernel, the fibre product.
  set g : (M0 × (Fin n → A)) →ₗ[A] M1 :=
    d ∘ₗ LinearMap.fst A M0 (Fin n → A) - a1 ∘ₗ LinearMap.snd A M0 (Fin n → A) with hgdef
  have hgapply : ∀ p : M0 × (Fin n → A), g p = d p.1 - a1 p.2 := fun p => rfl
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨v, x, hx⟩ := hcover z
    refine ⟨(x, -v), ?_⟩
    rw [hgapply]
    simp only [map_neg, sub_neg_eq_add]
    rw [hx]
    abel
  set N := ker g with hNdef
  have hexact : Function.Exact N.subtype g := g.exact_subtype_ker_map
  have hι : Function.Injective N.subtype := Submodule.injective_subtype N
  set k : N →ₗ[A] (Fin n → A) := LinearMap.snd A M0 (Fin n → A) ∘ₗ N.subtype with hk
  set a0 : N →ₗ[A] M0 := LinearMap.fst A M0 (Fin n → A) ∘ₗ N.subtype with ha0
  have hcomm : d ∘ₗ a0 = a1 ∘ₗ k := by
    ext x
    change d x.1.1 = a1 x.1.2
    exact sub_eq_zero.mp (mem_ker.mp x.2)
  -- Step 3: `N` is finitely generated (noetherianity + f.g. `H⁰`).
  have hker_inf : N ⊓ ker (LinearMap.snd A M0 (Fin n → A))
      = Submodule.map (LinearMap.inl A M0 (Fin n → A)) (ker d) := by
    ext p
    simp only [Submodule.mem_inf, mem_ker, hNdef, Submodule.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : p.2 = 0 := h2
      have h1' : d p.1 - a1 p.2 = 0 := h1
      rw [h2', map_zero, sub_zero] at h1'
      exact ⟨p.1, h1', Prod.ext rfl h2'.symm⟩
    · rintro ⟨x, hx, rfl⟩
      constructor
      · change d x - a1 (0 : Fin n → A) = 0
        rw [map_zero, sub_zero]
        exact hx
      · rfl
  have hNfg : N.FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd A M0 (Fin n → A))
    · exact IsNoetherian.noetherian _
    · rw [hker_inf]
      exact hH0.map _
  -- Step 4: `N` is flat (purity) and projective (f.p. + flat over noetherian).
  haveI hQflat : Module.Flat A (M0 × (Fin n → A)) := flat_prod
  have hpure : ∀ (C : Type u) [AddCommGroup C] [Module A C],
      Function.Injective (N.subtype.lTensor C) := fun C _ _ =>
    lTensor_injective_of_exact_of_flat hι hexact hg C
  haveI hNflat : Module.Flat A N := by
    rw [Module.Flat.iff_rTensor_injective']
    intro I
    have h1 : Function.Injective (I.subtype.rTensor (M0 × (Fin n → A))) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
    have h2 : Function.Injective (N.subtype.lTensor ↥I) := hpure ↥I
    have hcomp : (N.subtype.lTensor A).comp (I.subtype.rTensor ↥N)
        = (I.subtype.rTensor (M0 × (Fin n → A))).comp (N.subtype.lTensor ↥I) := by
      rw [lTensor_comp_rTensor, rTensor_comp_lTensor]
    have h3 : Function.Injective
        ⇑((N.subtype.lTensor A).comp (I.subtype.rTensor ↥N)) := by
      rw [hcomp, coe_comp]
      exact h1.comp h2
    rw [coe_comp] at h3
    exact h3.of_comp
  haveI hNfin : Module.Finite A N := Module.Finite.iff_fg.mpr hNfg
  haveI hNfp : Module.FinitePresentation A N := Module.finitePresentation_of_finite A ↥N
  have hNproj : Module.Projective A N := Module.Flat.projective_of_finitePresentation
  -- Step 5: assemble; the base-change clauses by the elementwise chase.
  refine ⟨⟨n, N, k, a0, a1, hNfin, hNproj, hcomm, ?_, ?_⟩⟩
  · -- `H⁰` comparison after base change
    intro B _ _
    have hexactB : Function.Exact (N.subtype.baseChange B) (g.baseChange B) :=
      lTensor_exact B hexact hg
    have hgBC : ∀ u : B ⊗[A] (M0 × (Fin n → A)),
        g.baseChange B u
          = d.baseChange B ((LinearMap.fst A M0 (Fin n → A)).baseChange B u)
            - a1.baseChange B ((LinearMap.snd A M0 (Fin n → A)).baseChange B u) := by
      intro u
      have hg' : g.baseChange B
          = d.baseChange B ∘ₗ (LinearMap.fst A M0 (Fin n → A)).baseChange B
            - a1.baseChange B ∘ₗ (LinearMap.snd A M0 (Fin n → A)).baseChange B := by
        rw [hgdef, baseChange_sub, baseChange_comp, baseChange_comp]
      rw [hg']
      rfl
    have hkBC : k.baseChange B
        = (LinearMap.snd A M0 (Fin n → A)).baseChange B ∘ₗ N.subtype.baseChange B := by
      rw [hk, baseChange_comp]
    have ha0BC : a0.baseChange B
        = (LinearMap.fst A M0 (Fin n → A)).baseChange B ∘ₗ N.subtype.baseChange B := by
      rw [ha0, baseChange_comp]
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨z, hzmem⟩ hz
      have hz0 : a0.baseChange B z = 0 := by
        simpa using congrArg Subtype.val hz
      have hzk : k.baseChange B z = 0 := mem_ker.mp hzmem
      rw [ha0BC, LinearMap.comp_apply] at hz0
      rw [hkBC, LinearMap.comp_apply] at hzk
      have hu : TensorProduct.prodRight A B B M0 (Fin n → A)
          (N.subtype.baseChange B z) = 0 := by
        have e1 : (TensorProduct.prodRight A B B M0 (Fin n → A)
            (N.subtype.baseChange B z)).1 = 0 := by
          rw [← fst_baseChange_apply]
          exact hz0
        have e2 : (TensorProduct.prodRight A B B M0 (Fin n → A)
            (N.subtype.baseChange B z)).2 = 0 := by
          rw [← snd_baseChange_apply]
          exact hzk
        exact Prod.ext e1 e2
      have hz1 : N.subtype.baseChange B z = 0 := by
        apply (TensorProduct.prodRight A B B M0 (Fin n → A)).injective
        rw [hu, map_zero]
      have hz2 : z = 0 := by
        apply hpure B
        rw [show (N.subtype.lTensor B) z = N.subtype.baseChange B z from rfl, hz1,
          map_zero]
      exact Subtype.ext hz2
    · intro x
      obtain ⟨u, hu1, hu2⟩ :=
        exists_baseChange_prod_pair B x.1 (0 : B ⊗[A] (Fin n → A))
      have hgu : g.baseChange B u = 0 := by
        rw [hgBC, hu1, hu2, map_zero, sub_zero]
        exact mem_ker.mp x.2
      obtain ⟨z, hz⟩ := (hexactB u).mp hgu
      have hzk : k.baseChange B z = 0 := by
        rw [hkBC, LinearMap.comp_apply, hz, hu2]
      refine ⟨⟨z, mem_ker.mpr hzk⟩, ?_⟩
      apply Subtype.ext
      change a0.baseChange B z = x.1
      rw [ha0BC, LinearMap.comp_apply, hz, hu1]
  · -- `H¹` comparison after base change
    intro B _ _
    have hexactB : Function.Exact (N.subtype.baseChange B) (g.baseChange B) :=
      lTensor_exact B hexact hg
    have hgBC : ∀ u : B ⊗[A] (M0 × (Fin n → A)),
        g.baseChange B u
          = d.baseChange B ((LinearMap.fst A M0 (Fin n → A)).baseChange B u)
            - a1.baseChange B ((LinearMap.snd A M0 (Fin n → A)).baseChange B u) := by
      intro u
      have hg' : g.baseChange B
          = d.baseChange B ∘ₗ (LinearMap.fst A M0 (Fin n → A)).baseChange B
            - a1.baseChange B ∘ₗ (LinearMap.snd A M0 (Fin n → A)).baseChange B := by
        rw [hgdef, baseChange_sub, baseChange_comp, baseChange_comp]
      rw [hg']
      rfl
    have hkBC : k.baseChange B
        = (LinearMap.snd A M0 (Fin n → A)).baseChange B ∘ₗ N.subtype.baseChange B := by
      rw [hk, baseChange_comp]
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [h1Map_mk, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨p, hp⟩ := hq
      obtain ⟨u, hu1, hu2⟩ := exists_baseChange_prod_pair B p w
      have hgu : g.baseChange B u = 0 := by
        rw [hgBC, hu1, hu2, hp, sub_self]
      obtain ⟨z, hz⟩ := (hexactB u).mp hgu
      refine ⟨z, ?_⟩
      rw [hkBC, LinearMap.comp_apply, hz, hu2]
    · intro q
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨u, hu⟩ := LinearMap.baseChange_surjective B hg z
      refine ⟨Submodule.Quotient.mk
        (-(LinearMap.snd A M0 (Fin n → A)).baseChange B u), ?_⟩
      rw [h1Map_mk, Submodule.Quotient.eq]
      refine ⟨-(LinearMap.fst A M0 (Fin n → A)).baseChange B u, ?_⟩
      rw [map_neg, map_neg, ← hu, hgBC]
      abel

/-- **The split-off corollary on a replacement** (the B5 gate input): if
`H¹ = coker d` vanishes, i.e. `d` is surjective, then the differential `k`
of any finite replacement is surjective onto the finite free `K¹ = A^n` —
hence split by projectivity of `A^n`, so `K⁰ ≅ ker k ⊕ A^n` with `ker k`
finite projective realizing `H⁰`.  Proved by descending the `H¹` comparison
at `B = A` along `TensorProduct.lid`. -/
theorem TwoTermFiniteReplacement.k_surjective_of_surjective
    {d : M0 →ₗ[A] M1} (R : TwoTermFiniteReplacement d)
    (hd : Function.Surjective d) : Function.Surjective R.k := by
  apply surjective_of_baseChange_self
  rw [← range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  haveI h1 : Subsingleton ((A ⊗[A] M1) ⧸ range (d.baseChange A)) := by
    rw [Submodule.Quotient.subsingleton_iff, range_eq_top]
    exact LinearMap.baseChange_surjective A hd
  exact ⟨fun a b => (R.h1_bijective A).injective (Subsingleton.elim _ _)⟩

end Replacement

end AlgebraicJacobian
