/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RigidPushforwardP1Engine

/-!
# B3-H0 — finiteness of `H⁰(ℙ¹_A, M)`: the audited hard leaf

This file attacks the named hypothesis `hH0` of the frozen wave-4 engine
`Adelic.p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`
(`Picard/RigidPushforwardP1Engine.lean` §5): finite generation of the Čech
kernel `H⁰ = ker (moduleSectionDiffBase)` — i.e. of `Γ(ℙ¹_A, M)` — over the
base ring, for a finitely presented module `M` on `ℙ¹_A` (`A` noetherian).

## Audit verdict (recorded per lane instructions; 3 candidate routes)

* **Route C (naive two-lattice degree window) — REJECTED.**  The wave-4
  audit failure mode is real and flatness does *not* rescue it: membership
  of an overlap section in the `u`-lattice `im σ₁` bounds no `t`-degree of
  any particular representation over the `t`-ladder, because ladder
  representations are not unique (the chart modules are merely *spanned*
  by the ladder, never freely).  Base-flatness of `M` is irrelevant to this
  failure: it controls `A`-torsion, while the obstruction is geometric
  (`x`-)torsion.

* **Route B (graded Rees module `⊕ₙ H⁰(M(n))` f.g. over `A[x₀,x₁]`) —
  REJECTED.**  Finite generation of the section graded module is exactly
  the deep Serre leaf (T14 audit: `sectionGradedModule_fg`), and for ℙ¹ its
  direct proof secretly re-runs the same window difficulty: an element of
  `H⁰(M(n))` need not be a degree-`≤ n` ladder combination of low-twist
  generators without kernel control.

* **Route A′ (Serre dévissage, module-theoretic; CHOSEN).**  Stacks
  01YS/EGA III 3.2.1 run a *descending induction on cohomological degree*:
  choose a surjection `E := ⊕ᵢ O(-dᵢ) ↠ M`, with kernel `K`; then
  `H⁰(E) → H⁰(M) → H¹(K)` pins `H⁰(M)` between explicitly finite modules,
  because `H¹` of *every* coherent module is already finite — and the wave-4
  A-coefficient Laurent ladder proves exactly that
  (`RelLaurentChartData.module_finite_h1`).  On the 2-chart Čech complex the
  whole dévissage is *elementary module theory*:

  1. **Global generation is free.**  The chart extension lemma
     (`exists_pow_smul_eq_res`) produces, for chart generators `gᵢ` of
     `Γ(M, U₁)` and `g'ⱼ` of `Γ(M, U₂)`, matching sections after twisting:
     `σ₀ gᵢ = t^d • σ₁ bᵢ` and `σ₀ aⱼ = t^d • σ₁ g'ⱼ` (uniform `d` by
     raising: `x^{d-m} •`, `y^{d-n} •`).  This *is* Serre's global
     generation for ℙ¹, with no sheaf theory.
  2. **The kernel datum stays in the ladder class.**  `K` never appears as
     a sheaf: only its chart kernels `K₀ = ker φ₀ ⊆ C₀^ι` (finite over the
     noetherian chart ring — `C₀` is noetherian since it is `A`-spanned by
     coordinate powers, hence a quotient of `A[X]`) and its overlap kernel
     `K₀₁ = ker φ₀₁ ⊆ C₀₁^ι`.  The two-lattice hypotheses for `K` follow
     elementwise from the ring extension lemma (`IsLocalization` on basic
     opens) plus elementwise `x`-power-torsion of the localization kernels,
     so the wave-4 abstract core `module_finite_quotient_of_smul_laurent_pair`
     yields `H¹(K)` finite.
  3. **`H⁰(E)` reduces to `H⁰(O)`.**  The twisted line kernel
     `S_d = {(c₀, c₁) : t^d ρ₀ c₀ = ρ₁ c₁}` embeds into the structure-sheaf
     kernel `S_0` by `(c₀, c₁) ↦ (x^d c₀, c₁)`, with kernel inside the
     (A-finite, by noetherianity + ladder span + elementwise torsion)
     localization kernel `ker ρ₀`.  So the **only** geometric input beyond
     the wave-4 substrate is `hS0`: finite generation of the Čech `H⁰` of
     the *structure sheaf* — `Γ(ℙ¹_A, 𝒪) ≅ A`, an `M`-independent,
     Serre-free statement (further reduced below, by the sheaf gluing axiom
     and `Hom.module_finite_top_of_bijective_appTop`, to bijectivity of the
     comparison map `Γ(Spec A, 𝒪) → Γ(ℙ¹_A, 𝒪)` — the `B1` conclusion shape
     of `Picard/StructureSheafPushforward.lean`, pending only
     `GeometricallyIntegral (p1Over k).hom`; the single remaining sub-leaf).
  4. **The snake.**  `0 → im(H⁰E) → H⁰M → H¹K` at the level of concrete
     kernels/cokernels of linear maps (`Submodule.fg_of_fg_map_of_fg_inf_ker`
     + `Submodule.ker_liftQ`), over the noetherian base.

  The whole route is executed **abstractly** (`AlgebraicJacobian.TwoChart`
  below): pure commutative algebra over an arbitrary "two-chart Laurent
  datum", consuming only the hypotheses that the wave-4 engine substrate
  already discharges for `ℙ¹_A`.  No `SerreTwist`, no sheaf kernels, no
  chart presentations.

## Main results

* `TwoChart.exists_uniform_twisted_generators` -- aligned finite generator
  families on the two Laurent charts after one positive common twist.
* `TwoChart.fg_ker_cechDiff_of_laurent` — the abstract H⁰-finiteness
  theorem (route A′, steps 1–4).
* `Adelic.p1Cech_h0_fg_of_structure_h0_fg` — the ℙ¹_A leaf, **verbatim** in
  the engine's `hH0` shape, from the single `M`-independent hypothesis
  `hS0` (structure-sheaf Čech `H⁰` finite).
* `Adelic.p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_structure_h0_fg`
  — the composite: the full wave-4 engine conclusion with `hH0` *replaced*
  by `hS0`.
* `Scheme.AffineCoverMVSquare.fg_ker_ringSectionDiffBase_of_module_finite_top`
  + `Scheme.Hom.module_finite_top_of_bijective_appTop` +
  `Adelic.p1Cech_h0_fg_of_bijective_appTop` — the anchor `hS0` reduced (by
  sheaf gluing, no injectivity or noetherianity) to bijectivity of
  `Γ(Spec A, 𝒪) → Γ(ℙ¹_A, 𝒪)`, i.e. to the `B1` comparison-map brick.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicJacobian

namespace TwoChart

/-! ## §0. Generic finiteness bricks -/

/-- Over a noetherian ring, a submodule contained in a finitely generated
submodule is finitely generated. -/
theorem fg_of_le_of_fg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] {N P : Submodule R M} (h : N ≤ P) (hP : P.FG) : N.FG := by
  haveI : IsNoetherian R ↥P := isNoetherian_of_fg_of_noetherian P hP
  have h1 : (N.comap P.subtype).FG := IsNoetherian.noetherian _
  have h2 : (N.comap P.subtype).map P.subtype = N := by
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr h
  simpa [h2] using h1.map P.subtype

/-- **A ring `A`-spanned by the powers of one element is noetherian** (over
a noetherian `A`): it is a quotient of the polynomial ring `A[X]`. -/
theorem isNoetherianRing_of_top_le_span_pow {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [IsNoetherianRing A] {x : C}
    (hx : ⊤ ≤ Submodule.span A (Set.range fun n : ℕ => x ^ n)) :
    IsNoetherianRing C := by
  have hsurj : Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] C) := by
    intro c
    have hc : c ∈ Submodule.span A (Set.range fun n : ℕ => x ^ n) := hx trivial
    induction hc using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, rfl⟩ := hz
      exact ⟨Polynomial.X ^ n, by simp⟩
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ ihy ihz =>
      obtain ⟨p, rfl⟩ := ihy
      obtain ⟨q, rfl⟩ := ihz
      exact ⟨p + q, map_add _ _ _⟩
    | smul a z _ ih =>
      obtain ⟨p, rfl⟩ := ih
      exact ⟨a • p, map_smul _ _ _⟩
  exact isNoetherianRing_of_surjective (Polynomial A) C
    (Polynomial.aeval x : Polynomial A →ₐ[A] C).toRingHom hsurj

/-- **An elementwise `x`-power-torsion ideal is a finite `A`-module** when
the ambient ring is `A`-spanned by the powers of `x` and `A` is noetherian:
the ideal is finite over the (noetherian) ring, a single power `x^N` kills
all its generators, and the ladder truncates at height `N`. -/
theorem fg_restrictScalars_of_forall_exists_pow_mul_eq_zero {A C : Type*}
    [CommRing A] [CommRing C] [Algebra A C] [IsNoetherianRing A] {x : C}
    (hx : ⊤ ≤ Submodule.span A (Set.range fun n : ℕ => x ^ n))
    (I : Ideal C) (hI : ∀ c ∈ I, ∃ n : ℕ, x ^ n * c = 0) :
    (I.restrictScalars A).FG := by
  classical
  haveI : IsNoetherianRing C := isNoetherianRing_of_top_le_span_pow hx
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  -- a uniform kill exponent over the finite generating set
  choose! nn hnn using hI
  set N : ℕ := s.sup nn + 1 with hN
  set window : Finset C := (Finset.range N ×ˢ s).image fun p => x ^ p.1 * p.2 with hw
  -- every ladder element over `s` lies in the window span (or is zero)
  have aux : ∀ c ∈ s, ∀ j : ℕ, x ^ j * c ∈ Submodule.span A (window : Set C) := by
    intro c hc j
    rcases lt_or_ge j N with hj | hj
    · exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨(j, c), Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hj, hc⟩, rfl⟩))
    · have hcI : c ∈ I := by
        rw [← hs]; exact Submodule.subset_span hc
      have hkill : x ^ nn c * c = 0 := hnn c hcI
      have hj' : nn c ≤ j := le_trans (le_trans (Finset.le_sup hc) (Nat.le_succ _)) hj
      have : x ^ j * c = x ^ (j - nn c) * (x ^ nn c * c) := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
      rw [this, hkill, mul_zero]
      exact Submodule.zero_mem _
  -- window-span is stable under multiplication by `x`-powers
  have aux2 : ∀ (n : ℕ) (z : C), z ∈ Submodule.span A (window : Set C) →
      x ^ n * z ∈ Submodule.span A (window : Set C) := by
    intro n z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨j, c⟩, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      have hcs : c ∈ s := (Finset.mem_product.mp hp).2
      have : x ^ n * (x ^ j * c) = x ^ (n + j) * c := by
        rw [← mul_assoc, ← pow_add]
      rw [this]
      exact aux c hcs (n + j)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add p q _ _ ihp ihq => rw [mul_add]; exact Submodule.add_mem _ ihp ihq
    | smul a w _ ih =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ ih
  refine ⟨window, le_antisymm ?_ ?_⟩
  · -- span ≤ I
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨⟨j, c⟩, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
    have hcI : c ∈ I := by
      rw [← hs]; exact Submodule.subset_span (Finset.mem_product.mp hp).2
    exact I.mul_mem_left _ hcI
  · -- I ≤ span
    intro z hz
    have hz' : z ∈ Submodule.span C (s : Set C) := by rw [hs]; exact hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem c hc =>
      have : (c : C) = x ^ 0 * c := by rw [pow_zero, one_mul]
      rw [this]
      exact aux c hc 0
    | zero => exact Submodule.zero_mem _
    | add p q _ _ ihp ihq => exact Submodule.add_mem _ ihp ihq
    | smul r w _ ih =>
      have hr : r ∈ Submodule.span A (Set.range fun n : ℕ => x ^ n) := hx trivial
      have hrw : r • w = r * w := smul_eq_mul r w
      rw [hrw]
      clear hrw
      induction hr using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨n, rfl⟩ := hp
        exact aux2 n w ih
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add p q _ _ ihp ihq => rw [add_mul]; exact Submodule.add_mem _ ihp ihq
      | smul a p _ ihp =>
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ _ ihp

/-! ## §1. The Čech difference of a two-chart pair of linear maps -/

/-- The **Čech difference map** of a pair of `A`-linear maps into the overlap
module: `(m₀, m₁) ↦ σ₀ m₀ − σ₁ m₁`.  Its kernel is the concrete Čech `H⁰`
of the two-chart datum; instantiated at the ℙ¹_A section restrictions it is
(the linear-map core of) `AffineCoverMVSquare.moduleSectionDiffBase`. -/
noncomputable def cechDiff {A M₀ M₁ V : Type*} [CommRing A]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup V]
    [Module A M₀] [Module A M₁] [Module A V]
    (σ₀ : M₀ →ₗ[A] V) (σ₁ : M₁ →ₗ[A] V) : (M₀ × M₁) →ₗ[A] V :=
  σ₀ ∘ₗ LinearMap.fst A M₀ M₁ - σ₁ ∘ₗ LinearMap.snd A M₀ M₁

@[simp] lemma cechDiff_apply {A M₀ M₁ V : Type*} [CommRing A]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup V]
    [Module A M₀] [Module A M₁] [Module A V]
    (σ₀ : M₀ →ₗ[A] V) (σ₁ : M₁ →ₗ[A] V) (p : M₀ × M₁) :
    cechDiff σ₀ σ₁ p = σ₀ p.1 - σ₁ p.2 :=
  rfl

/-! ## §2. `H⁰` of the twisted line: reduction to the structure sheaf

`S_d := ker ((t^d · ρ₀) − ρ₁)` is the concrete `H⁰(ℙ¹, O(-d))`.  It embeds
into `S_0 = H⁰(O)` by `(c₀, c₁) ↦ (x^d c₀, c₁)`; the kernel of the embedding
lives inside the (elementwise `x`-power-torsion) localization kernel
`ker ρ₀`, which is `A`-finite by §0. -/

theorem fg_ker_cechDiff_twisted {A C₀ C₁ C₀₁ : Type*} [CommRing A]
    [CommRing C₀] [CommRing C₁] [CommRing C₀₁]
    [Algebra A C₀] [Algebra A C₁] [Algebra A C₀₁] [IsNoetherianRing A]
    (ρ₀ : C₀ →ₐ[A] C₀₁) (ρ₁ : C₁ →ₐ[A] C₀₁) (x : C₀) (y : C₁)
    (htu : ρ₀ x * ρ₁ y = 1)
    (hspan₀ : ⊤ ≤ Submodule.span A (Set.range fun n : ℕ => x ^ n))
    (hRtor₀ : ∀ c : C₀, ρ₀ c = 0 → ∃ n : ℕ, x ^ n * c = 0)
    (hS0 : (LinearMap.ker (cechDiff ρ₀.toLinearMap ρ₁.toLinearMap)).FG) (d : ℕ) :
    (LinearMap.ker
      (cechDiff (LinearMap.mulLeft A (ρ₀ x ^ d) ∘ₗ ρ₀.toLinearMap) ρ₁.toLinearMap)).FG := by
  classical
  have hpow : ∀ n : ℕ, ρ₁ y ^ n * ρ₀ x ^ n = 1 := fun n => by
    rw [← mul_pow, mul_comm (ρ₁ y) (ρ₀ x), htu, one_pow]
  -- the multiplication-by-`x^d` comparison map into `S_0`
  set μ : (C₀ × C₁) →ₗ[A] (C₀ × C₁) :=
    (LinearMap.mulLeft A (x ^ d)).prodMap LinearMap.id with hμ
  refine Submodule.fg_of_fg_map_of_fg_inf_ker μ ?_ ?_
  · -- the image lands in `S_0`
    refine fg_of_le_of_fg ?_ hS0
    rintro _ ⟨⟨c₀, c₁⟩, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hc
    rw [LinearMap.mem_ker]
    rw [cechDiff_apply] at hc ⊢
    simp only [hμ, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, LinearMap.id_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply] at hc
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_mul, map_pow]
    exact hc
  · -- the kernel of the comparison sits inside `(ker ρ₀) × ⊥`, which is `A`-finite
    have hle : LinearMap.ker (cechDiff (LinearMap.mulLeft A (ρ₀ x ^ d) ∘ₗ ρ₀.toLinearMap)
        ρ₁.toLinearMap) ⊓ LinearMap.ker μ ≤
        ((RingHom.ker (ρ₀ : C₀ →+* C₀₁)).restrictScalars A).prod ⊥ := by
      rintro ⟨c₀, c₁⟩ hmem
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hmem
      rw [LinearMap.mem_ker] at h1 h2
      have hc₁ : c₁ = 0 := congrArg Prod.snd h2
      have h1' : ρ₀ x ^ d * ρ₀ c₀ = 0 := by
        rw [cechDiff_apply] at h1
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
          AlgHom.toLinearMap_apply] at h1
        rw [hc₁, map_zero, sub_zero] at h1
        exact h1
      have hker : ρ₀ c₀ = 0 := by
        have h := congrArg (fun z => ρ₁ y ^ d * z) h1'
        simpa [← mul_assoc, hpow d] using h
      refine Submodule.mem_prod.mpr ⟨?_, ?_⟩
      · simpa [Submodule.restrictScalars_mem, RingHom.mem_ker] using hker
      · simp [hc₁]
    refine fg_of_le_of_fg hle (Submodule.FG.prod ?_ Submodule.fg_bot)
    exact fg_restrictScalars_of_forall_exists_pow_mul_eq_zero hspan₀
      (RingHom.ker (ρ₀ : C₀ →+* C₀₁)) (fun c hc => hRtor₀ c (RingHom.mem_ker.mp hc))

/-! ## §3. The abstract `H⁰`-finiteness theorem for a two-chart Laurent datum

Route A′, steps 1–4 of the module docstring, in pure commutative algebra.
The data mirror `Scheme.RelLaurentChartData` + a quasi-coherent module on the
total space: chart rings `C₀, C₁`, overlap ring `C₀₁` with restrictions
`ρ₀, ρ₁` and mutually inverse coordinates `t = ρ₀ x`, `u = ρ₁ y`; chart
section modules `M₀, M₁`, overlap module `V`, semilinear restrictions
`σ₀, σ₁`; ladder spans, extension (localization surjectivity) and
elementwise-torsion (localization kernels) hypotheses; and the single
`M`-independent anchor `hS0` = finite generation of the structure-sheaf
Čech kernel. -/

/-- **Uniform twisted generators on two Laurent charts.** Given finite chart
modules whose sections extend across the overlap after multiplying by a power
of the opposite coordinate, there is one positive twist `d` and finite
generating families `aa`, `bb` on the two charts satisfying
`σ₀ (aa i) = (ρ₀ x)^d • σ₁ (bb i)` for every index.

This is the algebraic globalization datum used by the Čech dévissage below.
It also supplies the aligned homogeneous coordinates needed to embed a finite
cover of the projective line into projective space. -/
theorem exists_uniform_twisted_generators
    {A C₀ C₁ C₀₁ M₀ M₁ V : Type*} [CommRing A]
    [CommRing C₀] [CommRing C₁] [CommRing C₀₁]
    [Algebra A C₀] [Algebra A C₁] [Algebra A C₀₁]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup V]
    [Module C₀ M₀] [Module C₁ M₁] [Module C₀₁ V]
    [Module A M₀] [Module A M₁] [Module A V]
    [Module.Finite C₀ M₀] [Module.Finite C₁ M₁]
    (ρ₀ : C₀ →ₐ[A] C₀₁) (ρ₁ : C₁ →ₐ[A] C₀₁) (x : C₀) (y : C₁)
    (htu : ρ₀ x * ρ₁ y = 1)
    (σ₀ : M₀ →ₗ[A] V) (σ₁ : M₁ →ₗ[A] V)
    (hσ₀ : ∀ (c : C₀) (m : M₀), σ₀ (c • m) = ρ₀ c • σ₀ m)
    (hσ₁ : ∀ (c : C₁) (m : M₁), σ₁ (c • m) = ρ₁ c • σ₁ m)
    (hext₀ : ∀ v : V, ∃ (n : ℕ) (m : M₀), ρ₀ x ^ n • v = σ₀ m)
    (hext₁ : ∀ v : V, ∃ (n : ℕ) (m : M₁), ρ₁ y ^ n • v = σ₁ m) :
    ∃ (n₀ n₁ d : ℕ) (aa : Fin n₀ ⊕ Fin n₁ → M₀)
      (bb : Fin n₀ ⊕ Fin n₁ → M₁),
      0 < d ∧
        (∀ i, σ₀ (aa i) = ρ₀ x ^ d • σ₁ (bb i)) ∧
        Submodule.span C₀ (Set.range aa) = ⊤ ∧
        Submodule.span C₁ (Set.range bb) = ⊤ := by
  classical
  have hpow : ∀ n : ℕ, ρ₀ x ^ n * ρ₁ y ^ n = 1 := fun n => by
    rw [← mul_pow, htu, one_pow]
  obtain ⟨n₀, g, hg⟩ := Module.Finite.exists_fin (R := C₀) (M := M₀)
  obtain ⟨n₁, g', hg'⟩ := Module.Finite.exists_fin (R := C₁) (M := M₁)
  choose nb b hb using fun i : Fin n₀ => hext₁ (σ₀ (g i))
  choose ma a ha using fun j : Fin n₁ => hext₀ (σ₁ (g' j))
  set d : ℕ := max (max (Finset.univ.sup nb) (Finset.univ.sup ma)) 1
  have hd : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hdb : ∀ i, nb i ≤ d := fun i =>
    le_trans (Finset.le_sup (Finset.mem_univ i))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hda : ∀ j, ma j ≤ d := fun j =>
    le_trans (Finset.le_sup (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_left _ _))
  let aa : Fin n₀ ⊕ Fin n₁ → M₀ :=
    Sum.elim g (fun j => x ^ (d - ma j) • a j)
  let bb : Fin n₀ ⊕ Fin n₁ → M₁ :=
    Sum.elim (fun i => y ^ (d - nb i) • b i) g'
  have hab : ∀ i, σ₀ (aa i) = ρ₀ x ^ d • σ₁ (bb i) := by
    rintro (i | j)
    · have e1 : σ₁ (bb (Sum.inl i)) = ρ₁ y ^ (d - nb i) • σ₁ (b i) := by
        simp only [bb, Sum.elim_inl]
        rw [hσ₁, map_pow]
      have e2 : ρ₀ x ^ d * ρ₁ y ^ (d - nb i) = ρ₀ x ^ nb i := by
        have hsplit : ρ₀ x ^ d = ρ₀ x ^ nb i * ρ₀ x ^ (d - nb i) := by
          rw [← pow_add]
          congr 1
          have := hdb i
          omega
        rw [hsplit, mul_assoc, hpow (d - nb i), mul_one]
      calc σ₀ (aa (Sum.inl i)) = σ₀ (g i) := by simp only [aa, Sum.elim_inl]
        _ = (1 : C₀₁) • σ₀ (g i) := (one_smul _ _).symm
        _ = (ρ₀ x ^ nb i * ρ₁ y ^ nb i) • σ₀ (g i) := by rw [hpow]
        _ = ρ₀ x ^ nb i • (ρ₁ y ^ nb i • σ₀ (g i)) := by rw [mul_smul]
        _ = ρ₀ x ^ nb i • σ₁ (b i) := by rw [hb i]
        _ = (ρ₀ x ^ d * ρ₁ y ^ (d - nb i)) • σ₁ (b i) := by rw [e2]
        _ = ρ₀ x ^ d • (ρ₁ y ^ (d - nb i) • σ₁ (b i)) := by rw [mul_smul]
        _ = ρ₀ x ^ d • σ₁ (bb (Sum.inl i)) := by rw [← e1]
    · have e3 : (d - ma j) + ma j = d := by
        have := hda j
        omega
      calc σ₀ (aa (Sum.inr j)) = σ₀ (x ^ (d - ma j) • a j) := by
              simp only [aa, Sum.elim_inr]
        _ = ρ₀ x ^ (d - ma j) • σ₀ (a j) := by rw [hσ₀, map_pow]
        _ = ρ₀ x ^ (d - ma j) • (ρ₀ x ^ ma j • σ₁ (g' j)) := by rw [ha j]
        _ = (ρ₀ x ^ (d - ma j) * ρ₀ x ^ ma j) • σ₁ (g' j) := by
              rw [mul_smul]
        _ = ρ₀ x ^ d • σ₁ (bb (Sum.inr j)) := by
              rw [← pow_add, e3]
              simp only [bb, Sum.elim_inr]
  have hspanaa : Submodule.span C₀ (Set.range aa) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hg]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, by simp only [aa, Sum.elim_inl]⟩
  have hspanbb : Submodule.span C₁ (Set.range bb) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hg']
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inr j, by simp only [bb, Sum.elim_inr]⟩
  exact ⟨n₀, n₁, d, aa, bb, hd, hab, hspanaa, hspanbb⟩

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: a single long dévissage (uniform twisted family → kernel
-- datum → two-lattice core → snake) in one instance-heavy `letI`-free context.
/-- **Abstract `H⁰`-finiteness for a two-chart Laurent datum** (Serre
dévissage, Stacks 01YS / EGA III 3.2.1, made module-theoretic on the
two-term Čech complex).  For a noetherian base `A`, chart-finite `M₀, M₁`,
and the localization-style extension/torsion hypotheses of the wave-4
substrate, the Čech kernel `H⁰ = ker (σ₀ − σ₁)` is a finitely generated
`A`-submodule — given `hS0`, finiteness of the structure-sheaf Čech kernel
(`H⁰(O)`; the `M`-independent anchor).

Proof: uniform twisted generating family (`σ₀ aᵢ = t^d • σ₁ bᵢ` with the
`aᵢ` generating `M₀` over `C₀` and `bᵢ` generating `M₁` over `C₁`), giving
a twisted free datum `E = O(-d)^ι ↠ M`; its kernel datum `K` satisfies the
two-lattice hypotheses elementwise, so `Ȟ¹(K)` is `A`-finite by the wave-4
core `module_finite_quotient_of_smul_laurent_pair`; `Ȟ⁰(E) ≅ (S_d)^ι` is
`A`-finite by the `x^d`-embedding into `S_0`; and the connecting snake
`0 → im Ȟ⁰(E) → Ȟ⁰(M) → Ȟ¹(K)` finishes over the noetherian base. -/
theorem fg_ker_cechDiff_of_laurent {A C₀ C₁ C₀₁ M₀ M₁ V : Type*} [CommRing A]
    [CommRing C₀] [CommRing C₁] [CommRing C₀₁]
    [Algebra A C₀] [Algebra A C₁] [Algebra A C₀₁] [IsNoetherianRing A]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup V]
    [Module C₀ M₀] [Module C₁ M₁] [Module C₀₁ V]
    [Module A M₀] [Module A M₁] [Module A V]
    [IsScalarTower A C₀ M₀] [IsScalarTower A C₁ M₁] [IsScalarTower A C₀₁ V]
    [Module.Finite C₀ M₀] [Module.Finite C₁ M₁]
    (ρ₀ : C₀ →ₐ[A] C₀₁) (ρ₁ : C₁ →ₐ[A] C₀₁) (x : C₀) (y : C₁)
    (htu : ρ₀ x * ρ₁ y = 1)
    (hspan₀ : ⊤ ≤ Submodule.span A (Set.range fun n : ℕ => x ^ n))
    (σ₀ : M₀ →ₗ[A] V) (σ₁ : M₁ →ₗ[A] V)
    (hσ₀ : ∀ (c : C₀) (m : M₀), σ₀ (c • m) = ρ₀ c • σ₀ m)
    (hσ₁ : ∀ (c : C₁) (m : M₁), σ₁ (c • m) = ρ₁ c • σ₁ m)
    (hext₀ : ∀ v : V, ∃ (n : ℕ) (m : M₀), ρ₀ x ^ n • v = σ₀ m)
    (hext₁ : ∀ v : V, ∃ (n : ℕ) (m : M₁), ρ₁ y ^ n • v = σ₁ m)
    (htor₀ : ∀ m : M₀, σ₀ m = 0 → ∃ n : ℕ, x ^ n • m = 0)
    (htor₁ : ∀ m : M₁, σ₁ m = 0 → ∃ n : ℕ, y ^ n • m = 0)
    (hRext₀ : ∀ c : C₀₁, ∃ (n : ℕ) (q : C₀), ρ₀ x ^ n * c = ρ₀ q)
    (hRext₁ : ∀ c : C₀₁, ∃ (n : ℕ) (q : C₁), ρ₁ y ^ n * c = ρ₁ q)
    (hRtor₀ : ∀ c : C₀, ρ₀ c = 0 → ∃ n : ℕ, x ^ n * c = 0)
    (hS0 : (LinearMap.ker (cechDiff ρ₀.toLinearMap ρ₁.toLinearMap)).FG) :
    (LinearMap.ker (cechDiff σ₀ σ₁)).FG := by
  classical
  have hpow : ∀ n : ℕ, ρ₀ x ^ n * ρ₁ y ^ n = 1 := fun n => by
    rw [← mul_pow, htu, one_pow]
  haveI hNC₀ : IsNoetherianRing C₀ := isNoetherianRing_of_top_le_span_pow hspan₀
  -- ### Step 1: the uniform twisted generating family
  obtain ⟨n₀, n₁, d, aa, bb, -, hab, hspanaa, hspanbb⟩ :=
    exists_uniform_twisted_generators ρ₀ ρ₁ x y htu σ₀ σ₁ hσ₀ hσ₁ hext₀ hext₁
  -- ### Step 2: the twisted free datum `E` and its chart surjections
  set φ₀ : (Fin n₀ ⊕ Fin n₁ → C₀) →ₗ[C₀] M₀ := Fintype.linearCombination C₀ aa with hφ₀
  set φ₁ : (Fin n₀ ⊕ Fin n₁ → C₁) →ₗ[C₁] M₁ := Fintype.linearCombination C₁ bb with hφ₁
  set φ₀₁ : (Fin n₀ ⊕ Fin n₁ → C₀₁) →ₗ[C₀₁] V :=
    Fintype.linearCombination C₀₁ (fun i => σ₁ (bb i)) with hφ₀₁
  have hφ₀surj : Function.Surjective φ₀ := by
    rw [← LinearMap.range_eq_top, hφ₀, Fintype.range_linearCombination, hspanaa]
  have hφ₁surj : Function.Surjective φ₁ := by
    rw [← LinearMap.range_eq_top, hφ₁, Fintype.range_linearCombination, hspanbb]
  set ε₀ : (Fin n₀ ⊕ Fin n₁ → C₀) →ₗ[A] (Fin n₀ ⊕ Fin n₁ → C₀₁) :=
    LinearMap.pi (fun i =>
      LinearMap.mulLeft A (ρ₀ x ^ d) ∘ₗ ρ₀.toLinearMap ∘ₗ LinearMap.proj i) with hε₀
  set ε₁ : (Fin n₀ ⊕ Fin n₁ → C₁) →ₗ[A] (Fin n₀ ⊕ Fin n₁ → C₀₁) :=
    LinearMap.pi (fun i => ρ₁.toLinearMap ∘ₗ LinearMap.proj i) with hε₁
  have hε₀apply : ∀ (e : Fin n₀ ⊕ Fin n₁ → C₀) (i : Fin n₀ ⊕ Fin n₁),
      ε₀ e i = ρ₀ x ^ d * ρ₀ (e i) := fun e i => rfl
  have hε₁apply : ∀ (e : Fin n₀ ⊕ Fin n₁ → C₁) (i : Fin n₀ ⊕ Fin n₁),
      ε₁ e i = ρ₁ (e i) := fun e i => rfl
  -- the commuting squares
  have hsq₀ : ∀ e, φ₀₁ (ε₀ e) = σ₀ (φ₀ e) := by
    intro e
    rw [hφ₀₁, hφ₀, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hσ₀, hab i, smul_smul, hε₀apply, mul_comm]
  have hsq₁ : ∀ e, φ₀₁ (ε₁ e) = σ₁ (φ₁ e) := by
    intro e
    rw [hφ₀₁, hφ₁, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hσ₁, hε₁apply]
  -- semilinearity of the twisted inclusions over the coordinates
  have hε₀x : ∀ (j : ℕ) (e : Fin n₀ ⊕ Fin n₁ → C₀), ε₀ (x ^ j • e) = ρ₀ x ^ j • ε₀ e := by
    intro j e
    funext i
    rw [hε₀apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hε₀apply,
      map_mul, map_pow]
    ring
  have hε₁y : ∀ (j : ℕ) (e : Fin n₀ ⊕ Fin n₁ → C₁), ε₁ (y ^ j • e) = ρ₁ y ^ j • ε₁ e := by
    intro j e
    funext i
    rw [hε₁apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hε₁apply,
      map_mul, map_pow]
  -- ### Step 3: the kernel datum `K` and `Ȟ¹(K)` finiteness
  set K₀ : Submodule C₀ (Fin n₀ ⊕ Fin n₁ → C₀) := LinearMap.ker φ₀ with hK₀
  set K₁ : Submodule C₁ (Fin n₀ ⊕ Fin n₁ → C₁) := LinearMap.ker φ₁ with hK₁
  set K01 : Submodule C₀₁ (Fin n₀ ⊕ Fin n₁ → C₀₁) := LinearMap.ker φ₀₁ with hK01
  haveI hKfin : Module.Finite C₀ ↥K₀ :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K₀)
  haveI hscc : SMulCommClass A C₀₁ ↥K01 :=
    ⟨fun r c m => Subtype.ext (smul_comm r c (m : Fin n₀ ⊕ Fin n₁ → C₀₁))⟩
  have hε₀K : ∀ e ∈ K₀, ε₀ e ∈ K01 := by
    intro e he
    rw [hK01, LinearMap.mem_ker, hsq₀, LinearMap.mem_ker.mp he, map_zero]
  have hε₁K : ∀ e ∈ K₁, ε₁ e ∈ K01 := by
    intro e he
    rw [hK01, LinearMap.mem_ker, hsq₁, LinearMap.mem_ker.mp he, map_zero]
  set κ₀ : ↥K₀ →ₗ[A] ↥K01 :=
    { toFun := fun e => ⟨ε₀ e.1, hε₀K _ e.2⟩
      map_add' := fun e f => Subtype.ext (by
        change ε₀ (e.1 + f.1) = ε₀ e.1 + ε₀ f.1
        rw [map_add])
      map_smul' := fun r e => Subtype.ext (by
        change ε₀ (r • e.1) = r • ε₀ e.1
        rw [map_smul]) } with hκ₀
  set κ₁ : ↥K₁ →ₗ[A] ↥K01 :=
    { toFun := fun e => ⟨ε₁ e.1, hε₁K _ e.2⟩
      map_add' := fun e f => Subtype.ext (by
        change ε₁ (e.1 + f.1) = ε₁ e.1 + ε₁ f.1
        rw [map_add])
      map_smul' := fun r e => Subtype.ext (by
        change ε₁ (r • e.1) = r • ε₁ e.1
        rw [map_smul]) } with hκ₁
  have hκ₀x : ∀ (j : ℕ) (e : ↥K₀), κ₀ (x ^ j • e) = ρ₀ x ^ j • κ₀ e := by
    intro j e
    refine Subtype.ext ?_
    change ε₀ (x ^ j • e.1) = ρ₀ x ^ j • ε₀ e.1
    exact hε₀x j _
  have hκ₁y : ∀ (j : ℕ) (e : ↥K₁), κ₁ (y ^ j • e) = ρ₁ y ^ j • κ₁ e := by
    intro j e
    refine Subtype.ext ?_
    change ε₁ (y ^ j • e.1) = ρ₁ y ^ j • ε₁ e.1
    exact hε₁y j _
  -- t-side extension for the kernel datum
  have hextK₀ : ∀ κ : ↥K01, ∃ (n : ℕ) (e : ↥K₀), ρ₀ x ^ n • κ = κ₀ e := by
    intro κ
    choose nn cc hcc using fun i : Fin n₀ ⊕ Fin n₁ => hRext₀ (κ.1 i)
    set N : ℕ := Finset.univ.sup nn with hN
    set e : Fin n₀ ⊕ Fin n₁ → C₀ := fun i => x ^ (N - nn i) * cc i with he
    have he₀ : ε₀ e = ρ₀ x ^ (d + N) • (κ : Fin n₀ ⊕ Fin n₁ → C₀₁) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, hε₀apply, he]
      rw [map_mul, map_pow, ← hcc i]
      have hexp : ρ₀ x ^ d * (ρ₀ x ^ (N - nn i) * (ρ₀ x ^ nn i * κ.1 i)) =
          (ρ₀ x ^ d * ρ₀ x ^ (N - nn i) * ρ₀ x ^ nn i) * κ.1 i := by ring
      rw [hexp, ← pow_add, ← pow_add,
        show d + (N - nn i) + nn i = d + N by
          have : nn i ≤ N := Finset.le_sup (Finset.mem_univ i)
          omega]
    have hφe : σ₀ (φ₀ e) = 0 := by
      rw [← hsq₀, he₀, map_smul, LinearMap.mem_ker.mp κ.2, smul_zero]
    obtain ⟨m, hm⟩ := htor₀ (φ₀ e) hφe
    have hmem : x ^ m • e ∈ K₀ := by
      rw [hK₀, LinearMap.mem_ker, map_smul, hm]
    refine ⟨m + (d + N), ⟨x ^ m • e, hmem⟩, ?_⟩
    refine Subtype.ext ?_
    change ρ₀ x ^ (m + (d + N)) • κ.1 = ε₀ (x ^ m • e)
    rw [hε₀x m e, he₀, smul_smul, ← pow_add]
  -- u-side extension for the kernel datum
  have hextK₁ : ∀ κ : ↥K01, ∃ (n : ℕ) (e : ↥K₁), ρ₁ y ^ n • κ = κ₁ e := by
    intro κ
    choose nn cc hcc using fun i : Fin n₀ ⊕ Fin n₁ => hRext₁ (κ.1 i)
    set N : ℕ := Finset.univ.sup nn with hN
    set e : Fin n₀ ⊕ Fin n₁ → C₁ := fun i => y ^ (N - nn i) * cc i with he
    have he₀ : ε₁ e = ρ₁ y ^ N • (κ : Fin n₀ ⊕ Fin n₁ → C₀₁) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, hε₁apply, he]
      rw [map_mul, map_pow, ← hcc i]
      have hexp : ρ₁ y ^ (N - nn i) * (ρ₁ y ^ nn i * κ.1 i) =
          (ρ₁ y ^ (N - nn i) * ρ₁ y ^ nn i) * κ.1 i := by ring
      rw [hexp, ← pow_add,
        show N - nn i + nn i = N by
          have : nn i ≤ N := Finset.le_sup (Finset.mem_univ i)
          omega]
    have hφe : σ₁ (φ₁ e) = 0 := by
      rw [← hsq₁, he₀, map_smul, LinearMap.mem_ker.mp κ.2, smul_zero]
    obtain ⟨m, hm⟩ := htor₁ (φ₁ e) hφe
    have hmem : y ^ m • e ∈ K₁ := by
      rw [hK₁, LinearMap.mem_ker, map_smul, hm]
    refine ⟨m + N, ⟨y ^ m • e, hmem⟩, ?_⟩
    refine Subtype.ext ?_
    change ρ₁ y ^ (m + N) • κ.1 = ε₁ (y ^ m • e)
    rw [hε₁y m e, he₀, smul_smul, ← pow_add]
  -- the two lattices in `K₀₁` and the ladder span
  set NL₀ : Submodule A ↥K01 := LinearMap.range κ₀ with hNL₀
  set NL₁ : Submodule A ↥K01 := LinearMap.range κ₁ with hNL₁
  have h₀stab : ∀ z ∈ NL₀, ρ₀ x • z ∈ NL₀ := by
    rintro _ ⟨e, rfl⟩
    refine ⟨x • e, ?_⟩
    have h := hκ₀x 1 e
    rw [pow_one, pow_one] at h
    exact h
  have h₁stab : ∀ z ∈ NL₁, ρ₁ y • z ∈ NL₁ := by
    rintro _ ⟨e, rfl⟩
    refine ⟨y • e, ?_⟩
    have h := hκ₁y 1 e
    rw [pow_one, pow_one] at h
    exact h
  obtain ⟨G, hG⟩ := AlgebraicGeometry.Adelic.exists_finset_forall_mem_span_pow_smul
    (A := A) (MM := ↥K₀) x hspan₀
  set s : Set ↥K01 := ⇑κ₀ '' ↑G with hsdef
  have Hpow : ∀ κ : ↥K01, ∃ n : ℕ,
      ρ₀ x ^ n • κ ∈ Submodule.span A (⋃ j : ℕ, (fun z => ρ₀ x ^ j • z) '' s) := by
    intro κ
    obtain ⟨n, e, he⟩ := hextK₀ κ
    refine ⟨n, ?_⟩
    rw [he]
    have h1 : κ₀ e ∈ Submodule.map κ₀ (Submodule.span A
        (⋃ j : ℕ, (fun z => x ^ j • z) '' (G : Set ↥K₀))) :=
      Submodule.mem_map_of_mem (hG e)
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨j, w, hw, rfl⟩ := hz
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, ⟨κ₀ w, ⟨w, hw, rfl⟩, ?_⟩⟩)
    exact (hκ₀x j w).symm
  have hspanladder := AlgebraicGeometry.Adelic.span_smul_ladder_of_pow_smul_mem_span
    (A := A) htu s Hpow
  have hsfin : s.Finite := G.finite_toSet.image _
  have hsNL₀ : s ⊆ (NL₀ : Set ↥K01) := by
    rintro _ ⟨w, _, rfl⟩
    exact ⟨w, rfl⟩
  have hextcore : ∀ z ∈ s, ∃ n : ℕ, ρ₁ y ^ n • z ∈ NL₁ := by
    intro z _
    obtain ⟨n, e, he⟩ := hextK₁ z
    exact ⟨n, he ▸ ⟨e, rfl⟩⟩
  have hQfin : Module.Finite A (↥K01 ⧸ (NL₀ ⊔ NL₁)) :=
    AlgebraicGeometry.Adelic.module_finite_quotient_of_smul_laurent_pair
      h₀stab h₁stab hsfin hsNL₀ hspanladder hextcore
  -- ### Step 4: `Ȟ⁰(E)` is `A`-finite via the twisted-line reduction
  set τ₀ : C₀ →ₗ[A] C₀₁ := LinearMap.mulLeft A (ρ₀ x ^ d) ∘ₗ ρ₀.toLinearMap with hτ₀
  have hSd : (LinearMap.ker (cechDiff τ₀ ρ₁.toLinearMap)).FG :=
    fg_ker_cechDiff_twisted ρ₀ ρ₁ x y htu hspan₀ hRtor₀ hS0 d
  set DE : ((Fin n₀ ⊕ Fin n₁ → C₀) × (Fin n₀ ⊕ Fin n₁ → C₁)) →ₗ[A]
      (Fin n₀ ⊕ Fin n₁ → C₀₁) := cechDiff ε₀ ε₁ with hDE
  have hDEmem : ∀ z : (Fin n₀ ⊕ Fin n₁ → C₀) × (Fin n₀ ⊕ Fin n₁ → C₁),
      z ∈ LinearMap.ker DE ↔
        ∀ i, cechDiff τ₀ ρ₁.toLinearMap (z.1 i, z.2 i) = 0 := by
    intro z
    rw [LinearMap.mem_ker]
    constructor
    · intro h i
      have h' := congrFun h i
      simpa [hDE, cechDiff_apply, hτ₀, Pi.sub_apply, hε₀apply, hε₁apply] using h'
    · intro h
      funext i
      have h' := h i
      simpa [hDE, cechDiff_apply, hτ₀, Pi.sub_apply, hε₀apply, hε₁apply] using h'
  haveI hSdfin : Module.Finite A ↥(LinearMap.ker (cechDiff τ₀ ρ₁.toLinearMap)) :=
    Module.Finite.iff_fg.mpr hSd
  set Ξ : (Fin n₀ ⊕ Fin n₁ → ↥(LinearMap.ker (cechDiff τ₀ ρ₁.toLinearMap))) →ₗ[A]
      ↥(LinearMap.ker DE) :=
    { toFun := fun sfun => ⟨(fun i => ((sfun i : C₀ × C₁)).1, fun i => ((sfun i : C₀ × C₁)).2),
        (hDEmem _).mpr fun i => LinearMap.mem_ker.mp (sfun i).2⟩
      map_add' := fun sf sg => Subtype.ext (Prod.ext
        (funext fun i => rfl) (funext fun i => rfl))
      map_smul' := fun r sf => Subtype.ext (Prod.ext
        (funext fun i => rfl) (funext fun i => rfl)) } with hΞ
  have hΞsurj : Function.Surjective Ξ := by
    rintro ⟨⟨e₀, e₁⟩, hz⟩
    refine ⟨fun i => ⟨(e₀ i, e₁ i), LinearMap.mem_ker.mpr ((hDEmem _).mp hz i)⟩, ?_⟩
    exact Subtype.ext (Prod.ext rfl rfl)
  haveI hkerDEfin : Module.Finite A ↥(LinearMap.ker DE) :=
    Module.Finite.of_surjective Ξ hΞsurj
  -- ### Step 5: the connecting snake and the finiteness assembly
  set DM : (M₀ × M₁) →ₗ[A] V := cechDiff σ₀ σ₁ with hDM
  set W : Submodule A ((Fin n₀ ⊕ Fin n₁ → C₀) × (Fin n₀ ⊕ Fin n₁ → C₁)) :=
    LinearMap.ker ((φ₀₁.restrictScalars A) ∘ₗ DE) with hW
  set ΦW : ↥W →ₗ[A] ↥(LinearMap.ker DM) :=
    { toFun := fun w => ⟨(φ₀ w.1.1, φ₁ w.1.2), by
        rw [LinearMap.mem_ker, hDM, cechDiff_apply, ← hsq₀, ← hsq₁]
        have hw := LinearMap.mem_ker.mp w.2
        rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hw
        have hsub : φ₀₁ (ε₀ w.1.1) - φ₀₁ (ε₁ w.1.2) = φ₀₁ (DE w.1) := by
          rw [hDE, cechDiff_apply, map_sub]
        rw [hsub, hw]⟩
      map_add' := fun w w' => Subtype.ext (Prod.ext
        (by change φ₀ (w.1.1 + w'.1.1) = _; rw [map_add]; rfl)
        (by change φ₁ (w.1.2 + w'.1.2) = _; rw [map_add]; rfl))
      map_smul' := fun r w => Subtype.ext (Prod.ext
        (by change φ₀ (r • w.1.1) = _; rw [LinearMap.map_smul_of_tower]; rfl)
        (by change φ₁ (r • w.1.2) = _; rw [LinearMap.map_smul_of_tower]; rfl)) } with hΦW
  have hΦWsurj : Function.Surjective ΦW := by
    rintro ⟨⟨m₀, m₁⟩, hm⟩
    obtain ⟨e₀, rfl⟩ := hφ₀surj m₀
    obtain ⟨e₁, rfl⟩ := hφ₁surj m₁
    have hWmem : ((e₀, e₁) : (Fin n₀ ⊕ Fin n₁ → C₀) × (Fin n₀ ⊕ Fin n₁ → C₁)) ∈ W := by
      rw [hW, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        hDE, cechDiff_apply, map_sub, hsq₀, hsq₁]
      have := LinearMap.mem_ker.mp hm
      rw [hDM, cechDiff_apply] at this
      exact this
    exact ⟨⟨(e₀, e₁), hWmem⟩, Subtype.ext rfl⟩
  set DEK : ↥W →ₗ[A] ↥K01 :=
    { toFun := fun w => ⟨DE w.1, by
        rw [hK01, LinearMap.mem_ker]
        have hw := LinearMap.mem_ker.mp w.2
        rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hw
        exact hw⟩
      map_add' := fun w w' => Subtype.ext (by
        change DE (w.1 + w'.1) = DE w.1 + DE w'.1
        rw [map_add])
      map_smul' := fun r w => Subtype.ext (by
        change DE (r • w.1) = r • DE w.1
        rw [map_smul]) } with hDEK
  set Θb : ↥W →ₗ[A] (↥K01 ⧸ (NL₀ ⊔ NL₁)) := (NL₀ ⊔ NL₁).mkQ ∘ₗ DEK with hΘb
  have hkerincl : LinearMap.ker ΦW ≤ LinearMap.ker Θb := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hw' : φ₀ w.1.1 = 0 ∧ φ₁ w.1.2 = 0 := by
      have h := Subtype.ext_iff.mp hw
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have hd0 : DEK w = κ₀ ⟨w.1.1, LinearMap.mem_ker.mpr hw'.1⟩
        - κ₁ ⟨w.1.2, LinearMap.mem_ker.mpr hw'.2⟩ := by
      refine Subtype.ext ?_
      change DE w.1 = ε₀ w.1.1 - ε₁ w.1.2
      rw [hDE, cechDiff_apply]
    rw [hΘb, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hd0]
    exact sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ⟨_, rfl⟩)
  set ψ : (↥W ⧸ LinearMap.ker ΦW) →ₗ[A] (↥K01 ⧸ (NL₀ ⊔ NL₁)) :=
    (LinearMap.ker ΦW).liftQ Θb hkerincl with hψ
  -- the `Ȟ⁰(E)`-part of `W`
  have hDEleW : LinearMap.ker DE ≤ W := by
    intro z hz
    rw [hW, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.mem_ker.mp hz, map_zero]
  set J : Submodule A ↥W := (LinearMap.ker DE).comap W.subtype with hJ
  have hJfin : J.FG := by
    have e := Submodule.comapSubtypeEquivOfLe hDEleW
    haveI : Module.Finite A ↥J := Module.Finite.equiv e.symm
    exact Module.Finite.iff_fg.mp this
  have hkerΘb : LinearMap.ker Θb = J ⊔ LinearMap.ker ΦW := by
    refine le_antisymm ?_ (sup_le ?_ hkerincl)
    · intro w hw
      rw [LinearMap.mem_ker, hΘb, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hw
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hw
      obtain ⟨k₀, rfl⟩ := hp
      obtain ⟨k₁, rfl⟩ := hq
      have hamb : DE w.1 = ε₀ k₀.1 + ε₁ k₁.1 := by
        have h := congrArg Subtype.val hpq
        exact h.symm
      set kp : (Fin n₀ ⊕ Fin n₁ → C₀) × (Fin n₀ ⊕ Fin n₁ → C₁) :=
        (k₀.1, -k₁.1) with hkp
      have hDEkp : DE kp = ε₀ k₀.1 + ε₁ k₁.1 := by
        rw [hDE, cechDiff_apply, hkp]
        change ε₀ k₀.1 - ε₁ (-k₁.1) = _
        rw [map_neg, sub_neg_eq_add]
      have hkpW : kp ∈ W := by
        rw [hW, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
          hDEkp, map_add, hsq₀, hsq₁, LinearMap.mem_ker.mp k₀.2, LinearMap.mem_ker.mp k₁.2,
          map_zero, map_zero, add_zero]
      have hkpker : (⟨kp, hkpW⟩ : ↥W) ∈ LinearMap.ker ΦW := by
        rw [LinearMap.mem_ker]
        refine Subtype.ext (Prod.ext ?_ ?_)
        · change φ₀ k₀.1 = 0
          exact LinearMap.mem_ker.mp k₀.2
        · change φ₁ (-k₁.1) = 0
          rw [map_neg, LinearMap.mem_ker.mp k₁.2, neg_zero]
      have hsplit : w = (w - ⟨kp, hkpW⟩) + ⟨kp, hkpW⟩ := by
        rw [sub_add_cancel]
      rw [hsplit]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hkpker)
      rw [hJ, Submodule.mem_comap, LinearMap.mem_ker]
      change DE (w.1 - kp) = 0
      rw [map_sub, hamb, hDEkp, sub_self]
    · intro w hw
      rw [hJ, Submodule.mem_comap, LinearMap.mem_ker] at hw
      rw [LinearMap.mem_ker, hΘb, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      have hDEK0 : DEK w = 0 := Subtype.ext (by
        change DE w.1 = 0
        exact hw)
      rw [hDEK0]
      exact Submodule.zero_mem _
  have hkerψfg : (LinearMap.ker ψ).FG := by
    have hkerψ : LinearMap.ker ψ = (LinearMap.ker Θb).map (LinearMap.ker ΦW).mkQ :=
      Submodule.ker_liftQ _ _ _
    rw [hkerψ, hkerΘb, Submodule.map_sup]
    have h1 : (LinearMap.ker ΦW).map (LinearMap.ker ΦW).mkQ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hz
    rw [h1, sup_bot_eq]
    exact hJfin.map _
  haveI := hQfin
  haveI hQnoeth : IsNoetherian A (↥K01 ⧸ (NL₀ ⊔ NL₁)) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  have htop : (⊤ : Submodule A (↥W ⧸ LinearMap.ker ΦW)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker ψ ?_ ?_
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact hkerψfg
  haveI : Module.Finite A (↥W ⧸ LinearMap.ker ΦW) := Module.finite_def.mpr htop
  haveI : Module.Finite A ↥(LinearMap.ker DM) :=
    Module.Finite.equiv (ΦW.quotKerEquivOfSurjective hΦWsurj)
  exact Module.Finite.iff_fg.mp this

end TwoChart

end AlgebraicJacobian

namespace AlgebraicGeometry

/-! ## §4. Localization facts on affine charts (ring and module dialects)

The extension/torsion hypotheses of the abstract theorem, discharged from
mathlib's `IsAffineOpen.isLocalization_basicOpen` (ring side) and the qcqs
section-localization engine `isLocalizedModule_basicOpen_of_isCompact`
(module side, `Picard/QuotScheme.lean`), both in the caller-friendly
`W = X.basicOpen f` transport shape of `exists_pow_smul_eq_res`. -/

/-- **Ring-section extension over a basic open of an affine chart**: a section
of `𝒪_X` on `W = D(f) ⊆ U` extends to `U` after multiplication by a power of
`f|_W`.  (`IsLocalization.surj` for `hU.isLocalization_of_eq_basicOpen`.) -/
theorem exists_pow_mul_res_eq_res {X : Scheme.{u}} {U W : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (hW : W = X.basicOpen f) (hWU : W ≤ U) (c : Γ(X, W)) :
    ∃ (n : ℕ) (q : Γ(X, U)),
      (X.presheaf.map (homOfLE hWU).op).hom f ^ n * c
        = (X.presheaf.map (homOfLE hWU).op).hom q := by
  letI : Algebra Γ(X, U) Γ(X, W) := ((X.presheaf.map (homOfLE hWU).op).hom).toAlgebra
  haveI : IsLocalization.Away f Γ(X, W) :=
    hU.isLocalization_of_eq_basicOpen f (homOfLE hWU) hW
  obtain ⟨⟨q, s⟩, hqs⟩ := IsLocalization.surj (M := Submonoid.powers f) (S := Γ(X, W)) c
  obtain ⟨n, hn⟩ := s.2
  have hn' : (f ^ n : Γ(X, U)) = (s : Γ(X, U)) := hn
  refine ⟨n, q, ?_⟩
  have halg : ∀ z : Γ(X, U),
      algebraMap Γ(X, U) Γ(X, W) z = (X.presheaf.map (homOfLE hWU).op).hom z :=
    fun _ => rfl
  rw [← halg, ← halg, ← map_pow, hn', mul_comm]
  exact hqs

/-- **Ring-section torsion over a basic open of an affine chart**: a section of
`𝒪_X` on `U` restricting to `0` on `W = D(f)` is killed by a power of `f`.
(`IsLocalization.map_eq_zero_iff`.) -/
theorem exists_pow_mul_eq_zero_of_res_eq_zero {X : Scheme.{u}} {U W : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W = X.basicOpen f) (hWU : W ≤ U)
    (c : Γ(X, U)) (hc : (X.presheaf.map (homOfLE hWU).op).hom c = 0) :
    ∃ n : ℕ, f ^ n * c = 0 := by
  letI : Algebra Γ(X, U) Γ(X, W) := ((X.presheaf.map (homOfLE hWU).op).hom).toAlgebra
  haveI : IsLocalization.Away f Γ(X, W) :=
    hU.isLocalization_of_eq_basicOpen f (homOfLE hWU) hW
  have hc' : algebraMap Γ(X, U) Γ(X, W) c = 0 := hc
  obtain ⟨⟨s, hsmem⟩, hs⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Γ(X, W) c).mp hc'
  obtain ⟨n, rfl⟩ := hsmem
  exact ⟨n, hs⟩

/-- **Module-section torsion over a basic open of an affine chart**
(vanishing sibling of `Scheme.Modules.exists_pow_smul_eq_res`): a section of a
quasi-coherent `M` on the affine `U` restricting to `0` on `W = D(f)` is
killed by a power of `f`.  From the qcqs section-localization engine
(`IsLocalizedModule.exists_of_eq`). -/
theorem Scheme.Modules.exists_pow_smul_eq_zero_of_res {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hW : W = X.basicOpen f) (hWU : W ≤ U) (m : Γ(M, U))
    (hm : M.presheaf.map (homOfLE hWU).op m = 0) :
    ∃ n : ℕ, f ^ n • m = 0 := by
  subst hW
  letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := isLocalizedModule_basicOpen_of_isCompact M hU.isCompact
    hU.isQuasiSeparated f
  have hm' : Scheme.Modules.restrictBasicOpenₗ M f m
      = Scheme.Modules.restrictBasicOpenₗ M f 0 := by
    rw [map_zero]
    exact hm
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
    (f := Scheme.Modules.restrictBasicOpenₗ M f) hm'
  obtain ⟨n, hn⟩ := s.2
  have hn' : (f ^ n : Γ(X, U)) = (s : Γ(X, U)) := hn
  refine ⟨n, ?_⟩
  have h1 : (s : Γ(X, U)) • m = 0 := by
    rw [smul_zero] at hs
    exact hs
  rw [hn']
  exact h1

namespace Scheme

/-! ## §5. The base-linear structure-sheaf Čech difference (the `hS0` anchor) -/

variable {X S : Scheme.{u}}

/-- **The base-linear ring-section restriction as an algebra hom** over
`Γ(S, ⊤)` for the `appLE`-`toAlgebra` structures (the ring-side sibling of
`Hom.baseSectionsRes`; the algebra-hom property is `appLE_map` naturality).
This is the `ρ` of the abstract two-chart datum. -/
noncomputable def Hom.baseRingSectionsResAlgHom (p : X ⟶ S) {W W' : X.Opens} (h : W' ≤ W) :
    letI := ((p.appLE ⊤ W (le_top : W ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    letI := ((p.appLE ⊤ W' (le_top : W' ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    Γ(X, W) →ₐ[Γ(S, ⊤)] Γ(X, W') :=
  letI := ((p.appLE ⊤ W (le_top : W ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI := ((p.appLE ⊤ W' (le_top : W' ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  { toRingHom := (X.presheaf.map (homOfLE h).op).hom
    commutes' := fun r => by
      have h1 := congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(X, W') => φ.hom r)
        (p.appLE_map (le_top : W ≤ p ⁻¹ᵁ ⊤) (homOfLE h).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
      exact h1 }

/-- The underlying function of `baseRingSectionsResAlgHom` is the presheaf
restriction. -/
lemma Hom.baseRingSectionsResAlgHom_apply (p : X ⟶ S) {W W' : X.Opens} (h : W' ≤ W)
    (c : Γ(X, W)) :
    p.baseRingSectionsResAlgHom h c = (X.presheaf.map (homOfLE h).op).hom c :=
  rfl

/-- **The base-linear structure-sheaf Čech difference of a 2-affine cover**:
`(c₀, c₁) ↦ c₀|_{U₁⊓U₂} − c₁|_{U₁⊓U₂}`, `Γ(S, ⊤)`-linearly for the
`appLE`-`toAlgebra` structures.  Its kernel is the concrete Čech
`H⁰(X, 𝒪_X)` as a `Γ(S, ⊤)`-module; finite generation of this kernel is the
**single `M`-independent anchor** (`hS0`) of the B3-H0 leaf — for
`X = ℙ¹_A ⟶ S = Spec A` it says `Γ(ℙ¹_A, 𝒪)` is a finite `A`-module (true:
`Γ(ℙ¹_A, 𝒪) ≅ A`, Stacks 01XZ-adjacent; the remaining sub-leaf). -/
noncomputable def AffineCoverMVSquare.ringSectionDiffBase (V : X.AffineCoverMVSquare)
    (p : X ⟶ S) :
    letI := ((p.appLE ⊤ V.U₁ (le_top : V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    letI := ((p.appLE ⊤ V.U₂ (le_top : V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    letI := ((p.appLE ⊤ (V.U₁ ⊓ V.U₂) (le_top : V.U₁ ⊓ V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    (Γ(X, V.U₁) × Γ(X, V.U₂)) →ₗ[Γ(S, ⊤)] Γ(X, V.U₁ ⊓ V.U₂) :=
  letI := ((p.appLE ⊤ V.U₁ (le_top : V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI := ((p.appLE ⊤ V.U₂ (le_top : V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI := ((p.appLE ⊤ (V.U₁ ⊓ V.U₂) (le_top : V.U₁ ⊓ V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  AlgebraicJacobian.TwoChart.cechDiff
    (p.baseRingSectionsResAlgHom (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).toLinearMap
    (p.baseRingSectionsResAlgHom (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).toLinearMap

set_option maxHeartbeats 400000 in
-- Heartbeat headroom for the sheaf-condition gluing across the
-- `Scheme.Opens`/`Opens X.toTopCat` presentation diamond (fleet recipe, as in
-- `globalSectionsEquivKerModuleSectionDiffBase`).
/-- **The `hS0` anchor reduces to global sections.**  If `Γ(X, ⊤)` is a
finite `Γ(S, ⊤)`-module (for the `appLE`-`toAlgebra` structure — i.e. the
pushforward `p_* 𝒪_X` has base-finite global sections), then the
structure-sheaf Čech kernel of any 2-affine cover square is finitely
generated: by the sheaf gluing axiom the kernel is the *image* of the
pair-of-restrictions map from `Γ(X, ⊤)`, and images of finite modules are
finite.  (No separatedness, injectivity, or noetherianity enters.)  For
`X = ℙ¹_A` this reduces the B3-H0 sub-leaf to the single classical fact
`Γ(ℙ¹_A, 𝒪) ≅ A`. -/
theorem AffineCoverMVSquare.fg_ker_ringSectionDiffBase_of_module_finite_top
    (V : X.AffineCoverMVSquare) (p : X ⟶ S)
    (hfin :
      letI := ((p.appLE ⊤ (⊤ : X.Opens) (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
      Module.Finite Γ(S, ⊤) Γ(X, ⊤)) :
    letI := ((p.appLE ⊤ V.U₁ (le_top : V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    letI := ((p.appLE ⊤ V.U₂ (le_top : V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    letI := ((p.appLE ⊤ (V.U₁ ⊓ V.U₂) (le_top : V.U₁ ⊓ V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    (LinearMap.ker (V.ringSectionDiffBase p)).FG := by
  letI := ((p.appLE ⊤ (⊤ : X.Opens) (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI := ((p.appLE ⊤ V.U₁ (le_top : V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI := ((p.appLE ⊤ V.U₂ (le_top : V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI := ((p.appLE ⊤ (V.U₁ ⊓ V.U₂) (le_top : V.U₁ ⊓ V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  haveI := hfin
  classical
  -- the pair-of-restrictions map from the global sections
  set π : Γ(X, (⊤ : X.Opens)) →ₗ[Γ(S, ⊤)] Γ(X, V.U₁) × Γ(X, V.U₂) :=
    LinearMap.prod
      (p.baseRingSectionsResAlgHom (le_top : V.U₁ ≤ ⊤)).toLinearMap
      (p.baseRingSectionsResAlgHom (le_top : V.U₂ ≤ ⊤)).toLinearMap with hπ
  -- restriction composites collapse (functoriality + proof irrelevance)
  have hres : ∀ {W : X.Opens} (hIW : V.U₁ ⊓ V.U₂ ≤ W) (hW : W ≤ ⊤)
      (s : Γ(X, (⊤ : X.Opens))),
      (X.presheaf.map (homOfLE hIW).op).hom ((X.presheaf.map (homOfLE hW).op).hom s)
        = (X.presheaf.map (homOfLE (le_top : V.U₁ ⊓ V.U₂ ≤ ⊤)).op).hom s := by
    intro W hIW hW s
    have hcomp := X.presheaf.map_comp (homOfLE hW).op (homOfLE hIW).op
    exact (congrArg (fun f => (CategoryTheory.ConcreteCategory.hom f) s) hcomp).symm.trans rfl
  have hker : LinearMap.ker (V.ringSectionDiffBase p) = LinearMap.range π := by
    refine le_antisymm ?_ ?_
    · -- gluing: every Čech-kernel element comes from a global section
      rintro ⟨c₀, c₁⟩ hc
      rw [LinearMap.mem_ker] at hc
      have hagree : (X.presheaf.map
            (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom c₀ =
          (X.presheaf.map
            (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom c₁ := by
        have h : (X.presheaf.map
              (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom c₀ -
            (X.presheaf.map
              (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom c₁ = 0 := hc
        exact sub_eq_zero.mp h
      set sf : ∀ i : ULift.{u} Bool, Γ(X, V.pairFamily i) :=
        fun i => match i with
          | ⟨true⟩ => c₀
          | ⟨false⟩ => c₁ with hsf
      have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V.pairFamily sf := by
        intro i j
        have key : ∀ {U W W' : X.Opens} (hUV : W' ≤ U ⊓ W)
            (a : Γ(X, U)) (b : Γ(X, W)),
            (X.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op).hom a =
              (X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom b →
            (X.presheaf.map (homOfLE (hUV.trans inf_le_left)).op).hom a =
              (X.presheaf.map (homOfLE (hUV.trans inf_le_right)).op).hom b := by
          intro U W W' hUV a b hab
          have ha : (X.presheaf.map (homOfLE (hUV.trans inf_le_left)).op).hom a =
              (X.presheaf.map (homOfLE hUV).op).hom
                ((X.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op).hom a) := by
            have := X.presheaf.map_comp
              (homOfLE (inf_le_left : U ⊓ W ≤ U)).op (homOfLE hUV).op
            exact (congrArg (fun f => (CategoryTheory.ConcreteCategory.hom f) a) this).trans rfl
          have hb : (X.presheaf.map (homOfLE (hUV.trans inf_le_right)).op).hom b =
              (X.presheaf.map (homOfLE hUV).op).hom
                ((X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op).hom b) := by
            have := X.presheaf.map_comp
              (homOfLE (inf_le_right : U ⊓ W ≤ W)).op (homOfLE hUV).op
            exact (congrArg (fun f => (CategoryTheory.ConcreteCategory.hom f) b) this).trans rfl
          rw [ha, hb, hab]
        obtain ⟨bi⟩ := i
        obtain ⟨bj⟩ := j
        cases bi <;> cases bj
        · exact congrArg
            (fun g => (CategoryTheory.ConcreteCategory.hom (X.presheaf.map (Quiver.Hom.op g))) c₁)
            (Subsingleton.elim _ _)
        · exact (key (le_inf inf_le_right inf_le_left) c₀ c₁ hagree).symm
        · exact key le_rfl c₀ c₁ hagree
        · exact congrArg
            (fun g => (CategoryTheory.ConcreteCategory.hom (X.presheaf.map (Quiver.Hom.op g))) c₀)
            (Subsingleton.elim _ _)
      obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
        X.sheaf V.pairFamily ⊤ (fun _ => homOfLE le_top) V.le_iSup_pairFamily sf hcompat
      exact ⟨s, Prod.ext (hs ⟨true⟩) (hs ⟨false⟩)⟩
    · -- the complex property: restrictions of a global section agree
      rintro _ ⟨s, rfl⟩
      rw [LinearMap.mem_ker]
      have h : (X.presheaf.map (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom
            ((X.presheaf.map (homOfLE (le_top : V.U₁ ≤ ⊤)).op).hom s) -
          (X.presheaf.map (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom
            ((X.presheaf.map (homOfLE (le_top : V.U₂ ≤ ⊤)).op).hom s) = 0 := by
        rw [hres inf_le_left (le_top : V.U₁ ≤ ⊤) s,
          hres inf_le_right (le_top : V.U₂ ≤ ⊤) s, sub_self]
      exact h
  rw [hker, ← Submodule.map_top]
  exact (Module.finite_def.mp hfin).map π

/-! ## §6. THE LEAF: `H⁰`-finiteness over a relative Laurent chart datum -/

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: the proof repeatedly crosses the `Γ`-carrier and
-- `Module.compHom`/`toAlgebra` identifications (fleet elaboration recipe, as
-- in `RelLaurentChartData.module_finite_h1`).
/-- **`H⁰`-finiteness for a family with relative Laurent chart data**
(the B3-H0 leaf, general form).  For `p : X ⟶ S` with relative Laurent chart
data `D`, a quasi-coherent `M` with chart-finite section modules, a
noetherian base ring, and the single `M`-independent anchor `hS0`
(structure-sheaf Čech `H⁰` finite over the base), the Čech kernel
`H⁰ = ker (moduleSectionDiffBase) = Γ(X, M)` is a finitely generated
`Γ(S, ⊤)`-submodule.  This is the abstract Serre dévissage
`TwoChart.fg_ker_cechDiff_of_laurent` instantiated on the wave-4 substrate:
extension = `exists_pow_smul_eq_res` / `IsLocalization.surj`, torsion =
`exists_pow_smul_eq_zero_of_res` / `map_eq_zero_iff`, spans = `D.span_pow_x/y`. -/
theorem RelLaurentChartData.fg_ker_moduleSectionDiffBase {X S : Scheme.{u}} {p : X ⟶ S}
    (D : RelLaurentChartData p) (M : X.Modules) [M.IsQuasicoherent]
    (hnoeth : IsNoetherianRing Γ(S, ⊤))
    (hfin₁ : Module.Finite Γ(X, D.V.U₁) Γ(M, D.V.U₁))
    (hfin₂ : Module.Finite Γ(X, D.V.U₂) Γ(M, D.V.U₂))
    (hS0 :
      letI := ((p.appLE ⊤ D.V.U₁ (le_top : D.V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
      letI := ((p.appLE ⊤ D.V.U₂ (le_top : D.V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
      letI := ((p.appLE ⊤ (D.V.U₁ ⊓ D.V.U₂)
        (le_top : D.V.U₁ ⊓ D.V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
      (LinearMap.ker (D.V.ringSectionDiffBase p)).FG) :
    letI := p.baseSectionsModule M D.V.U₁
    letI := p.baseSectionsModule M D.V.U₂
    letI := p.baseSectionsModule M (D.V.U₁ ⊓ D.V.U₂)
    (LinearMap.ker (D.V.moduleSectionDiffBase p M)).FG := by
  letI := p.baseSectionsModule M D.V.U₁
  letI := p.baseSectionsModule M D.V.U₂
  letI := p.baseSectionsModule M (D.V.U₁ ⊓ D.V.U₂)
  letI iA₁ : Algebra Γ(S, ⊤) Γ(X, D.V.U₁) :=
    ((p.appLE ⊤ D.V.U₁ (le_top : D.V.U₁ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI iA₂ : Algebra Γ(S, ⊤) Γ(X, D.V.U₂) :=
    ((p.appLE ⊤ D.V.U₂ (le_top : D.V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  letI iA₁₂ : Algebra Γ(S, ⊤) Γ(X, D.V.U₁ ⊓ D.V.U₂) :=
    ((p.appLE ⊤ (D.V.U₁ ⊓ D.V.U₂) (le_top : D.V.U₁ ⊓ D.V.U₂ ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  haveI hT₁ : IsScalarTower Γ(S, ⊤) Γ(X, D.V.U₁) Γ(M, D.V.U₁) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hT₂ : IsScalarTower Γ(S, ⊤) Γ(X, D.V.U₂) Γ(M, D.V.U₂) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hT₁₂ : IsScalarTower Γ(S, ⊤) Γ(X, D.V.U₁ ⊓ D.V.U₂) Γ(M, D.V.U₁ ⊓ D.V.U₂) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := hfin₁
  haveI := hfin₂
  haveI := hnoeth
  set ρ₀ := p.baseRingSectionsResAlgHom (inf_le_left : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₁) with hρ₀
  set ρ₁ := p.baseRingSectionsResAlgHom (inf_le_right : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₂) with hρ₁
  set σ₀ := p.baseSectionsRes M (inf_le_left : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₁) with hσ₀def
  set σ₁ := p.baseSectionsRes M (inf_le_right : D.V.U₁ ⊓ D.V.U₂ ≤ D.V.U₂) with hσ₁def
  -- the coordinates are mutually inverse on the overlap
  have htu : ρ₀ D.x * ρ₁ D.y = 1 := D.res_x_mul_res_y
  -- semilinearity of the section restrictions
  have hσ₀sl : ∀ (c : Γ(X, D.V.U₁)) (m : Γ(M, D.V.U₁)), σ₀ (c • m) = ρ₀ c • σ₀ m := by
    intro c m
    rw [hσ₀def, p.baseSectionsRes_apply, p.baseSectionsRes_apply, Scheme.Modules.map_smul]
    rfl
  have hσ₁sl : ∀ (c : Γ(X, D.V.U₂)) (m : Γ(M, D.V.U₂)), σ₁ (c • m) = ρ₁ c • σ₁ m := by
    intro c m
    rw [hσ₁def, p.baseSectionsRes_apply, p.baseSectionsRes_apply, Scheme.Modules.map_smul]
    rfl
  -- module extension (localization surjectivity on sections)
  have hext₀ : ∀ v : Γ(M, D.V.U₁ ⊓ D.V.U₂),
      ∃ (n : ℕ) (m : Γ(M, D.V.U₁)), ρ₀ D.x ^ n • v = σ₀ m := by
    intro v
    obtain ⟨n, m, hm⟩ := Scheme.Modules.exists_pow_smul_eq_res M
      D.V.isAffineOpen_U₁ D.x D.inf_eq_basicOpen_x inf_le_left v
    exact ⟨n, m, hm⟩
  have hext₁ : ∀ v : Γ(M, D.V.U₁ ⊓ D.V.U₂),
      ∃ (n : ℕ) (m : Γ(M, D.V.U₂)), ρ₁ D.y ^ n • v = σ₁ m := by
    intro v
    obtain ⟨n, m, hm⟩ := Scheme.Modules.exists_pow_smul_eq_res M
      D.V.isAffineOpen_U₂ D.y D.inf_eq_basicOpen_y inf_le_right v
    exact ⟨n, m, hm⟩
  -- module torsion (localization kernels on sections)
  have htor₀ : ∀ m : Γ(M, D.V.U₁), σ₀ m = 0 → ∃ n : ℕ, D.x ^ n • m = 0 := fun m hm =>
    Scheme.Modules.exists_pow_smul_eq_zero_of_res M
      D.V.isAffineOpen_U₁ D.x D.inf_eq_basicOpen_x inf_le_left m hm
  have htor₁ : ∀ m : Γ(M, D.V.U₂), σ₁ m = 0 → ∃ n : ℕ, D.y ^ n • m = 0 := fun m hm =>
    Scheme.Modules.exists_pow_smul_eq_zero_of_res M
      D.V.isAffineOpen_U₂ D.y D.inf_eq_basicOpen_y inf_le_right m hm
  -- ring extension and torsion
  have hRext₀ : ∀ c : Γ(X, D.V.U₁ ⊓ D.V.U₂),
      ∃ (n : ℕ) (q : Γ(X, D.V.U₁)), ρ₀ D.x ^ n * c = ρ₀ q := by
    intro c
    obtain ⟨n, q, hq⟩ := exists_pow_mul_res_eq_res
      D.V.isAffineOpen_U₁ D.x D.inf_eq_basicOpen_x inf_le_left c
    exact ⟨n, q, hq⟩
  have hRext₁ : ∀ c : Γ(X, D.V.U₁ ⊓ D.V.U₂),
      ∃ (n : ℕ) (q : Γ(X, D.V.U₂)), ρ₁ D.y ^ n * c = ρ₁ q := by
    intro c
    obtain ⟨n, q, hq⟩ := exists_pow_mul_res_eq_res
      D.V.isAffineOpen_U₂ D.y D.inf_eq_basicOpen_y inf_le_right c
    exact ⟨n, q, hq⟩
  have hRtor₀ : ∀ c : Γ(X, D.V.U₁), ρ₀ c = 0 → ∃ n : ℕ, D.x ^ n * c = 0 := fun c hc =>
    exists_pow_mul_eq_zero_of_res_eq_zero
      D.V.isAffineOpen_U₁ D.x D.inf_eq_basicOpen_x inf_le_left c hc
  -- the abstract dévissage
  have key := AlgebraicJacobian.TwoChart.fg_ker_cechDiff_of_laurent
    (A := Γ(S, ⊤)) ρ₀ ρ₁ D.x D.y htu D.span_pow_x σ₀ σ₁ hσ₀sl hσ₁sl
    hext₀ hext₁ htor₀ htor₁ hRext₀ hRext₁ hRtor₀ hS0
  -- the two kernels agree
  have hkereq : LinearMap.ker (D.V.moduleSectionDiffBase p M)
      = LinearMap.ker (AlgebraicJacobian.TwoChart.cechDiff σ₀ σ₁) := by
    refine Submodule.ext fun q => ?_
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have happ : D.V.moduleSectionDiffBase p M q
        = AlgebraicJacobian.TwoChart.cechDiff σ₀ σ₁ q := rfl
    rw [happ]
  rw [hkereq]
  exact key

/-- **Base-finiteness of global sections from the comparison map**: if the
structure-sheaf comparison `Γ(S, ⊤) → Γ(X, ⊤)` (`p.appTop`) is bijective —
the conclusion shape of the `B1` brick `isIso_snd_appTop`
(`Picard/StructureSheafPushforward.lean`) — then `Γ(X, ⊤)` is a finite
`Γ(S, ⊤)`-module for the `appLE`-`toAlgebra` structure (it is generated by
`1`). -/
theorem Hom.module_finite_top_of_bijective_appTop {X S : Scheme.{u}} (p : X ⟶ S)
    (hbij : Function.Bijective (p.appTop).hom) :
    letI := ((p.appLE ⊤ (⊤ : X.Opens) (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
    Module.Finite Γ(S, ⊤) Γ(X, ⊤) := by
  letI := ((p.appLE ⊤ (⊤ : X.Opens) (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).hom).toAlgebra
  have heq : p ⁻¹ᵁ (⊤ : S.Opens) = ⊤ := p.preimage_top
  have hiso : IsIso (X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).op) := by
    haveI : IsIso (homOfLE (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)) :=
      ⟨⟨homOfLE heq.le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    infer_instance
  have hres : Function.Bijective ((X.presheaf.map
      (homOfLE (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).op).hom) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  have hsurj : Function.Surjective (algebraMap Γ(S, ⊤) Γ(X, ⊤)) := by
    have hcomp : ⇑(algebraMap Γ(S, ⊤) Γ(X, ⊤)) =
        ⇑((X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤)).op).hom) ∘
          ⇑((p.appTop).hom) := rfl
    rw [hcomp]
    exact hres.surjective.comp hbij.surjective
  exact Module.Finite.of_surjective (Algebra.linearMap Γ(S, ⊤) Γ(X, ⊤)) hsurj

end Scheme

namespace Adelic

open Scheme

/-! ## §7. The ℙ¹_A leaf, verbatim in the engine's `hH0` shape, and the composite -/

variable {k : Type u} [Field k]
variable (A : Type u) [CommRing A] [Algebra k A]

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the instance-heavy `letI` environment (fleet recipe,
-- as in the wave-4 endgame skeleton).
/-- **THE B3-H0 LEAF for `ℙ¹_A`** — the engine's named hypothesis `hH0`
(`p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`, verbatim shape), produced
from the single `M`-independent anchor `hS0`: finite generation of the
structure-sheaf Čech kernel of the standard 2-chart cover — i.e.
`Γ(ℙ¹_A, 𝒪)` is a finite `A`-module.  Everything `M`-dependent
(Serre-finiteness-grade in the classical references) is discharged
unconditionally by the dévissage; the audit's "not derivable from the
Laurent ladder" leaf is thereby reduced from coherent-sheaf cohomology to a
single structure-sheaf fact. -/
theorem p1Cech_h0_fg_of_structure_h0_fg [Algebra.FiniteType k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    [M.IsFinitePresentation]
    (hS0 :
      letI := (((pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
          ⊤ (p1BaseChangeCoverSquare A).U₁ le_top).hom).toAlgebra
      letI := (((pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
          ⊤ (p1BaseChangeCoverSquare A).U₂ le_top).hom).toAlgebra
      letI := (((pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
          ⊤ ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
          le_top).hom).toAlgebra
      (LinearMap.ker ((p1BaseChangeCoverSquare A).ringSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))))).FG) :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)).FG := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hnoeth : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    isNoetherianRing_of_ringEquiv A
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  exact (p1BaseChangeRelLaurentChartData A).fg_ker_moduleSectionDiffBase M hnoeth
    (Scheme.Modules.module_finite_sections_of_isFinitePresentation M
      ⟨(p1BaseChangeCoverSquare A).U₁, (p1BaseChangeCoverSquare A).isAffineOpen_U₁⟩)
    (Scheme.Modules.module_finite_sections_of_isFinitePresentation M
      ⟨(p1BaseChangeCoverSquare A).U₂, (p1BaseChangeCoverSquare A).isAffineOpen_U₂⟩)
    hS0


set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the instance-heavy `letI` environment (fleet recipe,
-- as in the wave-4 endgame skeleton).
/-- **THE COMPOSITE (engine + leaf): the B3 ℙ¹-endgame with the audited
`hH0` leaf discharged.**  The full wave-4 engine conclusion
(`p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`: `d` surjective, `H⁰ = ker d`
finite projective, formation of `H⁰` commutes with arbitrary base change) with
the Serre-finiteness-grade hypothesis `hH0` **replaced** by the single
`M`-independent anchor `hS0` (structure-sheaf Čech `H⁰` finite — the remaining
sub-leaf, `Γ(ℙ¹_A, 𝒪) ≅ A`). -/
theorem p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_structure_h0_fg
    [Algebra.FiniteType k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    [M.IsFinitePresentation]
    (hflat : Scheme.CoherentSheafFlat
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)
    (hS0 :
      letI := (((pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
          ⊤ (p1BaseChangeCoverSquare A).U₁ le_top).hom).toAlgebra
      letI := (((pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
          ⊤ (p1BaseChangeCoverSquare A).U₂ le_top).hom).toAlgebra
      letI := (((pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appLE
          ⊤ ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
          le_top).hom).toAlgebra
      (LinearMap.ker ((p1BaseChangeCoverSquare A).ringSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))))).FG) :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    ∀ _hfib : (∀ (m : Ideal Γ(Spec (CommRingCat.of A), ⊤)), m.IsMaximal →
      Function.Surjective
        (((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M).baseChange
          (Γ(Spec (CommRingCat.of A), ⊤) ⧸ m))),
    Function.Surjective ⇑((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) ∧
      Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
        (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) ∧
      Module.Projective Γ(Spec (CommRingCat.of A), ⊤)
        (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) ∧
      ∀ (B : Type u) [CommRing B] [Algebra Γ(Spec (CommRingCat.of A), ⊤) B],
        Function.Bijective (AlgebraicJacobian.TwoTerm.kerBaseChange
          ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
            (pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) B) := by
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₁
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      (p1BaseChangeCoverSquare A).U₂
  letI := (pullback.snd (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
      ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
  intro hfib
  exact p1Cech_h0_baseChange_of_fibrewise_h1_vanishing A M hflat
    (p1Cech_h0_fg_of_structure_h0_fg A M hS0) hfib

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the instance-heavy `letI` environment (fleet recipe).
/-- **The B3-H0 leaf from the structure-sheaf comparison map**: the engine's
`hH0`, given only that `Γ(Spec A, 𝒪) → Γ(ℙ¹_A, 𝒪)` is bijective — the exact
conclusion shape of the `B1` brick `bijective_snd_appTop_baseChange`
(`Picard/StructureSheafPushforward.lean`), which discharges it as soon as
`GeometricallyIntegral (p1Over k).hom` is provided (`IsProper` is already an
instance via `ProjectiveSpace.isProper_over`).  Chain:
comparison bijective ⟹ `Γ(ℙ¹_A, ⊤)` base-finite ⟹ (sheaf gluing) `hS0` ⟹
(Serre dévissage) `hH0`. -/
theorem p1Cech_h0_fg_of_bijective_appTop [Algebra.FiniteType k A]
    (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    [M.IsFinitePresentation]
    (hbij : Function.Bijective (((pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom)) :
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)).FG :=
  p1Cech_h0_fg_of_structure_h0_fg A M
    ((p1BaseChangeCoverSquare A).fg_ker_ringSectionDiffBase_of_module_finite_top
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      ((pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).module_finite_top_of_bijective_appTop
        hbij))

end Adelic

end AlgebraicGeometry
