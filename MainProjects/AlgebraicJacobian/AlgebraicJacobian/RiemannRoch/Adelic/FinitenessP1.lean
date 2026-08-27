/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.P1BaseCase
import AlgebraicJacobian.RiemannRoch.Adelic.Cokernel
import AlgebraicJacobian.Picard.SerreTwist

/-!
# H¹ finiteness of a curve via a finite map to ℙ¹ (node `N11`, the adelic keystone)

This file is part of the **adelic Riemann–Roch lane** (see the lane design document).
It proves the lane's primary keystone: for a curve `C` over a field `k` admitting a
finite morphism `π : C ⟶ Y` to a target carrying *Laurent chart data* (the abstract
form of the standard two-chart structure of `ℙ¹`), the two-cover Čech cokernel
`Ȟ¹ = Γ(U₀ ⊓ U₁, 𝒪_C) / (Γ(U₀, 𝒪_C) + Γ(U₁, 𝒪_C))` of the structure sheaf on the
pulled-back cover `U_i = π⁻¹V_i` is a **finite-dimensional `k`-vector space**.

## The mathematical route (the Weil/Stichtenoth two-lattice argument)

Fix the standard cover `ℙ¹ = V₀ ∪ V₁` with coordinate `x` on `V₀` and `y = x⁻¹`
on `V₁`, so `V₀ ⊓ V₁ = D(x) = D(y)` and `Γ(V₀) = k[x]`, `Γ(V₁) = k[y]`,
`Γ(V₀ ⊓ V₁) = k[x, x⁻¹]`.  Pull back along the finite morphism `π`:

* the preimages `U_i = π⁻¹V_i` and `U₀ ⊓ U₁` are affine (finite morphisms are
  affine), and `A_i := Γ(U_i, 𝒪_C)` is a **finite module** over the chart ring
  `Γ(V_i)` (`IsFinite.finite_app`, integral-closure finiteness — node `N10`);
* `U₀ ⊓ U₁` is the basic open of `t := π^♯x` inside `U₀` (and of `u := π^♯y`
  inside `U₁`), so `M := Γ(U₀ ⊓ U₁, 𝒪_C)` is the **localization** `(A₀)_t`
  (`IsAffineOpen.isLocalization_of_eq_basicOpen`); in particular every `m ∈ M`
  *extends to the charts*: `t^n · m` comes from `A₀`, and `u^n · m` comes from
  `A₁`, for `n ≫ 0` (the extension lemma `exists_pow_mul_eq_res`);
* choosing finitely many `Γ(V₀)`-module generators `g₁, …, g_r` of `A₀` and using
  that `Γ(V₀)` is the `k`-span of the powers of `x` (the ℙ¹ chart structure —
  the geometric source of the Laurent split of `P1BaseCase.lean`), `M` is the
  `k`-span of the doubly infinite ladder `{tʲ · ρ(gᵢ) : j ∈ ℤ}` (`t⁻¹ = u`);
* the rungs with `j ≥ 0` lie in the image `N₀` of `A₀`; by the extension property
  each generator has all rungs `j ≤ -Nᵢ` in the image `N₁` of `A₁`; the
  **finitely many** middle rungs `{u^j · ρ(gᵢ) : 0 < j < Nᵢ}` span the cokernel
  `M ⧸ (N₀ + N₁)`, which is therefore finite-dimensional over `k`.

This reproduces, over an arbitrary base field, the finiteness the solved
differential-geometry sibling imported from compactness (Dolbeault); references:
Stichtenoth, *Algebraic Function Fields and Codes*, I.4–I.5 (the two-lattice /
elementary-divisor step inside the proof of the Riemann inequality); design
document §3, node `N11`.

## Main statements

* `Adelic.module_finite_quotient_of_laurent_pair` — **the abstract two-lattice
  core**: in a commutative `k`-algebra `M` with `t * u = 1`, if `N₀` is a
  `t`-stable and `N₁` a `u`-stable `k`-submodule, `s ⊆ N₀` a finite set whose
  two-sided `t`/`u`-ladder spans `M` over `k`, and every element of `s` lands in
  `N₁` after enough multiplications by `u`, then `M ⧸ (N₀ ⊔ N₁)` is a finite
  `k`-module.
* `Adelic.exists_pow_mul_eq_res` — **the extension lemma**: on an affine open
  `U` of a scheme with `W = D(f)` for a section `f ∈ Γ(X, U)`, every section
  over `W` multiplied by a high power of `f|_W` is the restriction of a section
  over `U`.
* `Adelic.LaurentChartData` — the bundled standard-two-chart structure on a
  `Spec k`-scheme `Y`: two affine opens covering `Y`, coordinate sections `x, y`
  with `x · y = 1` on the overlap, overlap equal to the basic open of either
  coordinate, and each chart ring spanned over `k` by the powers of its
  coordinate (`Γ(V₀) = k[x]`, `Γ(V₁) = k[y]`, `Γ(V₀ ⊓ V₁) = k[x, x⁻¹]`).
* `Adelic.LaurentChartData.pullbackSquare` — the pulled-back 2-affine cover
  (`AffineCoverMVSquare`) on the source of a finite morphism to `Y`.
* `Adelic.LaurentChartData.module_finite_H1Cok` — **the keystone (node `N11`)**:
  `Module.Finite k (H1Cok (pullbackSquare π) (toModuleKSheaf C))` for every
  finite `k`-morphism `π : C ⟶ Y` to a target with Laurent chart data.
* `Adelic.P1HasLaurentChartData` — the gate recording the standard-chart
  computation for the concrete model `ℙ(ULift (Fin 2); Spec k)`.
* `Adelic.exists_affineCoverMVSquare_module_finite_H1Cok` — the consumable
  keystone under the gates `HasFiniteMapToP1 C` and `P1HasLaurentChartData k`:
  *some* 2-affine cover of `C` has finite-dimensional Čech `Ȟ¹`.
* `Adelic.module_finite_hModule_one_of_finite_map` — the `N12`-shaped corollary:
  once the `N5` comparison `HModule k (toModuleKSheaf C) 1 ≃ₗ[k] Ȟ¹` is supplied
  for 2-affine covers, genus finiteness `Module.Finite k (H¹(C, 𝒪_C))` follows.

## Gating

`HasFiniteMapToP1` (node `N9`, `P1BaseCase.lean`) and `P1HasLaurentChartData`
(the computation of the standard chart rings of the `Proj`-pullback model
`ℙ(ULift (Fin 2); Spec k)`) are `HasPicScheme`-style gates: single-field `Prop`
classes with **no sorried instances** — honest hypotheses to be discharged
later.  Everything else in this file is fully proved.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Adelic

/-! ## The abstract two-lattice core

Throughout this section `M` is a commutative `k`-algebra, `t, u ∈ M` with
`t * u = 1` (an "abstract Laurent pair": think `t = x`, `u = x⁻¹` in
`k[x, x⁻¹]`, or their pullbacks to the curve overlap ring). -/

section TwoLattice

variable {k : Type*} [Field k] {M : Type*} [CommRing M] [Algebra k M]

/-- Iterated stability: a `k`-submodule stable under multiplication by `t` is
stable under multiplication by every power `t ^ n`. -/
lemma pow_mul_mem {N : Submodule k M} {t : M} (h : ∀ a ∈ N, t * a ∈ N)
    (n : ℕ) {a : M} (ha : a ∈ N) : t ^ n * a ∈ N := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hrw : t ^ (n + 1) * a = t * (t ^ n * a) := by ring
    rw [hrw]
    exact h _ ih

/-- **Ladder-spanning producer.** If `t * u = 1` and every `m ∈ M` satisfies
`t ^ n * m ∈ span k {t^j · a : a ∈ s}` for some `n`, then the full two-sided
ladder `{t^j · a} ∪ {u^j · a}` (`a ∈ s`, `j ∈ ℕ`) spans `M` over `k`.  This is
the formal step combining the localization/extension property with the
chart-level spanning to produce the spanning hypothesis of the two-lattice
core. -/
theorem span_ladder_of_pow_mul_mem_span {t u : M} (htu : t * u = 1) (s : Set M)
    (H : ∀ m : M, ∃ n : ℕ,
      t ^ n * m ∈ Submodule.span k (⋃ j : ℕ, (fun z => t ^ j * z) '' s)) :
    ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z => t ^ j * z) '' s) ∪ (⋃ j : ℕ, (fun z => u ^ j * z) '' s)) := by
  have hpow : ∀ n : ℕ, u ^ n * t ^ n = 1 := fun n => by
    rw [← mul_pow, mul_comm u t, htu, one_pow]
  intro m _
  obtain ⟨n, hn⟩ := H m
  -- `m = u ^ n * (t ^ n * m)`
  have hm : m = u ^ n * (t ^ n * m) := by
    rw [← mul_assoc, hpow, one_mul]
  -- push the span through the `k`-linear map "multiplication by `u ^ n`"
  have hmem : u ^ n * (t ^ n * m) ∈ Submodule.map (LinearMap.mulLeft k (u ^ n))
      (Submodule.span k (⋃ j : ℕ, (fun z => t ^ j * z) '' s)) :=
    Submodule.mem_map_of_mem hn
  rw [Submodule.map_span, ← hm] at hmem
  refine Submodule.span_le.mpr ?_ hmem
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨j, a, ha, rfl⟩ := hz
  simp only [LinearMap.mulLeft_apply]
  rcases le_or_gt n j with hnj | hjn
  · -- `u^n · (t^j · a) = t^(j-n) · a`
    have key : u ^ n * (t ^ j * a) = t ^ (j - n) * a := by
      have hj : t ^ j = t ^ n * t ^ (j - n) := by
        rw [← pow_add]
        congr 1
        omega
      calc u ^ n * (t ^ j * a) = (u ^ n * t ^ n) * (t ^ (j - n) * a) := by rw [hj]; ring
        _ = t ^ (j - n) * a := by rw [hpow, one_mul]
    rw [key]
    exact Submodule.subset_span (Or.inl (Set.mem_iUnion.mpr
      ⟨j - n, Set.mem_image_of_mem _ ha⟩))
  · -- `u^n · (t^j · a) = u^(n-j) · a`
    have key : u ^ n * (t ^ j * a) = u ^ (n - j) * a := by
      have hn' : u ^ n = u ^ (n - j) * u ^ j := by
        rw [← pow_add]
        congr 1
        omega
      calc u ^ n * (t ^ j * a) = u ^ (n - j) * ((u ^ j * t ^ j) * a) := by rw [hn']; ring
        _ = u ^ (n - j) * a := by rw [hpow, one_mul]
    rw [key]
    exact Submodule.subset_span (Or.inr (Set.mem_iUnion.mpr
      ⟨n - j, Set.mem_image_of_mem _ ha⟩))

/-- **The abstract two-lattice core (node `N11`, algebraic heart).**
Let `M` be a commutative `k`-algebra and `t * u = 1` an abstract Laurent pair.
Suppose

* `N₀` is a `t`-stable `k`-submodule and `N₁` a `u`-stable `k`-submodule
  (the images of the two chart-section modules),
* `s ⊆ N₀` is a finite subset whose two-sided ladder
  `{t^j · a} ∪ {u^j · a}` spans `M` over `k` (the chart generators), and
* every `a ∈ s` lands in `N₁` after multiplication by a high power of `u`
  (the extension property).

Then the cokernel `M ⧸ (N₀ + N₁)` is a finite `k`-module: it is spanned by the
finitely many middle rungs `u^j · a`, `a ∈ s`, `j` below the uniform extension
bound. -/
theorem module_finite_quotient_of_laurent_pair {t u : M}
    {N₀ N₁ : Submodule k M}
    (h₀ : ∀ a ∈ N₀, t * a ∈ N₀) (h₁ : ∀ a ∈ N₁, u * a ∈ N₁)
    {s : Set M} (hs : s.Finite) (hsN₀ : s ⊆ N₀)
    (hspan : ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z => t ^ j * z) '' s) ∪ (⋃ j : ℕ, (fun z => u ^ j * z) '' s)))
    (hext : ∀ a ∈ s, ∃ n : ℕ, u ^ n * a ∈ N₁) :
    Module.Finite k (M ⧸ (N₀ ⊔ N₁)) := by
  classical
  -- a uniform extension bound over the finite set `s`
  set B : M → ℕ := fun a => if h : a ∈ s then (hext a h).choose else 0 with hB
  set N : ℕ := hs.toFinset.sup B with hNdef
  have hBmem : ∀ a ∈ s, u ^ B a * a ∈ N₁ := by
    intro a ha
    simp only [hB, dif_pos ha]
    exact (hext a ha).choose_spec
  have hN₁ : ∀ a ∈ s, ∀ n : ℕ, B a ≤ n → u ^ n * a ∈ N₁ := by
    intro a ha n hn
    have hrw : u ^ n * a = u ^ (n - B a) * (u ^ B a * a) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [hrw]
    exact pow_mul_mem h₁ _ (hBmem a ha)
  -- the finite middle band
  set T : Set M := ⋃ j ∈ Finset.range N, (fun z => u ^ j * z) '' s with hT
  have hTfin : T.Finite :=
    Set.Finite.biUnion (Finset.range N).finite_toSet fun j _ => hs.image _
  -- the middle band together with the two lattices spans everything
  have hkey : N₀ ⊔ N₁ ⊔ Submodule.span k T = ⊤ := by
    refine le_antisymm le_top (hspan.trans (Submodule.span_le.mpr ?_))
    rintro z (hz | hz) <;> simp only [Set.mem_iUnion, Set.mem_image] at hz
    · obtain ⟨j, a, ha, rfl⟩ := hz
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (pow_mul_mem h₀ j (hsN₀ ha)))
    · obtain ⟨j, a, ha, rfl⟩ := hz
      rcases lt_or_ge j N with hj | hj
      · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
        simp only [hT, Set.mem_iUnion, Set.mem_image]
        exact ⟨j, Finset.mem_range.mpr hj, a, ha, rfl⟩
      · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
        exact hN₁ a ha j (le_trans (Finset.le_sup (hs.mem_toFinset.mpr ha)) hj)
  -- pass to the quotient: the image of the middle band spans it
  have himg : Submodule.span k (⇑(N₀ ⊔ N₁).mkQ '' T) = ⊤ := by
    rw [Submodule.span_image]
    have h1 : Submodule.map (N₀ ⊔ N₁).mkQ (N₀ ⊔ N₁) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨y, hy, rfl⟩
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hy
    have h2 := congrArg (Submodule.map (N₀ ⊔ N₁).mkQ) hkey
    rw [Submodule.map_sup, h1, bot_sup_eq, Submodule.map_top, Submodule.range_mkQ] at h2
    exact h2
  have hfg : (⊤ : Submodule k (M ⧸ (N₀ ⊔ N₁))).FG :=
    ⟨(hTfin.image _).toFinset, by rw [Set.Finite.coe_toFinset]; exact himg⟩
  exact ⟨hfg⟩

end TwoLattice

/-! ## The extension lemma

Sections over a basic open extend to the chart after multiplication by a power
of the defining section — the affine incarnation of the qcqs section-extension
principle, obtained here directly from
`IsAffineOpen.isLocalization_of_eq_basicOpen`. -/

section Extension

variable {X : Scheme.{u}}

/-- **The extension lemma (`x^n · m` extends to the chart).**  Let `U` be an
affine open of a scheme `X`, `f ∈ Γ(X, U)` a section, and `W = D(f)` (recorded
as an arbitrary open equal to the basic open, so callers need not transport
along the equality).  Then for every `m ∈ Γ(X, W)` there are `n` and
`a ∈ Γ(X, U)` with `(f|_W)^n · m = a|_W`: sections of the localization extend
after multiplying by a power of `f`. -/
theorem exists_pow_mul_eq_res {U W : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (hW : W = X.basicOpen f) (hWU : W ≤ U) (m : Γ(X, W)) :
    ∃ (n : ℕ) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE hWU).op).hom f ^ n * m
        = (X.presheaf.map (homOfLE hWU).op).hom a := by
  letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, W) :=
    hU.isLocalization_of_eq_basicOpen f (homOfLE hWU) hW
  obtain ⟨⟨a, s⟩, hsurj⟩ := IsLocalization.surj (M := Submonoid.powers f) m
  obtain ⟨n, hn⟩ := s.2
  have hn' : f ^ n = (s : Γ(X, U)) := hn
  refine ⟨n, a, ?_⟩
  have halg : algebraMap Γ(X, U) Γ(X, W) = (X.presheaf.map (homOfLE hWU).op).hom :=
    RingHom.algebraMap_toAlgebra _
  rw [← halg, ← map_pow, hn', mul_comm]
  exact hsurj

end Extension

/-! ## Chart spanning

If `A` is a module-finite `R`-algebra and `R` is spanned over `k` by the powers
of a single element `x` (the ℙ¹ chart ring `k[x]`), then `A` is spanned over
`k` by the ladder `{φ(x)^n · g}` over a finite set of generators `g`. -/

section ChartSpan

variable {k : Type*} [Field k] {R A : Type*} [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A]

/-- **Chart spanning.**  For a `k`-algebra map `φ : R →+* A` that is module
finite, with `R` spanned over `k` by the powers of `x`, there is a finite set
`G ⊆ A` such that every element of `A` lies in the `k`-span of the ladder
`{φ(x)^n · g : n ∈ ℕ, g ∈ G}`. -/
theorem exists_finset_forall_mem_span_pow_mul
    {φ : R →+* A} (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k A c)
    (hfin : φ.Finite) {x : R}
    (hx : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => x ^ n)) :
    ∃ G : Finset A, ∀ a : A,
      a ∈ Submodule.span k (⋃ n : ℕ, (fun z => φ x ^ n * z) '' (G : Set A)) := by
  letI : Algebra R A := φ.toAlgebra
  haveI hfin' : Module.Finite R A := hfin
  obtain ⟨G, hG⟩ := Module.finite_def.mp hfin'
  refine ⟨G, fun a => ?_⟩
  have ha : a ∈ Submodule.span R (G : Set A) := by rw [hG]; trivial
  -- the `k`-linear incarnation of `φ`
  let φₗ : R →ₗ[k] A :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c r => by
        simp only [Algebra.smul_def, map_mul, hφ, RingHom.id_apply] }
  induction ha using Submodule.span_induction with
  | mem z hz =>
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨0, ⟨z, hz, ?_⟩⟩)
    simp
  | zero => exact zero_mem _
  | add y z hy hz ihy ihz => exact add_mem ihy ihz
  | smul r z hz ihz =>
    have hra : r • z = φ r * z := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rw [hra]
    -- `φ r` lies in the `k`-span of the powers of `φ x`
    have hr : φ r ∈ Submodule.span k (Set.range fun n : ℕ => φ x ^ n) := by
      have h1 : φ r ∈ Submodule.map φₗ (Submodule.span k (Set.range fun n : ℕ => x ^ n)) :=
        Submodule.mem_map_of_mem (hx trivial)
      rw [Submodule.map_span] at h1
      refine Submodule.span_le.mpr ?_ h1
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨n, (map_pow φ x n).symm⟩
    -- multiply the two spans
    have hmul := Submodule.mul_mem_mul hr ihz
    rw [Submodule.span_mul_span] at hmul
    refine Submodule.span_le.mpr ?_ hmul
    rintro _ ⟨p, hp, q, hq, rfl⟩
    obtain ⟨n, rfl⟩ := hp
    simp only [Set.mem_iUnion, Set.mem_image] at hq
    obtain ⟨j, g, hg, rfl⟩ := hq
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨n + j, ⟨g, hg, ?_⟩⟩)
    rw [pow_add]
    ring

end ChartSpan

/-! ## `k`-algebra compatibility of a morphism of `Spec k`-schemes

The pullback ring maps of a morphism `π : C ⟶ Y` in `Over (Spec k)` are
`k`-algebra maps for the structure-morphism `k`-algebra structures
(`Scheme.toModuleKSheaf.algebraSection`) on the section rings. -/

section OverAlgebra

variable {k : Type u} [Field k] {C Y : Over (Spec (CommRingCat.of k))}

/-- **`k`-linearity of the pullback map.**  For a morphism `π : C ⟶ Y` of
`Spec k`-schemes and an open `V ⊆ Y`, the pullback map
`π^♯ : Γ(Y, V) → Γ(C, π⁻¹V)` commutes with the structure-morphism `k`-algebra
maps (`Scheme.toModuleKSheaf.algebraSection`): it is a `k`-algebra map.

The proof unfolds both algebra maps to their `kToSection` composites, replaces
the structure morphism of `C` by `π.left ≫ Y.hom` via the over-category
triangle (`Over.w`, applied through an explicitly typed `congrArg` to avoid
dependent-motive rewriting), and finishes with the naturality of `π^♯`. -/
lemma app_algebraMap (π : C ⟶ Y) (V : Y.left.Opens) (c : k) :
    (π.left.app V).hom (algebraMap k Γ(Y.left, V) c)
      = algebraMap k Γ(C.left, π.left ⁻¹ᵁ V) c := by
  have hL : algebraMap k Γ(Y.left, V) c
      = (Y.left.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
          (Y.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) := rfl
  have hR : algebraMap k Γ(C.left, π.left ⁻¹ᵁ V) c
      = (C.left.presheaf.map (homOfLE (le_top : π.left ⁻¹ᵁ V ≤ ⊤)).op).hom
          (C.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) := rfl
  have hw : C.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
      = π.left.appTop.hom
          (Y.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) :=
    congrArg (fun h : C.left ⟶ Spec (CommRingCat.of k) =>
      h.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) (Over.w π).symm
  have hnat := congrArg
    (fun g : Γ(Y.left, ⊤) ⟶ Γ(C.left, π.left ⁻¹ᵁ V) => g.hom
      (Y.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))
    (π.left.naturality (homOfLE (le_top : V ≤ ⊤)).op)
  rw [hL, hR, hw]
  exact hnat

end OverAlgebra

/-! ## Laurent chart data and the pulled-back 2-affine cover -/

section ChartData

variable {k : Type u} [Field k]

/-- **Laurent chart data (the standard two-chart structure of `ℙ¹`).**
A bundled datum on a `Spec k`-scheme `Y` recording the standard affine
two-chart structure of the projective line: two affine opens `V₀, V₁` covering
`Y`, coordinate sections `x ∈ Γ(V₀)` and `y ∈ Γ(V₁)` that are mutually inverse
on the overlap, the overlap being the basic open of either coordinate, and each
chart ring being spanned over `k` by the powers of its coordinate
(`Γ(V₀) = k[x]`, `Γ(V₁) = k[y]`; hence `Γ(V₀ ⊓ V₁) = k[x, x⁻¹]`, the Laurent
ring of `P1BaseCase.lean`).

The `k`-module structures are the structure-morphism algebra structures
`Scheme.toModuleKSheaf.algebraSection`.  The keystone consumes this datum on
the *target* of a finite morphism; the instantiation for the concrete model
`ℙ(ULift (Fin 2); Spec k)` is gated behind `P1HasLaurentChartData`. -/
structure LaurentChartData (Y : Over (Spec (CommRingCat.of k))) : Type u where
  /-- The first standard chart (`x`-chart). -/
  V₀ : Y.left.Opens
  /-- The second standard chart (`y = x⁻¹`-chart). -/
  V₁ : Y.left.Opens
  /-- The first chart is affine. -/
  isAffineOpen_V₀ : IsAffineOpen V₀
  /-- The second chart is affine. -/
  isAffineOpen_V₁ : IsAffineOpen V₁
  /-- The two charts cover `Y`. -/
  cover : V₀ ⊔ V₁ = ⊤
  /-- The coordinate on the first chart. -/
  x : Γ(Y.left, V₀)
  /-- The coordinate on the second chart. -/
  y : Γ(Y.left, V₁)
  /-- The overlap is the basic open of `x`. -/
  inf_eq_basicOpen_x : V₀ ⊓ V₁ = Y.left.basicOpen x
  /-- The overlap is the basic open of `y`. -/
  inf_eq_basicOpen_y : V₀ ⊓ V₁ = Y.left.basicOpen y
  /-- The coordinates are mutually inverse on the overlap: `x · y = 1`. -/
  res_x_mul_res_y :
    (Y.left.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op).hom x
      * (Y.left.presheaf.map (homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op).hom y = 1
  /-- The first chart ring is the `k`-span of the powers of `x`
  (`Γ(V₀) = k[x]`). -/
  span_pow_x : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => x ^ n)
  /-- The second chart ring is the `k`-span of the powers of `y`
  (`Γ(V₁) = k[y]`). -/
  span_pow_y : ⊤ ≤ Submodule.span k (Set.range fun n : ℕ => y ^ n)

variable {Y C : Over (Spec (CommRingCat.of k))}

/-- **The pulled-back 2-affine cover (node `N10`).**  The preimages of the two
standard charts under a finite morphism `π : C ⟶ Y` form a 2-affine cover of
the curve with affine overlap: finite morphisms are affine, so all three
preimage opens are affine (`IsAffineOpen.preimage`), and preimages preserve the
covering property. -/
noncomputable def LaurentChartData.pullbackSquare (D : LaurentChartData Y)
    (π : C ⟶ Y) [IsFinite π.left] : C.left.AffineCoverMVSquare where
  U₁ := π.left ⁻¹ᵁ D.V₀
  U₂ := π.left ⁻¹ᵁ D.V₁
  isAffineOpen_U₁ := D.isAffineOpen_V₀.preimage π.left
  isAffineOpen_U₂ := D.isAffineOpen_V₁.preimage π.left
  isAffineOpen_inf := by
    have hinf : IsAffineOpen (D.V₀ ⊓ D.V₁) := by
      rw [D.inf_eq_basicOpen_x]
      exact D.isAffineOpen_V₀.basicOpen D.x
    exact hinf.preimage π.left
  cover := by
    change π.left ⁻¹ᵁ (D.V₀ ⊔ D.V₁) = ⊤
    rw [D.cover]
    rfl

/-- **The keystone (node `N11`): `H¹` finiteness of the curve over the Laurent
chart target.**  For a finite morphism `π : C ⟶ Y` of `Spec k`-schemes to a
target with Laurent chart data `D`, the two-cover Čech cokernel
`Ȟ¹ = Γ(U₀ ⊓ U₁, 𝒪_C) ⧸ (Γ(U₀, 𝒪_C) + Γ(U₁, 𝒪_C))` of the structure sheaf on
the pulled-back cover `U_i = π⁻¹V_i` is a finite `k`-module.

This is the Weil/Stichtenoth two-lattice argument: `Γ(U₀)` is module-finite
over `Γ(V₀) = k[x]` (finiteness of `π`), the overlap ring is its localization
at `t = π^♯x` (basic-open localization), so the ladder `{t^j·g}` over finitely
many generators spans; positive rungs come from `Γ(U₀)`, sufficiently negative
rungs from `Γ(U₁)` (the extension lemma at the `y`-chart), leaving a finite
middle band to span the cokernel.

The proof crosses the `Scheme.Opens` versus `Opens X.toTopCat` presentation
diamond and the `ModuleCat.of`/`Γ` carrier identifications explicitly. -/
theorem LaurentChartData.module_finite_H1Cok (D : LaurentChartData Y)
    (π : C ⟶ Y) [IsFinite π.left] :
    Module.Finite k ((D.pullbackSquare π).H1Cok (Scheme.toModuleKSheaf C)) := by
  classical
  -- ### Notation
  -- `σᵢ` the `k`-linear restrictions from the pulled-back charts to the
  -- overlap; `x₀, y₁` the pulled-back coordinates; `t, u` their restrictions
  -- to the overlap (the abstract Laurent pair).
  set σ₀ : Γ(C.left, π.left ⁻¹ᵁ D.V₀) →ₗ[k]
      Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)) :=
    Scheme.sectionRestrict (Scheme.toModuleKSheaf C) inf_le_left with hσ₀def
  set σ₁ : Γ(C.left, π.left ⁻¹ᵁ D.V₁) →ₗ[k]
      Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)) :=
    Scheme.sectionRestrict (Scheme.toModuleKSheaf C) inf_le_right with hσ₁def
  have hσ₀app : ∀ a, σ₀ a = (C.left.presheaf.map (homOfLE
      (inf_le_left : (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁) ≤ π.left ⁻¹ᵁ D.V₀)).op).hom a :=
    fun _ => rfl
  have hσ₁app : ∀ a, σ₁ a = (C.left.presheaf.map (homOfLE
      (inf_le_right : (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁) ≤ π.left ⁻¹ᵁ D.V₁)).op).hom a :=
    fun _ => rfl
  set x₀ : Γ(C.left, π.left ⁻¹ᵁ D.V₀) := (π.left.app D.V₀).hom D.x with hx₀def
  set y₁ : Γ(C.left, π.left ⁻¹ᵁ D.V₁) := (π.left.app D.V₁).hom D.y with hy₁def
  set t := σ₀ x₀ with htdef
  set u := σ₁ y₁ with hudef
  -- ### The overlap is the basic open of either pulled-back coordinate
  have hWx : (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁) = C.left.basicOpen x₀ := by
    have h1 : (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁) = π.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁) := rfl
    rw [h1, D.inf_eq_basicOpen_x, Scheme.preimage_basicOpen, hx₀def]
  have hWy : (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁) = C.left.basicOpen y₁ := by
    have h1 : (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁) = π.left ⁻¹ᵁ (D.V₀ ⊓ D.V₁) := rfl
    rw [h1, D.inf_eq_basicOpen_y, Scheme.preimage_basicOpen, hy₁def]
  -- ### Naturality: the pulled-back coordinates restricted to the overlap are
  -- the overlap pullbacks of the chart coordinates
  have hnat₀ : t = (π.left.app (D.V₀ ⊓ D.V₁)).hom
      ((Y.left.presheaf.map (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom D.x) := by
    have h := congrArg (fun g : Γ(Y.left, D.V₀) ⟶
        Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)) => g.hom D.x)
      (π.left.naturality (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op)
    rw [htdef, hσ₀app, hx₀def]
    exact h.symm
  have hnat₁ : u = (π.left.app (D.V₀ ⊓ D.V₁)).hom
      ((Y.left.presheaf.map (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op).hom D.y) := by
    have h := congrArg (fun g : Γ(Y.left, D.V₁) ⟶
        Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)) => g.hom D.y)
      (π.left.naturality (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op)
    rw [hudef, hσ₁app, hy₁def]
    exact h.symm
  -- ### The abstract Laurent pair: `t * u = 1`
  -- (term-mode chain: `rw`/`simp` motive checks fail across the
  -- `Scheme.Opens`/`Opens X.toTopCat` presentation diamond)
  have htu : t * u = 1 := by
    rw [hnat₀, hnat₁]
    exact ((map_mul _ _ _).symm.trans (congrArg _ D.res_x_mul_res_y)).trans (map_one _)
  -- ### The extension lemmas at the two charts
  have hext₀ : ∀ m : Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)),
      ∃ (n : ℕ) (a : Γ(C.left, π.left ⁻¹ᵁ D.V₀)), t ^ n * m = σ₀ a := by
    intro m
    obtain ⟨n, a, ha⟩ := exists_pow_mul_eq_res (D.isAffineOpen_V₀.preimage π.left) x₀ hWx
      inf_le_left m
    refine ⟨n, a, ?_⟩
    rw [htdef, hσ₀app, hσ₀app]
    exact ha
  have hext₁ : ∀ m : Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)),
      ∃ (n : ℕ) (b : Γ(C.left, π.left ⁻¹ᵁ D.V₁)), u ^ n * m = σ₁ b := by
    intro m
    obtain ⟨n, b, hb⟩ := exists_pow_mul_eq_res (D.isAffineOpen_V₁.preimage π.left) y₁ hWy
      inf_le_right m
    refine ⟨n, b, ?_⟩
    rw [hudef, hσ₁app, hσ₁app]
    exact hb
  -- ### The two lattices and their stability
  have h₀ : ∀ a ∈ LinearMap.range σ₀, t * a ∈ LinearMap.range σ₀ := by
    rintro _ ⟨b, rfl⟩
    refine ⟨x₀ * b, ?_⟩
    simp only [htdef, hσ₀app, map_mul]
  have h₁ : ∀ a ∈ LinearMap.range σ₁, u * a ∈ LinearMap.range σ₁ := by
    rintro _ ⟨b, rfl⟩
    refine ⟨y₁ * b, ?_⟩
    simp only [hudef, hσ₁app, map_mul]
  -- ### Chart-0 generators (module-finiteness over `Γ(V₀) = k[x]`)
  obtain ⟨G, hG⟩ := exists_finset_forall_mem_span_pow_mul
    (φ := (π.left.app D.V₀).hom) (app_algebraMap π D.V₀)
    (π.left.finite_app D.V₀ D.isAffineOpen_V₀) D.span_pow_x
  simp only [← hx₀def] at hG
  -- ### The ladder over the images of the generators spans the overlap ring
  have Hpow : ∀ m : Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)), ∃ n : ℕ,
      t ^ n * m ∈ Submodule.span k
        (⋃ j : ℕ, (fun z => t ^ j * z) '' (⇑σ₀ '' (G : Set _))) := by
    intro m
    obtain ⟨n, a, ha⟩ := hext₀ m
    refine ⟨n, ?_⟩
    rw [ha]
    have h1 : σ₀ a ∈ Submodule.map σ₀ (Submodule.span k
        (⋃ j : ℕ, (fun z => x₀ ^ j * z) '' (G : Set _))) :=
      Submodule.mem_map_of_mem (hG a)
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image] at hz
    obtain ⟨j, g, hg, rfl⟩ := hz
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, ⟨σ₀ g, ⟨g, hg, rfl⟩, ?_⟩⟩)
    simp only [htdef, hσ₀app, map_mul, map_pow]
  have hspan : ⊤ ≤ Submodule.span k
      ((⋃ j : ℕ, (fun z => t ^ j * z) '' (⇑σ₀ '' (G : Set _)))
        ∪ (⋃ j : ℕ, (fun z => u ^ j * z) '' (⇑σ₀ '' (G : Set _)))) :=
    span_ladder_of_pow_mul_mem_span htu _ Hpow
  -- ### The remaining hypotheses of the two-lattice core
  have hsfin : (⇑σ₀ '' (G : Set _)).Finite := G.finite_toSet.image _
  have hsN₀ : ⇑σ₀ '' (G : Set _) ⊆ (LinearMap.range σ₀ : Set _) := by
    rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  have hext : ∀ a ∈ ⇑σ₀ '' (G : Set _), ∃ n : ℕ, u ^ n * a ∈ LinearMap.range σ₁ := by
    intro a _
    obtain ⟨n, b, hb⟩ := hext₁ a
    exact ⟨n, b, hb.symm⟩
  -- ### The two-lattice core
  have hcore : Module.Finite k
      (Γ(C.left, (π.left ⁻¹ᵁ D.V₀) ⊓ (π.left ⁻¹ᵁ D.V₁)) ⧸
        (LinearMap.range σ₀ ⊔ LinearMap.range σ₁)) :=
    module_finite_quotient_of_laurent_pair h₀ h₁ hsfin hsN₀ hspan hext
  -- ### The Čech difference range is the sum of the two lattices
  -- (stated with the `Γ`-presentation on the left so the whole equation
  -- elaborates in the section-ring world; the two inclusions are proved by
  -- exhibiting `σ₀, σ₁` as compositions with the difference map)
  have hrange : LinearMap.range σ₀ ⊔ LinearMap.range σ₁
      = LinearMap.range ((D.pullbackSquare π).sectionDiff (Scheme.toModuleKSheaf C)) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · have hcomp₀ : σ₀ = ((D.pullbackSquare π).sectionDiff
            (Scheme.toModuleKSheaf C)).comp (LinearMap.inl k _ _) := by
          ext a
          change σ₀ a = σ₀ a - σ₁ 0
          rw [map_zero, sub_zero]
        rw [hcomp₀]
        exact LinearMap.range_comp_le_range _ _
      · have hcomp₁ : -σ₁ = ((D.pullbackSquare π).sectionDiff
            (Scheme.toModuleKSheaf C)).comp (LinearMap.inr k _ _) := by
          ext b
          change -(σ₁ b) = σ₀ 0 - σ₁ b
          rw [map_zero, zero_sub]
        rw [← LinearMap.range_neg σ₁, hcomp₁]
        exact LinearMap.range_comp_le_range _ _
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact sub_mem (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right ⟨b, rfl⟩)
  rw [hrange] at hcore
  exact hcore

end ChartData

/-! ## The standard 2-chart affine cover of the projective line

For the concrete model `ℙ¹ = ℙ(ULift (Fin 2); Spec k)` (the pullback of the
integral `Proj ℤ[X₀, X₁]`, `Picard/ProjectiveSpace.lean`), the preimages of the
`Proj` basic opens `D₊(X₀), D₊(X₁)` under the projection to the integral model
form a 2-affine cover with affine overlap: the projection is an affine morphism
(base change of the affine `Spec k ⟶ ⊤`), so preimages of the affine `D₊`'s
are affine.  This is the `AffineCoverMVSquare` on which the Laurent chart data
of ℙ¹ lives; the remaining chart-ring computation (`Γ(V₀) = k[x]` etc. for the
pullback model) is the content of the `P1HasLaurentChartData` gate below. -/

section P1Square

variable (k : Type u) [Field k]

/-- The projection from relative projective space to the integral model is an
affine morphism whenever the base is affine (it is the base change of the
affine morphism `S ⟶ ⊤` along `⊤_ ⟶ Proj ℤ[Xᵢ]`). -/
instance isAffineHom_toProjInt (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    IsAffineHom (ProjectiveSpace.toProjInt n S) := by
  rw [ProjectiveSpace.toProjInt_eq_snd]
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The `i`-th standard chart of `ℙ¹ = ℙ(ULift (Fin 2); Spec k)`: the preimage
of the `Proj` basic open `D₊(Xᵢ)` of the integral model. -/
noncomputable def p1Chart (i : ULift.{u} (Fin 2)) :
    (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).Opens :=
  ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (MvPolynomial.X i)

/-- Each standard chart of `ℙ¹` is affine: `D₊(Xᵢ)` is affine in the integral
model (`Xᵢ` is homogeneous of degree `1 > 0`) and the projection is an affine
morphism. -/
lemma isAffineOpen_p1Chart (i : ULift.{u} (Fin 2)) :
    IsAffineOpen (p1Chart k i) :=
  (Proj.isAffineOpen_basicOpen _ _ (ProjTwist.X_mem_deg_one _ i) one_pos).preimage _

/-- The overlap of the two standard charts of `ℙ¹` is affine: it is the
preimage of `D₊(X₀ · X₁)` (`X₀X₁` is homogeneous of degree `2 > 0`). -/
lemma isAffineOpen_p1Chart_inf :
    IsAffineOpen (p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩) := by
  have h : p1Chart k ⟨0⟩ ⊓ p1Chart k ⟨1⟩
      = ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (MvPolynomial.X ⟨0⟩ * MvPolynomial.X ⟨1⟩) := by
    rw [Proj.basicOpen_mul]
    rfl
  rw [h]
  exact (Proj.isAffineOpen_basicOpen _ _
    (ProjTwist.X_mul_X_mem_deg_two _ (⟨0⟩ : ULift.{u} (Fin 2)) (⟨1⟩ : ULift.{u} (Fin 2)))
    two_pos).preimage _

/-- The two standard charts cover `ℙ¹`: the basic opens `D₊(X₀), D₊(X₁)` cover
the integral model (the variables generate the irrelevant ideal), and preimages
preserve covers. -/
lemma p1Chart_sup_eq_top : p1Chart k ⟨0⟩ ⊔ p1Chart k ⟨1⟩ = ⊤ := by
  have h : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2))
        (ULift.{u} ℤ)) (MvPolynomial.X ⟨0⟩)
      ⊔ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2))
        (ULift.{u} ℤ)) (MvPolynomial.X ⟨1⟩) = ⊤ := by
    rw [← ProjTwist.iSup_basicOpen_X_eq_top (ULift.{u} (Fin 2))]
    apply le_antisymm
    · exact sup_le
        (le_iSup (fun i : ULift.{u} (Fin 2) => Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (MvPolynomial.X i)) ⟨0⟩)
        (le_iSup (fun i : ULift.{u} (Fin 2) => Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
          (MvPolynomial.X i)) ⟨1⟩)
    · refine iSup_le fun i => ?_
      obtain ⟨i⟩ := i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
  change ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k)) ⁻¹ᵁ
    (Proj.basicOpen _ (MvPolynomial.X ⟨0⟩) ⊔ Proj.basicOpen _ (MvPolynomial.X ⟨1⟩)) = ⊤
  rw [h]
  rfl

/-- **The standard 2-chart affine cover square of the projective line**
`ℙ¹ = ℙ(ULift (Fin 2); Spec k)` — the geometric substrate of the ℙ¹ Laurent
chart data (its `V₀, V₁, isAffineOpen_*, cover` fields). -/
noncomputable def p1CoverSquare :
    (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).AffineCoverMVSquare where
  U₁ := p1Chart k ⟨0⟩
  U₂ := p1Chart k ⟨1⟩
  isAffineOpen_U₁ := isAffineOpen_p1Chart k ⟨0⟩
  isAffineOpen_U₂ := isAffineOpen_p1Chart k ⟨1⟩
  isAffineOpen_inf := isAffineOpen_p1Chart_inf k
  cover := p1Chart_sup_eq_top k

end P1Square

/-! ## The gated ℙ¹ instantiation and the consumable keystone -/

section Keystone

variable {k : Type u} [Field k]

/-- **The ℙ¹-chart gate.**  A `HasPicScheme`-style single-field `Prop` class
recording that the concrete projective line `ℙ(ULift (Fin 2); Spec k)` carries
Laurent chart data: the standard 2-chart structure (`p1CoverSquare`) together
with the chart-ring computation `Γ(V₀) = k[x]`, `Γ(V₁) = k[x⁻¹]`,
`V₀ ⊓ V₁ = D(x)` for the `Proj`-pullback model.

Mathematically this is classical bookkeeping (the sections of the pullback
`Spec k ×_ℤ Proj ℤ[X₀, X₁]` over the chart preimages are
`k ⊗_ℤ ℤ[X₁/X₀] = k[x]`, with `x = X₁/X₀` and `y = X₀/X₁` mutually inverse on
the overlap `D₊(X₀X₁)`), but the pullback-section computation is a genuine
formalisation effort; the class carries **no instance** and is supplied at use
sites, in the `HasPicScheme`/`HasFiniteMapToP1` gating pattern. -/
class P1HasLaurentChartData (k : Type u) [Field k] : Prop where
  /-- The concrete projective line carries Laurent chart data. -/
  nonempty_laurentChartData : Nonempty (LaurentChartData
    (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))))

/-- **The consumable keystone (node `N11` under the gates).**  For a curve
`C` over `k` with a finite morphism to the projective line (`HasFiniteMapToP1`)
and given the ℙ¹ chart-ring computation (`P1HasLaurentChartData`), *some*
2-affine cover of `C` — namely the pullback of the standard ℙ¹ charts — has
finite-dimensional two-cover Čech cokernel:
`Module.Finite k (Ȟ¹(C, 𝒪_C))`. -/
theorem exists_affineCoverMVSquare_module_finite_H1Cok
    (C : Over (Spec (CommRingCat.of k))) [HasFiniteMapToP1 C]
    [P1HasLaurentChartData k] :
    ∃ S : C.left.AffineCoverMVSquare,
      Module.Finite k (S.H1Cok (Scheme.toModuleKSheaf C)) := by
  obtain ⟨π, hπ⟩ := HasFiniteMapToP1.nonempty_finite_map (C := C)
  obtain ⟨D⟩ := P1HasLaurentChartData.nonempty_laurentChartData (k := k)
  haveI := hπ
  exact ⟨D.pullbackSquare π, D.module_finite_H1Cok π⟩

/-- **The `N12`-shaped corollary: genus finiteness given the `N5` comparison.**
Once the 2-cover Čech comparison `HModule k (toModuleKSheaf C) 1 ≃ₗ[k] Ȟ¹`
(nodes `N5`/`N6`, the `Cokernel.lean` side of the lane) is supplied for
2-affine covers, the gates deliver the AJC's genus carrier:
`H¹(C, 𝒪_C) = HModule k (toModuleKSheaf C) 1` is a finite `k`-module, so
`genus C = finrank k H¹(C, 𝒪_C)` is an honest natural number. -/
theorem module_finite_hModule_one_of_finite_map
    (C : Over (Spec (CommRingCat.of k))) [HasFiniteMapToP1 C]
    [P1HasLaurentChartData k]
    [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))]
    (hcomp : ∀ S : C.left.AffineCoverMVSquare,
      Nonempty (Scheme.HModule k (Scheme.toModuleKSheaf C) 1 ≃ₗ[k]
        S.H1Cok (Scheme.toModuleKSheaf C))) :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  obtain ⟨S, hS⟩ := exists_affineCoverMVSquare_module_finite_H1Cok C
  obtain ⟨e⟩ := hcomp S
  haveI := hS
  exact Module.Finite.equiv e.symm

end Keystone

end AlgebraicGeometry.Adelic
