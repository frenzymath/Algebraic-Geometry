/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Trivializing an invertible module away from finitely many primes ((C2), brick E4)

The pure-algebra core of the (C2) piece-selection moving lemma: an invertible module
over a commutative ring becomes **free** after inverting a single element avoiding any
prescribed finite set of primes; and, for a finite (integral) algebra, an element of the
extension avoiding every prime over a base prime `p` divides the image of an element of
the base avoiding `p` — the **algebraic tube**.

* `Module.Invertible.free_of_span_singleton_eq_top` — a cyclic invertible module is
  free: the section `r ↦ r • m₀` is injective because a dual functional pairs `m₀` to a
  unit (surjectivity of the contraction), and surjective by cyclicity.
* `Module.Invertible.exists_notMem_isUnit_free` — **the avoidance brick**: for an
  invertible `N` over `R` and finitely many primes `q i`, there is `f ∉ ⋃ q i` such that
  `S ⊗[R] N` is free over every `R`-algebra `S` in which `f` becomes a unit.  Route:
  localize at the complement `S₀` of `⋃ q i`; the localization is semilocal (every
  maximal ideal is one of the localized `q i` by prime avoidance), so its Picard group
  is trivial (mathlib) and `LocalizedModule S₀ N` is cyclic; clearing denominators in
  the generator relations of finitely many generators of `N` produces `f`.
* `Algebra.exists_notMem_algebraMap_eq_mul` — **the algebraic tube**: for an integral
  algebra `S → R`, a prime `p` of `S`, and `f : R` avoiding every prime of `R` lying
  over `p`, some `g ∉ p` has `algebraMap S R g = f * h` — going-up
  (`Ideal.exists_ideal_over_prime_of_isIntegral`) applied to the ideal `(f)`.

These feed `AlgebraicJacobian.Picard.EffectivityMoving`: the primes are the finitely
many points of the fiber of the cover inclusion `cg` over a point `x` (finiteness by
quasi-finiteness of the module-finite piece rings), and the tube converts the basic
open `D(f)` of the cover piece into the preimage of a basic open `D(g) ∋ x` downstairs.
-/

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Module.Invertible

variable {R : Type u} [CommRing R]

/-! ## Cyclic invertible modules are free -/

/-- A cyclic invertible module is free on its generator: the section `r ↦ r • m₀` is
bijective.  Injectivity: if `r • m₀ = 0` then `r` kills all of `N = R ∙ m₀`, so `r`
kills every element of `Dual N ⊗ N`, whose contraction hits `1`. -/
theorem bijective_toSpanSingleton_of_span_eq_top (N : Type u) [AddCommGroup N]
    [Module R N] [Module.Invertible R N] (m₀ : N)
    (hspan : Submodule.span R {m₀} = ⊤) :
    Function.Bijective (LinearMap.toSpanSingleton R N m₀) := by
  constructor
  · -- injectivity
    rw [injective_iff_map_eq_zero]
    intro r hr
    rw [LinearMap.toSpanSingleton_apply] at hr
    -- `r` kills every element of `N`
    have hker : ∀ n : N, r • n = 0 := by
      intro n
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp
        (hspan ▸ Submodule.mem_top : n ∈ Submodule.span R {m₀})
      rw [smul_comm, hr, smul_zero]
    -- hence `r • idₙ = 0`, so `r` kills `Dual N ⊗ N`
    have hzero : (r • LinearMap.id : N →ₗ[R] N) = 0 :=
      LinearMap.ext fun n => hker n
    have hAll : ∀ w : Module.Dual R N ⊗[R] N,
        r • w = LinearMap.lTensor (Module.Dual R N)
          (r • LinearMap.id : N →ₗ[R] N) w := by
      intro w
      induction w with
      | zero => simp
      | tmul f n => simp
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    obtain ⟨w, hw⟩ := (Module.Invertible.bijective (R := R) (M := N)).surjective 1
    have hsmul : r • w = 0 := by
      rw [hAll w, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]
    calc r = r * contractLeft R N w := by rw [hw, mul_one]
      _ = contractLeft R N (r • w) := by rw [map_smul, smul_eq_mul]
      _ = 0 := by rw [hsmul, map_zero]
  · -- surjectivity
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, hspan]

/-- A cyclic invertible module is free. -/
theorem free_of_span_singleton_eq_top (N : Type u) [AddCommGroup N] [Module R N]
    [Module.Invertible R N] (m₀ : N) (hspan : Submodule.span R {m₀} = ⊤) :
    Module.Free R N :=
  Module.Free.of_equiv
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N m₀)
      (bijective_toSpanSingleton_of_span_eq_top N m₀ hspan))

/-! ## The avoidance brick -/

/-- The localization of `R` at the complement of a finite union of primes is
semilocal: every maximal ideal is the localization of one of the primes. -/
private theorem finite_maximalSpectrum_localization {ι : Type*} [Finite ι]
    [Nonempty ι] (q : ι → Ideal R) [hq : ∀ i, (q i).IsPrime] :
    Finite (MaximalSpectrum (Localization (⨅ i, (q i).primeCompl))) := by
  classical
  cases nonempty_fintype ι
  set S₀ : Submonoid R := ⨅ i, (q i).primeCompl with hS₀
  -- every maximal ideal of the localization is a localized `q i`
  have key : ∀ m : MaximalSpectrum (Localization S₀),
      ∃ i, m.asIdeal = Ideal.map (algebraMap R (Localization S₀)) (q i) := by
    intro m
    haveI : m.asIdeal.IsPrime := m.isMaximal.isPrime
    set P := (IsLocalization.orderIsoOfPrime S₀ (Localization S₀))
      ⟨m.asIdeal, inferInstance⟩ with hP
    -- the contraction is contained in the union of the `q i`
    have hsub : (P.1 : Set R) ⊆ ⋃ i ∈ (Finset.univ : Finset ι), (q i : Set R) := by
      intro a ha
      have hnot : a ∉ S₀ := fun hmem =>
        Set.disjoint_left.mp P.2.2 hmem ha
      rw [hS₀] at hnot
      simp only [Submonoid.mem_iInf, not_forall] at hnot
      obtain ⟨i, hi⟩ := hnot
      have hai : a ∈ q i := by
        by_contra hne
        exact hi hne
      exact Set.mem_biUnion (Finset.mem_univ i) hai
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    haveI : P.1.IsPrime := P.2.1
    obtain ⟨i, -, hle⟩ := (Ideal.subset_union_prime (f := q) i₀ i₀
      (fun j _ _ _ => hq j)).mp hsub
    -- `q i` is prime and disjoint from `S₀`
    have hdisj : Disjoint (S₀ : Set R) (q i : Set R) := by
      rw [Set.disjoint_left]
      intro a haS haq
      rw [hS₀] at haS
      exact Submonoid.mem_iInf.mp haS i haq
    -- compare through the order isomorphism
    have hle' : (⟨m.asIdeal, inferInstance⟩ : {p : Ideal (Localization S₀) // p.IsPrime})
        ≤ (IsLocalization.orderIsoOfPrime S₀ (Localization S₀)).symm
          ⟨q i, hq i, hdisj⟩ := by
      rw [← (IsLocalization.orderIsoOfPrime S₀ (Localization S₀)).le_iff_le,
        OrderIso.apply_symm_apply]
      exact hle
    refine ⟨i, ?_⟩
    have hne : ((IsLocalization.orderIsoOfPrime S₀ (Localization S₀)).symm
        ⟨q i, hq i, hdisj⟩).1 ≠ ⊤ :=
      ((IsLocalization.orderIsoOfPrime S₀ (Localization S₀)).symm
        ⟨q i, hq i, hdisj⟩).2.ne_top
    have heq := m.isMaximal.eq_of_le hne hle'
    rw [heq]
    rfl
  choose ind hind using key
  refine _root_.Finite.of_injective ind fun m₁ m₂ h => ?_
  ext1
  rw [hind m₁, hind m₂, h]

/-- **The avoidance brick**: an invertible module over `R` trivializes away from a
single element avoiding any prescribed finite family of primes — for every `R`-algebra
in which that element becomes a unit, the base change is free. -/
theorem exists_notMem_isUnit_free (N : Type u) [AddCommGroup N] [Module R N]
    [Module.Invertible R N] {ι : Type*} [Finite ι] (q : ι → Ideal R)
    [hq : ∀ i, (q i).IsPrime] :
    ∃ f : R, (∀ i, f ∉ q i) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S f) →
        Module.Free S (S ⊗[R] N) := by
  classical
  -- generators of `N`
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := N)
  -- a single element `m₀` of `N` and denominators `d j ∈ S₀` with
  -- `(d j) • g j ∈ R ∙ m₀`
  have key : ∃ m₀ : N, ∃ d : Fin n → R, ∃ r : Fin n → R,
      (∀ i (j : Fin n), d j ∉ q i) ∧ ∀ j, d j • g j = r j • m₀ := by
    cases isEmpty_or_nonempty ι with
    | inl hempty =>
      -- no primes to avoid: take `d = 0`
      exact ⟨0, fun _ => 0, fun _ => 0,
        fun i => (IsEmpty.false i).elim, fun j => by simp⟩
    | inr hne =>
      set S₀ : Submonoid R := ⨅ i, (q i).primeCompl with hS₀
      haveI := finite_maximalSpectrum_localization q
      -- the localized module is cyclic: the Picard group of the semilocal
      -- localization is trivial
      have h1 : CommRing.Pic.mk (Localization S₀) (LocalizedModule S₀ N) = 1 :=
        Subsingleton.elim _ _
      obtain ⟨e⟩ := CommRing.Pic.mk_eq_one_iff.mp h1
      set z : LocalizedModule S₀ N := e.symm 1 with hz
      have hgen : ∀ w : LocalizedModule S₀ N, w = e w • z := by
        intro w
        apply e.injective
        rw [map_smul, hz, e.apply_symm_apply, smul_eq_mul, mul_one]
      obtain ⟨m₀, s₀, hms⟩ : ∃ m s, z = LocalizedModule.mk m s := by
        induction z using LocalizedModule.induction_on with
        | _ m s => exact ⟨m, s, rfl⟩
      -- each generator, cleared of denominators, lands in `R ∙ m₀`
      have hj : ∀ j : Fin n, ∃ d ∈ S₀, ∃ r : R, d • g j = r • m₀ := by
        intro j
        have h2 := hgen (LocalizedModule.mk (g j) 1)
        obtain ⟨a, t, hat⟩ : ∃ a t, e (LocalizedModule.mk (g j) 1)
            = Localization.mk a t := by
          induction e (LocalizedModule.mk (g j) 1) using Localization.induction_on with
          | _ y => exact ⟨y.1, y.2, rfl⟩
        rw [hat, hms, LocalizedModule.mk_smul_mk] at h2
        obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h2
        -- `u • ((t * s₀) • g j) = u • (1 • (a • m₀))`
        rw [one_smul] at hu
        refine ⟨(u : R) * ((t : R) * (s₀ : R)), ?_, (u : R) * a, ?_⟩
        · exact mul_mem u.2 (mul_mem t.2 s₀.2)
        · calc ((u : R) * ((t : R) * (s₀ : R))) • g j
              = (u : R) • ((t : R) * (s₀ : R)) • g j := (mul_smul _ _ _)
            _ = (u : R) • ((t * s₀ : S₀) : R) • g j := rfl
            _ = (u : R) • (a • m₀) := by
                rw [show ((t * s₀ : S₀) : R) • g j = (t * s₀ : S₀) • g j from rfl,
                  show (u : R) • ((t * s₀ : S₀) • g j) = u • ((t * s₀ : S₀) • g j)
                    from rfl, hu]
                rfl
            _ = ((u : R) * a) • m₀ := (mul_smul _ _ _).symm
      choose d hd r hr using hj
      refine ⟨m₀, d, r, fun i j => ?_, hr⟩
      have := hd j
      rw [hS₀, Submonoid.mem_iInf] at this
      exact this i
  obtain ⟨m₀, d, r, hdq, hdr⟩ := key
  refine ⟨∏ j, d j, fun i => ?_, ?_⟩
  · -- the product avoids each prime
    intro hmem
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hdq i j hj
  · -- freeness after inverting the product
    intro S _ _ hunit
    -- the pure tensors `1 ⊗ₜ x` lie in the span of `1 ⊗ₜ m₀`
    have hgen : ∀ x : N, (1 : S) ⊗ₜ[R] x ∈ Submodule.span S {(1 : S) ⊗ₜ[R] m₀} := by
      intro x
      have hx : x ∈ Submodule.span R (Set.range g) := by rw [hg]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        -- invert the product to reach `1 ⊗ₜ g j`
        have hprod : (∏ l, d l) • g j
            = ((∏ l ∈ Finset.univ.erase j, d l) * r j) • m₀ := by
          rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j), mul_comm,
            mul_smul, hdr j, mul_smul]
        have h1 : algebraMap R S (∏ l, d l) • ((1 : S) ⊗ₜ[R] g j)
            ∈ Submodule.span S {(1 : S) ⊗ₜ[R] m₀} := by
          rw [algebraMap_smul, ← TensorProduct.tmul_smul, hprod,
            TensorProduct.tmul_smul, ← algebraMap_smul (A := S)]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        have h2 := Submodule.smul_mem _ (↑hunit.unit⁻¹ : S) h1
        rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at h2
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul (A := S)]
        exact Submodule.smul_mem _ _ hx
    -- the base change is generated by `1 ⊗ₜ m₀`
    have hspan : Submodule.span S {(1 : S) ⊗ₜ[R] m₀} = ⊤ := by
      rw [eq_top_iff]
      rintro w -
      induction w with
      | zero => exact Submodule.zero_mem _
      | add x y hx hy => exact Submodule.add_mem _ hx hy
      | tmul s x =>
        have hsx : s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hsx]
        exact Submodule.smul_mem _ s (hgen x)
    exact free_of_span_singleton_eq_top (S ⊗[R] N) ((1 : S) ⊗ₜ[R] m₀) hspan

end Module.Invertible

/-! ## The algebraic tube -/

namespace Algebra

/-- **The algebraic tube**: for an integral algebra `S → R`, a prime `p` of `S` and an
element `f : R` avoiding every prime of `R` lying over `p`, some `g ∉ p` maps to a
multiple of `f`.  Going-up applied to the ideal `(f)`: if `(f) ∩ S ≤ p`, a prime of `R`
containing `f` would lie over `p`. -/
theorem exists_notMem_algebraMap_eq_mul {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] [Algebra.IsIntegral S R] (p : Ideal S) [p.IsPrime] {f : R}
    (hf : ∀ Q : Ideal R, Q.IsPrime → Q.comap (algebraMap S R) = p → f ∉ Q) :
    ∃ g : S, g ∉ p ∧ ∃ h : R, algebraMap S R g = f * h := by
  have hnle : ¬ (Ideal.span {f}).comap (algebraMap S R) ≤ p := by
    intro hle
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral p (Ideal.span {f}) hle
    exact hf Q hQprime hQcomap (hQge (Ideal.mem_span_singleton_self f))
  obtain ⟨g, hgmem, hgp⟩ := SetLike.not_le_iff_exists.mp hnle
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hgmem
  exact ⟨g, hgp, h, by rw [← hh, mul_comm]⟩

end Algebra
