/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteGaloisQuotientAffine

/-!
# Γ-stable affine covers from the orbit-in-affine hypothesis (campaign `G2(a)`)

Let `L/K` be a finite Galois extension with group `Γ = Gal(L/K)` and let `X` be a
scheme over `Spec L` with a semilinear `Γ`-action `ρ` (`SemilinearGalAction`).  This
file discharges the gate `HasStableAffineCover` (the EGA II 4.5.4 pattern) from the
orbit-in-affine hypothesis `ρ.OrbitsInAffineOpen`: **every point of `X` has a
`Γ`-stable affine open neighbourhood** (`hasStableAffineCover_of_orbitsInAffineOpen`,
registered as the sanctioned instance).  This is the geometric step `G2(a)` feeding
the quotient gluing `G2(c)`; the deep gate `HasGaloisQuotient` is instance-free only for
a **non-affine** total space — `Picard/GaloisQuotientAffineGeneral.lean` discharges it
globally under `[IsAffine X]`.

## Pinned route (recorded before proving, per the campaign plan)

Fix `x : X` with orbit inside the affine open `U` (the hypothesis; the orbit is
finite because `Γ` is finite for finite-dimensional `L/K`).  Pin the **ambient open**
`W := ⋂_γ (act γ)⁻¹ U` — a `Γ`-stable open (not necessarily affine) containing the
orbit and contained in `U` (the `γ = 1` factor).

1. **Prime avoidance** (`exists_mem_basicOpen_le_of_finite`, then transported into
   the scheme by `IsAffineOpen.fromSpec` bookkeeping in
   `exists_basicOpen_le_of_finite`): there is `s ∈ Γ(X, U)` with
   `orbit ⊆ D(s) ⊆ W`.  The algebraic heart is `Ideal.subset_union_prime`: the
   vanishing ideal of `X \ W` in `Γ(X, U)` is not contained in the union of the
   finitely many primes of the orbit points.
2. **The norm** `N := ∏_γ γ(s)|_W ∈ Γ(X, W)`, where `γ(s) := (act γ).app U s` is the
   section transport `Γ(X, U) → Γ(X, (act γ)⁻¹ U)`.  Then
   `D(N) = ⋂_γ (act γ)⁻¹ D(s)`, by `D(product) = ⋂ D(factor)` and
   `Scheme.preimage_basicOpen`.
3. **Wall bypass (audit)**: `Γ`-stability of `D(N)` is proved at the level of
   *opens*, never of sections: `(act τ)⁻¹ D(N) = ⋂_γ (act τ)⁻¹ (act γ)⁻¹ D(s)
   = ⋂_γ (act (γτ))⁻¹ D(s) = D(N)` by preimage functoriality and reindexing the
   finite intersection along `γ ↦ γτ⁻¹`.  No `γ`-twisted section identities (the
   "norm is `Γ`-invariant" wall named in the gate docstring) are needed; the only
   section transport used is `Scheme.preimage_basicOpen`.  In particular no
   separatedness is assumed anywhere.
4. **Affineness**: `D(N) ⊆ D(s)` (the `γ = 1` factor), so `D(N) = D(N|_{D(s)})`
   is a basic open of the affine `D(s)` (`Scheme.basicOpen_res` +
   `IsAffineOpen.basicOpen`), hence affine.  This is why no affineness of `W` (nor
   of intersections of affines) is ever required.
5. **Membership**: `x ∈ (act γ)⁻¹ D(s)` for every `γ` is exactly the prime-avoidance
   conclusion `orbit ⊆ D(s)`.

## Main results

* `exists_mem_basicOpen_le_of_finite` — finite prime avoidance in `Spec R`: finitely
  many points of an open `W` lie in a basic open contained in `W`.
* `exists_basicOpen_le_of_finite` — the scheme form, for finitely many points of an
  affine open `U` (reusable infrastructure; the one-point case is mathlib's
  `IsAffineOpen.exists_basicOpen_le`).
* `SemilinearGalAction.exists_stable_affineOpen_of_orbitsInAffineOpen` — every point
  has a `Γ`-stable affine open neighbourhood.
* `hasStableAffineCover_of_orbitsInAffineOpen` — the gate `HasStableAffineCover`
  holds under `[FiniteDimensional K L] [IsGalois K L] [ρ.OrbitsInAffineOpen]`
  (instance; this is the sanctioned discharge of this gate and of no other).

Campaign reference: `G2(a)` of `informal/pic-representability-campaign.md`.  Sources:
EGA II 4.5.4 for the refinement pattern; SGA I V.1 and Mumford, *Abelian Varieties*
§7 use the same norm trick for quotients by finite groups.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicJacobian.GaloisDescent

/-! ## Finite-intersection and finite-product bookkeeping -/

/-- Membership in a finite infimum of opens is membership in every member.  (The
infinite `iInf` version is false — `iInf` of opens takes an interior — which is why
the `Γ`-stable hull below is a `Finset.inf`.) -/
lemma mem_finset_inf {α : Type*} [TopologicalSpace α] {ι : Type*} {s : Finset ι}
    {F : ι → Opens α} {x : α} :
    x ∈ s.inf F ↔ ∀ i ∈ s, x ∈ F i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => simp [Opens.mem_inf, ih]

/-- The preimage of a finite infimum of opens under a morphism of schemes is the
finite infimum of the preimages. -/
lemma preimage_finset_inf {X Y : Scheme.{u}} (h : X ⟶ Y) {ι : Type*} (s : Finset ι)
    (F : ι → Y.Opens) :
    h ⁻¹ᵁ s.inf F = s.inf fun i => h ⁻¹ᵁ F i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih => rw [Finset.inf_cons, Finset.inf_cons, h.preimage_inf, ih]

/-- The basic open of a finite product of sections is the finite infimum of the
basic opens of the factors (nonempty index set; the empty product would need the
ambient open on the right). -/
lemma basicOpen_finset_prod {X : Scheme.{u}} {V : X.Opens} {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (g : ι → Γ(X, V)) :
    X.basicOpen (∏ i ∈ s, g i) = s.inf fun i => X.basicOpen (g i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a t ha ht ih => rw [Finset.prod_cons, Scheme.basicOpen_mul, ih, Finset.inf_cons]

/-! ## Finite prime avoidance -/

/-- **Finite prime avoidance in `Spec R`**: finitely many points of an open
`W ⊆ Spec R` lie in a common basic open `D(f) ⊆ W`.  Writing `X \ W = V(I)`, each
point is a prime not containing `I`; by prime avoidance (`Ideal.subset_union_prime`)
`I` is not contained in the union of these primes, and any `f ∈ I` avoiding all of
them works. -/
theorem exists_mem_basicOpen_le_of_finite {R : Type*} [CommRing R]
    (W : Opens (PrimeSpectrum R)) {ι : Type*} [Finite ι]
    (p : ι → PrimeSpectrum R) (hp : ∀ i, p i ∈ W) :
    ∃ f : R, (∀ i, p i ∈ PrimeSpectrum.basicOpen f) ∧ PrimeSpectrum.basicOpen f ≤ W := by
  classical
  obtain ⟨c, hc⟩ := (PrimeSpectrum.isOpen_iff (W : Set (PrimeSpectrum R))).mp W.2
  have hWc : (W : Set (PrimeSpectrum R)) = (PrimeSpectrum.zeroLocus c)ᶜ := by
    rw [← hc, compl_compl]
  cases isEmpty_or_nonempty ι with
  | inl h =>
    refine ⟨0, fun i => (h.false i).elim, ?_⟩
    rw [PrimeSpectrum.basicOpen_zero]
    exact bot_le
  | inr h =>
    cases nonempty_fintype ι
    have hnle : ∀ i, ¬Ideal.span c ≤ (p i).asIdeal := by
      intro i hle
      have hpi : p i ∈ (PrimeSpectrum.zeroLocus c)ᶜ := by
        rw [← hWc]; exact hp i
      exact hpi ((PrimeSpectrum.mem_zeroLocus _ _).mpr (Ideal.span_le.mp hle))
    obtain ⟨f, hfc, hf⟩ : ∃ f ∈ Ideal.span c, ∀ i, f ∉ (p i).asIdeal := by
      by_contra habs
      push Not at habs
      have hsub : (Ideal.span c : Set R) ⊆
          ⋃ i ∈ ((Finset.univ : Finset ι) : Set ι), ((p i).asIdeal : Set R) := by
        intro f hf
        obtain ⟨i, hi⟩ := habs f hf
        exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) hi
      obtain ⟨i, -, hle⟩ := (Ideal.subset_union_prime h.some h.some
        fun i _ _ _ => (p i).isPrime).mp hsub
      exact hnle i hle
    refine ⟨f, fun i => (PrimeSpectrum.mem_basicOpen f (p i)).mpr (hf i), fun q hq => ?_⟩
    have hq' : f ∉ q.asIdeal := (PrimeSpectrum.mem_basicOpen f q).mp hq
    rw [← SetLike.mem_coe, hWc]
    intro hzl
    exact hq' (Ideal.span_le.mpr ((PrimeSpectrum.mem_zeroLocus _ _).mp hzl) hfc)

/-- **Finite prime avoidance in an affine open of a scheme** (reusable
infrastructure; the one-point case is mathlib's `IsAffineOpen.exists_basicOpen_le`):
finitely many points of an open `V` all lying in an affine open `U` lie in a common
basic open `D(s) ⊆ V` of a section `s ∈ Γ(X, U)`.  Proved by transporting
`exists_mem_basicOpen_le_of_finite` along `hU.fromSpec`. -/
theorem exists_basicOpen_le_of_finite {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} {ι : Type*} [Finite ι]
    (y : ι → X) (hyU : ∀ i, y i ∈ U) (hyV : ∀ i, y i ∈ V) :
    ∃ s : Γ(X, U), (∀ i, y i ∈ X.basicOpen s) ∧ X.basicOpen s ≤ V := by
  obtain ⟨s, hmem, hle⟩ := exists_mem_basicOpen_le_of_finite (hU.fromSpec ⁻¹ᵁ V)
    (fun i => hU.primeIdealOf ⟨y i, hyU i⟩)
    (fun i => by
      change hU.fromSpec (hU.primeIdealOf ⟨y i, hyU i⟩) ∈ V
      rw [hU.fromSpec_primeIdealOf]
      exact hyV i)
  refine ⟨s, fun i => ?_, ?_⟩
  · have h := hmem i
    rw [← hU.fromSpec_preimage_basicOpen] at h
    have h2 : hU.fromSpec (hU.primeIdealOf ⟨y i, hyU i⟩) ∈ X.basicOpen s := h
    rwa [hU.fromSpec_primeIdealOf] at h2
  · rw [← hU.fromSpec_image_basicOpen]
    exact (hU.fromSpec.image_mono hle).trans (hU.fromSpec.image_preimage_le V)

/-! ## The Γ-stable affine neighbourhood -/

namespace SemilinearGalAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}

lemma act_one_hom (ρ : SemilinearGalAction K L X f) : (ρ.act 1).hom = 𝟙 X := by
  rw [map_one]; rfl

lemma act_mul_hom (ρ : SemilinearGalAction K L X f) (γ τ : L ≃ₐ[K] L) :
    (ρ.act (γ * τ)).hom = (ρ.act τ).hom ≫ (ρ.act γ).hom := by
  rw [map_mul]; rfl

/-- **The `Γ`-stable affine neighbourhood theorem** (campaign `G2(a)`, EGA II 4.5.4
pattern): under the orbit-in-affine hypothesis, every point of `X` has a `Γ`-stable
affine open neighbourhood — the content of the gate `HasStableAffineCover`.  See the
module docstring for the pinned route (prime avoidance + norm, with `Γ`-stability
proved at the level of opens by reindexing, bypassing the section-transport wall). -/
theorem exists_stable_affineOpen_of_orbitsInAffineOpen [FiniteDimensional K L]
    (ρ : SemilinearGalAction K L X f) [ρ.OrbitsInAffineOpen] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ρ.IsStableOpen U := by
  classical
  obtain ⟨U, hxU⟩ := OrbitsInAffineOpen.exists_affineOpen (ρ := ρ) x
  -- the whole orbit of `x` meets every translated chart:
  -- `act γ (act τ x) = act (γ * τ) x ∈ U`.
  have horb : ∀ τ γ : L ≃ₐ[K] L, (ρ.act γ).hom.base ((ρ.act τ).hom.base x) ∈ U.1 := by
    intro τ γ
    have h : (ρ.act γ).hom.base ((ρ.act τ).hom.base x) = (ρ.act (γ * τ)).hom.base x := by
      rw [ρ.act_mul_hom γ τ]; rfl
    rw [h]; exact hxU (γ * τ)
  -- prime avoidance: `orbit ⊆ D(s) ⊆ W := ⋂_γ (act γ)⁻¹ U`.
  obtain ⟨s, hs_mem, hs_le⟩ := exists_basicOpen_le_of_finite U.2
    (fun γ : L ≃ₐ[K] L => (ρ.act γ).hom.base x) hxU
    (V := Finset.univ.inf fun γ : L ≃ₐ[K] L => (ρ.act γ).hom ⁻¹ᵁ U.1)
    (fun τ => mem_finset_inf.mpr fun γ _ => horb τ γ)
  -- `W ≤ (act γ)⁻¹ U` for every `γ`, so the transported sections restrict to `W`.
  have hWle : ∀ γ : L ≃ₐ[K] L,
      (Finset.univ.inf fun δ : L ≃ₐ[K] L => (ρ.act δ).hom ⁻¹ᵁ U.1) ≤
        (ρ.act γ).hom ⁻¹ᵁ U.1 :=
    fun γ => Finset.inf_le (Finset.mem_univ γ)
  -- the norm `N = ∏_γ γ(s)|_W` and its factors
  set t : (L ≃ₐ[K] L) → Γ(X, Finset.univ.inf fun δ : L ≃ₐ[K] L => (ρ.act δ).hom ⁻¹ᵁ U.1) :=
    fun γ => X.presheaf.map (homOfLE (hWle γ)).op ((ρ.act γ).hom.app U.1 s) with ht
  set N : Γ(X, Finset.univ.inf fun δ : L ≃ₐ[K] L => (ρ.act δ).hom ⁻¹ᵁ U.1) :=
    ∏ γ : L ≃ₐ[K] L, t γ with hN
  -- each factor cuts out the corresponding translate of `D(s)` inside `W`
  have hbo_t : ∀ γ : L ≃ₐ[K] L,
      X.basicOpen (t γ) =
        (Finset.univ.inf fun δ : L ≃ₐ[K] L => (ρ.act δ).hom ⁻¹ᵁ U.1) ⊓
          (ρ.act γ).hom ⁻¹ᵁ X.basicOpen s := by
    intro γ
    rw [ht, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  -- the `γ = 1` translate is `D(s)` itself
  have hP1 : (ρ.act (1 : L ≃ₐ[K] L)).hom ⁻¹ᵁ X.basicOpen s = X.basicOpen s := by
    rw [ρ.act_one_hom]; rfl
  -- `D(N) = ⋂_γ (act γ)⁻¹ D(s)`
  have hbo_N : X.basicOpen N =
      Finset.univ.inf fun γ : L ≃ₐ[K] L => (ρ.act γ).hom ⁻¹ᵁ X.basicOpen s := by
    rw [hN, basicOpen_finset_prod ⟨1, Finset.mem_univ 1⟩,
      Finset.inf_congr rfl fun γ _ => hbo_t γ]
    refine le_antisymm
      (Finset.le_inf fun γ _ => (Finset.inf_le (Finset.mem_univ γ)).trans inf_le_right)
      (Finset.le_inf fun γ _ => le_inf (le_trans ?_ hs_le)
        (Finset.inf_le (Finset.mem_univ γ)))
    exact le_of_le_of_eq (Finset.inf_le (Finset.mem_univ 1)) hP1
  -- `D(N) ⊆ D(s)` (the `γ = 1` factor)
  have hNs : X.basicOpen N ≤ X.basicOpen s := by
    rw [hbo_N]
    exact le_of_le_of_eq (Finset.inf_le (Finset.mem_univ 1)) hP1
  refine ⟨X.basicOpen N, ?_, ?_, ?_⟩
  · -- affineness: `D(N)` is the basic open of `N|_{D(s)}` in the affine `D(s)`
    have heq : X.basicOpen (X.presheaf.map (homOfLE hs_le).op N) = X.basicOpen N := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr hNs
    rw [← heq]
    exact (U.2.basicOpen s).basicOpen _
  · -- membership: prime avoidance put the whole orbit in `D(s)`
    rw [hbo_N, mem_finset_inf]
    intro γ _
    change (ρ.act γ).hom.base x ∈ X.basicOpen s
    exact hs_mem γ
  · -- `Γ`-stability, at the level of opens: preimage functoriality + reindexing
    intro τ
    rw [hbo_N, preimage_finset_inf]
    have hPτ : ∀ γ : L ≃ₐ[K] L,
        (ρ.act τ).hom ⁻¹ᵁ ((ρ.act γ).hom ⁻¹ᵁ X.basicOpen s) =
          (ρ.act (γ * τ)).hom ⁻¹ᵁ X.basicOpen s := by
      intro γ
      rw [ρ.act_mul_hom]; rfl
    rw [Finset.inf_congr rfl fun γ _ => hPτ γ]
    refine le_antisymm (Finset.le_inf fun δ _ => ?_) (Finset.le_inf fun δ _ => ?_)
    · have h := Finset.inf_le (s := Finset.univ)
        (f := fun γ : L ≃ₐ[K] L => (ρ.act (γ * τ)).hom ⁻¹ᵁ X.basicOpen s)
        (Finset.mem_univ (δ * τ⁻¹))
      rwa [inv_mul_cancel_right] at h
    · exact Finset.inf_le (Finset.mem_univ (δ * τ))

end SemilinearGalAction

/-- **Discharge of the gate `HasStableAffineCover`** (campaign `G2(a)`; this is the
sanctioned instance): for finite Galois `L/K`, a semilinear `Γ`-action whose orbits
lie in affine opens admits a `Γ`-stable affine cover.  The Hironaka trap (module
docstring of `FiniteGaloisQuotient`) shows the orbit hypothesis cannot be dropped;
`HasGaloisQuotient` is instance-free only off the affine locus (discharged there by
`Picard/GaloisQuotientAffineGeneral.lean`). -/
instance hasStableAffineCover_of_orbitsInAffineOpen
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) [ρ.OrbitsInAffineOpen] :
    HasStableAffineCover K L ρ :=
  ⟨fun x => ρ.exists_stable_affineOpen_of_orbitsInAffineOpen x⟩

end AlgebraicJacobian.GaloisDescent
