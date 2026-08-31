/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.FiniteInAffine
import AlgebraicJacobian.Curve.P1
import AlgebraicJacobian.Cohomology.RelativeTwoCover

/-!
# Finite subsets of relative curves lie in affine opens

This file proves `Scheme.FiniteInAffine` for `Proj` by graded prime avoidance. It then
applies the result to the projective line, descends it along a finite map from a curve,
and pulls it back to the relative curve along the affine first projection.

No projectivity vocabulary or change of projective coordinates is needed: the only
geometric input for the curve is an existing finite morphism to `P1`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MvPolynomial

namespace AlgebraicGeometry.Scheme

section GradedAvoidance

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A finite infimum of homogeneous ideals is homogeneous. -/
theorem Ideal.IsHomogeneous.finsetInf {ι : Type*} (s : Finset ι) (p : ι → Ideal A)
    (h : ∀ i ∈ s, (p i).IsHomogeneous 𝒜) : (s.inf p).IsHomogeneous 𝒜 := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.inf_empty]
      exact fun _ _ _ => Submodule.mem_top
  | insert a t _ IH =>
      rw [Finset.inf_insert]
      exact fun i x hx =>
        ⟨h a (Finset.mem_insert_self a t) i hx.1,
          IH (fun j hj => h j (Finset.mem_insert_of_mem hj)) i hx.2⟩

/-- A homogeneous ideal not contained in a relevant homogeneous prime contains a
positive-degree homogeneous element outside that prime. -/
theorem exists_homogeneous_pos_mem_notMem
    {I p : Ideal A} [hp : p.IsPrime] (hI : I.IsHomogeneous 𝒜)
    (hrel : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p) (hIp : ¬ I ≤ p) :
    ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧ f ∈ I ∧ f ∉ p := by
  classical
  obtain ⟨n, f₀, hf₀deg, hf₀I, hf₀p⟩ : ∃ (n : ℕ) (f : A), f ∈ 𝒜 n ∧ f ∈ I ∧ f ∉ p := by
    obtain ⟨x, hxI, hxp⟩ := SetLike.not_le_iff_exists.mp hIp
    by_contra hcon
    push Not at hcon
    exact hxp (by
      rw [← DirectSum.sum_support_decompose 𝒜 x]
      refine Ideal.sum_mem _ fun i _ => ?_
      by_contra h
      exact h (hcon i _ (SetLike.coe_mem _) ((hI.mem_iff).mp hxI i)))
  obtain ⟨m, g, hm, hgdeg, hgp⟩ : ∃ (m : ℕ) (g : A), 0 < m ∧ g ∈ 𝒜 m ∧ g ∉ p := by
    obtain ⟨x, hxirr, hxp⟩ := SetLike.not_le_iff_exists.mp hrel
    by_contra hcon
    push Not at hcon
    exact hxp (by
      rw [← DirectSum.sum_support_decompose 𝒜 x]
      refine Ideal.sum_mem _ fun i _ => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have hz : (DirectSum.decompose 𝒜 x 0 : A) = 0 := by
          have := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 x).mp hxirr
          simpa [GradedRing.proj_apply] using this
        simp [hz]
      · exact hcon i _ hi (SetLike.coe_mem _))
  exact ⟨n + m, f₀ * g, by omega, SetLike.mul_mem_graded hf₀deg hgdeg,
    I.mul_mem_right _ hf₀I, fun h => (hp.mem_or_mem h).elim hf₀p hgp⟩

/-- Graded prime avoidance for a finite antichain of relevant homogeneous primes. -/
theorem exists_homogeneous_pos_mem_forall_notMem_of_antichain
    (T : Finset (Ideal A)) (hp : ∀ q ∈ T, q.IsPrime)
    (hph : ∀ q ∈ T, q.IsHomogeneous 𝒜)
    (hrel : ∀ q ∈ T, ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ q)
    (hanti : ∀ q ∈ T, ∀ q' ∈ T, q ≠ q' → ¬ q ≤ q')
    {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (hIp : ∀ q ∈ T, ¬ I ≤ q)
    (hM : ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧ f ∈ I) :
    ∃ (M : ℕ) (h : A), 0 < M ∧ h ∈ 𝒜 M ∧ h ∈ I ∧ ∀ q ∈ T, h ∉ q := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨m, f, hm, hfd, hfI⟩ := hM
    exact ⟨m, f, hm, hfd, hfI, by simp⟩
  have key : ∀ q ∈ T, ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧
      f ∈ (I ⊓ (T.erase q).inf id) ∧ f ∉ q := by
    intro q hq
    haveI := hp q hq
    refine exists_homogeneous_pos_mem_notMem 𝒜 (I := I ⊓ (T.erase q).inf id) ?_
      (hrel q hq) ?_
    · exact fun i x hx =>
        ⟨hI i hx.1,
          Ideal.IsHomogeneous.finsetInf 𝒜 _ id
            (fun q' hq' => hph q' (Finset.mem_of_mem_erase hq')) i hx.2⟩
    · intro hle
      rcases (hp q hq).inf_le.mp hle with h | h
      · exact hIp q hq h
      · obtain ⟨q', hq', hq'le⟩ := (hp q hq).inf_le'.mp h
        exact hanti q' (Finset.mem_of_mem_erase hq') q hq
          (Finset.ne_of_mem_erase hq') hq'le
  choose! m f hmpos hfdeg hfmem hfout using key
  have hfI : ∀ q ∈ T, f q ∈ I := fun q hq => (hfmem q hq).1
  have hfin : ∀ q ∈ T, ∀ q' ∈ T.erase q, f q ∈ q' := fun q hq q' hq' =>
    Finset.inf_le (f := id) hq' (hfmem q hq).2
  set M : ℕ := ∏ q ∈ T, m q with hMdef
  have hMpos : 0 < M := Finset.prod_pos hmpos
  have hquot : ∀ q ∈ T, 0 < M / m q := fun q hq =>
    Nat.div_pos (Finset.single_le_prod' (fun i hi => hmpos i hi) hq) (hmpos q hq)
  set F : Ideal A → A := fun q => (f q) ^ (M / m q) with hFdef
  have hFdeg : ∀ q ∈ T, F q ∈ 𝒜 M := by
    intro q hq
    have h2 := SetLike.pow_mem_graded (M / m q) (hfdeg q hq)
    rwa [smul_eq_mul, Nat.div_mul_cancel (Finset.dvd_prod_of_mem m hq)] at h2
  have hFI : ∀ q ∈ T, F q ∈ I := fun q hq =>
    Ideal.pow_mem_of_mem I (hfI q hq) _ (hquot q hq)
  have hFin : ∀ q ∈ T, ∀ q' ∈ T.erase q, F q ∈ q' := fun q hq q' hq' =>
    Ideal.pow_mem_of_mem _ (hfin q hq q' hq') _ (hquot q hq)
  have hFout : ∀ q ∈ T, F q ∉ q := fun q hq hmem =>
    hfout q hq ((hp q hq).mem_of_pow_mem _ hmem)
  refine ⟨M, ∑ q ∈ T, F q, hMpos, sum_mem hFdeg,
    Ideal.sum_mem _ fun q hq => hFI q hq, ?_⟩
  intro q hq hmem
  rw [← Finset.add_sum_erase T F hq] at hmem
  have hrest : (∑ q' ∈ T.erase q, F q') ∈ q :=
    Ideal.sum_mem _ fun q' hq' => hFin q' (Finset.mem_of_mem_erase hq') q
      (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hq').symm, hq⟩)
  exact hFout q hq ((Ideal.add_mem_iff_left _ hrest).mp hmem)

/-- Graded prime avoidance for an arbitrary finite family of relevant homogeneous primes. -/
theorem exists_homogeneous_pos_mem_forall_notMem
    {ι : Type*} (s : Finset ι) (p : ι → Ideal A)
    (hp : ∀ i ∈ s, (p i).IsPrime) (hph : ∀ i ∈ s, (p i).IsHomogeneous 𝒜)
    (hrel : ∀ i ∈ s, ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p i)
    {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (hIp : ∀ i ∈ s, ¬ I ≤ p i)
    (hM : ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧ f ∈ I) :
    ∃ (M : ℕ) (f : A), 0 < M ∧ f ∈ 𝒜 M ∧ f ∈ I ∧ ∀ i ∈ s, f ∉ p i := by
  classical
  set S : Finset (Ideal A) := s.image p with hS
  set T : Finset (Ideal A) := S.filter (fun q => Maximal (fun x => x ∈ S) q) with hT
  have hTmem : ∀ q ∈ T, ∃ i ∈ s, q = p i := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    exact ⟨i, hi, rfl⟩
  have hTdom : ∀ i ∈ s, ∃ q ∈ T, p i ≤ q := by
    intro i hi
    obtain ⟨q, hle, hmax⟩ := S.exists_le_maximal (Finset.mem_image_of_mem p hi)
    exact ⟨q, Finset.mem_filter.mpr ⟨hmax.1, hmax⟩, hle⟩
  obtain ⟨M, f, hMpos, hfdeg, hfI, hfout⟩ :=
    exists_homogeneous_pos_mem_forall_notMem_of_antichain 𝒜 T
      (fun q hq => by obtain ⟨i, hi, rfl⟩ := hTmem q hq; exact hp i hi)
      (fun q hq => by obtain ⟨i, hi, rfl⟩ := hTmem q hq; exact hph i hi)
      (fun q hq => by obtain ⟨i, hi, rfl⟩ := hTmem q hq; exact hrel i hi)
      (fun q hq q' hq' hne hle =>
        hne ((Finset.mem_filter.mp hq).2.eq_of_ge (Finset.mem_filter.mp hq').1 hle).symm)
      hI (fun q hq => by obtain ⟨i, hi, rfl⟩ := hTmem q hq; exact hIp i hi) hM
  refine ⟨M, f, hMpos, hfdeg, hfI, fun i hi hmem => ?_⟩
  obtain ⟨q, hq, hle⟩ := hTdom i hi
  exact hfout q hq (hle hmem)

/-- Every finite subset of a projective spectrum lies in one affine basic open. -/
theorem finiteInAffine_proj : FiniteInAffine (Proj 𝒜) := by
  classical
  intro s hs
  lift s to Finset (Proj 𝒜) using hs with t ht
  rcases isEmpty_or_nonempty (Proj 𝒜) with hem | ⟨⟨x₀⟩⟩
  · exact ⟨⟨⊤, isAffineOpen_top _⟩, fun x _ => (hem.false x).elim⟩
  obtain ⟨M, f, hMpos, hfdeg, -, hfout⟩ :=
    exists_homogeneous_pos_mem_forall_notMem 𝒜 t
      (fun x => (x.asHomogeneousIdeal).toIdeal)
      (fun x _ => x.isPrime)
      (fun x _ => x.asHomogeneousIdeal.isHomogeneous)
      (fun x _ => x.not_irrelevant_le)
      (I := (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
      (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous
      (fun x _ => x.not_irrelevant_le)
      (by
        obtain ⟨m, g, hm, hgdeg, -, -⟩ :=
          exists_homogeneous_pos_mem_notMem 𝒜
            (I := (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
            (p := (x₀.asHomogeneousIdeal).toIdeal)
            (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous
            x₀.not_irrelevant_le x₀.not_irrelevant_le
        exact ⟨m, g, hm, hgdeg, HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hm hgdeg⟩)
  exact ⟨⟨Proj.basicOpen 𝒜 f, Proj.isAffineOpen_basicOpen 𝒜 f hfdeg hMpos⟩,
    fun x hx => hfout x (by exact_mod_cast hx)⟩

end GradedAvoidance

/-! ## The projective line, the curve, and its base changes -/

/-- Every finite subset of the projective line lies in one affine open. -/
theorem finiteInAffine_p1 (k : Type u) [Field k] : FiniteInAffine (P1 k) := by
  change FiniteInAffine (Proj (homogeneousSubmodule (Fin 2) k))
  exact finiteInAffine_proj (homogeneousSubmodule (Fin 2) k)

/-- A curve finite over the projective line satisfies `FiniteInAffine`. -/
theorem finiteInAffine_left_of_isFinite_toP1 {k : Type u} [Field k]
    {C : Over (Spec (.of k))} (π : C.left ⟶ P1 k) [IsFinite π] :
    FiniteInAffine C.left :=
  finiteInAffine_of_isAffineHom π (finiteInAffine_p1 k)

/-- The relative curve satisfies `FiniteInAffine`, by descent along its affine first
projection to a curve finite over the projective line. -/
theorem finiteInAffine_relCurve_of_isFinite_toP1 {k : Type u} [Field k]
    (C : Over (Spec (.of k))) (R : Type u) [CommRing R] [Algebra k R]
    (π : C.left ⟶ P1 k) [IsFinite π] : FiniteInAffine (relCurve C R) := by
  change FiniteInAffine (C ⊗ overSpec k R).left
  exact finiteInAffine_of_isAffineHom (fst C (overSpec k R)).left
    (finiteInAffine_left_of_isFinite_toP1 π)

end AlgebraicGeometry.Scheme
