/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon
-/
import AlgebraicJacobian.Picard.PicEtPointedReduction
import AlgebraicJacobian.Picard.ProjectiveMorphism
import AlgebraicJacobian.Picard.CurveProjectivity
import AlgebraicJacobian.Picard.AmbientPicNotProper
import AlgebraicJacobian.Picard.StableAffineCover

/-!
# Quasi-projectivity, as the vocabulary `FiniteInAffine` was standing in for

`Scheme.FiniteInAffine X` (`Picard/PicEtPointedReduction.lean`) says every finite
subset of `X` lies in a single affine open.  It is the elementary, action-free form
of the EGA II 4.5.4 hypothesis that the whole finite-Galois-quotient engine runs
on, and up to now the project carried it **by hand**, with the same sentence
written in three places: *"it holds for quasi-projective `X`, but mathlib has no
quasi-projectivity vocabulary at this pin, so for the curve it must be supplied by
hand"* (`Picard/PicEtPointedReduction.lean`,
`Albanese/StableAffineCoverGroup.lean`, `Picard/FiniteGaloisQuotient.lean`).

This file removes the hand: it derives `FiniteInAffine` from the project's
finite-projective-space notion `Scheme.Hom.IsHQuasiProjective`; projectivity is
the closed-immersion special case.  The chain is

  graded prime avoidance  ⟹  `FiniteInAffine (Proj 𝒜)`
                          ⟹  `FiniteInAffine ℙ(n; S)`   (affine morphism descent)
                          ⟹  `FiniteInAffine X` for `X` H-quasi-projective over `S`.

## The two avoidance inputs

The original deep input is the first step, and it is **absent from mathlib
`v4.31`**: there is no *graded* prime avoidance.  Mathlib has
`Ideal.subset_union_prime_finite` — a homogeneous ideal not contained in the union
of finitely many primes is not contained in any one of them — but the element it
produces is an arbitrary element of the ideal, while
`AlgebraicGeometry.Proj.isAffineOpen_basicOpen` demands `f ∈ 𝒜 m` with `0 < m`.
Getting a **homogeneous** avoiding element of **positive degree** is §1, and it is
where the grading is consumed.

For a closed immersion the final transport is cheap: `IsClosedImmersion →
IsAffineHom`, and `IsAffineOpen.preimage` pulls affine opens back.  An open
immersion needs a second prime-avoidance step: after placing the finite image in
an affine open, `GaloisDescent.exists_basicOpen_le_of_finite` shrinks it to a
basic open lying inside the immersion range.  The standard closed/open
factorization then gives transport along every immersion.

Thus graded avoidance is the new algebraic result in this file.  Open-immersion
transport is the only additional substantive geometric step; its algebra is
delegated to the already-landed finite prime-avoidance theorem.  The remaining
H-quasi-projective and coproduct declarations are factorization and packaging.

## What this does and does not buy

It does **not** discharge the `FiniteInAffine` conjunct of
`Scheme.PointedPicSharpRep`.  That conjunct is about the **Picard scheme**, and
nothing in this project produces an H-quasi-projective witness for the relevant
Picard component.  Kleiman §5 `th:qpp&p` gives quasi-projectivity of `Pic^0`;
formalizing and transporting that source theorem remains open.  What changes is the *kind* of thing
that is open: the antecedent's last non-projection conjunct is now reducible to a
standard geometric hypothesis with a standard proof, rather than an elementary
condition invented here.  Stated as
`Scheme.finiteInAffine_of_isHQuasiProjective` in §3.

It **does** discharge, unconditionally and for free, the orbit hypothesis of the
Galois-descent engine at every projective scheme
(`Scheme.orbitsInAffineOpen_of_isProjective`), which is what
`Picard/GaloisQuotientNonVacuity.lean` had only for *affine* `X` and what the
Albanese lane's `OrbitsInAffineOpen` had for no `X` at all.  Smooth proper
geometrically integral curves **are** projective in this project
(`AlgebraicGeometry.Adelic.isProjective_of_smoothProperGeometricallyIntegral`,
`Picard/CurveProjectivity.lean`), so §3 fires at the curve itself with no
hypothesis beyond its own binders.

## What §5 is NOT: read this before consuming `PointedPicSharpRepProjective`

§5 restates the seam's antecedent with `IsProjective` of the representing scheme in
place of `FiniteInAffine`.  **That antecedent is refuted at the object it is about**,
and the refutation is landed here as a theorem, not left as prose:
`Scheme.not_isProjective_of_infinite_disjoint_open_cover`.  Projectivity over a field
forces `IsProper`, hence `UniversallyClosed`, hence — over the compact `Spec k` —
`CompactSpace` (`Scheme.compactSpace_of_isProjective`); and the full Picard scheme is a
**disjoint union over `deg ∈ ℤ`** (Kleiman §6 `ex:curves`), which is not quasi-compact.
So `PointedPicSharpRepProjective` is not the standard hypothesis restated — it is
strictly stronger and false at `Pic_{C/k}`.

This is verbatim the trap `Picard/AmbientPicNotProper.lean` exists to record, "trap (c):
a `P → Q` whose antecedent is unsatisfiable in the intended setting", and it is caught by
that file's own theorems.  Kleiman's `th:qpp&p` gives quasi-projectivity of `Pic^0`,
not projectivity of the ambient scheme.  §5 therefore survives only as a
*conditional* reduction with an explicitly refuted antecedent; §3 and §4, which do not
mention the ambient Picard scheme, are unaffected.

An earlier revision of this section said §5 states the seam "with no condition invented
in this project anywhere in it".  Both halves were wrong: `Scheme.Hom.IsProjective` is
project-local (`Picard/ProjectiveMorphismBasic.lean`, mathlib `v4.31` has no
morphism-level projectivity at all), as are `PicScheme.picSharp` and
`Scheme.HasRationalPoint`; and the antecedent is not merely non-standard but refutable.
The defensible statement is the narrow one: the *mathematical notion* is standard even
though the Lean definition is ours.

## Non-vacuity

`FiniteInAffine` is satisfiable at an affine scheme with `⊤`
(`Scheme.finiteInAffine_of_isAffine`, already landed) and that witness is
*degenerate*: it says nothing about the projective case.  So the honest
non-degeneracy evidence for §2 is what a fresh-context audit could **verify**, and it
is at `Proj`: `Proj (homogeneousSubmodule (Fin 2) ℚ)` is nonempty (the point
`V(X₀)`), and the hypotheses of `Scheme.exists_homogeneous_pos_mem_notMem` are jointly
satisfiable there, both checked by elaborating them at that named object.

**What is NOT verified, stated because an earlier revision of this paragraph asserted
it as the ground of non-degeneracy:** that `ℙ(n; S)` fails to be affine for `n` with at
least two elements.  It is true, but it is proved nowhere in mathlib at this pin
(no `¬ IsAffine` results at all) nor in this project, so
`Scheme.finiteInAffine_projectiveSpace` being a *non-affine* witness rests on prose.
That earlier revision also claimed the caution "is recorded as
`Scheme.finiteInAffine_projectiveSpace`"; that theorem records no such thing — it has no
`Nonempty` hypothesis and no non-affineness content.
-/

universe u v

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-! ## §1. Graded prime avoidance

The new algebraic input.  The open-immersion theorem in §2 is the other
substantive geometric step, delegating its algebra to `StableAffineCover`.
-/

section GradedAvoidance

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **A finite `inf` of homogeneous ideals is homogeneous.** Bookkeeping for the
avoidance argument, which needs `I ⊓ ⨅_{i ≠ j} p i` to be homogeneous in order to
extract a homogeneous element from it. -/
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

/-- **Graded prime avoidance at a single relevant homogeneous prime.** If a
homogeneous ideal `I` is not contained in a homogeneous prime `p`, and `p` does not
contain the irrelevant ideal, then `I` has a homogeneous element of **strictly
positive** degree outside `p`.

Two separate uses of the grading, and it is worth naming both because the second is
the one an ungraded intuition drops:

* `I` homogeneous and `¬ I ≤ p` gives a homogeneous element of `I` outside `p` —
  decompose a witness and note that if every component were in `p` so would the
  witness be. Its degree is **not controlled** and may be `0`.
* Relevance of `p` (`¬ 𝒜₊ ≤ p`) gives a homogeneous `g ∉ p` of positive degree, by
  the same decomposition applied to a witness in the irrelevant ideal, whose
  degree-`0` component is zero by definition.

Then `f₀ * g` is homogeneous of degree `> 0`, lies in `I` (an ideal) and avoids `p`
(a prime). Relevance is exactly what makes this possible: over a `p` containing
`𝒜₊` — i.e. at a point *not* in `Proj` — every positive-degree homogeneous element
lies in `p` and the conclusion is false. -/
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

/-- **Graded prime avoidance for an incomparable family** — the case with the
construction in it.

Given finitely many pairwise-incomparable relevant homogeneous primes `q ∈ T`, none
containing the homogeneous ideal `I`, there is a **single** homogeneous element of
`I` of **positive** degree outside every one of them.

The classical product/sum trick, with the grading forcing one extra step:

* Incomparability makes `I ⊓ ⨅_{q' ∈ T, q' ≠ q} q'` not contained in `q` — if it
  were, primality would put one of the factors inside `q`. So
  `exists_homogeneous_pos_mem_notMem` supplies, for each `q`, a homogeneous
  `f q ∈ I` of positive degree `m q` that lies in every *other* member of `T` and
  not in `q`.
* Those degrees differ, so their sum need not be homogeneous. Equalise: with
  `M := ∏ m q` each `m q` divides `M`, and `F q := (f q) ^ (M / m q)` is homogeneous
  of the **common** degree `M > 0`, still in `I` and with the same membership
  pattern (a prime contains a power iff it contains the base).
* `∑_{q ∈ T} F q` is then homogeneous of degree `M`, lies in `I`, and modulo any
  `q ∈ T` reduces to `F q ≠ 0 mod q` because every other summand is in `q`.

This is the only place in the file where anything is constructed; §2 onwards is
transport. -/
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
  -- Choose, for each `q ∈ T`, a homogeneous positive-degree element of
  -- `I ⊓ ⨅_{q' ≠ q} q'` outside `q`.
  have key : ∀ q ∈ T, ∃ (m : ℕ) (f : A), 0 < m ∧ f ∈ 𝒜 m ∧
      f ∈ (I ⊓ (T.erase q).inf id) ∧ f ∉ q := by
    intro q hq
    haveI := hp q hq
    refine exists_homogeneous_pos_mem_notMem 𝒜 (I := I ⊓ (T.erase q).inf id) ?_ (hrel q hq) ?_
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
  -- Equalise the degrees: `M := ∏ m q`, and `F q := (f q) ^ (M / m q)` has degree `M`.
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

/-- **Graded prime avoidance, general form** — the incomparability hypothesis of
`exists_homogeneous_pos_mem_forall_notMem_of_antichain` removed.

Any finite family of ideals is dominated by its **maximal** members, and avoiding
those avoids all of them: if `f ∉ q` and `q' ≤ q` then `f ∉ q'`, since `f ∈ q'` would
put `f` in `q`. The maximal members form an antichain by construction, so the
previous theorem applies to them.

Note the direction. It is the *maximal* primes that must be avoided, not the minimal
ones — the inclusion runs the useful way only for a superset. Reducing to minimal
primes, which is the reflex from the ungraded theory, would prove nothing here. -/
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
  -- every member of `T` is one of the `p i`
  have hTmem : ∀ q ∈ T, ∃ i ∈ s, q = p i := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    exact ⟨i, hi, rfl⟩
  -- every `p i` sits below some member of `T`
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

/-- **`Proj 𝒜` satisfies `FiniteInAffine`.** The geometric half of §1, and the first
statement in the chain that is about a scheme.

A point of `Proj 𝒜` *is* a relevant homogeneous prime, and "relevant" is literally the
hypothesis `exists_homogeneous_pos_mem_forall_notMem` needs — the structure field
`ProjectiveSpectrum.not_irrelevant_le` serves simultaneously as the relevance input
and as `¬ I ≤ p x` for `I := 𝒜₊`. So with the irrelevant ideal as `I`, avoidance
returns a homogeneous `f` of positive degree lying outside every one of the finitely
many given points, i.e. `D₊(f)` contains them all; and `D₊(f)` is affine by
`Proj.isAffineOpen_basicOpen`, whose `f ∈ 𝒜 m` and `0 < m` hypotheses are exactly what
§1 was built to deliver.

The degenerate case is handled by the same field: the non-degeneracy input (some
positive-degree homogeneous element exists) is derived from *any* point of `Proj 𝒜`,
and when there is no point the finite set is empty and any affine open serves. This is
the finite generalisation of the argument mathlib runs one point at a time inside
`Proj`'s own `local_affine` field. -/
theorem _root_.AlgebraicGeometry.Scheme.finiteInAffine_proj :
    Scheme.FiniteInAffine (Proj 𝒜) := by
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

/-! ## §2. Descent along affine morphisms and immersions

The affine and closed-immersion cases are transport.  The open-immersion case
uses the independent finite prime-avoidance result from `StableAffineCover`; all
later results are factorization or packaging.
-/

/-- **`FiniteInAffine` descends along any affine morphism.**

The preimage of an affine open under an affine morphism is an affine open
(`IsAffineOpen.preimage`), and a finite set upstairs has a finite image downstairs.
So the property propagates in the direction that is useful for embeddings: from the
ambient space to a subscheme.

This generalises the already-landed `Scheme.finiteInAffine_left_of_isAffineHom`
(`Picard/PicEtPointedReduction.lean`), which is the special case `Y = Spec k`: there
the conclusion came from `X` being outright affine, whereas here `Y` need only satisfy
`FiniteInAffine`; relative projective space supplies the important application.
That is the whole reason this direction is worth having as a separate lemma. -/
theorem finiteInAffine_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (h : FiniteInAffine Y) : FiniteInAffine X := by
  intro s hs
  obtain ⟨U, hU⟩ := h (f.base '' s) (hs.image _)
  exact ⟨⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩, fun x hx => hU ⟨x, hx, rfl⟩⟩

/-- `FiniteInAffine` descends along open immersions.  The ambient affine open
containing the finite image need not lie in the immersion range.  Finite prime
avoidance shrinks it to a basic open that does; its pullback is affine and still
contains the original finite set. -/
theorem finiteInAffine_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hY : FiniteInAffine Y) : FiniteInAffine X := by
  classical
  intro s hs
  obtain ⟨U, hU⟩ := hY (f.base '' s) (hs.image f.base)
  letI : Fintype s := hs.fintype
  obtain ⟨r, hr, hrle⟩ :=
    AlgebraicJacobian.GaloisDescent.exists_basicOpen_le_of_finite U.2
      (fun x : s => f.base x)
      (fun x => hU ⟨x, x.2, rfl⟩)
      (fun x => Scheme.Hom.mem_opensRange.mpr ⟨(x : X), rfl⟩)
  refine ⟨⟨f ⁻¹ᵁ Y.basicOpen r,
    (U.2.basicOpen r).preimage_of_isOpenImmersion f hrle⟩, ?_⟩
  intro x hx
  change f.base x ∈ Y.basicOpen r
  exact hr ⟨x, hx⟩

/-- `FiniteInAffine` descends along arbitrary immersions.  Mathlib factors an
immersion as a closed immersion followed by an open immersion; the closed part
is affine and the open part is handled by finite prime avoidance above. -/
theorem finiteInAffine_of_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] (hY : FiniteInAffine Y) : FiniteInAffine X := by
  obtain ⟨Z, g₁, g₂, hg₁, hg₂, -⟩ :=
    (AlgebraicGeometry.IsImmersion.isImmersion_iff_exists (f := f)).mp
      (inferInstance : IsImmersion f)
  haveI := hg₁
  haveI := hg₂
  exact finiteInAffine_of_isAffineHom g₁
    (finiteInAffine_of_isOpenImmersion g₂ hY)

/-- **Relative projective space over an affine base satisfies `FiniteInAffine`** —
and this is the non-vacuity witness that matters.

`ℙ(n; S)` is by definition the base change of `Proj ℤ[Xᵢ]` along `S ⟶ ⊤_ Scheme`, so
`toProjInt` is a pullback of `terminal.from S`, which is affine exactly when `S` is;
`IsAffineHom` is stable under base change, and §2 then transports
`finiteInAffine_proj`.

Contrast the cheap witness `Scheme.finiteInAffine_of_isAffine`
(`Picard/PicEtPointedReduction.lean`, `⊤` as the affine open). That one is degenerate
— it says nothing about a projective object — and its own docstring says so. This
theorem records the projective-space transport itself; no non-affineness theorem for
`ℙ(n; S)` is available at this mathlib pin, as the module-level non-vacuity note
states. -/
theorem finiteInAffine_projectiveSpace (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    FiniteInAffine (ProjectiveSpace n S) := by
  haveI : IsAffineHom (ProjectiveSpace.toProjInt n S) := by
    rw [ProjectiveSpace.toProjInt_eq_snd]
    exact MorphismProperty.pullback_snd _ _ inferInstance
  exact finiteInAffine_of_isAffineHom (ProjectiveSpace.toProjInt n S)
    (finiteInAffine_proj (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)))

/-! ## §3. The theorem the project was carrying by hand -/

/-- **A scheme projective over an affine base satisfies `FiniteInAffine`.**

This is the statement three files in this project asserted in prose and none proved.
`Scheme.Hom.IsProjective` (`Picard/ProjectiveMorphismBasic.lean`) unfolds to a closed
immersion into `ℙ(n; S)`; a closed immersion is affine (mathlib instance), so §2 pulls
`finiteInAffine_projectiveSpace` back along it.

`FiniteInAffine` is a property of the *underlying scheme*, so the base being affine is
the only hypothesis beyond projectivity — and for the seam the base is `Spec k`, which
is affine. -/
theorem finiteInAffine_of_isProjective {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S}
    (h : π.IsProjective) : FiniteInAffine X := by
  obtain ⟨n, -, i, hi, -⟩ := h
  haveI := hi
  exact finiteInAffine_of_isAffineHom i (finiteInAffine_projectiveSpace n S)

/-- **An H-quasi-projective scheme over an affine base satisfies
`FiniteInAffine`.**  Its quasi-compact immersion witness lands in finite relative
projective space; `FiniteInAffine` descends along the underlying immersion.

The affine-base hypothesis is essential to the projective-space input.  This
does not assert an equivalence with general relative ampleness over arbitrary
bases. -/
theorem finiteInAffine_of_isHQuasiProjective {X S : Scheme.{u}} [IsAffine S]
    {π : X ⟶ S} (h : π.IsHQuasiProjective) : FiniteInAffine X := by
  obtain ⟨n, hn, i, hi, _, -⟩ := h
  letI : Finite n := hn
  haveI : IsImmersion i := hi
  exact finiteInAffine_of_isImmersion i (finiteInAffine_projectiveSpace n S)

/-- The carried relatively very ample form of
`finiteInAffine_of_isHQuasiProjective`. -/
theorem finiteInAffine_of_isHQuasiProjectiveWith {X S : Scheme.{0}} [IsAffine S]
    {π : X ⟶ S} {L : X.Modules} (h : π.IsHQuasiProjectiveWith L) :
    FiniteInAffine X :=
  finiteInAffine_of_isHQuasiProjective h.isHQuasiProjective

/-! ## §4. What it discharges

Two consumers, and the difference between them is the honest measure of this file.
§4.1 closes a gate outright; §4.2 does not, and says which conjunct survives.
-/

/-- **§4.1 — The orbit hypothesis of the Galois-descent engine, at every projective
scheme.** No affineness, no hand-supplied hypothesis.

`SemilinearGalAction.OrbitsInAffineOpen` (`Picard/FiniteGaloisQuotient.lean`) is the
EGA II 4.5.4 input the whole finite-Galois-quotient machine binds. Its producers in
this project were `instOrbitsInAffineOpen_of_isAffine` (affine total space, where the
hypothesis has no room to be false) and a base-change transport
(`Picard/GaloisQuotientNonVacuity.lean`). This adds the case the docstrings kept
pointing at.

Composes with the landed `Scheme.orbitsInAffineOpen_of_finiteInAffine`
(`Picard/PicEtPointedReduction.lean`), which does the orbit-is-finite step. -/
theorem orbitsInAffineOpen_of_isProjective
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction K L X f)
    {S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} (h : π.IsProjective) :
    ρ.OrbitsInAffineOpen :=
  orbitsInAffineOpen_of_finiteInAffine ρ (finiteInAffine_of_isProjective h)

/-- **The orbit hypothesis of the Galois-descent engine for every
H-quasi-projective scheme.**  The finite projective-space immersion in
`IsHQuasiProjective` supplies `FiniteInAffine`, which contains every finite
Galois orbit in an affine open. -/
theorem orbitsInAffineOpen_of_isHQuasiProjective
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction K L X f)
    {S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} (h : π.IsHQuasiProjective) :
    ρ.OrbitsInAffineOpen :=
  orbitsInAffineOpen_of_finiteInAffine ρ (finiteInAffine_of_isHQuasiProjective h)

/-- **§4.2 — The curve itself satisfies `FiniteInAffine`, unconditionally.**

Smooth proper geometrically integral curves are projective in this project
(`AlgebraicGeometry.Adelic.isProjective_of_smoothProperGeometricallyIntegral`,
`Picard/CurveProjectivity.lean`), and `Spec k` is affine, so §3 fires with no
hypothesis beyond the curve's own binders.

**What this does NOT do, since it is the natural over-reading.** It does not discharge
the `FiniteInAffine` conjunct of `Scheme.PointedPicSharpRep`
(`Picard/PicEtPointedReduction.lean`), and it does not touch
`Scheme.fgaPicardRepresentability`. That conjunct is about the scheme representing
`picSharp` — the **Picard** scheme — not about `C`, and nothing in this project
produces the H-quasi-projective `Pic^0` witness corresponding to Kleiman §5
`th:qpp&p`; that formalization is still open.

What has changed is the *kind* of thing that remains. Before, the last non-projection
conjunct of the antecedent was an elementary condition invented here, with no
mathematical statement behind it and no route to one at this mathlib pin. Now it is
implied by projectivity of the representing scheme, which is a standard theorem with a
standard proof, and §3 is the implication. A lane proving `IsProjective` of the Picard
scheme gets the conjunct by `exact`. -/
theorem finiteInAffine_curve {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom] :
    FiniteInAffine C.left :=
  finiteInAffine_of_isProjective
    (AlgebraicGeometry.Adelic.isProjective_of_smoothProperGeometricallyIntegral C)

/-! ## §5. The seam's antecedent, restated in standard vocabulary

`Scheme.PointedPicSharpRep` carries `FiniteInAffine X.left` — the elementary condition
this file exists to explain. With §3 in hand the antecedent can be stated with
**projectivity** of the representing scheme instead.  This is an intentionally
strong conditional restatement, not Kleiman's conclusion: §5 `th:qpp&p` gives
quasi-projectivity of `Pic^0`, while the whole Picard scheme is not projective.
This section carries the over-strong restatement only far enough to expose its
failure below.
-/

/-- **The pointed Picard theorem, with projectivity in place of `FiniteInAffine`.**

Identical to `Scheme.PointedPicSharpRep` except in the last conjunct: it asks that the
representing scheme be **projective over the base**, rather than asking directly
that finite subsets lie in affine opens.  This is stronger than the FGA/Kleiman
conclusion and is refuted at the intended ambient Picard scheme in §5.5.

Every remark in `PointedPicSharpRep`'s docstring about the *shape* still applies — the
uniformity in `K` is what lets §4 of `Picard/PicEtPointedReduction.lean` apply it at a
Galois level, and `IsSeparated` is still absent because it is free. What changes is only
that a lane discharging this owes a theorem someone has written down. -/
def PointedPicSharpRepProjective : Prop :=
  ∀ {K : Type u} [Field K] (E : Over (Spec (CommRingCat.of K))),
    ∀ [SmoothOfRelativeDimension 1 E.hom] [IsProper E.hom] [GeometricallyIntegral E.hom],
      Scheme.HasRationalPoint E →
      ∃ X : Over (Spec (CommRingCat.of K)),
        Nonempty ((PicScheme.picSharp E).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ X.hom.IsProjective

/-- **The projective antecedent implies the elementary one.** Directly by §3, since the
base of the representing object is `Spec K`, which is affine.

So §5's antecedent is at least as strong as §4's; whether it is *strictly* stronger is
not claimed here, and the converse is not proved — `FiniteInAffine` does not obviously
recover a closed immersion into projective space.  The H-quasi-projective
vocabulary now available in this project supplies a useful sufficient condition
without providing this converse.  The only claim here is the displayed implication. -/
theorem pointedPicSharpRep_of_projective (H : PointedPicSharpRepProjective.{u}) :
    PointedPicSharpRep.{u} := by
  intro K _ E _ _ _ hpt
  obtain ⟨X, hrep, hlft, hproj⟩ := H E hpt
  exact ⟨X, hrep, hlft, finiteInAffine_of_isProjective hproj⟩

/-- **The new conjunct is satisfiable** — `Spec k` is projective over itself, via the
finite-to-affine producer (`AlgebraicGeometry.IsFinite.isProjective_of_isAffine`).

Recorded as a declaration rather than asserted, per `I-0838`: replacing a conjunct with
an unsatisfiable one would make §5 vacuously true, and that is the failure mode the
2026-07-29 audit found seventeen times.

**And it is not free**, which is the other half and the one that is easy to skip:
`exact?` fails on `X.hom.IsProjective` for an arbitrary `X : Over (Spec k)` carrying
`[LocallyOfFiniteType X.hom]`, so §5's antecedent is not `PointedPicSharpRep` with an
extra conjunct that instance search discharges. Both measurements were run; neither is
recalled. -/
theorem isProjective_id_spec {k : Type u} [Field k] :
    (Over.mk (𝟙 (Spec (CommRingCat.of k)))).hom.IsProjective := by
  haveI : IsFinite (Over.mk (𝟙 (Spec (CommRingCat.of k)))).hom := by
    change IsFinite (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  exact AlgebraicGeometry.IsFinite.isProjective_of_isAffine _

/-- **The seam, verbatim, from the projective antecedent** — the statement of
`Scheme.fgaPicardRepresentability` character for character.

Composing §5.2 with `Scheme.fgaPicardRepresentability_of_pointedPicSharpRep`
(`Picard/PicEtPointedReduction.lean`). So the project's central `sorry` now follows by
`exact` from *projectivity* of the pointed Picard scheme, uniformly in the base field —
an antecedent whose *mathematical* notion is standard, though every Lean definition in it
(`Scheme.Hom.IsProjective`, `PicScheme.picSharp`, `Scheme.HasRationalPoint`) is
project-local.

**AND ITS ANTECEDENT IS REFUTED AT THE INTENDED OBJECT — read §5.5 before consuming
this.** `PointedPicSharpRepProjective` demands projectivity of the scheme representing
the *whole* of `picSharp`, and §5.5 shows that forces `CompactSpace`, which the
degree-graded Picard scheme is not. So this theorem is a true implication with a false
antecedent: it does not bring the seam closer and must not be reported as doing so. The
usable output of this file is §3 and §4, which never mention the ambient Picard scheme.

An earlier revision of this docstring said the antecedent contains "no condition invented
in this project anywhere in it" and framed §5 as merely renaming the hypothesis. Both
were wrong, and the second was the expensive one: the restatement is not conservative, it
is a strengthening into falsity. Corrected here rather than only in a report. -/
theorem fgaPicardRepresentability_of_projective {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (H : PointedPicSharpRepProjective.{u}) :
    (∃ X : Over (Spec (CommRingCat.of k)),
        Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ IsSeparated X.hom)
      ∧ (Scheme.HasRationalPoint C → IsIso (PicScheme.picEtComparison C)) :=
  fgaPicardRepresentability_of_pointedPicSharpRep C (pointedPicSharpRep_of_projective H)

/-! ## §5.5. §5's antecedent is REFUTED at the object it is about

Landed as theorems rather than left as a caveat, because a caveat is what let the
overclaim through in the first place. A fresh-context audit of §5 found this; both
statements below were reproduced before the correction was accepted.
-/

/-- **Projectivity over a field forces a compact space.**

`IsProjective → IsProper` is `Scheme.Hom.IsProjective.isProper`; mathlib derives
`QuasiCompact` from `UniversallyClosed` at `priority := 900`, and `Spec k` is compact, so
`Scheme.compactSpace_of_universallyClosed` (`Picard/AmbientPicNotProper.lean`) finishes.

That file is where this chain was worked out, for `UniversallyClosed`. The point of
restating it for `IsProjective` is that §5's antecedent asks for the *projectivity*, so the
obstruction has to be visible from the hypothesis §5 actually carries. -/
theorem compactSpace_of_isProjective {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) (h : X.hom.IsProjective) :
    CompactSpace X.left :=
  haveI := h.isProper
  compactSpace_of_universallyClosed X.hom

/-- **A scheme with an infinite disjoint open cover is not projective over a field** —
the refutation of §5's antecedent, at scheme generality and with no Picard vocabulary.

Composes `compactSpace_of_isProjective` with the pure-topology
`not_compactSpace_of_infinite_disjoint_open_cover` (`Picard/AmbientPicNotProper.lean`).

**Why this refutes §5 and not §3 or §4.** The full relative Picard scheme is a disjoint
union of open pieces indexed by `deg ∈ ℤ` — that is the second clause of Kleiman §4
`th:main`(1), and it is what `HasPicScheme` bundles. An infinite family of pairwise
disjoint nonempty opens covering a space has no finite subcover, so `Pic_{C/k}` is not
quasi-compact and hence not projective over `k`. `PointedPicSharpRepProjective` asks for
exactly that projectivity, so it is false at its intended witness.

Kleiman's `th:qpp&p` gives quasi-projectivity of `Pic^0`.  Extending this to other
components requires the appropriate translation/torsor inputs and a degree-graded
carrier, neither of which this file constructs.  A repaired §5 consumes such witnesses
piecewise through the carrier-agnostic infrastructure below.  §3 and §4 are untouched:
neither mentions the ambient Picard scheme, and `finiteInAffine_curve` is about the
curve, which *is* projective. -/
theorem not_isProjective_of_infinite_disjoint_open_cover {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) {ι : Type v} [Infinite ι]
    (U : ι → Set X.left) (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : _root_.Pairwise (Function.onFun Disjoint U))
    (hcov : (Set.univ : Set X.left) ⊆ ⋃ i, U i) :
    ¬ X.hom.IsProjective := fun h =>
  not_compactSpace_of_infinite_disjoint_open_cover U hopen hne hdisj hcov
    (compactSpace_of_isProjective X h)

/-! ## §6. The repair §5 needs: localise to one open piece

§5.5 refutes the *global* projectivity hypothesis.  Kleiman's `th:qpp&p` supplies
quasi-projectivity of `Pic^0`; translation to other components and their degree-graded
assembly are separate inputs.  The reusable repair is therefore not a different global
condition, but a way to consume an H-quasi-projective witness **one piece at a time**.

This section supplies the transport that makes that possible, and stops there. What it
deliberately does **not** do is define a "locally `FiniteInAffine`" predicate of the form
"every finite set that happens to lie in a good open lies in an affine open": that
proposition is **provable outright** from §6.1, with no hypothesis at all, so it would be a
tautology dressed as a weakened hypothesis. Measured before writing this paragraph — the
would-be predicate closed by `exact restrict …` with its own hypothesis unused. It is the
failure mode another lane filed the same day (`I-1660`): an outer quantifier that
re-consumes its own localisation.

The honest remaining gap is therefore stated, not hidden: descent needs to know a Galois
orbit lands in **one** piece, which is degree-invariance of the action, and the
degree-graded decomposition of `PicSchemeEt` is not available in this file. That is real
work, not plumbing.
-/

/-- **`FiniteInAffine` of an open subscheme suffices for finite sets inside it.**

If `U` is an open subscheme satisfying `FiniteInAffine` and the finite set `s` lies in `U`,
then `s` lies in an affine open **of `X`** — push the affine open forward along the open
immersion `U.ι`, which preserves affineness of opens
(`IsAffineOpen.image_of_isOpenImmersion`).

This is what lets H-quasi-projectivity be consumed piecewise: one such piece containing
the whole set is enough, and the ambient scheme need not be projective — which §5.5 shows
it is not. -/
theorem exists_affineOpen_of_subset_finiteInAffine_opens {X : Scheme.{u}} (U : X.Opens)
    (hU : FiniteInAffine U.toScheme) {s : Set X} (hs : s.Finite) (hsub : s ⊆ U.1) :
    ∃ V : X.affineOpens, s ⊆ V.1 := by
  obtain ⟨W, hW⟩ := hU (U.ι.base ⁻¹' s) (hs.preimage U.ι.isOpenEmbedding.injective.injOn)
  refine ⟨⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩, ?_⟩
  intro x hx
  exact ⟨⟨x, hsub hx⟩, hW (by simpa using hx), rfl⟩

/-- **The piecewise form of §3**: a finite set contained in an open subscheme that is
projective over an affine base lies in an affine open of the ambient scheme.

Composing §6.1 with the projective special case of §3.  This stronger adapter
applies when the chosen open piece is projective; the H-quasi-projective form
below is the one intended for the Picard-piece input.

What is still missing to run the descent from here, stated so it is not mistaken for
plumbing: that a Galois orbit lies in a **single** piece, i.e. degree-invariance of the
semilinear action, together with the degree-graded decomposition of `PicSchemeEt`. Neither
is available in this file. -/
theorem exists_affineOpen_of_subset_isProjective_opens {X : Scheme.{u}} (U : X.Opens)
    {S : Scheme.{u}} [IsAffine S] {π : U.toScheme ⟶ S} (hproj : π.IsProjective)
    {s : Set X} (hs : s.Finite) (hsub : s ⊆ U.1) :
    ∃ V : X.affineOpens, s ⊆ V.1 :=
  exists_affineOpen_of_subset_finiteInAffine_opens U
    (finiteInAffine_of_isProjective hproj) hs hsub

/-- The H-quasi-projective form of the piecewise transport: a finite set lying
in one H-quasi-projective open piece over an affine base lies in an affine open
of the ambient scheme.  Unlike the globally projective hypothesis of §5, this
is compatible with an ambient infinite coproduct of quasi-projective pieces. -/
theorem exists_affineOpen_of_subset_isHQuasiProjective_opens {X : Scheme.{u}}
    (U : X.Opens) {S : Scheme.{u}} [IsAffine S] {π : U.toScheme ⟶ S}
    (hqp : π.IsHQuasiProjective) {s : Set X} (hs : s.Finite) (hsub : s ⊆ U.1) :
    ∃ V : X.affineOpens, s ⊆ V.1 :=
  exists_affineOpen_of_subset_finiteInAffine_opens U
    (finiteInAffine_of_isHQuasiProjective hqp) hs hsub

/-! ## §7. `FiniteInAffine` is closed under coproducts — the repair of §5's refutation

`§5.5` shows the antecedent `PointedPicSharpRepProjective` — projectivity of the scheme
representing the *whole* of `picSharp` — is FALSE at its intended object, because
`Pic_{C/k} = ∐_{d ∈ ℤ} Pic^d` is a countable disjoint union and projectivity of it would
force `CompactSpace` (`compactSpace_of_isProjective`), which `Pic_{C/k}` is not
(`not_isProjective_of_infinite_disjoint_open_cover`).  The usable replacement is a
coproduct of components that each carry an H-quasi-projective witness.  Constructing
those component witnesses is a separate producer obligation.

`FiniteInAffine`, unlike `IsProjective` or `CompactSpace`, **is** closed under such
coproducts: a finite set meets only finitely many components, each hit in an affine open,
and finitely many disjoint affine opens have an affine `iSup`
(`IsAffineOpen.biSup_of_disjoint`).  So this section turns the refuted globally-projective
antecedent into a degree-graded substrate — `FiniteInAffine` of the ambient coproduct
follows from H-quasi-projectivity of each supplied component, which is exactly the
geometric adapter a future degree assembly can consume.  This file does not construct
that assembly or any Picard representer.

Everything here is about coproducts of arbitrary schemes and carries **no** hypothesis
about the curve; nothing closes the seam.  It is the substrate the earlier sections said
was missing ("degree-invariance of the semilinear action, together with the degree-graded
decomposition of `PicSchemeEt`" — the second half). -/

section Coproduct

/-- **`FiniteInAffine` is closed under arbitrary set-indexed coproducts.**  If every
component scheme `g i` satisfies `FiniteInAffine`, so does `∐ g`.

A finite `s ⊆ ∐ g` meets only the finitely many components indexed by `idx '' s`; within
each, `s` pulls back along the open immersion `Sigma.ι g i` to a finite set covered by an
affine open `U i`; the images `Sigma.ι g i ''ᵁ U i` are pairwise disjoint
(`disjoint_opensRange_sigmaι`) affine opens (image of an affine open under an open
immersion), so their finite `iSup` is affine (`IsAffineOpen.biSup_of_disjoint`) and
contains `s`.

This is the property `§5.5`'s refutation identified as the one the degree-graded Picard
scheme has and global projectivity does not. -/
theorem finiteInAffine_sigma {σ : Type v} [Small.{u, v} σ] (g : σ → Scheme.{u})
    (h : ∀ i, FiniteInAffine (g i)) : FiniteInAffine (∐ g) := by
  classical
  letI : ∀ i, IsOpenImmersion (Sigma.ι g i) := fun i =>
    Scheme.IsLocallyDirected.instIsOpenImmersionι (Discrete.functor g) { as := i }
  intro s hs
  have hcomp : ∀ x : (∐ g : Scheme.{u}), ∃ i, x ∈ Set.range (Sigma.ι g i).base := by
    intro x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover g).exists_eq x
    exact ⟨i, y, hy⟩
  choose idx hidx using hcomp
  have hpre : ∀ i : σ, ((Sigma.ι g i).base ⁻¹' s).Finite := fun i =>
    hs.preimage ((Sigma.ι g i).isOpenEmbedding.injective).injOn
  choose U hU using fun i => h i _ (hpre i)
  set J : Set σ := idx '' s with hJ
  have hJfin : J.Finite := hs.image idx
  refine ⟨⟨⨆ i ∈ J, (Sigma.ι g i) ''ᵁ (U i).1, ?_⟩, ?_⟩
  · apply IsAffineOpen.biSup_of_disjoint hJfin
    · intro i _
      exact (U i).2.image_of_isOpenImmersion _
    · intro i _ j _ hij
      exact Disjoint.mono (Scheme.Hom.image_le_opensRange _ _)
        (Scheme.Hom.image_le_opensRange _ _) (disjoint_opensRange_sigmaι g i j hij)
  · intro x hx
    obtain ⟨y, hy⟩ := hidx x
    have hyU : y ∈ (U (idx x)).1 := by
      apply hU (idx x)
      simp only [Set.mem_preimage, hy]
      exact hx
    have hmem : x ∈ (Sigma.ι g (idx x)) ''ᵁ (U (idx x)).1 := ⟨y, hyU, hy⟩
    exact (le_iSup₂ (f := fun i _ => (Sigma.ι g i) ''ᵁ (U i).1) (idx x)
      ⟨x, hx, rfl⟩) hmem

/-- A coproduct of schemes that are projective over one affine base satisfies
`FiniteInAffine`. This is the degree-piece bridge: projectivity is checked on
each component, while `FiniteInAffine` is concluded for their possibly infinite
coproduct. -/
theorem finiteInAffine_sigma_of_isProjective
    {σ : Type v} [Small.{u, v} σ] {S : Scheme.{u}} [IsAffine S]
    (X : σ → Over S) (hX : ∀ i, (X i).hom.IsProjective) :
    FiniteInAffine (∐ fun i => (X i).left) :=
  finiteInAffine_sigma _ fun i => finiteInAffine_of_isProjective (hX i)

/-- A coproduct of H-quasi-projective schemes over one affine base satisfies
`FiniteInAffine`, even when the coproduct itself is not quasi-compact. -/
theorem finiteInAffine_sigma_of_isHQuasiProjective
    {σ : Type v} [Small.{u, v} σ] {S : Scheme.{u}} [IsAffine S]
    (X : σ → Over S) (hX : ∀ i, (X i).hom.IsHQuasiProjective) :
    FiniteInAffine (∐ fun i => (X i).left) :=
  finiteInAffine_sigma _ fun i => finiteInAffine_of_isHQuasiProjective (hX i)

/-- The carried very-ample form of `finiteInAffine_sigma_of_isProjective`.
At `Scheme.{0}`, `IsProjectiveWith` records a line bundle together with its
closed immersion into relative projective space; forgetting those certificates
piecewise gives `FiniteInAffine` for the coproduct. -/
theorem finiteInAffine_sigma_of_isProjectiveWith
    {σ : Type v} [Small.{0, v} σ] {S : Scheme.{0}} [IsAffine S]
    (X : σ → Over S) (L : ∀ i, (X i).left.Modules)
    (hX : ∀ i, (X i).hom.IsProjectiveWith (L i)) :
    FiniteInAffine (∐ fun i => (X i).left) :=
  finiteInAffine_sigma_of_isProjective X fun i => (hX i).isProjective

/-- The carried relatively very ample form of
`finiteInAffine_sigma_of_isHQuasiProjective`. -/
theorem finiteInAffine_sigma_of_isHQuasiProjectiveWith
    {σ : Type v} [Small.{0, v} σ] {S : Scheme.{0}} [IsAffine S]
    (X : σ → Over S) (L : ∀ i, (X i).left.Modules)
    (hX : ∀ i, (X i).hom.IsHQuasiProjectiveWith (L i)) :
    FiniteInAffine (∐ fun i => (X i).left) :=
  finiteInAffine_sigma_of_isHQuasiProjective X fun i =>
    (hX i).isHQuasiProjective

/-- A coproduct in `Over S` is locally of finite type when each of its
components is. The proof compares its structure morphism with the descent
morphism from the coproduct of the underlying schemes and uses that
`LocallyOfFiniteType` is Zariski-local at the source. -/
theorem locallyOfFiniteType_sigma
    {σ : Type v} [Small.{u, v} σ] {S : Scheme.{u}}
    (X : σ → Over S) (hX : ∀ i, LocallyOfFiniteType (X i).hom) :
    LocallyOfFiniteType (∐ X).hom := by
  have hhom : (∐ X).hom = (PreservesCoproduct.iso (Over.forget S) X).hom ≫
      Sigma.desc (fun i => (X i).hom) := by
    haveI : HasColimit (Discrete.functor X ⋙ Over.forget S) :=
      hasColimit_of_iso (F := Discrete.functor (fun i => (X i).left))
        (Discrete.natIso (fun i => Iso.refl _))
    refine (PreservesCoproduct.iso (Over.forget S) X).inv_comp_eq.mp ?_
    rw [PreservesCoproduct.inv_hom]
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [ι_comp_sigmaComparison_assoc, Sigma.ι_desc]
    exact Over.w (Sigma.ι X i)
  rw [hhom]
  exact MorphismProperty.comp_mem @LocallyOfFiniteType
    (PreservesCoproduct.iso (Over.forget S) X).hom
    (Sigma.desc fun i => (X i).hom)
    (by infer_instance)
    (IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) hX)

/-- The underlying scheme of the canonical coproduct in `Over S` inherits
`FiniteInAffine` from its components.  This comparison lemma is independent of
projectivity and is the reusable coproduct boundary. -/
theorem finiteInAffine_over_sigma
    {σ : Type v} [Small.{u, v} σ] {S : Scheme.{u}}
    (X : σ → Over S) (hX : ∀ i, FiniteInAffine (X i).left) :
    FiniteInAffine (∐ X).left :=
  finiteInAffine_of_iso (PreservesCoproduct.iso (Over.forget S) X).symm
    (finiteInAffine_sigma _ hX)

/-- The canonical coproduct in `Over S` satisfies `FiniteInAffine` when every
component is projective over the affine base. This is the form used by a
degree-piece representability assembly; `Over.forget S` identifies its
underlying scheme with the coproduct handled by
`finiteInAffine_sigma_of_isProjective`. -/
theorem finiteInAffine_over_sigma_of_isProjective
    {σ : Type v} [Small.{u, v} σ] {S : Scheme.{u}} [IsAffine S]
    (X : σ → Over S) (hX : ∀ i, (X i).hom.IsProjective) :
    FiniteInAffine (∐ X).left :=
  finiteInAffine_over_sigma X fun i => finiteInAffine_of_isProjective (hX i)

/-- The canonical coproduct in `Over S` satisfies `FiniteInAffine` when each
component is H-quasi-projective over the affine base. -/
theorem finiteInAffine_over_sigma_of_isHQuasiProjective
    {σ : Type v} [Small.{u, v} σ] {S : Scheme.{u}} [IsAffine S]
    (X : σ → Over S) (hX : ∀ i, (X i).hom.IsHQuasiProjective) :
    FiniteInAffine (∐ X).left :=
  finiteInAffine_over_sigma X fun i =>
    finiteInAffine_of_isHQuasiProjective (hX i)

/-- Very-ample projective degree pieces supply the two geometric side
conditions required of their canonical coproduct by `PointedPicSharpRep`:
local finite type of its structure morphism and `FiniteInAffine` of its
underlying scheme. No representability hypothesis is introduced here. -/
theorem locallyOfFiniteType_and_finiteInAffine_sigma_of_isProjectiveWith
    {σ : Type v} [Small.{0, v} σ] {S : Scheme.{0}} [IsAffine S]
    (X : σ → Over S) (L : ∀ i, (X i).left.Modules)
    (hX : ∀ i, (X i).hom.IsProjectiveWith (L i)) :
    LocallyOfFiniteType (∐ X).hom ∧ FiniteInAffine (∐ X).left :=
  ⟨locallyOfFiniteType_sigma X fun i => (hX i).locallyOfFiniteType,
    finiteInAffine_over_sigma_of_isProjective X fun i => (hX i).isProjective⟩

/-- H-quasi-projective degree pieces carrying specified relatively very ample
line bundles supply the two geometric side conditions for their canonical
coproduct: local finite type and `FiniteInAffine`.  The theorem deliberately
introduces no representability hypothesis; constructing the Picard degree
pieces remains a separate producer obligation. -/
theorem locallyOfFiniteType_and_finiteInAffine_sigma_of_isHQuasiProjectiveWith
    {σ : Type v} [Small.{0, v} σ] {S : Scheme.{0}} [IsAffine S]
    (X : σ → Over S) (L : ∀ i, (X i).left.Modules)
    (hX : ∀ i, (X i).hom.IsHQuasiProjectiveWith (L i)) :
    LocallyOfFiniteType (∐ X).hom ∧ FiniteInAffine (∐ X).left :=
  ⟨locallyOfFiniteType_sigma X fun i => (hX i).locallyOfFiniteType,
    finiteInAffine_over_sigma X fun i =>
      finiteInAffine_of_isHQuasiProjectiveWith (hX i)⟩

/-- **`FiniteInAffine` is closed under binary coproducts.**  The two-piece case of
`finiteInAffine_sigma`, via `coprodIsoSigma` and the landed
`Scheme.finiteInAffine_of_iso` (`Picard/PicEtPointedReduction.lean`). -/
theorem finiteInAffine_coprod {X Y : Scheme.{u}} (hX : FiniteInAffine X)
    (hY : FiniteInAffine Y) : FiniteInAffine (X ⨿ Y) := by
  refine finiteInAffine_of_iso (coprodIsoSigma X Y).symm ?_
  apply finiteInAffine_sigma
  rintro ⟨i⟩
  cases i
  · simpa using hX
  · simpa using hY

end Coproduct

end AlgebraicGeometry.Scheme
