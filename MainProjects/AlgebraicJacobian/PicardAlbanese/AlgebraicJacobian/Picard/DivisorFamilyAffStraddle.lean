/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffSwallow
import AlgebraicJacobian.Picard.DivisorFamilyAffExtraction
import AlgebraicJacobian.Picard.DivisorFamilyAffGlue

/-!
# `SwallowedBy` from the Stacks `0B8B` input ALONE (R2, human decision I-0492)

`AffCoverData.SwallowedBy` (`DivisorFamilyAffSwallow.lean`) is the hypothesis that some piece
contains the whole support locus **and every other piece misses it**.  Stated that way it looks
like two inputs, and `DivisorFamilyAffSwallow.lean`'s `ofSwallowingPiece` assembles a cover from
a straddling affine open `W` plus an arbitrary cover of the rest — leaving `SwallowedBy` itself
still to be supplied.

**The second half is free.**  The support locus is CLOSED (`Scheme.LocalEquations.
isClosed_supportLocus`), so its complement is open; choose the other pieces inside that
complement and they miss the support by construction.  Since affine opens are a basis and the
relative curve is quasi-compact for a proper `C` (`DivisorFamilyAffExtraction.lean`), such a
family exists and is finite.

So the ONLY geometric input `SwallowedBy` needs is the Stacks `0B8B` half:

> `supp D` is finite over `R`, hence lies in a single affine open `W` of `C ×_k Spec R`.

which is exactly what protection I-0492 clause 2 says to USE rather than re-derive.  This file
narrows the obligation to that one statement and discharges everything around it.

## Main declarations

* `AlgebraicGeometry.AffCoverData.swallowedBy_ofSwallowingPiece` — `SwallowedBy` for the explicit
  `ofSwallowingPiece` cover, when the other pieces avoid the support.
* `AlgebraicGeometry.exists_affCoverData_swallowedBy` — from an affine open `W ⊇ supp d`, a
  widened cover with `W` as a piece which `SwallowedBy d`.
* `AlgebraicGeometry.exists_affAdaptation_swallowedBy` — the same **carrying an adaptation**, from
  the *subordinate* form of the input (`W` inside one member of `d.cover`).  `AffAdaptation` needs
  subordination and the bare containment does not give it — see the section comment there.
* `AlgebraicGeometry.exists_isCertified_of_swallowing_affineOpen` — the endpoint: the two named
  geometric inputs plus the rank datum give a widened cover, an adaptation, and **all seven**
  certificate clauses, with no hypothesis on `|P¹(k)|` anywhere in the chain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

namespace AffCoverData

variable {C R}

/-- **`SwallowedBy` for the explicit straddling cover**, given that the other pieces avoid the
support.  This is bookkeeping over `Fin.snoc`: the last piece is `W`, which contains the
support; every other index is a `castSucc`, whose piece is disjoint from it. -/
theorem swallowedBy_ofSwallowingPiece {d : (relCurve C R).LocalEquations}
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W) {m : ℕ}
    {Ws : Fin m → (relCurve C R).Opens} (hWs : ∀ i, IsAffineOpen (Ws i))
    (hcover : W ⊔ (⨆ i, Ws i) = ⊤)
    (hsub : d.supportLocus ⊆ (W : Set (relCurve C R)))
    (hmiss : ∀ i, Disjoint d.supportLocus (Ws i : Set (relCurve C R))) :
    (ofSwallowingPiece W hW Ws hWs hcover).SwallowedBy d := by
  refine ⟨Fin.last m, ?_, ?_⟩
  · change d.supportLocus ⊆ ((Fin.snoc Ws W : Fin (m + 1) → _) (Fin.last m) : Set _)
    rw [Fin.snoc_last]
    exact hsub
  · intro j hj
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    change Disjoint d.supportLocus ((Fin.snoc Ws W : Fin (m + 1) → _) i.castSucc : Set _)
    rw [Fin.snoc_castSucc]
    exact hmiss i

end AffCoverData

/-- **`SwallowedBy` from the Stacks `0B8B` input alone.**  Given an affine open `W` containing
the support locus — the one geometric datum protection I-0492 clause 2 directs the lane to use
rather than re-derive — there IS a widened cover swallowed by `d`.

The rest is free, and the reason is that the support locus is CLOSED: cover the complement
`supportLocusᶜ`, which is open, by affine opens contained in it, so they miss the support by
construction; quasi-compactness (free for proper `C`) makes the family finite.  No fibre
analysis, no support tube, no packet idempotent, and no chart.  The stronger conclusion
retains the inserted support piece so downstream principalization can put its global
equation on that exact member. -/
theorem exists_affCoverData_swallowedBy_with_piece [IsProper C.hom]
    (d : (relCurve C R).LocalEquations) {W : (relCurve C R).Opens}
    (hW : IsAffineOpen W) (hsub : d.supportLocus ⊆ (W : Set (relCurve C R))) :
    ∃ (D : AffCoverData C R) (j0 : D.index),
      D.SwallowedBy d ∧ D.pieces j0 = W ∧
        ∀ j : D.index, j ≠ j0 →
          Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)) := by
  classical
  -- (the cover produced here is swallowed; whether it also carries an ADAPTATION is a
  -- separate question, answered by `exists_affAdaptation_swallowedBy` below)
  -- the complement of the support is open, and contains everything outside `W`
  let U : (relCurve C R).Opens := ⟨d.supportLocusᶜ, d.isClosed_supportLocus.isOpen_compl⟩
  -- an affine open inside `U` around each point of `U`
  have hV : ∀ z : U, ∃ V : (relCurve C R).Opens, IsAffineOpen V ∧ (z : relCurve C R) ∈ V
      ∧ V ≤ U := by
    intro z
    obtain ⟨V, hVmem, hzV, hVle⟩ :=
      Opens.isBasis_iff_nbhd.mp (relCurve C R).isBasis_affineOpens z.2
    exact ⟨V, hVmem, hzV, hVle⟩
  choose V hVaff hzV hVle using hV
  -- `W` together with those affine opens covers the curve: a point is in the support (hence in
  -- `W`) or in `U`
  have hcov : (Set.univ : Set (relCurve C R)) ⊆
      (W : Set (relCurve C R)) ∪ ⋃ z : U, (V z : Set (relCurve C R)) := by
    intro z _
    by_cases hz : z ∈ d.supportLocus
    · exact Or.inl (hsub hz)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
  -- extract a finite subfamily of the `V`s
  have hWU : IsCompact ((W : Set (relCurve C R))ᶜ) :=
    (isClosed_compl_iff.mpr W.isOpen).isCompact
  have hsubU : (W : Set (relCurve C R))ᶜ ⊆ ⋃ z : U, (V z : Set (relCurve C R)) := by
    intro z hz
    rcases hcov (Set.mem_univ z) with h | h
    · exact absurd h hz
    · exact h
  obtain ⟨t, ht⟩ := hWU.elim_finite_subcover
    (fun z : U => (V z : Set (relCurve C R))) (fun z => (V z).isOpen) hsubU
  set e : Fin (Fintype.card {z // z ∈ t}) ≃ {z // z ∈ t} :=
    (Fintype.equivFin {z // z ∈ t}).symm with he
  -- assemble and verify the two clauses, retaining the inserted last piece
  have hcover : W ⊔ (⨆ j, V (e j).1) = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    by_cases hz : z ∈ (W : Set (relCurve C R))
    · exact (Opens.mem_sup ..).mpr (Or.inl hz)
    · obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.mp (ht hz)
      exact (Opens.mem_sup ..).mpr (Or.inr
        (Opens.mem_iSup.mpr ⟨e.symm ⟨s, hs⟩, by rw [Equiv.apply_symm_apply]; exact hzs⟩))
  let D := AffCoverData.ofSwallowingPiece W hW (fun j => V (e j).1)
    (fun j => hVaff (e j).1) hcover
  have hmissV : ∀ j, Disjoint d.supportLocus (V (e j).1 : Set (relCurve C R)) := by
    intro j
    refine Set.disjoint_left.mpr fun z hzsupp hzV => ?_
    exact (hVle (e j).1 hzV) hzsupp
  have hsw : D.SwallowedBy d := by
    exact AffCoverData.swallowedBy_ofSwallowingPiece hW _ _ hsub hmissV
  have hmissD : ∀ j : D.index, j ≠ Fin.last _ →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)) := by
    intro j hj
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    simpa [D, AffCoverData.ofSwallowingPiece] using hmissV i
  refine ⟨D, Fin.last _, hsw, ?_, hmissD⟩
  simp [D, AffCoverData.ofSwallowingPiece]

/-- **`SwallowedBy` from one affine support neighbourhood.** -/
theorem exists_affCoverData_swallowedBy [IsProper C.hom]
    (d : (relCurve C R).LocalEquations) {W : (relCurve C R).Opens}
    (hW : IsAffineOpen W) (hsub : d.supportLocus ⊆ (W : Set (relCurve C R))) :
    ∃ D : AffCoverData C R, D.SwallowedBy d := by
  obtain ⟨D, _, hsw, _, _⟩ :=
    exists_affCoverData_swallowedBy_with_piece C R d hW hsub
  exact ⟨D, hsw⟩

/-! ## A swallowed cover that also carries an adaptation

`exists_affCoverData_swallowedBy` gives a cover, but `AffAdaptation` additionally needs every
piece to be **subordinate** to a member of `d.cover` (that is what `ofAnchors` consumes, and
`eqn_rel` is not derivable without it).  The non-swallowing pieces of the construction above
are already subordinate — they were carved out of a basis, so they can be shrunk into any
member — but the swallowing piece `W` is only known to CONTAIN the support.

So the input has to be the 0B8B statement in its subordinate form:

> `supp D` lies in a single affine open `W` **which is contained in one member of `d.cover`**.

That is not a strengthening of 0B8B in substance — `supp D` finite over `R` sits inside a member
of any pointed cover of a neighbourhood of it — but it IS a strengthening of the Lean hypothesis,
and stating it is better than discovering later that the two producers do not compose. -/

/-- **A swallowed cover carrying an adaptation**, from the subordinate form of the 0B8B input:
the affine open containing the support is required to lie inside one member of `d.cover`.

Both conclusions at once, which is what the assembler
`AffAdaptation.isCertified_of_swallowedBy` needs: a cover swallowed by `d`, and an adaptation of
`d` to it. -/
theorem exists_affAdaptation_swallowedBy [IsProper C.hom]
    (d : (relCurve C R).LocalEquations) {W : (relCurve C R).Opens}
    (hW : IsAffineOpen W) (hsub : d.supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ d.cover.opens z₀) :
    ∃ (D : AffCoverData C R) (_ : AffAdaptation D d), D.SwallowedBy d := by
  classical
  let U : (relCurve C R).Opens := ⟨d.supportLocusᶜ, d.isClosed_supportLocus.isOpen_compl⟩
  -- around each point of `U`, an affine open inside `U` AND inside a member of `d.cover`
  have hV : ∀ z : U, ∃ V : (relCurve C R).Opens, IsAffineOpen V ∧ (z : relCurve C R) ∈ V
      ∧ V ≤ U ⊓ d.cover.opens (z : relCurve C R) := by
    intro z
    obtain ⟨V, hVmem, hzV, hVle⟩ :=
      Opens.isBasis_iff_nbhd.mp (relCurve C R).isBasis_affineOpens
        (show (z : relCurve C R) ∈ U ⊓ d.cover.opens (z : relCurve C R) from
          ⟨z.2, d.cover.mem_opens _⟩)
    exact ⟨V, hVmem, hzV, hVle⟩
  choose V hVaff hzV hVle using hV
  have hcov : (W : Set (relCurve C R))ᶜ ⊆ ⋃ z : U, (V z : Set (relCurve C R)) := by
    intro z hz
    have hzU : z ∈ d.supportLocusᶜ := fun hc => hz (hsub hc)
    exact Set.mem_iUnion.mpr ⟨⟨z, hzU⟩, hzV ⟨z, hzU⟩⟩
  obtain ⟨t, ht⟩ := ((isClosed_compl_iff.mpr W.isOpen).isCompact).elim_finite_subcover
    (fun z : U => (V z : Set (relCurve C R))) (fun z => (V z).isOpen) hcov
  set e : Fin (Fintype.card {z // z ∈ t}) ≃ {z // z ∈ t} :=
    (Fintype.equivFin {z // z ∈ t}).symm with he
  have hcover : W ⊔ (⨆ j, V (e j).1) = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    by_cases hz : z ∈ (W : Set (relCurve C R))
    · exact (Opens.mem_sup ..).mpr (Or.inl hz)
    · obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.mp (ht hz)
      exact (Opens.mem_sup ..).mpr (Or.inr
        (Opens.mem_iSup.mpr ⟨e.symm ⟨s, hs⟩, by rw [Equiv.apply_symm_apply]; exact hzs⟩))
  set D := AffCoverData.ofSwallowingPiece W hW (fun j => V (e j).1)
    (fun j => hVaff (e j).1) hcover with hD
  -- every piece is subordinate: the last to `d.cover.opens z₀`, the others to their own point
  set pt : D.index → relCurve C R :=
    Fin.snoc (fun j => ((e j).1 : relCurve C R)) z₀ with hpt
  have hle : ∀ j : D.index, D.pieces j ≤ d.cover.opens (pt j) := by
    refine Fin.lastCases ?_ ?_
    · change (Fin.snoc (fun j => V (e j).1) W : Fin _ → _) (Fin.last _)
        ≤ d.cover.opens (pt (Fin.last _))
      rw [hpt, Fin.snoc_last, Fin.snoc_last]
      exact hWle
    · intro i
      change (Fin.snoc (fun j => V (e j).1) W : Fin _ → _) i.castSucc
        ≤ d.cover.opens (pt i.castSucc)
      rw [hpt, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact (hVle (e i).1).trans inf_le_right
  refine ⟨D, AffAdaptation.ofAnchors
    (fun j => ((relCurve C R).presheaf.map (homOfLE (hle j)).op).hom (d.eqn (pt j)))
    pt hle (fun _ => 1) (fun _ => by rw [Units.val_one, one_mul]), ?_⟩
  refine AffCoverData.swallowedBy_ofSwallowingPiece hW _ _ hsub fun j => ?_
  refine Set.disjoint_left.mpr fun z hzsupp hzV => ?_
  exact ((hVle (e j).1).trans inf_le_left) hzV hzsupp

/-! ## The endpoint: a CERTIFIED widened family from the two named inputs

This is what the lane is for, and it composes the pieces so that the remaining obligations are
visible in one signature rather than spread over five files. -/

/-- **A certified widened family from the two geometric inputs, and nothing else.**  Given

* the subordinate Stacks `0B8B` input — an affine open `W` containing `supp d` and contained in
  one member of `d.cover` (I-0492 clause 2: USE, do not re-derive);
* `hfib`, fibrewise regularity of the piece equations, which must come from the seed's own degree
  data (I-0492 clause 4(i); `AffAdaptation.eqn_tmul_one_mem_nonZeroDivisors_iff` reads it on the
  fibre curve);
* `hrank`, the constant-fibre-rank datum, which is the honest content of "the divisor has degree
  `n`" and cannot come from anywhere else,

there is a widened cover, an adaptation of `d` to it, and a degree-`n` certificate — **all seven
clauses**.

Everything between those inputs and this conclusion is landed: the swallowed cover and its
adaptation (`exists_affAdaptation_swallowedBy`), (c1)-finiteness from the straddling piece
(`forall_finite_colength_of_swallowedBy`), (c1)-projectivity from `hfib` through the widened
flatness route (`projective_colength_of_forall_tmul_residueField`), and (c2)/(c3)/(c4) from (c1)
plus the rank datum on a straddling cover (`isCertified_of_swallowedBy_of_c1`).

No hypothesis on `|P¹(k)|` appears anywhere in the chain — that is the point of R2. -/
theorem exists_isCertified_of_swallowing_affineOpen [IsProper C.hom] [IsNoetherianRing R]
    {n : ℕ} (d : (relCurve C R).LocalEquations)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : d.supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ d.cover.opens z₀)
    (hfib : ∀ (D : AffCoverData C R) (A : AffAdaptation D d) (j : D.index)
      (p : PrimeSpectrum R),
      (A.eqn j ⊗ₜ[R] (1 : p.asIdeal.ResidueField) :
          Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField) ∈
        nonZeroDivisors (Γ(relCurve C R, D.pieces j) ⊗[R] p.asIdeal.ResidueField))
    (hrank : ∀ (D : AffCoverData C R) (A : AffAdaptation D d) (p : PrimeSpectrum R),
      Module.rankAtStalk A.Glued p = n) :
    ∃ (D : AffCoverData C R) (A : AffAdaptation D d), A.IsCertified n := by
  obtain ⟨D, A, hsw⟩ := exists_affAdaptation_swallowedBy C R d hW hsub z₀ hWle
  haveI hfin : ∀ j, Module.Finite R (A.colength j) :=
    A.forall_finite_colength_of_swallowedBy hsw
  refine ⟨D, A, A.isCertified_of_swallowedBy_of_c1 hsw hfin (fun j => ?_) (hrank D A)⟩
  haveI := hfin j
  exact A.projective_colength_of_forall_tmul_residueField j (hfib D A j)

/-- **Non-vacuity of the swallowing hypotheses** (trap (c) of the workspace axiom-probe
catalogue, inbox `I-0442`: a theorem with a FALSE named hypothesis is vacuously true and reports
clean axioms like any other).  The hypothesis set of `exists_affAdaptation_swallowedBy` is
inhabited: for a system with empty support locus — the zero divisor, `eqn ≡ 1` — the containment
holds for ANY affine open inside a cover member.

This does not make the theorem useful at the zero divisor; it certifies that its hypotheses are
satisfiable, so the theorem is not vacuous. -/
theorem exists_affAdaptation_swallowedBy_of_supportLocus_empty [IsProper C.hom]
    (d : (relCurve C R).LocalEquations) (hempty : d.supportLocus = ∅)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (z₀ : relCurve C R) (hWle : W ≤ d.cover.opens z₀) :
    ∃ (D : AffCoverData C R) (_ : AffAdaptation D d), D.SwallowedBy d :=
  exists_affAdaptation_swallowedBy C R d hW (by rw [hempty]; exact Set.empty_subset _) z₀ hWle

end AlgebraicGeometry
