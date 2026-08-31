/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFibre
import AlgebraicJacobian.Picard.DivisorFamilyAffRank
import AlgebraicJacobian.Picard.DivisorFamilyAffStraddle

/-!
# The R2 endpoint AT A SEED: one geometric input left

`DivisorFamilyAffStraddle.lean` gave the widened endpoint
`exists_isCertified_of_swallowing_affineOpen`, whose three inputs were the Stacks `0B8B` datum,
the fibrewise-regularity datum `hfib` (protection I-0492 obligation 4(i)), and the rank datum
`hrank`.  Two of those three are now discharged rather than assumed:

* `hfib` — by `ThetaGeneratorSeed.affAdaptation_fibre_regular` (`…AffFibre.lean`), from the
  seed's own clause, at every widened cover and every widened adaptation;
* `hrank` — reduced by `…AffRank.lean` from the glued module over an unknown finite cover to
  the colength of the ONE swallowing piece.

This file composes them, so what a producer owes is visible in a single signature.  The point
of doing it here rather than leaving it to the reader is the lesson of run 0070 s0006: a
producer and a consumer can each be correct and still not compose (`AffAdaptation` needs
subordination, which bare containment does not give).  Composition is checked by the elaborator
below, not asserted in prose.

## What is left, and it is ONE statement

`exists_isCertified_of_seed_of_swallowing_affineOpen` takes:

1. the **subordinate Stacks `0B8B` input** — an affine open `W ⊇ supp d` inside one member of
   `d.cover` (I-0492 clause 2: USE, do not re-derive; mathlib has no `0B8B` and this tree
   constructs no curve but `P¹`);
2. the **degree datum at `W`** — the colength of the swallowing piece has constant fibre rank
   `n`.  This is "the divisor has degree `n`", read where the divisor actually is.

and returns a widened cover, an adaptation, and **all seven** certificate clauses.  No
`|P¹(k)|` hypothesis appears anywhere in the chain, which is the whole purpose of R2.

## Main declarations

* `AlgebraicGeometry.exists_isCertified_of_seed_of_swallowing_affineOpen` — the endpoint.
* `AlgebraicGeometry.exists_isCertified_of_seed_of_swallowing_affineOpen_of_rank_glued` — the
  same with the rank datum in its original glued form, for a consumer that already has it.
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
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- **The R2 endpoint at a theta-generator seed, with the rank datum on the swallowing piece.**

The two obligations protection I-0492 clause 4 relocated are now in different states, and the
signature says which is which:

* obligation 4(i), fibrewise-finite support, is **discharged** — it does not appear, because
  `ThetaGeneratorSeed.affAdaptation_fibre_regular` supplies it from the seed;
* the Stacks `0B8B` input is **assumed**, per clause 2, in its subordinate form (`hWle`);
* the degree datum is assumed at the swallowing piece, which is where a degree statement lives.

`hproj` is the (c1)-projectivity the assembler already needed, and it now follows from the
discharged fibrewise datum — so it is derived here too, not assumed. -/
theorem exists_isCertified_of_seed_of_swallowing_affineOpen [IsProper C.hom]
    [IsNoetherianRing R] {n : ℕ} {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    ∃ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD)),
      A.IsCertified n := by
  classical
  obtain ⟨Dc, A, hsw⟩ :=
    exists_affAdaptation_swallowedBy C R (D.localEquations hD) hW hsub z₀ hWle
  obtain ⟨j₀, hj₀sub, hj₀miss⟩ := hsw
  -- (c1)-finiteness from the straddling shape
  haveI hfin : ∀ j, Module.Finite R (A.colength j) :=
    A.forall_finite_colength_of_swallowedBy ⟨j₀, hj₀sub, hj₀miss⟩
  -- (c1)-projectivity from the DISCHARGED fibrewise datum, not from a hypothesis
  have hproj : ∀ j, Module.Projective R (A.colength j) := fun j => by
    haveI := hfin j
    exact A.projective_colength_of_forall_tmul_residueField j
      (fun p => D.affAdaptation_fibre_regular hD Dc A j p)
  exact ⟨Dc, A, A.isCertified_of_swallowedBy_of_c1_of_rank_piece hj₀sub hj₀miss hfin hproj
    (hrank Dc A j₀ hj₀sub hj₀miss)⟩

/-- **The same endpoint with the rank datum in its glued form**, for a consumer that already
has `hrank` about `Glued` (e.g. one carrying it through a base change, where
`rankAtStalk_glued_pullback` is stated on the glued module).

Kept as a separate statement rather than as the primary one: the glued form quantifies over a
cover the producer does not choose, and the one-piece form is what the geometry supplies. -/
theorem exists_isCertified_of_seed_of_swallowing_affineOpen_of_rank_glued [IsProper C.hom]
    [IsNoetherianRing R] {n : ℕ} {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (p : PrimeSpectrum R), Module.rankAtStalk (R := R) A.Glued p = n) :
    ∃ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD)),
      A.IsCertified n :=
  exists_isCertified_of_swallowing_affineOpen C R (D.localEquations hD) hW hsub z₀ hWle
    (fun Dc A j p => D.affAdaptation_fibre_regular hD Dc A j p) hrank

/-! ## Non-vacuity of the endpoint

Trap (c) of the workspace axiom-probe catalogue (`I-0442`): a theorem whose hypotheses cannot
be jointly satisfied is vacuously true and reports clean axioms like any other.  The endpoint
above has five hypotheses, and a clean `#print axioms` says nothing about whether they can hold
together.  So the joint inhabitation is exhibited rather than assumed. -/

/-- **The endpoint's hypothesis set is jointly inhabited**, at the zero divisor with `n = 0`:
the support locus is empty, so the `0B8B` containment holds for ANY affine open inside a cover
member, and every colength vanishes so the degree datum holds at `n = 0`.

This does not make the endpoint useful at the zero divisor — it certifies that the five
hypotheses are simultaneously satisfiable, so the theorem is not about nothing.

**The exact strength of this witness, stated so nobody over-reads it.**  It inhabits the
hypothesis set at `n = 0`, i.e. at the DEGENERATE value of the index.  That rules out the
failure mode where the hypotheses contradict each other outright, and it does not rule out the
weaker-but-real possibility that they are satisfiable *only* at `n = 0`.  What is known about
`n > 0`: the endpoint fires whenever the degree datum is supplied at that `n` — nothing in the
hypothesis set forces `n = 0`, checked by elaborating the general instantiation — but supplying
that datum from geometry at a specific `n > 0` is the seed layer's business, not this file's.
So read this as "not self-contradictory", not as "non-trivially inhabited". Cf. inbox `I-0596`,
which records a sibling lane shipping a trivial-witness refutation that did not rule out
vacuity where it mattered. -/
theorem exists_isCertified_of_seed_of_supportLocus_empty [IsProper C.hom] [IsNoetherianRing R]
    {D : ThetaGeneratorSeed C R pi a K} (hD : D.IsGenerator)
    (hempty : (D.localEquations hD).supportLocus = (∅ : Set (relCurve C R)))
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀) :
    ∃ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD)),
      A.IsCertified 0 :=
  exists_isCertified_of_seed_of_swallowing_affineOpen C R hD hW
    (by rw [hempty]; exact Set.empty_subset _) z₀ hWle
    (fun _ A _ _ _ p => A.rankAtStalk_colength_eq_zero_of_supportLocus_empty hempty _ p)

end AlgebraicGeometry
