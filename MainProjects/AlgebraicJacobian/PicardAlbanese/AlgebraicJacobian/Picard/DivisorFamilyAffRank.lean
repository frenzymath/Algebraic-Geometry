/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffGlue

/-!
# The rank datum on a straddling cover is a statement about ONE piece

`AffAdaptation.isCertified_of_swallowedBy_of_c1` (`DivisorFamilyAffGlue.lean`) reduces the
seven certificate clauses to (c1) plus the rank datum

  `hrank : ∀ p, Module.rankAtStalk A.Glued p = n`

and the node's own summary calls `hrank` "the honest content of *the divisor has degree n*".
That is right, but as stated it is a hypothesis about the GLUED module over the whole cover,
whereas a degree statement is about the divisor — which on a straddling cover lives entirely
inside the swallowing piece.

This file closes that gap.  On a cover `SwallowedBy d`:

* `Glued ≃ chartProd = ∏_j colength j` (`gluedEquivChartProd_of_swallowedBy`);
* every non-swallowing piece misses the support, so its colength is SUBSINGLETON
  (`subsingleton_colength_of_disjoint_supportLocus`), hence has rank `0` at every prime;
* so the rank of `Glued` is the rank of the single swallowing colength.

Consequently `hrank` need only be supplied at `j₀`, and the input a producer owes shrinks from
a statement about a product over an unknown finite cover to a statement about one affine open —
the one the Stacks `0B8B` datum handed over.

## Main declarations

* `AlgebraicGeometry.AffAdaptation.rankAtStalk_colength_eq_zero_of_disjoint` — a piece missing
  the support contributes nothing.
* `AlgebraicGeometry.AffAdaptation.rankAtStalk_glued_eq_of_swallowedBy` — the rank of the glued
  module IS the rank of the swallowing piece's colength.
* `AlgebraicGeometry.AffAdaptation.isCertified_of_swallowedBy_of_c1_of_rank_piece` — the
  assembler with `hrank` replaced by its one-piece form.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
variable (A : AffAdaptation D d)

/-- **A piece that misses the support contributes rank zero.**  Its colength module is
subsingleton, so its `Module.support` is empty and `rankAtStalk` vanishes at every prime.

The flatness and finiteness instances `rankAtStalk_eq_zero_iff_notMem_support` wants are free
for a subsingleton module: it is free (on the empty basis), hence flat, and finite. -/
lemma rankAtStalk_colength_eq_zero_of_disjoint (j : D.index)
    (hdisj : Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (A.colength j) p = 0 := by
  haveI := A.subsingleton_colength_of_disjoint_supportLocus j
    (fun _ hz hsupp => (Set.disjoint_left.mp hdisj) hsupp hz)
  haveI : Module.Free R (A.colength j) := Module.Free.of_subsingleton R (A.colength j)
  haveI : Module.Flat R (A.colength j) := Module.Flat.of_free
  haveI : Module.Finite R (A.colength j) := Module.Finite.of_finite
  rw [Module.rankAtStalk_eq_zero_iff_notMem_support,
    Module.support_eq_empty (R := R) (M := A.colength j)]
  exact Set.notMem_empty p

/-- **The rank datum on a straddling cover is the rank of the swallowing piece.**

`Glued ≃ ∏_j colength j` because the difference arrow vanishes identically, and
`Module.rankAtStalk_pi` turns the rank of the product into the finsum of the ranks — of which
every term but `j₀` is zero by `rankAtStalk_colength_eq_zero_of_disjoint`.

The (c1) inputs are the ones the assembler already demands, so this costs the consumer
nothing it was not already supplying. -/
theorem rankAtStalk_glued_eq_of_swallowedBy {j₀ : D.index}
    (hsub : d.supportLocus ⊆ (D.pieces j₀ : Set (relCurve C R)))
    (hmiss : ∀ j : D.index, j ≠ j₀ →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (hfin : ∀ j, Module.Finite R (A.colength j))
    (hproj : ∀ j, Module.Projective R (A.colength j))
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) A.Glued p
      = Module.rankAtStalk (R := R) (A.colength j₀) p := by
  classical
  haveI := hfin
  haveI : ∀ j, Module.Flat R (A.colength j) := fun j => by
    haveI := hproj j; exact Module.Flat.of_projective
  -- the glued module is the product of the piece colengths (term-level, to avoid rewriting
  -- under the section-ring instances)
  have hglue : Module.rankAtStalk (R := R) A.Glued p
      = Module.rankAtStalk (R := R) A.chartProd p :=
    congrFun (Module.rankAtStalk_eq_of_equiv
      (A.gluedEquivChartProd_of_swallowedBy ⟨j₀, hsub, hmiss⟩)) p
  -- and the product's rank is the finsum of the component ranks (`chartProd` IS that product)
  have hpi : Module.rankAtStalk (R := R) A.chartProd p
      = ∑ᶠ j : D.index, Module.rankAtStalk (R := R) (A.colength j) p :=
    Module.rankAtStalk_pi (R := R) (fun j : D.index => A.colength j) p
  -- every term but `j₀` vanishes
  have hzero : ∀ j : D.index, j ≠ j₀ → Module.rankAtStalk (R := R) (A.colength j) p = 0 :=
    fun j hj => A.rankAtStalk_colength_eq_zero_of_disjoint j (hmiss j hj) p
  have hsingle : (∑ᶠ j : D.index, Module.rankAtStalk (R := R) (A.colength j) p)
      = Module.rankAtStalk (R := R) (A.colength j₀) p :=
    finsum_eq_single (fun j : D.index => Module.rankAtStalk (R := R) (A.colength j) p) j₀ hzero
  exact hglue.trans (hpi.trans hsingle)

/-- **The assembler with the rank datum read on the swallowing piece.**  Identical to
`isCertified_of_swallowedBy_of_c1` except that the degree input is a statement about the ONE
affine open the `0B8B` datum produced, rather than about the glued module over the whole cover.

This is the form a producer can actually discharge: the divisor lives inside `pieces j₀`, so
"the divisor has degree `n`" is a statement there and nowhere else. -/
theorem isCertified_of_swallowedBy_of_c1_of_rank_piece {n : ℕ} {j₀ : D.index}
    (hsub : d.supportLocus ⊆ (D.pieces j₀ : Set (relCurve C R)))
    (hmiss : ∀ j : D.index, j ≠ j₀ →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (hfin : ∀ j, Module.Finite R (A.colength j))
    (hproj : ∀ j, Module.Projective R (A.colength j))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    A.IsCertified n :=
  A.isCertified_of_swallowedBy_of_c1 ⟨j₀, hsub, hmiss⟩ hfin hproj
    (fun p => (A.rankAtStalk_glued_eq_of_swallowedBy hsub hmiss hfin hproj p).trans (hrank p))

/-- **Non-vacuity of the one-piece rank datum** (trap (c) of the workspace axiom-probe
catalogue, inbox `I-0442`: a theorem whose named hypothesis cannot hold is vacuously true and
reports clean axioms like any other).  At the zero divisor — empty support locus — every piece
misses the support, so its colength vanishes and the datum holds with `n = 0`.

Not a useful instance, but it certifies that `hrank` at `j₀` is satisfiable, so the reduction
above is a reduction rather than a statement about nothing. -/
theorem rankAtStalk_colength_eq_zero_of_supportLocus_empty
    (hempty : d.supportLocus = (∅ : Set (relCurve C R))) (j₀ : D.index)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (A.colength j₀) p = 0 :=
  A.rankAtStalk_colength_eq_zero_of_disjoint j₀
    (by rw [hempty]; exact Set.empty_disjoint _) p

end AffAdaptation

end AlgebraicGeometry
