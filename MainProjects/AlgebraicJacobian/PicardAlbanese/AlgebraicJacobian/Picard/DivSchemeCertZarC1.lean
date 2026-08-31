/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarChartPair

/-!
# Clause (c1) is *equivalent* to leak-freeness

`SupportTubeFinite.lean` proves one direction of the (c1) engine: a closed piece trace makes
the chart-local colength a finite `R`-module.  The converse was assumed throughout the
certificate lane — memory I-0209 states the Z-clopen principle as an "iff", and
`DivSchemeCertZarConn.lean` needs it to upgrade its verdict from "the assembler route is
unavailable" to "the certificate itself is unavailable" — but no declaration proved it.

It follows from the same triangle the forward direction uses, run backwards.  If
`Γ(X, V) ⧸ I` is a finite `R`-module then `Spec (Γ(X, V) ⧸ I) ⟶ Spec R` is a finite morphism,
hence universally closed; that morphism factors through `X`, and `X ⟶ Spec R` is separated, so
the first leg `Spec (Γ(X, V) ⧸ I) ⟶ X` is universally closed too
(`UniversallyClosed.of_comp_of_isSeparated`).  A universally closed morphism is a closed map,
so its range — which `range_specMap_quotient_mk_fromSpec` identifies with the trace — is closed.

Consequences, both recorded here:

* the (c1)-finite clause of `IsCertified` is *equivalent* to leak-freeness at that piece, so
  the necessity results of `DivSchemeCertZarChartTrace.lean` and the verdict of
  `DivSchemeCertZarConn.lean` apply to `IsCertified` itself and not only to the assemblers;
* in particular a **certified** adaptation of a connected divisor forces that divisor inside a
  single pinned chart of `pi`.  `DivFamZar` is therefore blind to connected divisors meeting
  both `pi⁻¹(0)` and `pi⁻¹(∞)` — over any base, after any Zariski shrink, for any adaptation.

## Main declarations

* `AlgebraicGeometry.IsAffineOpen.isClosed_zeroLocus_inter_of_finite_quotient` — the converse
  of the abstract finiteness engine.
* `AlgebraicGeometry.DivisorAdaptation.supportLeak_eq_empty_of_finite_colength` — clause
  (c1)-finite at a piece implies leak-freeness there.
* `AlgebraicGeometry.DivisorAdaptation.supportLeak_eq_empty_iff_finite_colength` — the two are
  equivalent.
* `AlgebraicGeometry.DivisorAdaptation.supportLocus_subset_chart_of_isCertified` — **the
  verdict for `IsCertified`**: a certified adaptation of a connected divisor confines it to one
  pinned chart.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The converse of the abstract finiteness engine -/

namespace IsAffineOpen

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
variable {R : Type u} [CommRing R] [X.Over (Spec (CommRingCat.of R))]

include hV in
/-- **The converse of the abstract (c1) engine.** If the chart-local quotient `Γ(X, V) ⧸ I` is
a finite `R`-module then the closed subscheme it cuts has closed image in `X`.

The forward direction (`finite_quotient_of_isClosed`) turns closedness into finiteness through
`Spec (Γ(X, V) ⧸ I) ⟶ X ⟶ Spec R`; this runs the same triangle backwards.  Finiteness makes
the composite universally closed, separatedness of `X ⟶ Spec R` transfers that to the first
leg, and a universally closed morphism has closed range. -/
theorem isClosed_zeroLocus_inter_of_finite_quotient
    [IsSeparated (X ↘ Spec (CommRingCat.of R))]
    (I : Ideal Γ(X, V)) (h : Module.Finite R (Γ(X, V) ⧸ I)) :
    IsClosed (X.zeroLocus (I : Set Γ(X, V)) ∩ (V : Set X)) := by
  have hfin : IsFinite ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec)
      ≫ (X ↘ Spec (CommRingCat.of R))) := by
    rw [Category.assoc, hV.specMap_quotient_mk_fromSpec_over]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr h)
  haveI : UniversallyClosed (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      ≫ hV.fromSpec) :=
    UniversallyClosed.of_comp_of_isSeparated _ (X ↘ Spec (CommRingCat.of R))
  rw [← hV.range_specMap_quotient_mk_fromSpec I, ← Set.image_univ]
  exact (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    ≫ hV.fromSpec).isClosedMap _ isClosed_univ

end IsAffineOpen

/-! ## Clause (c1) and leak-freeness are the same condition -/

namespace DivisorAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R π d)

/-- **Clause (c1)-finite at a piece implies leak-freeness there** — the direction the lane had
assumed since I-0209 without a proof.  With `finite_colength_of_supportLeak_eq_empty` it makes
the two conditions equivalent. -/
theorem supportLeak_eq_empty_of_finite_colength (j : A.index)
    (h : Module.Finite R (A.colength j)) :
    d.supportLeak (A.pieces j) = ∅ := by
  refine (d.isClosed_supportLocus_inter_iff_supportLeak_eq_empty (A.pieces j)).mp ?_
  have hclosed := IsAffineOpen.isClosed_zeroLocus_inter_of_finite_quotient
    (A.toFinCoverData.isAffineOpen_pieces j) (Ideal.span {A.eqn j}) h
  rw [Scheme.zeroLocus_span] at hclosed
  have hset : (relCurve C R).zeroLocus {A.eqn j} ∩ (A.pieces j : Set (relCurve C R))
      = (A.pieces j : Set (relCurve C R))
        \ ((relCurve C R).basicOpen (A.eqn j) : Set (relCurve C R)) := by
    ext x
    simp only [Set.mem_inter_iff, Scheme.mem_zeroLocus_iff, Set.mem_singleton_iff,
      forall_eq, Set.mem_sdiff, SetLike.mem_coe]
    exact and_comm
  rw [A.supportLocus_inter_pieces j, ← hset]
  exact hclosed

/-- **Leak-freeness and clause (c1)-finite are the same condition at a piece.** -/
theorem supportLeak_eq_empty_iff_finite_colength (j : A.index) :
    d.supportLeak (A.pieces j) = ∅ ↔ Module.Finite R (A.colength j) :=
  ⟨A.finite_colength_of_supportLeak_eq_empty j, A.supportLeak_eq_empty_of_finite_colength j⟩

/-- **The verdict, for `IsCertified` itself.** A certified adaptation of a connected divisor
confines that divisor to a single pinned chart of `pi`.  Together with
`DivSchemeCertZarConn.lean`'s obstruction this says `DivFamZar` cannot see a connected divisor
meeting both `pi⁻¹(0)` and `pi⁻¹(∞)`, over any base and after any Zariski shrink. -/
theorem supportLocus_subset_chart_of_isCertified {n : ℕ}
    (hconn : _root_.IsPreconnected d.supportLocus) (hc : A.IsCertified n) :
    d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₀ : Set (relCurve C R))
      ∨ d.supportLocus ⊆ ((relCover C R (fiberTwoCover π)).V₁ : Set (relCurve C R)) :=
  A.supportLocus_subset_chart_of_isPreconnected hconn
    fun j => A.supportLeak_eq_empty_of_finite_colength j (hc.finite_colength j)

end DivisorAdaptation

end AlgebraicGeometry
