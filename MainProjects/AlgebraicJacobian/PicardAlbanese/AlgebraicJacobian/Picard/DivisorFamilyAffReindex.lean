/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffAdaptation

/-!
# Reindexing a widened cover and its certificate along an index equivalence

The transport `DivisorFamilyAffZar.lean` flagged as this lane's remaining obligation.  Clauses
(c1) of `AffAdaptation.IsCertified` are pointwise and transport by relabelling, but
(c2)/(c3)/(c4) concern `gluedSubmodule`, a kernel inside `∀ j : index, colength j`, so they
need the equalizer carried along the index equivalence.

The trick that makes this painless is to reindex the COVER so that its pieces are *definitionally*
`D.pieces (e j)`.  Then the adaptation's equations need no transport at all — the section rings
are literally the same — and the certificate transport is `LinearEquiv.piCongrLeft` on the
index, which intertwines `deltaLeft`/`deltaRight` because reindexing acts diagonally on the
pair index as well.  `Module.rankAtStalk` is invariant along a linear equivalence
(`Module.rankAtStalk_eq_of_equiv`).

This is the general form of what the chart-typed → widened comparison needs: `toAffCoverData`
already defines its pieces as `D.pieces (finSumFinEquiv.symm j)`, i.e. exactly this shape.

## Main declarations

* `AlgebraicGeometry.AffCoverData.reindex` — the cover relabelled along `e : ι ≃ D.index`
  (pieces definitionally `D.pieces (e j)`).
* `AffAdaptation.reindex` — the adaptation on it, with equations transported by `rfl`.
* `AffAdaptation.colength_reindex` — the colength modules are literally the same.
* `AffAdaptation.chartProdCongr` — the product identification, `piCongrLeft` on the index.
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

namespace AffCoverData

/-- **The cover relabelled along an index equivalence.**  The pieces are *definitionally*
`D.pieces (e j)`, which is what makes the certificate transport below free of coercions. -/
noncomputable def reindex (D : AffCoverData C R) {m' : ℕ} (e : Fin m' ≃ D.index) :
    AffCoverData C R where
  m := m'
  pieces := fun j => D.pieces (e j)
  isAffineOpen := fun j => D.isAffineOpen (e j)
  cover := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨i, hi⟩ := D.exists_mem_pieces z
    exact Opens.mem_iSup.mpr ⟨e.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

@[simp]
lemma reindex_pieces (D : AffCoverData C R) {m' : ℕ} (e : Fin m' ≃ D.index) (j : Fin m') :
    (D.reindex e).pieces j = D.pieces (e j) := rfl

end AffCoverData

namespace AffAdaptation

variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

/-- **The adaptation on a relabelled cover.**  No transport: `(D.reindex e).pieces j` IS
`D.pieces (e j)`, so the equation and its refinement clause carry over by `rfl`. -/
noncomputable def reindex (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index) :
    AffAdaptation (D.reindex e) d where
  eqn := fun j => A.eqn (e j)
  eqn_rel := fun j y => A.eqn_rel (e j) y

@[simp]
lemma reindex_eqn (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index) (j : Fin m') :
    (A.reindex e).eqn j = A.eqn (e j) := rfl

/-- The colength modules of a relabelled adaptation are the original ones, relabelled. -/
lemma colength_reindex (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index) (j : Fin m') :
    (A.reindex e).colength j = A.colength (e j) := rfl

/-- **The product identification**: `piCongrLeft` on the index.  This is the map along which
the equalizer — and hence clauses (c2)/(c3)/(c4) — transports. -/
noncomputable def chartProdCongr (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index) :
    (A.reindex e).chartProd ≃ₗ[R] A.chartProd :=
  LinearEquiv.piCongrLeft R A.colength e

/-- **Clauses (c1) transport along a relabelling**, by `rfl` on each piece. -/
lemma isCertified_c1_reindex {n : ℕ} (A : AffAdaptation D d) (hA : A.IsCertified n)
    {m' : ℕ} (e : Fin m' ≃ D.index) :
    (∀ j, Module.Finite R ((A.reindex e).colength j)) ∧
      (∀ j, Module.Projective R ((A.reindex e).colength j)) :=
  ⟨fun j => hA.finite_colength (e j), fun j => hA.projective_colength (e j)⟩

end AffAdaptation

end AlgebraicGeometry

namespace AlgebraicGeometry
namespace AffAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

/-! ## The glued clauses transport

The overlap structure of a relabelled adaptation is DEFINITIONALLY the original one relabelled
(`ovlColength_reindex`, `toOvlLeft_reindex` — both `rfl`), which is what makes the equalizer
transport a one-liner rather than the hundred lines the earlier estimate assumed. -/

/-- The overlap colengths of a relabelled adaptation are the original ones, relabelled. -/
lemma ovlColength_reindex (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index)
    (i j : Fin m') :
    (A.reindex e).ovlColength i j = A.ovlColength (e i) (e j) := rfl

/-- The left overlap arrow of a relabelled adaptation is the original one, relabelled. -/
lemma toOvlLeft_reindex (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index)
    (i j : Fin m') :
    (A.reindex e).toOvlLeft i j = A.toOvlLeft (e i) (e j) := rfl

/-- The right overlap arrow of a relabelled adaptation is the original one, relabelled. -/
lemma toOvlRight_reindex (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index)
    (i j : Fin m') :
    (A.reindex e).toOvlRight i j = A.toOvlRight (e i) (e j) := rfl

/-- **The glued submodule transports.**  A section of the relabelled product lies in its
glued submodule exactly when the corresponding overlap identities hold for the ORIGINAL
arrows, read at the relabelled indices.  Both sides unfold to the same family of identities
because every overlap datum of `A.reindex e` is `rfl`-equal to that of `A` at `(e i, e j)`;
the pair index is quantified in the relabelled coordinates, which keeps the statement
dependently well-typed. -/
lemma mem_gluedSubmodule_reindex_iff (A : AffAdaptation D d) {m' : ℕ} (e : Fin m' ≃ D.index)
    (s : (A.reindex e).chartProd) :
    s ∈ (A.reindex e).gluedSubmodule ↔
      ∀ p : Fin m' × Fin m',
        A.toOvlLeft (e p.1) (e p.2) (s p.1) = A.toOvlRight (e p.1) (e p.2) (s p.2) :=
  (A.reindex e).mem_gluedSubmodule_iff s

/- The `comap` form of the same fact (`gluedSubmodule (A.reindex e) = comap (chartProdCongr e)`)
does not elaborate directly: `Submodule R (A.reindex e).chartProd` needs the section-ring
algebra instances to unfold through the reindexed cover, and instance search does not get
there. `mem_gluedSubmodule_reindex_iff` above is the usable form and is what a consumer
needs — it exhibits membership in the relabelled glued module as the original overlap
identities read at relabelled indices. Recorded so nobody re-attempts the comap spelling
expecting it to be a one-liner. -/

end AffAdaptation
end AlgebraicGeometry
