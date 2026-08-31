/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffStraddle
import AlgebraicJacobian.Picard.LocalEquationsPrincipalization

/-!
# Widened adaptations from a principal support piece

A widened cover swallowed by a divisor needs no subordination to the original
local-equation cover once its swallowing piece carries a principal equation.  On that
piece the principalization comparison supplies `AffAdaptation.eqn_rel`.  Every other
piece misses the support, so each restricted original equation is a unit and equation
`1` supplies the comparison there.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.LocalEquations

variable {X : Scheme.{u}} (d : X.LocalEquations)

/-- On an open disjoint from the support, the constant equation `1` agrees with every
original equation up to a unit. -/
theorem exists_one_eq_unit_mul_of_disjoint_supportLocus
    {U : X.Opens} (hU : Disjoint d.supportLocus (U : Set X)) (y : X) :
    ∃ u : Γ(X, U ⊓ d.cover.opens y)ˣ,
      (1 : Γ(X, U ⊓ d.cover.opens y)) =
        (u : Γ(X, U ⊓ d.cover.opens y)) * X.resHom inf_le_right (d.eqn y) := by
  have he : IsUnit (X.resHom
      (inf_le_right : U ⊓ d.cover.opens y ≤ d.cover.opens y) (d.eqn y)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    change IsUnit ((X.presheaf.germ (U ⊓ d.cover.opens y) z hz).hom
      ((X.presheaf.map (homOfLE
        (inf_le_right : U ⊓ d.cover.opens y ≤ d.cover.opens y)).op).hom (d.eqn y)))
    rw [TopCat.Presheaf.germ_res_apply]
    by_contra hnu
    exact Set.disjoint_left.mp hU
      ((d.mem_supportLocus_iff_not_isUnit_germ hz.2).mpr hnu) hz.1
  refine ⟨he.unit⁻¹, ?_⟩
  have hinv := Units.inv_mul he.unit
  rw [he.unit_spec] at hinv
  exact hinv.symm

end Scheme.LocalEquations

namespace AffAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

/-- Construct a widened adaptation from one principal piece and support-disjoint
remaining pieces.  The equations are the supplied principal equation at `j0` and `1`
elsewhere. -/
noncomputable def ofPrincipalPiece (j0 : D.index)
    (hmiss : ∀ j : D.index, j ≠ j0 →
      Disjoint d.supportLocus (D.pieces j : Set (relCurve C R)))
    (f : Γ(relCurve C R, D.pieces j0))
    (hf : ∀ y : relCurve C R,
      ∃ u : Γ(relCurve C R, D.pieces j0 ⊓ d.cover.opens y)ˣ,
        (relCurve C R).resHom inf_le_left f =
          (u : Γ(relCurve C R, D.pieces j0 ⊓ d.cover.opens y))
            * (relCurve C R).resHom inf_le_right (d.eqn y)) :
    AffAdaptation D d := by
  classical
  let eqn : ∀ j : D.index, Γ(relCurve C R, D.pieces j) := fun j =>
    dite (j = j0) (fun h => by subst j; exact f) (fun _ => 1)
  refine { eqn := eqn, eqn_rel := fun j y => ?_ }
  by_cases hj : j = j0
  · subst j
    simpa only [eqn, dite_true, Scheme.resHom] using hf y
  · simpa only [eqn, dite_false, hj, map_one, Scheme.resHom] using
      d.exists_one_eq_unit_mul_of_disjoint_supportLocus (hmiss j hj) y

/-- A Picard-trivial affine open containing the support produces a swallowed widened
cover together with an adaptation.  Unlike `exists_affAdaptation_swallowedBy`, this
requires no containment in one member of the original local-equation cover. -/
theorem exists_swallowedBy_of_cechPicMap_ι_eq_one [IsProper C.hom]
    (d : (relCurve C R).LocalEquations) {W : (relCurve C R).Opens}
    (hW : IsAffineOpen W) (hsub : d.supportLocus ⊆ (W : Set (relCurve C R)))
    (hpic : Scheme.CechPic.map W.ι d.picClass = 1) :
    ∃ (D : AffCoverData C R) (_ : AffAdaptation D d), D.SwallowedBy d := by
  obtain ⟨D, j0, hsw, hj0, hmiss⟩ :=
    exists_affCoverData_swallowedBy_with_piece C R d hW hsub
  have hpic' : Scheme.CechPic.map (D.pieces j0).ι d.picClass = 1 := by
    rw [hj0]
    exact hpic
  obtain ⟨f, hf⟩ := d.exists_eqn_unit_mul_of_cechPicMap_ι_eq_one hpic'
  exact ⟨D, AffAdaptation.ofPrincipalPiece j0 hmiss f hf, hsw⟩

end AffAdaptation
end AlgebraicGeometry
