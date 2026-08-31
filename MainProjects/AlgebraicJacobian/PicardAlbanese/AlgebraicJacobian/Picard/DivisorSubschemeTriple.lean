/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaTripleBaseChange

/-!
# Triple intersections in the intrinsic divisor subscheme

The coordinate ring of the intrinsic divisor over a triple intersection is the
`tripleColength` used by theta descent.  This file identifies the geometric restriction
maps from the first pair and the third piece with `ovlToTriple` and
`pieceToTripleThird`.  These are the naturality inputs for the tensor-pushout comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

/-- The inverse image in the divisor subscheme of any affine ambient open is affine. -/
theorem isAffineOpen_divisorPreimageAffine [IsProper C.hom]
    (A : AffAdaptation D d) (U : (relCurve C R).affineOpens) :
    IsAffineOpen (A.divisorSubschemeι ⁻¹ᵁ (U : (relCurve C R).Opens)) := by
  rw [← A.cartierIdeal.opensRange_subschemeCover_map U]
  exact isAffineOpen_opensRange _

/-- Sections of the intrinsic divisor on a triple intersection are the triple colength
algebra. -/
noncomputable def divisorSubschemeTripleIso [IsProper C.hom]
    (A : AffAdaptation D d) (i j l : D.index) :
    Γ(A.divisorSubscheme,
      A.divisorSubschemeι ⁻¹ᵁ A.thetaTripleOpen i j l) ≅
      CommRingCat.of (A.tripleColength i j l) :=
  A.cartierIdeal.subschemeObjIso (A.thetaTripleAffineOpen i j l)

/-- The triple section identification carries the ambient quotient map to reduction
modulo the intrinsic triple ideal. -/
lemma divisorSubschemeι_app_tripleIso [IsProper C.hom]
    (A : AffAdaptation D d) (i j l : D.index) :
    A.divisorSubschemeι.app (A.thetaTripleOpen i j l) ≫
      (A.divisorSubschemeTripleIso i j l).hom =
    CommRingCat.ofHom (Ideal.Quotient.mk (A.thetaTripleIdeal i j l)) := by
  change A.cartierIdeal.subschemeι.app
      ((A.thetaTripleAffineOpen i j l : (relCurve C R).affineOpens) :
        (relCurve C R).Opens) ≫
      (A.cartierIdeal.subschemeObjIso (A.thetaTripleAffineOpen i j l)).hom = _
  rw [A.cartierIdeal.subschemeι_app (A.thetaTripleAffineOpen i j l)]
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [Category.comp_id]

/-- The triple intersection lies in its third piece. -/
theorem thetaTripleOpen_le_third (A : AffAdaptation D d) (i j l : D.index) :
    A.thetaTripleOpen i j l ≤ D.pieces l :=
  inf_le_right

/-- Restrict the third piece directly to the triple intersection, via the existing
right-pair restriction followed by pair-to-triple restriction. -/
noncomputable def pieceToTripleThird [IsProper C.hom]
    (A : AffAdaptation D d) (i j l : D.index) :
    A.colength l →ₐ[R] A.tripleColength i j l :=
  (A.ovlToTriple j l i j l (A.thetaTripleOpen_le_pair23 i j l)).comp
    (A.toOvlRight j l)

@[simp]
theorem pieceToTripleThird_mk [IsProper C.hom]
    (A : AffAdaptation D d) (i j l : D.index)
    (s : Γ(relCurve C R, D.pieces l)) :
    A.pieceToTripleThird i j l
        (Ideal.Quotient.mk (Ideal.span {A.eqn l}) s) =
      Ideal.Quotient.mk (A.thetaTripleIdeal i j l)
        (relResAlgHom C R (A.thetaTripleOpen_le_third i j l) s) := by
  rw [pieceToTripleThird, AlgHom.comp_apply, A.toOvlRight_mk,
    A.ovlToTriple_mk]
  congr 1
  exact Scheme.resHom_resHom _ _ s

/-- Restriction from the first pairwise divisor intersection is `ovlToTriple`. -/
lemma divisorSubschemeOverlapIso_res_triple12 [IsProper C.hom]
    (A : AffAdaptation D d) (i j l : D.index) :
    A.divisorSubscheme.presheaf.map
        (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ A.thetaTripleOpen i j l ≤
          A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) by
            intro x hx
            exact hx.1)).op ≫
      (A.divisorSubschemeTripleIso i j l).hom =
    (A.divisorSubschemeOverlapIso i j).hom ≫
      CommRingCat.ofHom
        (A.ovlToTriple i j i j l (A.thetaTripleOpen_le_pair12 i j l)).toRingHom := by
  letI : Epi (A.divisorSubschemeι.app (D.pieces i ⊓ D.pieces j)) :=
    ConcreteCategory.epi_of_surjective _
      (A.cartierIdeal.subschemeι_app_surjective
        ⟨D.pieces i ⊓ D.pieces j, D.hasAffineOverlaps_of_isProper i j⟩)
  rw [← cancel_epi (A.divisorSubschemeι.app (D.pieces i ⊓ D.pieces j))]
  rw [← Category.assoc, ← Category.assoc]
  have hr :
      A.divisorSubscheme.presheaf.map
          (((Opens.map A.divisorSubschemeι.base).map
            (homOfLE (A.thetaTripleOpen_le_pair12 i j l)).op.unop).op) =
        A.divisorSubscheme.presheaf.map
          (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ A.thetaTripleOpen i j l ≤
            A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) by
              intro x hx
              exact hx.1)).op := by
    congr 1
  rw [← hr]
  rw [← A.divisorSubschemeι.naturality
    (homOfLE (A.thetaTripleOpen_le_pair12 i j l)).op]
  rw [Category.assoc, A.divisorSubschemeι_app_tripleIso i j l]
  rw [A.divisorSubschemeι_app_overlapIso i j]
  apply ConcreteCategory.hom_ext
  intro s
  exact (A.ovlToTriple_mk i j i j l
    (A.thetaTripleOpen_le_pair12 i j l) s).symm

/-- Restriction from the third divisor piece is `pieceToTripleThird`. -/
lemma divisorSubschemePieceIso_res_tripleThird [IsProper C.hom]
    (A : AffAdaptation D d) (i j l : D.index) :
    A.divisorSubscheme.presheaf.map
        (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ A.thetaTripleOpen i j l ≤
          A.divisorSubschemeι ⁻¹ᵁ D.pieces l by
            intro x hx
            exact hx.2)).op ≫
      (A.divisorSubschemeTripleIso i j l).hom =
    (A.divisorSubschemePieceIso l).hom ≫
      CommRingCat.ofHom (A.pieceToTripleThird i j l).toRingHom := by
  letI : Epi (A.divisorSubschemeι.app (D.pieces l)) :=
    ConcreteCategory.epi_of_surjective _
      (A.cartierIdeal.subschemeι_app_surjective ⟨D.pieces l, D.isAffineOpen l⟩)
  rw [← cancel_epi (A.divisorSubschemeι.app (D.pieces l))]
  rw [← Category.assoc, ← Category.assoc]
  have hr :
      A.divisorSubscheme.presheaf.map
          (((Opens.map A.divisorSubschemeι.base).map
            (homOfLE (A.thetaTripleOpen_le_third i j l)).op.unop).op) =
        A.divisorSubscheme.presheaf.map
          (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ A.thetaTripleOpen i j l ≤
            A.divisorSubschemeι ⁻¹ᵁ D.pieces l by
              intro x hx
              exact hx.2)).op := by
    congr 1
  rw [← hr]
  rw [← A.divisorSubschemeι.naturality
    (homOfLE (A.thetaTripleOpen_le_third i j l)).op]
  rw [Category.assoc, A.divisorSubschemeι_app_tripleIso i j l]
  rw [A.divisorSubschemeι_app_pieceIso l]
  apply ConcreteCategory.hom_ext
  intro s
  exact (A.pieceToTripleThird_mk i j l s).symm

end AffAdaptation

end AlgebraicGeometry
