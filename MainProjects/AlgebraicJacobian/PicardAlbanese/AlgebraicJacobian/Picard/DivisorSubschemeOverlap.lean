/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorSubschemeFinite

/-!
# Overlaps in the intrinsic divisor subscheme

The coordinate ring of the intrinsic divisor over a pairwise intersection is the existing
`AffAdaptation.ovlColength`.  Under this identification, restriction from either divisor
piece is exactly the corresponding equalizer arrow `toOvlLeft` or `toOvlRight`.

These comparisons connect the geometric affine cover of the divisor to the pre-existing
Čech algebra and theta descent datum, without changing their carrier or hypotheses.
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

/-- On an adapted overlap, the intrinsic Cartier ideal is the symmetric overlap ideal
already used by the widened equalizer. -/
theorem cartierIdeal_ideal_overlap_eq_ovlIdeal [IsProper C.hom]
    (A : AffAdaptation D d) (i j : D.index) :
    A.cartierIdeal.ideal
        ⟨D.pieces i ⊓ D.pieces j,
          Over.isAffineOpen_inf C (D.isAffineOpen i) (D.isAffineOpen j)⟩ =
      A.ovlIdeal i j := by
  let U : (relCurve C R).affineOpens :=
    ⟨D.pieces i ⊓ D.pieces j,
      Over.isAffineOpen_inf C (D.isAffineOpen i) (D.isAffineOpen j)⟩
  let V : (relCurve C R).affineOpens := ⟨D.pieces i, D.isAffineOpen i⟩
  have hUV : U ≤ V := by
    intro x hx
    exact hx.1
  change A.cartierIdeal.ideal U = A.ovlIdeal i j
  calc
    A.cartierIdeal.ideal U =
      (A.cartierIdeal.ideal V).map
        ((relCurve C R).presheaf.map
          (homOfLE (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).op).hom :=
        (A.cartierIdeal.map_ideal hUV).symm
    _ = Ideal.span {relResAlgHom C R
          (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i) (A.eqn i)} := by
      rw [A.cartierIdeal_ideal_eq_span_eqn i, Ideal.map_span, Set.image_singleton]
      rfl
    _ = A.ovlIdeal i j := (A.ovlIdeal_eq_span_left i j).symm

/-- Sections of the divisor over a pairwise overlap are the symmetric overlap colength
algebra used in `AffAdaptation.gluedSubalgebra`. -/
noncomputable def divisorSubschemeOverlapIso [IsProper C.hom]
    (A : AffAdaptation D d) (i j : D.index) :
    Γ(A.divisorSubscheme,
      A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j)) ≅
      CommRingCat.of (A.ovlColength i j) :=
  A.cartierIdeal.subschemeObjIso
      ⟨D.pieces i ⊓ D.pieces j,
        Over.isAffineOpen_inf C (D.isAffineOpen i) (D.isAffineOpen j)⟩ ≪≫
    (Ideal.quotientEquivAlgOfEq R
      (A.cartierIdeal_ideal_overlap_eq_ovlIdeal i j)).toRingEquiv.toCommRingCatIso

/-- The overlap section identification carries the ambient quotient map to reduction
modulo `ovlIdeal`. -/
lemma divisorSubschemeι_app_overlapIso [IsProper C.hom]
    (A : AffAdaptation D d) (i j : D.index) :
    A.divisorSubschemeι.app (D.pieces i ⊓ D.pieces j) ≫
      (A.divisorSubschemeOverlapIso i j).hom =
    CommRingCat.ofHom (Ideal.Quotient.mk (A.ovlIdeal i j)) := by
  rw [A.cartierIdeal.subschemeι_app
    ⟨D.pieces i ⊓ D.pieces j,
      Over.isAffineOpen_inf C (D.isAffineOpen i) (D.isAffineOpen j)⟩]
  simp only [divisorSubschemeOverlapIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext s
  exact Ideal.quotientEquivAlgOfEq_mk R
    (A.cartierIdeal_ideal_overlap_eq_ovlIdeal i j) s

/-- Restriction from the left divisor piece is the widened equalizer's left arrow. -/
lemma divisorSubschemePieceIso_res_left [IsProper C.hom]
    (A : AffAdaptation D d) (i j : D.index) :
    A.divisorSubscheme.presheaf.map
        (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
          A.divisorSubschemeι ⁻¹ᵁ D.pieces i by
            intro x hx
            exact hx.1)).op ≫
      (A.divisorSubschemeOverlapIso i j).hom =
    (A.divisorSubschemePieceIso i).hom ≫
      CommRingCat.ofHom (A.toOvlLeft i j).toRingHom := by
  letI : Epi (A.divisorSubschemeι.app (D.pieces i)) :=
    ConcreteCategory.epi_of_surjective _
      (A.cartierIdeal.subschemeι_app_surjective
        ⟨D.pieces i, D.isAffineOpen i⟩)
  rw [← cancel_epi (A.divisorSubschemeι.app (D.pieces i))]
  rw [← Category.assoc, ← Category.assoc]
  have hr :
      A.divisorSubscheme.presheaf.map
          (((Opens.map A.divisorSubschemeι.base).map
            (homOfLE
              (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).op.unop).op) =
        A.divisorSubscheme.presheaf.map
          (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
            A.divisorSubschemeι ⁻¹ᵁ D.pieces i by
              intro x hx
              exact hx.1)).op := by
    congr 1
  rw [← hr]
  rw [← A.divisorSubschemeι.naturality
    (homOfLE (inf_le_left : D.pieces i ⊓ D.pieces j ≤ D.pieces i)).op]
  rw [Category.assoc, A.divisorSubschemeι_app_overlapIso i j]
  rw [A.divisorSubschemeι_app_pieceIso i]
  apply ConcreteCategory.hom_ext
  intro s
  exact (A.toOvlLeft_mk i j s).symm

/-- Restriction from the right divisor piece is the widened equalizer's right arrow. -/
lemma divisorSubschemePieceIso_res_right [IsProper C.hom]
    (A : AffAdaptation D d) (i j : D.index) :
    A.divisorSubscheme.presheaf.map
        (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
          A.divisorSubschemeι ⁻¹ᵁ D.pieces j by
            intro x hx
            exact hx.2)).op ≫
      (A.divisorSubschemeOverlapIso i j).hom =
    (A.divisorSubschemePieceIso j).hom ≫
      CommRingCat.ofHom (A.toOvlRight i j).toRingHom := by
  letI : Epi (A.divisorSubschemeι.app (D.pieces j)) :=
    ConcreteCategory.epi_of_surjective _
      (A.cartierIdeal.subschemeι_app_surjective
        ⟨D.pieces j, D.isAffineOpen j⟩)
  rw [← cancel_epi (A.divisorSubschemeι.app (D.pieces j))]
  rw [← Category.assoc, ← Category.assoc]
  have hr :
      A.divisorSubscheme.presheaf.map
          (((Opens.map A.divisorSubschemeι.base).map
            (homOfLE
              (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).op.unop).op) =
        A.divisorSubscheme.presheaf.map
          (homOfLE (show A.divisorSubschemeι ⁻¹ᵁ (D.pieces i ⊓ D.pieces j) ≤
            A.divisorSubschemeι ⁻¹ᵁ D.pieces j by
              intro x hx
              exact hx.2)).op := by
    congr 1
  rw [← hr]
  rw [← A.divisorSubschemeι.naturality
    (homOfLE (inf_le_right : D.pieces i ⊓ D.pieces j ≤ D.pieces j)).op]
  rw [Category.assoc, A.divisorSubschemeι_app_overlapIso i j]
  rw [A.divisorSubschemeι_app_pieceIso j]
  apply ConcreteCategory.hom_ext
  intro s
  exact (A.toOvlRight_mk i j s).symm

end AffAdaptation

end AlgebraicGeometry
