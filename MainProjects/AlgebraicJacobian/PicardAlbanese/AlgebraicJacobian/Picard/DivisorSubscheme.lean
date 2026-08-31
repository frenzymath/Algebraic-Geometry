/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorIdealSheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The divisor subscheme of a widened affine adaptation

The intrinsic Cartier ideal of a widened adaptation defines a closed divisor subscheme.
Its inverse image over every adapted affine piece is affine, with coordinate ring exactly
the existing `AffAdaptation.colength`.  These spectra form an affine open cover indexed by
the arbitrary widened cover, without a fixed chart partition or `SwallowedBy` hypothesis.
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

/-- The closed divisor subscheme cut out by the intrinsic Cartier ideal. -/
noncomputable abbrev divisorSubscheme (A : AffAdaptation D d) : Scheme :=
  A.cartierIdeal.subscheme

/-- The closed immersion of the divisor subscheme into the relative curve. -/
noncomputable abbrev divisorSubschemeι (A : AffAdaptation D d) :
    A.divisorSubscheme ⟶ relCurve C R :=
  A.cartierIdeal.subschemeι

instance isClosedImmersion_divisorSubschemeι (A : AffAdaptation D d) :
    IsClosedImmersion A.divisorSubschemeι := by
  infer_instance

/-- The kernel of the divisor inclusion is the intrinsic Cartier ideal. -/
theorem ker_divisorSubschemeι (A : AffAdaptation D d) :
    A.divisorSubschemeι.ker = A.cartierIdeal :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The divisor subscheme as a scheme over the affine test base. -/
noncomputable def divisorSubschemeOver (A : AffAdaptation D d) :
    Over (Spec (.of R)) :=
  Over.mk (A.divisorSubschemeι ≫ (relCurve C R ↘ Spec (.of R)))

/-- Replacing the Cartier ideal by its adapted principal generator identifies the local
quotient algebra with the existing colength algebra. -/
noncomputable def divisorPieceQuotientEquiv [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    (Γ(relCurve C R, D.pieces i) ⧸
      A.cartierIdeal.ideal ⟨D.pieces i, D.isAffineOpen i⟩) ≃ₐ[R]
      A.colength i :=
  Ideal.quotientEquivAlgOfEq R (A.cartierIdeal_ideal_eq_span_eqn i)

/-- Sections of the divisor subscheme over a widened affine piece are its recorded
colength algebra. -/
noncomputable def divisorSubschemePieceIso [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    Γ(A.divisorSubscheme, A.divisorSubschemeι ⁻¹ᵁ D.pieces i) ≅
      CommRingCat.of (A.colength i) :=
  A.cartierIdeal.subschemeObjIso ⟨D.pieces i, D.isAffineOpen i⟩ ≪≫
    (A.divisorPieceQuotientEquiv i).toRingEquiv.toCommRingCatIso

/-- Ring-equivalence spelling of `divisorSubschemePieceIso`. -/
noncomputable def divisorSubschemePieceRingEquiv [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    Γ(A.divisorSubscheme, A.divisorSubschemeι ⁻¹ᵁ D.pieces i) ≃+*
      A.colength i :=
  (A.divisorSubschemePieceIso i).commRingCatIsoToRingEquiv

/-- Under the local section identification, restriction to the divisor subscheme is the
existing quotient map by the adapted equation. -/
lemma divisorSubschemeι_app_pieceIso [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    A.divisorSubschemeι.app (D.pieces i) ≫
      (A.divisorSubschemePieceIso i).hom =
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {A.eqn i})) := by
  rw [A.cartierIdeal.subschemeι_app ⟨D.pieces i, D.isAffineOpen i⟩]
  simp only [divisorSubschemePieceIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext s
  exact Ideal.quotientEquivAlgOfEq_mk R
    (A.cartierIdeal_ideal_eq_span_eqn i) s

/-- The inverse image of every adapted affine piece in the divisor subscheme is affine. -/
theorem isAffineOpen_divisorPiece [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    IsAffineOpen (A.divisorSubschemeι ⁻¹ᵁ D.pieces i) := by
  rw [← A.cartierIdeal.opensRange_subschemeCover_map
    ⟨D.pieces i, D.isAffineOpen i⟩]
  exact isAffineOpen_opensRange _

/-- The colength spectrum of one adapted piece, mapped into the divisor subscheme. -/
noncomputable def divisorPieceMap [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    Spec (.of (A.colength i)) ⟶ A.divisorSubscheme :=
  Spec.map (A.divisorPieceQuotientEquiv i).toRingEquiv.toCommRingCatIso.hom ≫
    A.cartierIdeal.subschemeCover.f ⟨D.pieces i, D.isAffineOpen i⟩

instance isOpenImmersion_divisorPieceMap [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    IsOpenImmersion (A.divisorPieceMap i) := by
  dsimp only [divisorPieceMap]
  infer_instance

/-- The image of a colength chart is exactly the inverse image of its adapted piece. -/
theorem opensRange_divisorPieceMap [IsProper C.hom]
    (A : AffAdaptation D d) (i : D.index) :
    (A.divisorPieceMap i).opensRange =
      A.divisorSubschemeι ⁻¹ᵁ D.pieces i := by
  dsimp only [divisorPieceMap]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact A.cartierIdeal.opensRange_subschemeCover_map
    ⟨D.pieces i, D.isAffineOpen i⟩

/-- The divisor subscheme is covered by the spectra of the widened piece colength
algebras.  Its index type and members are literally those of `AffCoverData`. -/
noncomputable def divisorPieceCover [IsProper C.hom]
    (A : AffAdaptation D d) :
    A.divisorSubscheme.AffineOpenCover where
  I₀ := D.index
  X i := .of (A.colength i)
  f i := A.divisorPieceMap i
  idx x := (D.exists_mem_pieces (A.divisorSubschemeι x)).choose
  covers x := by
    change x ∈ (A.divisorPieceMap
      (D.exists_mem_pieces (A.divisorSubschemeι x)).choose).opensRange
    rw [A.opensRange_divisorPieceMap]
    exact (D.exists_mem_pieces (A.divisorSubschemeι x)).choose_spec

end AffAdaptation

end AlgebraicGeometry
