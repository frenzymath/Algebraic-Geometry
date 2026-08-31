/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaKernel

/-!
# The global intrinsic theta kernel

The intrinsic theta evaluation on an arbitrary widened affine cover has exactly the
cover-independent vanishing submodule as its kernel.  The proof uses the componentwise
principal-ideal criterion from `DivisorFamilyAffThetaKernel`; it neither assigns a pinned
chart to a widened piece nor assumes such an assignment exists.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaPieceSectionsModule

omit [IsProper C.hom] in
private lemma intrinsicThetaPiece_germ_inl (a : ℕ)
    (x : relThetaSections C R π a) (j : D.index) (z : relCurve C R)
    (hz : z ∈ D.pieces j ⊓
      (thetaChartDatum C R π a).pieces (Sum.inl PUnit.unit)) :
    ((relCurve C R).presheaf.germ
        (D.pieces j ⊓ (thetaChartDatum C R π a).pieces (Sum.inl PUnit.unit)) z hz).hom
        ((secRes (thetaChartDatum C R π a).sheaf le_top
          ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)).val
            (Sum.inl PUnit.unit)) =
      ((relCurve C R).presheaf.germ
        ((⊤ : (relCurve C R).Opens) ⊓ (relCover C R (fiberTwoCover π)).V₀) z
          ⟨trivial, by
            exact thetaChartCover_pieces_le_inl C R π PUnit.unit hz.2⟩).hom
        x.val.1 := by
  change ((relCurve C R).presheaf.germ _ z hz).hom
      ((relCurve C R).resHom _ ((relCurve C R).resHom _ x.val.1)) = _
  calc
    _ = _ := TopCat.Presheaf.germ_res_apply _ _ _ _ _
    _ = _ := TopCat.Presheaf.germ_res_apply _ _ _ _ _

omit [IsProper C.hom] in
private lemma intrinsicThetaPiece_germ_inr (a : ℕ)
    (x : relThetaSections C R π a) (j : D.index) (z : relCurve C R)
    (hz : z ∈ D.pieces j ⊓
      (thetaChartDatum C R π a).pieces (Sum.inr PUnit.unit)) :
    ((relCurve C R).presheaf.germ
        (D.pieces j ⊓ (thetaChartDatum C R π a).pieces (Sum.inr PUnit.unit)) z hz).hom
        ((secRes (thetaChartDatum C R π a).sheaf le_top
          ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)).val
            (Sum.inr PUnit.unit)) =
      ((relCurve C R).presheaf.germ
        ((⊤ : (relCurve C R).Opens) ⊓ (relCover C R (fiberTwoCover π)).V₁) z
          ⟨trivial, by
            exact thetaChartCover_pieces_le_inr C R π PUnit.unit hz.2⟩).hom
        x.val.2 := by
  change ((relCurve C R).presheaf.germ _ z hz).hom
      ((relCurve C R).resHom _ ((relCurve C R).resHom _ x.val.2)) = _
  calc
    _ = _ := TopCat.Presheaf.germ_res_apply _ _ _ _ _
    _ = _ := TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- The kernel of intrinsic theta evaluation on every widened affine adaptation is the
cover-independent vanishing submodule of the divisor family. -/
theorem ker_intrinsicThetaEvalRel (A : AffAdaptation D d) (a : ℕ) :
    LinearMap.ker (A.intrinsicThetaEvalRel (π := π) a) =
      d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a) := by
  ext x
  rw [LinearMap.mem_ker, Scheme.LocalEquations.mem_vanishingSubmodule_iff]
  constructor
  · intro hx
    have hpiece (j : D.index) :
        secRes (thetaChartDatum C R π a).sheaf le_top
            ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x) ∈
          A.thetaPieceVanishing (π := π) a j := by
      letI : Module Γ(relCurve C R, D.pieces j)
          (A.ThetaPieceSections (π := π) a j) :=
        A.thetaPieceSectionsModule (π := π) a j
      have hxj := congrArg
        (fun y : A.IntrinsicThetaGlued (π := π) a =>
          (y : A.ThetaPieceProd (π := π) a) j) hx
      change Submodule.Quotient.mk
          (secRes (thetaChartDatum C R π a).sheaf le_top
            ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) = 0 at hxj
      exact (Submodule.Quotient.mk_eq_zero
        (A.thetaPieceVanishing (π := π) a j)).mp hxj
    constructor
    · intro z hz
      obtain ⟨j, hj⟩ := D.exists_mem_pieces z
      have hlocal := (A.mem_thetaPieceVanishing_iff_forall_germ (π := π) a j _).mp
        (hpiece j) (Sum.inl PUnit.unit) z ⟨hj, by
          exact (thetaChartCover_pieces_inl C R π PUnit.unit).ge hz.2⟩
      rwa [intrinsicThetaPiece_germ_inl (C := C) (R := R) (π := π) a x j] at hlocal
    · intro z hz
      obtain ⟨j, hj⟩ := D.exists_mem_pieces z
      have hlocal := (A.mem_thetaPieceVanishing_iff_forall_germ (π := π) a j _).mp
        (hpiece j) (Sum.inr PUnit.unit) z ⟨hj, by
          exact (thetaChartCover_pieces_inr C R π PUnit.unit).ge hz.2⟩
      rwa [intrinsicThetaPiece_germ_inr (C := C) (R := R) (π := π) a x j] at hlocal
  · rintro ⟨hx₀, hx₁⟩
    apply Subtype.ext
    funext j
    letI : Module Γ(relCurve C R, D.pieces j)
        (A.ThetaPieceSections (π := π) a j) :=
      A.thetaPieceSectionsModule (π := π) a j
    change Submodule.Quotient.mk
        (secRes (thetaChartDatum C R π a).sheaf le_top
          ((gluedTwistEquiv C R π a (⊤ : (relCurve C R).Opens)).symm x)) = 0
    rw [Submodule.Quotient.mk_eq_zero (A.thetaPieceVanishing (π := π) a j)]
    apply (A.mem_thetaPieceVanishing_iff_forall_germ (π := π) a j _).mpr
    rintro (q | q) z hz
    · cases q
      rw [intrinsicThetaPiece_germ_inl (C := C) (R := R) (π := π) a x j]
      exact hx₀ z ⟨trivial, by
        exact thetaChartCover_pieces_le_inl C R π PUnit.unit hz.2⟩
    · cases q
      rw [intrinsicThetaPiece_germ_inr (C := C) (R := R) (π := π) a x j]
      exact hx₁ z ⟨trivial, by
        exact thetaChartCover_pieces_le_inr C R π PUnit.unit hz.2⟩

/-- The quotient by divisor-family vanishing is canonically the actual range of intrinsic
theta evaluation.  Thus right exactness is precisely the assertion that this range is the
whole intrinsic descent module. -/
noncomputable def intrinsicThetaQuotEquivRange (A : AffAdaptation D d) (a : ℕ) :
    (relThetaSections C R π a ⧸
        d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
          (relCover C R (fiberTwoCover π)).V₁ (relThetaCocycle C R π a)) ≃ₗ[R]
      ↥(LinearMap.range (A.intrinsicThetaEvalRel (π := π) a)) :=
  (Submodule.quotEquivOfEq _ _ (A.ker_intrinsicThetaEvalRel (π := π) a).symm).trans
    (A.intrinsicThetaEvalRel (π := π) a).quotKerEquivRange

@[simp]
theorem intrinsicThetaQuotEquivRange_mk (A : AffAdaptation D d) (a : ℕ)
    (x : relThetaSections C R π a) :
    ((A.intrinsicThetaQuotEquivRange (π := π) a (Submodule.Quotient.mk x) :
      ↥(LinearMap.range (A.intrinsicThetaEvalRel (π := π) a))) :
        A.IntrinsicThetaGlued (π := π) a) =
      A.intrinsicThetaEvalRel (π := π) a x := by
  rfl

/-! ## The intrinsic high-window carve -/

noncomputable local instance instOverCleftAffThetaKernelWindow :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))] [IsDominant π]

/-- The high-window sections evaluated in the intrinsic, chart-free theta restriction. -/
noncomputable def intrinsicWindowCarve (A : AffAdaptation D d) (a : ℕ)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤) →ₗ[R]
      A.IntrinsicThetaGlued (π := π) a :=
  (A.intrinsicThetaEvalRel (π := π) a).comp
    (relThetaWindowEquiv C R π a hH1).toLinearMap

/-- The intrinsic high-window carve has exactly the established divisor window as its
kernel, without typing widened pieces into either pinned chart. -/
theorem ker_intrinsicWindowCarve (A : AffAdaptation D d) (a : ℕ)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    LinearMap.ker (A.intrinsicWindowCarve (π := π) a hH1) =
      divisorWindow d hH1 := by
  rw [intrinsicWindowCarve, LinearMap.ker_comp, A.ker_intrinsicThetaEvalRel,
    divisorWindow]

/-- The established high-window quotient is canonically the range of the intrinsic
chart-free carve, with no surjectivity premise. -/
noncomputable def intrinsicWindowQuotEquivRange (A : AffAdaptation D d) (a : ℕ)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1) :
    ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1) ≃ₗ[R]
      ↥(LinearMap.range (A.intrinsicWindowCarve (π := π) a hH1)) :=
  (Submodule.quotEquivOfEq _ _ (A.ker_intrinsicWindowCarve (π := π) a hH1).symm).trans
    (A.intrinsicWindowCarve (π := π) a hH1).quotKerEquivRange

end AffAdaptation

end AlgebraicGeometry
