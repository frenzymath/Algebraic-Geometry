/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveMap
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveSite
import AlgebraicJacobian.Picard.Pic0ChartCoverageDegreeStep2

/-!
# Target identities for admissible Abel lifts

This module packages the class-level equalities used after an affine Picard class has been
honestified and a widened divisor family has been constructed.  It identifies the honest
twisted Cech class with the chart twist, computes its degree after every field-valued base
change, and turns equality of widened Picard classes into the literal Abel and chart-value
equalities required by the local lifting argument.

No representability, quotient, atlas, or local-surjectivity assertion is made here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/- The degree API is stated on `relCurve`; install the product-spelled base-change instances
under that alias for every field used below. -/
noncomputable local instance instIsIntegralRelCurveTarget
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveTarget
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQuasiCompactRelCurveTarget
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFiniteH0RelCurveTarget
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFiniteH1RelCurveTarget
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-! ## The honest twisted target -/

/-- If a degree-zero target becomes the honest Cech class `c` on an affine test, then its
chart twist is the unit image of `c` multiplied by the base-changed collapsed twist class. -/
theorem relPicToPicEt_twistedClass_eq_chartTwist
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T)
    {B : Type u} [CommRing B] [Algebra k B]
    (g : overSpec k B ⟶ T)
    (c : (relCurve C B).CechPic)
    (hpic : picEtMap C g (lam : picEt C T) =
      relPicToPicEt C (overSpec k B) (relPicMk C (overSpec k B) c))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    relPicToPicEt C (overSpec k B)
        (relPicMk C (overSpec k B)
          (c * Scheme.CechPic.map (relCurveMap C k B)
            (chartTwistClass C m Z))) =
      chartTwist C m Z (overSpec k B)
        (pic0Map C g lam : picEt C (overSpec k B)) := by
  apply (picEtAffineEquiv C B).injective
  rw [picEtAffineEquiv_relPicToPicEt,
    chartTwist_eq_mul_thetaFamily_chartTwistClass]
  change PicEtAff.unit C B
      (relPicMk C (overSpec k B)
        (c * Scheme.CechPic.map (relCurveMap C k B) (chartTwistClass C m Z))) =
    picEtAffineEquiv C B
      (picEtMap C g (lam : picEt C T) *
        thetaFamily C (chartTwistClass C m Z) (overSpec k B))
  rw [map_mul (picEtAffineEquiv C B), hpic,
    picEtAffineEquiv_relPicToPicEt,
    picEtAffineEquiv_thetaFamily_eq_unit_relPicMk]
  exact map_mul ((PicEtAff.unit C B).comp (relPicMk C (overSpec k B))) _ _

/-- Datum-facing orientation of `relPicToPicEt_twistedClass_eq_chartTwist`: a datum presenting
the twisted class honestly presents the chart twist of the restricted target. -/
theorem chartTwist_picEtMap_eq_relPicToPicEt_cechPicClass
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T)
    {B : Type u} [CommRing B] [Algebra k B]
    (g : overSpec k B ⟶ T)
    (c : (relCurve C B).CechPic)
    (hpic : picEtMap C g (lam : picEt C T) =
      relPicToPicEt C (overSpec k B) (relPicMk C (overSpec k B) c))
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    (D : BasicOpenCocycleDatum C B pi)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hD : D.cechPicClass =
      c * Scheme.CechPic.map (relCurveMap C k B) (chartTwistClass C m Z)) :
    chartTwist C m Z (overSpec k B) (picEtMap C g (lam : picEt C T)) =
      relPicToPicEt C (overSpec k B)
        (relPicMk C (overSpec k B) D.cechPicClass) := by
  rw [hD]
  exact (relPicToPicEt_twistedClass_eq_chartTwist lam g c hpic m Z).symm

/-! ## Uniform degree of the twisted target -/

variable {n : ℕ}

/-- The honest twisted class has the chart parameter as its degree after every field-valued
base change of the affine test. -/
theorem classDeg_twistedClass_eq
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T)
    {B : Type u} [CommRing B] [Algebra k B]
    (g : overSpec k B ⟶ T)
    (c : (relCurve C B).CechPic)
    (hpic : picEtMap C g (lam : picEt C T) =
      relPicToPicEt C (overSpec k B) (relPicMk C (overSpec k B) c))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z =
      (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (K : Type u) [Field K] [Algebra k K] [Algebra B K]
    [IsScalarTower k B K] :
    classDeg K (Scheme.CechPic.map (relCurveMap C B K)
      (c * Scheme.CechPic.map (relCurveMap C k B)
        (chartTwistClass C m Z))) = (n : ℤ) := by
  let t : overSpec k K ⟶ overSpec k B :=
    Over.overSpecMap (IsScalarTower.toAlgHom k B K)
  have h := congrArg
    (fun mu : picEt C (overSpec k B) => degAt mu t)
    (relPicToPicEt_twistedClass_eq_chartTwist lam g c hpic m Z)
  rw [degAt_relPicToPicEt, relPicMap_mk, relPicDeg_relPicMk,
    degAt_chartTwist m Z (pic0Map C g lam).2 t] at h
  have ht : (C ◁ t).left = relCurveMap C B K := by
    refine congrArg (fun q : overSpec k K ⟶ overSpec k B => (C ◁ q).left) ?_
    exact Over.OverMorphism.ext rfl
  rw [ht] at h
  calc
    _ = (m : ℤ) * classDeg k (thetaCechClass C) -
        Scheme.CurveDivisor.deg k Z := h
    _ = (n : ℤ) := by rw [hdeg]; ring

/-- Any Cech class identified with the honest twisted class has constant field degree equal to
the chart parameter.  This is the form consumed by datum and local-equation producers. -/
theorem classDeg_eq_of_eq_twistedClass
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T)
    {B : Type u} [CommRing B] [Algebra k B]
    (g : overSpec k B ⟶ T)
    (c d : (relCurve C B).CechPic)
    (hpic : picEtMap C g (lam : picEt C T) =
      relPicToPicEt C (overSpec k B) (relPicMk C (overSpec k B) c))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z =
      (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (hd : d = c * Scheme.CechPic.map (relCurveMap C k B)
      (chartTwistClass C m Z))
    (K : Type u) [Field K] [Algebra k K] [Algebra B K]
    [IsScalarTower k B K] :
    classDeg K (Scheme.CechPic.map (relCurveMap C B K) d) = (n : ℤ) := by
  rw [hd]
  exact classDeg_twistedClass_eq lam g c hpic m Z hdeg K

/-! ## Widened Abel and chart-value consequences -/

/-- A widened family whose Picard class is the honest twisted target has Abel value equal to
the chart twist of the restricted degree-zero target. -/
theorem abelDivAff'_eq_chartTwist_of_picClass_eq
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T)
    {B : Type u} [CommRing B] [Algebra k B]
    (g : overSpec k B ⟶ T)
    (c : (relCurve C B).CechPic)
    (hpic : picEtMap C g (lam : picEt C T) =
      relPicToPicEt C (overSpec k B) (relPicMk C (overSpec k B) c))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (F : DivFamZarAff C B n)
    (hF : F.picClass =
      c * Scheme.CechPic.map (relCurveMap C k B) (chartTwistClass C m Z)) :
    abelDivAff' C n (overSpec k B)
        ((divFamZarAffAffineEquiv C n B).symm F) =
      chartTwist C m Z (overSpec k B)
        (pic0Map C g lam : picEt C (overSpec k B)) := by
  calc
    abelDivAff' C n (overSpec k B)
        ((divFamZarAffAffineEquiv C n B).symm F) =
        relPicToPicEt C (overSpec k B)
          (relPicMk C (overSpec k B) F.picClass) := by
      apply (picEtAffineEquiv C B).injective
      rw [picEtAffineEquiv_abelDivAff'_affineEquiv_symm F,
        abelDivAffPlus, picEtAffineEquiv_relPicToPicEt]
    _ = relPicToPicEt C (overSpec k B)
          (relPicMk C (overSpec k B)
            (c * Scheme.CechPic.map (relCurveMap C k B)
              (chartTwistClass C m Z))) := by rw [hF]
    _ = chartTwist C m Z (overSpec k B)
          (pic0Map C g lam : picEt C (overSpec k B)) :=
      relPicToPicEt_twistedClass_eq_chartTwist lam g c hpic m Z

/-- The chart transformation sends a widened family with the honest twisted Picard class to
the restricted degree-zero target itself. -/
theorem chartValueAffTrans_app_eq_of_picClass_eq
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T)
    {B : Type u} [CommRing B] [Algebra k B]
    (g : overSpec k B ⟶ T)
    (c : (relCurve C B).CechPic)
    (hpic : picEtMap C g (lam : picEt C T) =
      relPicToPicEt C (overSpec k B) (relPicMk C (overSpec k B) c))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z =
      (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (F : DivFamZarAff C B n)
    (hF : F.picClass =
      c * Scheme.CechPic.map (relCurveMap C k B) (chartTwistClass C m Z)) :
    (chartValueAffTrans C n m Z hdeg).app (op (overSpec k B))
        ((divFamZarAffAffineEquiv C n B).symm F) =
      pic0Map C g lam := by
  exact chartValueAffTrans_app_eq_of_abelDivAff'_eq_chartTwist
    m Z hdeg _ _
      (abelDivAff'_eq_chartTwist_of_picClass_eq lam g c hpic m Z F hF)

end

end AlgebraicGeometry
