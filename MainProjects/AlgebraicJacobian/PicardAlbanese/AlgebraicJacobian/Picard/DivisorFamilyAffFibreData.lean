/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffCert
import AlgebraicJacobian.Picard.DivisorFamilyAffStalkEval
import AlgebraicJacobian.Picard.DivisorFamilyExtraction
import AlgebraicJacobian.Picard.DivisorThetaFibreData

/-!
# Fibrewise H1 witnesses on the widened divisor carrier

The chart-typed fibre theorem in `DivisorThetaFibreData.lean` has two geometric inputs:

* a certified adaptation stays certified after passing to a residue field, so its fibre
  presentation divisor has the certificate degree;
* subtracting that fibre divisor from a sufficiently positive theta window gives a divisor
  with the required Picard class and vanishing `H1`.

Neither input depends on a chart typing of the adaptation cover.  This file proves both for
`AffAdaptation`, whose pieces are arbitrary affine opens.  The conclusion is deliberately the
geometric witness itself, rather than a hypothesis about a not-yet-constructed widened Cech
engine: it is directly reusable by any right-exactness or classifier construction on the
widened carrier and introduces no new premise.

## Main declarations

* `AffAdaptation.IsCertified.deg_presentationDivisor_pulledEquations` -- the fibre divisor of
  a widened certified adaptation has the certificate degree.
* `AffAdaptation.IsCertified.fibrewise_thetaSub_h1_witness` -- at every residue field, the
  explicit divisor `N(a) - d_p` has the transported theta-minus-family class and vanishing
  `H1` once `a` is in the existing high window.
* `AffAdaptation.IsCertified.exists_chartAdaptation_thetaGluedEval_surjective` -- an auxiliary
  finite chart presentation of the same local equations has surjective high-window evaluation;
  the chart presentation is extracted, not assumed or certified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

section FibreData

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [IsDominant pi] [IsIntegral C.left]

attribute [local instance] instOverCleftWFT

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

noncomputable local instance instIsIntegralRelCurveAffFibre (K : Type u) [Field K]
    [Algebra k K] : IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveAffFibre (K : Type u) [Field K]
    [Algebra k K] :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveAffFibre (K : Type u) [Field K]
    [Algebra k K] : QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveAffFibre (K : Type u) [Field K]
    [Algebra k K] : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveAffFibre (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveAffFibre (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

omit [IsDominant pi] [IsIntegral C.left] in
private lemma chi_relCurve_of_chi_aff (g : Nat)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (K : Type u) [Field K] [Algebra k K] :
    Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : Int) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have h1 : Sheaf.chi ((relCurve C K).moduleKSheaf K)
      = 1 - (genus (baseChangeBundle C K) : Int) := chi_moduleKSheaf (baseChangeBundle C K)
  have h2 : genus (baseChangeBundle C K) = genus C := genus_baseField C K
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : Int) := chi_moduleKSheaf C
  have h4 : (genus C : Int) = (g : Int) := by rw [h3] at hchi; linarith
  rw [h1, h2, h4]

private lemma picClass_neg_aff {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] (D : X.CurveDivisor) :
    Scheme.CurveDivisor.picClass K (-D) = (Scheme.CurveDivisor.picClass K D)⁻¹ := by
  have h := Scheme.CurveDivisor.picClass_add K (-D) D
  rw [neg_add_cancel, Scheme.CurveDivisor.picClass_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

namespace AffAdaptation

/-- The divisor cut on a field-valued fibre by a widened certified adaptation has exactly the
certificate degree.  Properness makes the intersections of the affine pieces affine, so the
widened certificate base-change theorem applies without an extra overlap hypothesis. -/
theorem IsCertified.deg_presentationDivisor_pulledEquations
    {K : Type u} [Field K] [Algebra k K]
    [Algebra R K] [IsScalarTower k R K]
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {n : Nat} (hc : A.IsCertified n) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K
      ((A.pulledEquations K hc.projective_colength).presentation)) = (n : Int) := by
  have h := (A.pullback K hc.projective_colength).deg_presentationDivisor
  rwa [(A.isCertified_pullback K D.hasAffineOverlaps_of_isProper hc).finrank_glued] at h

/-- At every field-valued point of the base, a widened certified family supplies the actual
high-window cohomology witness: `N(a) - d_p` represents the pullback of
`[Theta^a] * [d]^-1` and has vanishing `H1`.  This is the geometric producer needed by the
widened right-exactness/classifier layer; no chart typing of the adaptation cover occurs. -/
theorem IsCertified.fibrewise_thetaSub_h1_witness
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : Nat} (hc : A.IsCertified g)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    {a : Nat} (ha1 : Subsingleton (relTwistPair C k pi (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a)
    (p : PrimeSpectrum R) :
    ∃ W : (relCurve C p.asIdeal.ResidueField).CurveDivisor,
      Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
          = Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField)
              ((thetaChartDatum C R pi a).cechPicClass * d.picClass⁻¹)
        ∧ Subsingleton (Sheaf.HModule
            ((relCurve C p.asIdeal.ResidueField).divisorSheaf
              p.asIdeal.ResidueField W) 1) := by
  let K := p.asIdeal.ResidueField
  let dp := Scheme.presentationDivisor K
    ((A.pulledEquations K hc.projective_colength).presentation)
  refine ⟨windowTransportDivisor C K pi a - dp, ?_, ?_⟩
  · have e1 : Scheme.CurveDivisor.picClass K dp
        = Scheme.CechPic.map (relCurveMap C R K) d.picClass := by
      dsimp [dp]
      rw [Scheme.CurveDivisor.picClass_presentationDivisor,
        Scheme.LocalEquations.presentation_picClass]
      exact A.picClass_pulledEquations K hc.projective_colength
    have e2 : Scheme.CurveDivisor.picClass K (windowTransportDivisor C K pi a)
        = Scheme.CechPic.map (relCurveMap C R K)
            ((thetaChartDatum C R pi a).cechPicClass) :=
      (picClass_windowTransportDivisor C K pi a).trans
        (cechPicClass_map_thetaChartDatum C R pi a K).symm
    calc Scheme.CurveDivisor.picClass K (windowTransportDivisor C K pi a - dp)
        = Scheme.CurveDivisor.picClass K (windowTransportDivisor C K pi a)
            * (Scheme.CurveDivisor.picClass K dp)⁻¹ := by
          rw [sub_eq_add_neg, Scheme.CurveDivisor.picClass_add, picClass_neg_aff]
      _ = Scheme.CechPic.map (relCurveMap C R K)
            ((thetaChartDatum C R pi a).cechPicClass * d.picClass⁻¹) := by
          rw [e1, e2, map_mul, map_inv]
  · refine subsingleton_h1_windowTransportDivisor_sub C pi hpi K g a
      ha1 hMa hO hchi (chi_relCurve_of_chi_aff C g hchi K) dp ?_
    have hdeg := hc.deg_presentationDivisor_pulledEquations
      (C := C) (R := R) (K := K)
    dsimp [dp] at hdeg ⊢
    rw [hdeg]
    have := Int.natCast_nonneg g
    linarith

/-- The widened certified family supplies the same fibrewise theta-minus-divisor
witness when its degree `g` is independent of the curve parameter `gamma ≤ g`. -/
theorem IsCertified.fibrewise_thetaSub_h1_witness_at
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g gamma : Nat} (hc : A.IsCertified g)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    {a : Nat} (hMa : windowM_choice pi hpi g ≤ a)
    (p : PrimeSpectrum R) :
    ∃ W : (relCurve C p.asIdeal.ResidueField).CurveDivisor,
      Scheme.CurveDivisor.picClass p.asIdeal.ResidueField W
          = Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField)
              ((thetaChartDatum C R pi a).cechPicClass * d.picClass⁻¹)
        ∧ Subsingleton (Sheaf.HModule
            ((relCurve C p.asIdeal.ResidueField).divisorSheaf
              p.asIdeal.ResidueField W) 1) := by
  let K := p.asIdeal.ResidueField
  let dp := Scheme.presentationDivisor K
    ((A.pulledEquations K hc.projective_colength).presentation)
  refine ⟨windowTransportDivisor C K pi a - dp, ?_, ?_⟩
  · have e1 : Scheme.CurveDivisor.picClass K dp
        = Scheme.CechPic.map (relCurveMap C R K) d.picClass := by
      dsimp [dp]
      rw [Scheme.CurveDivisor.picClass_presentationDivisor,
        Scheme.LocalEquations.presentation_picClass]
      exact A.picClass_pulledEquations K hc.projective_colength
    have e2 : Scheme.CurveDivisor.picClass K (windowTransportDivisor C K pi a)
        = Scheme.CechPic.map (relCurveMap C R K)
            ((thetaChartDatum C R pi a).cechPicClass) :=
      (picClass_windowTransportDivisor C K pi a).trans
        (cechPicClass_map_thetaChartDatum C R pi a K).symm
    calc Scheme.CurveDivisor.picClass K (windowTransportDivisor C K pi a - dp)
        = Scheme.CurveDivisor.picClass K (windowTransportDivisor C K pi a)
            * (Scheme.CurveDivisor.picClass K dp)⁻¹ := by
          rw [sub_eq_add_neg, Scheme.CurveDivisor.picClass_add, picClass_neg_aff]
      _ = Scheme.CechPic.map (relCurveMap C R K)
            ((thetaChartDatum C R pi a).cechPicClass * d.picClass⁻¹) := by
          rw [e1, e2, map_mul, map_inv]
  · refine subsingleton_h1_windowTransportDivisor_sub_at
      C pi hpi K g a hMa hgamma (chi_relCurve_of_chi_aff C gamma hchi K) dp ?_
    have hdeg := hc.deg_presentationDivisor_pulledEquations
      (C := C) (R := R) (K := K)
    dsimp [dp] at hdeg ⊢
    rw [hdeg]
    have := Int.natCast_nonneg g
    linarith

/-- The widened fibre witnesses fire the existing right-exactness engine on an auxiliary finite
chart presentation of the same local-equation system.  Such a presentation exists for every
`d`; it is neither an input nor required to be certified.  Its theta-ideal datum has the
intrinsic class `[Theta^a] * [d]^-1`, so the widened witness supplies exactly the residue-field
divisor and `H1` vanishing that `thetaGluedEval_surjective_of_fibre_witness` consumes.

This is the chart-free right-exactness bridge at the cover-independent window: the resulting
evaluation has kernel `d.vanishingSubmodule`, hence its window carve has kernel
`divisorWindow d ha1`, while the original widened certificate is used only to produce the
fibre witnesses. -/
theorem IsCertified.exists_chartAdaptation_thetaGluedEval_surjective
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : Nat} (hc : A.IsCertified g)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    {a : Nat} (ha1 : Subsingleton (relTwistPair C k pi (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a) :
    ∃ B : DivisorAdaptation C R pi d, Function.Surjective (B.thetaGluedEval a) := by
  obtain ⟨B⟩ := exists_divisorAdaptation C R pi d
  refine ⟨B, B.thetaGluedEval_surjective_of_fibre_witness hpi (fun p => ?_)⟩
  obtain ⟨W, hWclass, hWH1⟩ :=
    hc.fibrewise_thetaSub_h1_witness C R pi hpi hO hchi ha1 hMa p
  refine ⟨W, ?_, hWH1⟩
  rw [BasicOpenCocycleDatum.cechPicClass_baseChange,
    B.cechPicClass_thetaIdealDatum]
  exact hWclass

/-- The cover-independent widened window quotient therefore has a finite chart presentation:
it is linearly equivalent to the theta-twisted colength module of an extracted adaptation.
No certificate is transported to that adaptation (which would contradict the strict R2
examples); only the intrinsic local equations and the right-exactness witness are used. -/
theorem IsCertified.exists_chartAdaptation_windowQuotEquiv
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : Nat} (hc : A.IsCertified g)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    {a : Nat} (ha1 : Subsingleton (relTwistPair C k pi (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a) :
    ∃ B : DivisorAdaptation C R pi d,
      Nonempty (((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
          divisorWindow d ha1) ≃ₗ[R] B.ThetaGlued a) := by
  obtain ⟨B, hsurj⟩ := hc.exists_chartAdaptation_thetaGluedEval_surjective
    C R pi hpi hO hchi ha1 hMa
  exact ⟨B, ⟨windowQuotEquiv B ha1 hsurj⟩⟩

end AffAdaptation

end FibreData

end AlgebraicGeometry
