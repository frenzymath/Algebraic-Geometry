/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafExtraction
import AlgebraicJacobian.Picard.Pic0ChartPlusFibreProducer
import AlgebraicJacobian.Picard.Pic0ChartPlusFibreTower
import AlgebraicJacobian.Picard.Pic0RankOnePresentation
import AlgebraicJacobian.Picard.ThetaShift

/-!
# The lambda-tied datum underlying a native rank-one presentation

Every affine Picard value is represented on an etale cover. This file exposes that actual
representative and refines its relative Picard class to a basic-open cocycle datum. The output is
tied to the displayed value; it makes no cohomology, rank, evaluation-divisor, or base-change
claim.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

/--
The part of a native presentation forced by the displayed Picard value.

`represents` ties the etale-plus representative to `lam`, while `datum_class` ties the
basic-open cocycle datum to that same representative. The geometric certificates that enrich
this datum are intentionally absent.
-/
structure PicRankOneNativeDatum
    (lam : picDegLayer C (genus C : ℤ) (overSpec k A)) : Type (u + 1) where
  cover : Algebra.EtaleCover A
  representative : descentClasses C cover
  represents :
    PicEtAff.mk C cover representative = picEtAffineEquiv C A lam.1
  datum : BasicOpenCocycleDatum C cover.Carrier pi
  datum_class :
    (representative : relPic C (overSpec k cover.Carrier)) =
      relPicMk C (overSpec k cover.Carrier) datum.cechPicClass

namespace PicRankOneNativeDatum

/-- Every displayed affine Picard value has a tied basic-open cocycle datum.

The proof exposes an etale-plus representative of the displayed value, chooses a Cech
representative of its relative Picard class, and refines that class to a basic-open datum.
-/
theorem nonempty
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (lam : picDegLayer C (genus C : ℤ) (overSpec k A)) :
    Nonempty (PicRankOneNativeDatum pi lam) := by
  have hplus : ∀ a : PicEtAff C A,
      ∃ (E : Algebra.EtaleCover A) (x : descentClasses C E),
        PicEtAff.mk C E x = a := by
    intro a
    induction a using PicEtAff.ind with
    | mk E x => exact ⟨E, x, rfl⟩
  obtain ⟨E, x, hrep⟩ := hplus (picEtAffineEquiv C A lam.1)
  obtain ⟨c, hc⟩ := relPicMk_surjective C (overSpec k E.Carrier)
    (x : relPic C (overSpec k E.Carrier))
  obtain ⟨D, hD⟩ := BasicOpenCocycleDatum.exists_cechPicClass_eq
    (C := C) (B := E.Carrier) (π := pi) c
  refine ⟨
    { cover := E
      representative := x
      represents := hrep
      datum := D
      datum_class := ?_ }⟩
  calc
    (x : relPic C (overSpec k E.Carrier)) =
        relPicMk C (overSpec k E.Carrier) c := hc.symm
    _ = relPicMk C (overSpec k E.Carrier) D.cechPicClass :=
      congrArg (relPicMk C (overSpec k E.Carrier)) hD.symm

noncomputable local instance (priority := 20000) nativeDatumDegreeOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance nativeDatumDegreeSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance nativeDatumDegreeIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance nativeDatumDegreeQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance nativeDatumDegreeFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance nativeDatumDegreeFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- The datum extracted from a genus-degree class has genus degree after every field-valued
coefficient extension.

This is forced by the two class-identification fields of `P`; it is not an additional rank-one
hypothesis. -/
theorem classDeg_baseChange
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneNativeDatum pi lam)
    (L : Type u) [Field L] [Algebra k L] [Algebra P.cover.Carrier L]
    [IsScalarTower k P.cover.Carrier L] :
    classDeg L
      (Scheme.CechPic.map (relCurveMap C P.cover.Carrier L)
        P.datum.cechPicClass) = genus C :=
  PicRankOneLocalPresentation.datum_classDeg_baseChange_of_representation
    P.cover P.representative P.represents P.datum P.datum_class L

/-- Split witnesses for the represented class on every residue field give the exact residue
`H¹` witnesses for the same extracted datum.

The proof first identifies the datum with its relative Picard representative, uses the existing
pointwise presentation equivalence, and then transports across the canonical comparison between
the scheme-theoretic and algebraic residue fields. -/
theorem residueH1Witness_of_isSplitWitness
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
    (P : PicRankOneNativeDatum pi lam)
    (hsplit : ∀ t : (overSpec k P.cover.Carrier).left,
      IsSplitWitness C
        (picEtMap C (Over.testPoint t)
          (relPicToPicEt C (overSpec k P.cover.Carrier)
            (P.representative : relPic C (overSpec k P.cover.Carrier))))) :
    ∀ p : PrimeSpectrum P.cover.Carrier,
      P.datum.HasWitnessH1Vanishing p.asIdeal.ResidueField := by
  intro p
  have hfib : IsChartDatumPlusFibre C pi
      (relPicToPicEt C (overSpec k P.cover.Carrier)
        (relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass))
      P.datum :=
    isChartDatumPlusFibre_of_relPicToPicEt C pi
      P.datum.cechPicClass P.datum rfl
  have hpres := isChartDatumPresentation_of_plusFibre_tower C pi hfib
  have hs : IsSplitWitness C
      (picEtMap C (Over.testPoint
        (show (overSpec k P.cover.Carrier).left from p))
        (relPicToPicEt C (overSpec k P.cover.Carrier)
          (relPicMk C (overSpec k P.cover.Carrier) P.datum.cechPicClass))) := by
    simpa only [← P.datum_class] using hsplit p
  have hp : P.datum.HasWitnessH1Vanishing
      (Over.testPointField (T := overSpec k P.cover.Carrier) p) :=
    (hpres p).mpr hs
  letI : Algebra p.asIdeal.ResidueField
      (Over.testPointField (T := overSpec k P.cover.Carrier) p) :=
    ((Scheme.Spec.residueFieldIso (.of P.cover.Carrier) p).inv).hom.toAlgebra
  haveI : IsScalarTower P.cover.Carrier p.asIdeal.ResidueField
      (Over.testPointField (T := overSpec k P.cover.Carrier) p) :=
    IsScalarTower.of_algebraMap_eq'
      (algebraMap_testPointFieldAffine_factors p)
  exact (P.datum.hasWitnessH1Vanishing_iff_of_fieldExtension
    p.asIdeal.ResidueField
      (Over.testPointField (T := overSpec k P.cover.Carrier) p)).mpr hp

end PicRankOneNativeDatum

end AlgebraicGeometry
