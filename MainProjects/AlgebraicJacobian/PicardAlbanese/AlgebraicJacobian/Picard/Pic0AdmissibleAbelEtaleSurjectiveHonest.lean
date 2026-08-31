/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelKernel
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveTarget
import AlgebraicJacobian.Picard.Pic0ChartPlusFibreProducer
import AlgebraicJacobian.Picard.Pic0ChartPlusFibreTower

/-!
# Honest affine data for the admissible Abel chart

This module honestifies an affine degree-zero Picard class over one etale presentation,
presents its fixed admissible chart twist by a basic-open cocycle datum, and obtains an
H1-vanishing witness at every prime of the presentation carrier from unconditional Pic0
coverage.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

set_option maxHeartbeats 1000000 in
-- The chosen chart unfolds the uniform coverage witnesses and their finiteness instances.
/-- The chart fixed inside the admissible Abel transformation covers every Pic0 class. -/
theorem chartLocus_admissibleAbelChart_eq_univ
    {T : Over (Spec (.of k))} (lam : pic0Subgroup C T) :
    chartLocus C (admissibleAbelChartIndex C)
      (admissibleAbelChartDivisor C) lam.1 = Set.univ := by
  classical
  letI : C.left.Over (Spec (.of k)) := .ofHom C.hom
  haveI : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.hom)
  haveI : IsIntegral C.left := isIntegral_left_of_geometricallyReduced C
  haveI : LocallyOfFiniteType (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType C.hom)
  haveI : QuasiCompact (C.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact C.hom)
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0) :=
    moduleFinite_hModule_zero C
  haveI : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1) :=
    moduleFinite_hModule_one C
  exact (exists_uniform_admissibleCoverageChart_eq_univ
    (C := C) (divRepAffP1Map_comp C) (genus C)
      (chi_moduleKSheaf C)).choose_spec.choose_spec.2 lam

/-- A datum witness at the scheme-theoretic test-point field descends across the canonical
residue-field isomorphism to the prime's algebraic residue field. -/
theorem BasicOpenCocycleDatum.hasWitnessH1Vanishing_residueField_of_testPointField
    {B : Type u} [CommRing B] [Algebra k B]
    {pi : C.left ⟶ P1 k} [IsFinite pi]
    (D : BasicOpenCocycleDatum C B pi) (p : PrimeSpectrum B)
    (hp : D.HasWitnessH1Vanishing
      (Over.testPointField (T := overSpec k B) p)) :
    D.HasWitnessH1Vanishing p.asIdeal.ResidueField := by
  letI : Algebra p.asIdeal.ResidueField
      (Over.testPointField (T := overSpec k B) p) :=
    ((Scheme.Spec.residueFieldIso (.of B) p).inv).hom.toAlgebra
  haveI : IsScalarTower B p.asIdeal.ResidueField
      (Over.testPointField (T := overSpec k B) p) :=
    IsScalarTower.of_algebraMap_eq'
      (algebraMap_testPointFieldAffine_factors p)
  exact (D.hasWitnessH1Vanishing_iff_of_fieldExtension
    p.asIdeal.ResidueField
      (Over.testPointField (T := overSpec k B) p)).mpr hp

set_option maxHeartbeats 1000000 in
-- Honestification and the full-locus chart elaborate a dependent datum presentation.
/-- An affine Pic0 class admits one etale presentation on whose carrier its admissible twist
is presented by a datum with an H1-vanishing witness at every prime. -/
theorem exists_admissibleAbelDatum_of_affine
    {A : Type u} [CommRing A] [Algebra k A]
    (lam : pic0Subgroup C (overSpec k A)) :
    ∃ (E : Algebra.EtaleCover A)
      (c : (relCurve C E.Carrier).CechPic)
      (D : BasicOpenCocycleDatum C E.Carrier (divRepAffP1Map C)),
      let g := Over.overSpecMap
        ((Algebra.ofId A E.Carrier).restrictScalars k)
      picEtMap C g lam.1 =
          relPicToPicEt C (overSpec k E.Carrier)
            (relPicMk C (overSpec k E.Carrier) c) ∧
        D.cechPicClass =
          c * Scheme.CechPic.map (relCurveMap C k E.Carrier)
            (chartTwistClass C (admissibleAbelChartIndex C)
              (admissibleAbelChartDivisor C)) ∧
        ∀ p : PrimeSpectrum E.Carrier,
          D.HasWitnessH1Vanishing p.asIdeal.ResidueField := by
  classical
  obtain ⟨E, x, hx⟩ : ∃ (E : Algebra.EtaleCover A) (x : descentClasses C E),
      picEtAffineEquiv C A lam.1 = PicEtAff.mk C E x := by
    induction picEtAffineEquiv C A lam.1 using PicEtAff.ind with
    | mk E x => exact ⟨E, x, rfl⟩
  obtain ⟨c, hc⟩ := relPicMk_surjective C (overSpec k E.Carrier)
    (x : relPic C (overSpec k E.Carrier))
  obtain ⟨D, hD⟩ :=
    exists_datum_cechPicClass_chartTwistClass
      (C := C) (π := divRepAffP1Map C) c
        (admissibleAbelChartIndex C) (admissibleAbelChartDivisor C)
  let g : overSpec k E.Carrier ⟶ overSpec k A :=
    Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k)
  have hpic : picEtMap C g lam.1 =
      relPicToPicEt C (overSpec k E.Carrier)
        (relPicMk C (overSpec k E.Carrier) c) := by
    calc
      picEtMap C g lam.1 =
          relPicToPicEt C (overSpec k E.Carrier)
            (x : relPic C (overSpec k E.Carrier)) :=
        picEtMap_eq_relPicToPicEt_of_affineRepresentative
          C lam.1 E x hx
      _ = _ := by rw [hc]
  refine ⟨E, c, D, hpic, hD, ?_⟩
  intro p
  have htwist :=
    chartTwist_picEtMap_eq_relPicToPicEt_cechPicClass
      lam g c hpic D (admissibleAbelChartIndex C)
        (admissibleAbelChartDivisor C) hD
  have hplus :
      IsChartDatumPlusFibre C (divRepAffP1Map C)
        (relPicToPicEt C (overSpec k E.Carrier)
          (relPicMk C (overSpec k E.Carrier) D.cechPicClass)) D :=
    isChartDatumPlusFibre_of_relPicToPicEt C (divRepAffP1Map C)
      D.cechPicClass D rfl
  have hpres : IsChartDatumPresentation C (divRepAffP1Map C)
      (chartTwist C (admissibleAbelChartIndex C)
        (admissibleAbelChartDivisor C) (overSpec k E.Carrier)
          (picEtMap C g lam.1)) D := by
    rw [htwist]
    exact isChartDatumPresentation_of_plusFibre_tower
      C (divRepAffP1Map C) hplus
  have hmem : p ∈ chartLocus C (admissibleAbelChartIndex C)
      (admissibleAbelChartDivisor C) (pic0Map C g lam).1 := by
    rw [chartLocus_admissibleAbelChart_eq_univ]
    trivial
  have hpTest : D.HasWitnessH1Vanishing
      (Over.testPointField (T := overSpec k E.Carrier) p) :=
    (mem_chartLocus_iff_hasWitnessH1Vanishing hpres p).mp hmem
  exact D.hasWitnessH1Vanishing_residueField_of_testPointField p hpTest

end

end AlgebraicGeometry
