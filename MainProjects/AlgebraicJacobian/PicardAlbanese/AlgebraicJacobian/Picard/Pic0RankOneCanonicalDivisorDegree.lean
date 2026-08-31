/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneDatumGluedDivisor
import AlgebraicJacobian.Picard.DivisorDatumRankOne
import AlgebraicJacobian.Cohomology.DatumDescent
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesFiniteStage
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Degree of a rank-one datum at a finite stage

This module isolates the reverse Riemann--Roch calculation used by the
Noetherian-free canonical rank-one divisor construction.  Rank one at every
residue fibre pins the degree there, and the residue-field law then extends to
arbitrary field-valued points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable local instance canonicalDegreeOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

noncomputable local instance (priority := 20000) canonicalDegreeOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance canonicalDegreeSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance canonicalDegreeIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance canonicalDegreeQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance canonicalDegreeFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance canonicalDegreeFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 2000000 in
-- The residue-fibre comparison expands the datum base-change and presentation sheaf isomorphisms.
set_option synthInstance.maxHeartbeats 800000 in
/-- Rank one at a stage prime forces the residue-fibre class to have degree `genus C`. -/
theorem stage_classDeg_residueField
    {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
    (D : BasicOpenCocycleDatum C R pi)
    (hH1 : Subsingleton (datumPair D).H1)
    [Module.Finite R (Sheaf.HModule D.sheaf 0)]
    [Module.Projective R (Sheaf.HModule D.sheaf 0)]
    (p : PrimeSpectrum R)
    (hrank : Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1) :
    classDeg p.asIdeal.ResidueField
      (Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField) D.cechPicClass)
      = (genus C : ℤ) := by
  rw [← D.cechPicClass_baseChange p.asIdeal.ResidueField]
  have hfibre : Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf = 1 := by
    have hcalc : Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p
        = Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf := by
      calc Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p
          = Module.finrank p.asIdeal.ResidueField
              (p.asIdeal.ResidueField ⊗[R] (Sheaf.HModule D.sheaf 0)) :=
            Module.rankAtStalk_eq p
        _ = Module.finrank p.asIdeal.ResidueField
              (Sheaf.HModule (D.baseChange p.asIdeal.ResidueField).sheaf 0) :=
            (D.datumH0BaseChange p.asIdeal.ResidueField hH1).finrank_eq
        _ = Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf := rfl
    rw [← hcalc, hrank]
  have hsub : Subsingleton
      (Sheaf.HModule (D.baseChange p.asIdeal.ResidueField).sheaf 1) :=
    D.datum_subsingleton_h1_baseChange p.asIdeal.ResidueField hH1
  set P : (relCurve C p.asIdeal.ResidueField).MeromorphicPresentation :=
    Scheme.MeromorphicPresentation.ofCocycle
      (D.baseChange p.asIdeal.ResidueField).pointedCover
      (gluedSubordCocycle (D.baseChange p.asIdeal.ResidueField).isGluingCocycle
        (D.baseChange p.asIdeal.ResidueField).pointedCover
        (D.baseChange p.asIdeal.ResidueField).pieceIndex
        fun _ => le_rfl) with hP
  have hsubP : Subsingleton (Sheaf.HModule (P.gluedSheaf p.asIdeal.ResidueField) 1) :=
    (Sheaf.HModule.mapEquiv
      (BasicOpenCocycleDatum.presentationSheafIso
        (D.baseChange p.asIdeal.ResidueField))
      1).toEquiv.subsingleton_congr.mp hsub
  have h0eq : Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf
      = Sheaf.h0 (P.gluedSheaf p.asIdeal.ResidueField) :=
    Sheaf.h0_congr (BasicOpenCocycleDatum.presentationSheafIso
      (D.baseChange p.asIdeal.ResidueField))
  have hformula := h0_gluedSheaf_eq_classDeg_add_chi p.asIdeal.ResidueField P hsubP
  have hPclass : P.picClass = (D.baseChange p.asIdeal.ResidueField).cechPicClass := rfl
  have hchi : Sheaf.chi ((relCurve C p.asIdeal.ResidueField).moduleKSheaf
      p.asIdeal.ResidueField) = 1 - (genus C : ℤ) :=
    chi_relCurve (chi_moduleKSheaf C) p.asIdeal.ResidueField
  have h1 : ((Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf : ℕ) : ℤ)
      = classDeg p.asIdeal.ResidueField
          (D.baseChange p.asIdeal.ResidueField).cechPicClass
        + (1 - (genus C : ℤ)) := by
    rw [h0eq, hformula, hPclass, hchi]
  rw [hfibre] at h1
  push_cast at h1
  linarith

set_option maxHeartbeats 1000000 in
-- The residue-field lift synthesizes two scalar towers through a localized quotient.
set_option synthInstance.maxHeartbeats 400000 in
/-- A residue-field degree law extends to every field-valued point of the stage. -/
theorem stage_classDeg_field
    {R : Type u} [CommRing R] [Algebra k R]
    (D : BasicOpenCocycleDatum C R pi)
    (hres : ∀ p : PrimeSpectrum R,
      classDeg p.asIdeal.ResidueField
        (Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField) D.cechPicClass)
        = (genus C : ℤ))
    (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K] :
    classDeg K (Scheme.CechPic.map (relCurveMap C R K) D.cechPicClass)
      = (genus C : ℤ) := by
  classical
  haveI hker : (RingHom.ker (algebraMap R K)).IsPrime := RingHom.ker_isPrime _
  set p : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R K), hker⟩ with hpdef
  have hcompl : p.asIdeal.primeCompl ≤
      (IsUnit.submonoid K).comap (IsScalarTower.toAlgHom k R K) := by
    intro x hx
    rw [Submonoid.mem_comap]
    exact isUnit_iff_ne_zero.mpr fun h0 => hx (RingHom.mem_ker.mpr h0)
  let rho : p.asIdeal.ResidueField →ₐ[k] K :=
    Ideal.ResidueField.liftₐ p.asIdeal (IsScalarTower.toAlgHom k R K) le_rfl hcompl
  letI : Algebra p.asIdeal.ResidueField K := rho.toRingHom.toAlgebra
  haveI : IsScalarTower k p.asIdeal.ResidueField K :=
    .of_algebraMap_eq fun x => (rho.commutes x).symm
  haveI : IsScalarTower R p.asIdeal.ResidueField K :=
    .of_algebraMap_eq fun x =>
      (Ideal.ResidueField.liftₐ_algebraMap p.asIdeal
        (IsScalarTower.toAlgHom k R K) le_rfl hcompl x).symm
  have hcurve : (C ◁ Over.overSpecMap rho).left
      = relCurveMap C p.asIdeal.ResidueField K := by
    refine congrArg
      (fun t : overSpec k K ⟶ overSpec k p.asIdeal.ResidueField =>
        (C ◁ t).left) ?_
    exact Over.OverMorphism.ext rfl
  have hinv := classDeg_cechPicMap_baseFieldTransition C rho
    (Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField) D.cechPicClass)
  rw [hcurve] at hinv
  calc classDeg K (Scheme.CechPic.map (relCurveMap C R K) D.cechPicClass)
      = classDeg K (Scheme.CechPic.map (relCurveMap C p.asIdeal.ResidueField K)
          (Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField)
            D.cechPicClass)) := by
        rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, relCurveMap_comp]
    _ = classDeg p.asIdeal.ResidueField
          (Scheme.CechPic.map (relCurveMap C R p.asIdeal.ResidueField)
            D.cechPicClass) := hinv
    _ = (genus C : ℤ) := hres p

set_option maxHeartbeats 2000000 in
-- The composition crosses the residue-field comparison and its scalar-tower lift.
set_option synthInstance.maxHeartbeats 800000 in
/-- Finite-projective rank-one certificates force the degree law at every field-valued point. -/
theorem stage_classDeg_all_fields
    {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
    (D : BasicOpenCocycleDatum C R pi)
    (hH1 : Subsingleton (datumPair D).H1)
    (cert : RankOneFamilyCertificates D) :
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K]
      [IsScalarTower k R K],
      classDeg K (Scheme.CechPic.map (relCurveMap C R K) D.cechPicClass)
        = (genus C : ℤ) := by
  letI : Module.Finite R (Sheaf.HModule D.sheaf 0) := cert.h0_finite
  letI : Module.Projective R (Sheaf.HModule D.sheaf 0) := cert.h0_projective
  intro K _ _ _ _
  exact stage_classDeg_field pi D
    (fun p => stage_classDeg_residueField pi D hH1 p (cert.h0_rank_one p)) K

end AlgebraicGeometry
