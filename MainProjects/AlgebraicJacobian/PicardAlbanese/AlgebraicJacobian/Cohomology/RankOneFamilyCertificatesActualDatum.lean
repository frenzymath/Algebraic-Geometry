/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesActualDatumRank
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesDescent
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificatesFiniteStage
import AlgebraicJacobian.Cohomology.RigidEngine2Nakayama
import AlgebraicJacobian.Cohomology.RigidEngine4Assembly

/-!
# Rank-one certificates for the displayed arbitrary-affine datum

This file removes the caller-chosen descent stage from the certificate producer.  Starting with
the displayed cocycle datum, it descends that datum to a finite stage, refines the stage until
the actual pair `H^1` vanishes, runs the Noetherian rigid engine only there, and transports finite
projective `H^0` back to the original coefficient ring.  Stalk rank is then computed on the
original datum, so the degree law is never required away from the displayed family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable local instance actualDatumOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/- Re-key the canonical field base-change package for the degree predicate. -/
noncomputable local instance (priority := 20000) actualDatumDegreeOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance actualDatumDegreeSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance actualDatumDegreeIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance actualDatumDegreeQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance actualDatumDegreeFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance actualDatumDegreeFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-! ## Geometric inputs on the displayed datum -/

/-- Residue-field divisor witnesses for the displayed cocycle datum. -/
abbrev BasicOpenCocycleDatum.ResidueH1Witness
    (D : BasicOpenCocycleDatum C B pi) : Prop :=
  ∀ p : PrimeSpectrum B,
    D.HasWitnessH1Vanishing p.asIdeal.ResidueField

/-- The fibrewise degree law for the class of the displayed cocycle datum. -/
abbrev BasicOpenCocycleDatum.FibreClassDegree
    (D : BasicOpenCocycleDatum C B pi) (n : ℕ) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra k L] [Algebra B L]
    [IsScalarTower k B L],
    classDeg L (Scheme.CechPic.map (relCurveMap C B L) D.cechPicClass) = (n : ℤ)

namespace RankOneFamilyCertificates

set_option maxHeartbeats 2000000 in
-- Finite-stage refinement and its scalar-extension equivalences need a larger budget.
set_option synthInstance.maxHeartbeats 800000 in
-- The same construction synthesizes two nontrivial scalar-tower module structures.
/-- Produce all four certificates for the displayed datum over an arbitrary coefficient ring.

The only H1 input is a divisor witness on each residue field.  It first gives pair-H1
vanishing for the displayed datum.  A finite presentation of that datum is then refined until
the same pair-H1 vanishing holds at the stage itself; the Noetherian rigid engine is used only
at that stage.  Its finite-projective H0 is transported back canonically, and rank one is
computed on the displayed datum from its own class-degree law. -/
noncomputable def ofActualDatum
    (D : BasicOpenCocycleDatum C B pi)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hW : D.ResidueH1Witness)
    (hdegree : D.FibreClassDegree (genus C)) :
    RankOneFamilyCertificates D := by
  have hfib : ∀ p : PrimeSpectrum B,
      Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) := by
    intro p
    exact (D.hasWitnessH1Vanishing_iff_subsingleton p.asIdeal.ResidueField).mp (hW p)
  have hpair : Subsingleton (datumPair D).H1 :=
    by
      letI := D.moduleFinite_aeval'_pair_t₀ hpi
      letI := D.moduleFinite_aeval'_pair_t₁ hpi
      letI : Module.Finite B (datumPair D).H1 :=
        (datumPair D).moduleFinite_h1
      exact
        AlgebraicJacobian.RigidEngine.subsingleton_of_forall_subsingleton_residueField_tensor
          hfib
  have h1 : Subsingleton (Sheaf.HModule D.sheaf 1) :=
    (subsingleton_datumPair_h1_iff D).mp hpair

  obtain ⟨B0, hB0fg, D0, hD0⟩ := D.exists_fg_subalgebra_baseChange_eq
  have hpairBase : Subsingleton (datumPair (D0.baseChange (B' := B))).H1 := by
    rw [hD0]
    exact hpair
  have htensor : Subsingleton ((datumPair D0).H1 ⊗[B0] B) :=
    D0.subsingleton_h1_tensor_of_baseChange B hpairBase
  obtain ⟨A, _, _, hAnoeth, hpairA, hAA⟩ :=
    BasicOpenCocycleDatum.exists_fg_pairH1_vanishing_stage
      (C := C) (pi := pi) B0 hB0fg D0 hpi htensor

  letI : IsNoetherianRing A := hAnoeth
  letI : Subsingleton (datumPair (D0.baseChange A)).H1 := hpairA
  have hfibA : ∀ p : PrimeSpectrum A,
      Subsingleton
        ((datumPair (D0.baseChange A)).H1 ⊗[A] p.asIdeal.ResidueField) := by
    intro p
    infer_instance
  letI := (D0.baseChange A).moduleFinite_aeval'_pair_t₀ hpi
  letI := (D0.baseChange A).moduleFinite_aeval'_pair_t₁ hpi
  letI := (D0.baseChange A).projective_sections₀
  letI := (D0.baseChange A).projective_sections₁
  letI := (D0.baseChange A).projective_sectionsInf
  letI : Module.Projective A
      (((D0.baseChange A).sheaf.obj.obj
          (op (relCover C A (fiberTwoCover pi)).V₀)) ×
        ((D0.baseChange A).sheaf.obj.obj
          (op (relCover C A (fiberTwoCover pi)).V₁))) :=
    Module.Projective.prod
  obtain ⟨_, hfiniteA, hprojectiveA⟩ :=
    (D0.baseChange A).pairData.rigidEngine
      (relCover_isAffineOpen₀ C A (fiberTwoCover pi))
      (relCover_isAffineOpen₁ C A (fiberTwoCover pi))
      (relCover_sup C A (fiberTwoCover pi)) hfibA

  have hbase : (D0.baseChange A).baseChange B = D := hAA.trans hD0
  let Q := Sheaf.HModule (D0.baseChange A).sheaf 0
  letI : Module.Finite A Q := hfiniteA
  letI : Module.Projective A Q := hprojectiveA
  let e : B ⊗[A] Q ≃ₗ[B] Sheaf.HModule D.sheaf 0 :=
    ((D0.baseChange A).datumH0BaseChange B hpairA).trans
      (Sheaf.HModule.mapEquiv
        (eqToIso (congrArg
          (fun E : BasicOpenCocycleDatum C B pi => E.sheaf) hbase)) 0)
  letI : Module.Finite B (B ⊗[A] Q) := by infer_instance
  letI : Module.Projective B (B ⊗[A] Q) := by infer_instance
  have hfinite : Module.Finite B (Sheaf.HModule D.sheaf 0) :=
    Module.Finite.equiv e
  have hprojective : Module.Projective B (Sheaf.HModule D.sheaf 0) :=
    Module.Projective.of_equiv e
  have hrank : ∀ p : PrimeSpectrum B,
      Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 :=
    D.rankAtStalk_hModule_zero_eq_one_of_actualPairH1
      (n := genus C) (chi_moduleKSheaf C) hpair hfinite hprojective hdegree
  exact ⟨h1, hfinite, hprojective, hrank⟩

end RankOneFamilyCertificates

end AlgebraicGeometry
