/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorDegree
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageCert

/-!
# Admissibility of a finite rank-one stage

This module packages the two polymorphic inputs of the glued-divisor keystone at a fixed
Noetherian stage: fibrewise `H^1` vanishing and the degree law at every field-valued point.
Keeping this construction opaque prevents downstream divisor descent from re-elaborating the
finite-stage rank and reverse Riemann--Roch proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance stageAdmissibilityOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

noncomputable local instance (priority := 20000) stageAdmissibilityOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance stageAdmissibilitySmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance stageAdmissibilityIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance stageAdmissibilityQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance stageAdmissibilityFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance stageAdmissibilityFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

namespace PicRankOneNoetherianStage

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
variable {P : PicRankOneLocalPresentation pi lam}

/-- The fibre-vanishing and degree inputs needed to construct a divisor at a finite stage. -/
structure Admissibility (S : PicRankOneNoetherianStage P) : Prop where
  h1 : ∀ p : PrimeSpectrum S.A0,
    (S.D0.baseChange S.A0).HasWitnessH1Vanishing p.asIdeal.ResidueField
  degree : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra S.A0 K]
    [IsScalarTower k S.A0 K],
    classDeg K (Scheme.CechPic.map (relCurveMap C S.A0 K)
      (S.D0.baseChange S.A0).cechPicClass) = (genus C : ℤ)

set_option maxHeartbeats 4000000 in
-- The result combines the opaque stage certificates with the polymorphic residue-field degree law.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every finite rank-one stage is admissible for the glued-divisor keystone. -/
theorem admissibility (S : PicRankOneNoetherianStage P)
    (hpi : pi ≫ P1.structureMap k = C.hom) : S.Admissibility := by
  letI : IsNoetherianRing S.A0 := S.hAnoeth
  letI : Subsingleton (datumPair (S.D0.baseChange S.A0)).H1 := S.hpair
  have hwit : ∀ p : PrimeSpectrum S.A0,
      (S.D0.baseChange S.A0).HasWitnessH1Vanishing p.asIdeal.ResidueField :=
    fun p => ((S.D0.baseChange S.A0).hasWitnessH1Vanishing_iff_subsingleton
      p.asIdeal.ResidueField).mpr inferInstance
  have cert : RankOneFamilyCertificates (S.D0.baseChange S.A0) := S.certificates hpi
  exact ⟨hwit, stage_classDeg_all_fields pi (S.D0.baseChange S.A0) S.hpair cert⟩

end PicRankOneNoetherianStage

end AlgebraicGeometry
