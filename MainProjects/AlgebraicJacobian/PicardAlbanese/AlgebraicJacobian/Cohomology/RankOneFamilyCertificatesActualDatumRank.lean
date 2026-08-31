/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.RankOneFamilyCertificates
import AlgebraicJacobian.Picard.DivisorDatumRankOne

/-!
# Arbitrary-ring rank for the displayed cocycle datum

This file computes the stalk rank of the actual datum over an arbitrary coefficient ring once
pair `H^1` vanishing and finite projective `H^0` have been established.  Its degree hypothesis is
the fibrewise degree law for the class of that same datum, rather than for an auxiliary module or
an unrelated family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable local instance instOverCleftActualDatumRank :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/- The degree stack and `relCurve.instOver` use extensionally equal structure maps under
different instance keys.  Re-key the canonical base-change package before stating the
field-valued degree hypothesis. -/
noncomputable local instance (priority := 20000) actualDatumRankOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance actualDatumRankSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance actualDatumRankIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance actualDatumRankQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance actualDatumRankFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance actualDatumRankFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- Compute rank one on the displayed datum without a Noetherian hypothesis on its coefficient
ring.  The finite projective module is exactly `H⁰(D.sheaf)`, and every fibre degree is taken
from `D.cechPicClass`. -/
theorem BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_actualPairH1
    (D : BasicOpenCocycleDatum C B pi)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hpair : Subsingleton (datumPair D).H1)
    (hfinite : Module.Finite B (Sheaf.HModule D.sheaf 0))
    (hprojective : Module.Projective B (Sheaf.HModule D.sheaf 0))
    (hdegree : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra B L]
      [IsScalarTower k B L],
      classDeg L (Scheme.CechPic.map (relCurveMap C B L) D.cechPicClass) = (n : ℤ)) :
    ∀ p : PrimeSpectrum B,
      Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 := by
  letI : Module.Finite B (Sheaf.HModule D.sheaf 0) := hfinite
  letI : Module.Projective B (Sheaf.HModule D.sheaf 0) := hprojective
  intro p
  letI : (relCurve C p.asIdeal.ResidueField).Over
      (Spec (.of p.asIdeal.ResidueField)) :=
    instOverBaseChange C p.asIdeal.ResidueField
  haveI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  haveI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘ Spec (.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  haveI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘ Spec (.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule
        ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 0) :=
    instModuleFiniteHModuleZeroBaseChange C p.asIdeal.ResidueField
  haveI : Module.Finite p.asIdeal.ResidueField
      (Sheaf.HModule
        ((relCurve C p.asIdeal.ResidueField).moduleKSheaf p.asIdeal.ResidueField) 1) :=
    instModuleFiniteHModuleOneBaseChange C p.asIdeal.ResidueField
  have hdegreep : classDeg p.asIdeal.ResidueField
      (D.baseChange p.asIdeal.ResidueField).cechPicClass = (n : ℤ) := by
    rw [D.cechPicClass_baseChange p.asIdeal.ResidueField]
    exact hdegree p.asIdeal.ResidueField
  have hfibre : Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf = 1 :=
    D.h0_sheaf_baseChange_eq_one hchi p.asIdeal.ResidueField hdegreep
      (D.datum_subsingleton_h1_baseChange p.asIdeal.ResidueField hpair)
  calc Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p
      = Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[B] (Sheaf.HModule D.sheaf 0)) :=
        Module.rankAtStalk_eq p
    _ = Module.finrank p.asIdeal.ResidueField
          (Sheaf.HModule (D.baseChange p.asIdeal.ResidueField).sheaf 0) :=
        (D.datumH0BaseChange p.asIdeal.ResidueField hpair).finrank_eq
    _ = Sheaf.h0 (D.baseChange p.asIdeal.ResidueField).sheaf := rfl
    _ = 1 := hfibre

end AlgebraicGeometry
