/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.RankOneFamilyCertificates
import AlgebraicJacobian.Picard.DivisorDatumRankOne

/-!
# Arbitrary-ring stalk rank for a tied cocycle datum

This file separates the final rank computation from the Noetherian rigid engine.  Once the
displayed datum already has pair-`H^1` vanishing and finite projective `H^0`, its stalk rank is
computed over an arbitrary coefficient ring by the canonical datum base-change equivalence and
the fibre Riemann--Roch calculation.  The degree hypothesis is stated for the class of the same
datum after every field-valued coefficient extension, matching the native presentation input.
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

noncomputable local instance instOverCleftArbitraryRank :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

/-- The final datum-level rank calculation over an arbitrary coefficient ring.

The hypotheses are conclusions about `D.sheaf` and the class of the same `D`; in particular,
there is no Noetherian assumption and no separately chosen module. -/
theorem BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_pairH1
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
  haveI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  haveI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘
        Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  haveI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘
        Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
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
    rw [D.cechPicClass_baseChange]
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

/-- The arbitrary-ring rank calculation from the actual fibre-witness predicate.

`hpi` is used only to propagate the residue-field pair vanishings to pair-`H^1` over `B`; the
rank calculation is then the noetherian-free theorem above. -/
theorem BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one_of_fibreWitness
    (D : BasicOpenCocycleDatum C B pi)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (n : ℤ))
    (hW : D.FibreH1Witness)
    (hfinite : Module.Finite B (Sheaf.HModule D.sheaf 0))
    (hprojective : Module.Projective B (Sheaf.HModule D.sheaf 0))
    (hdegree : ∀ (L : Type u) [Field L] [Algebra k L] [Algebra B L]
      [IsScalarTower k B L],
      classDeg L (Scheme.CechPic.map (relCurveMap C B L) D.cechPicClass) = (n : ℤ)) :
    ∀ p : PrimeSpectrum B,
      Module.rankAtStalk (Sheaf.HModule D.sheaf 0) p = 1 := by
  have hfib : ∀ p : PrimeSpectrum B,
      Subsingleton ((datumPair D).H1 ⊗[B] p.asIdeal.ResidueField) := by
    intro p
    exact D.subsingleton_pairH1_tensor_of_fibreWitness hW p.asIdeal.ResidueField
  have hpair : Subsingleton (datumPair D).H1 :=
    D.datum_subsingleton_pairH1 hpi hfib
  exact D.rankAtStalk_hModule_zero_eq_one_of_pairH1 hchi hpair hfinite hprojective hdegree

end AlgebraicGeometry
