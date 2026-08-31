/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Cohomology.DatumDescent
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificates
import AlgebraicJacobian.Picard.DivisorDatumRankOne

/-!
# Arbitrary-ring production of rank-one family certificates

The rigid engine is Noetherian, but the public certificate is not.  This file applies the engine
to a genuine finitely generated descent datum and transports its conclusions back to the original
unrestricted coefficient ring by the canonical datum H0 base-change equivalence.
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

namespace RankOneFamilyCertificates

variable {D : BasicOpenCocycleDatum C B pi}

/- The standard base-change geometry is keyed by the structure morphism supplied by
`relCurve.instOver`; re-key it locally so the rank theorem sees the same `Over` object. -/
noncomputable local instance (priority := 20000) rankOneCertificateOver
    (L : Type u) [Field L] [Algebra k L] :
    (relCurve C L).Over (Spec (.of L)) :=
  instOverBaseChange C L

noncomputable local instance rankOneCertificateSmooth
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance rankOneCertificateIntegral
    (L : Type u) [Field L] [Algebra k L] :
    IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance rankOneCertificateQuasiCompact
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance rankOneCertificateFiniteH0
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance rankOneCertificateFiniteH1
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Construct the certificate package after a genuine finitely generated descent stage.

`hW0` is the fibre-divisor/H1 antecedent at the stage and `hdegree` is the corresponding
class-degree calculation.  Neither field mentions the desired global H1/H0/rank conclusions.
The Noetherian instance is created only for `B0`; the result is over the original, unrestricted
ring `B` by the canonical datum base-change equivalence. -/
noncomputable def ofDescentStage
    {B0 : Subalgebra k B} (hfg : B0.FG)
    (D0 : BasicOpenCocycleDatum C (B0 : Type u) pi)
    (hbc : D0.baseChange (B' := B) = D)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hW0 : D0.FibreH1Witness)
    (hdegree : forall p : PrimeSpectrum (B0 : Type u),
      classDeg p.asIdeal.ResidueField
        (D0.baseChange p.asIdeal.ResidueField).cechPicClass = (genus C : Int)) :
    RankOneFamilyCertificates D := by
  subst D
  letI : IsNoetherianRing (B0 : Type u) := hfg.isNoetherianRing
  have hfib : forall p : PrimeSpectrum (B0 : Type u),
      Subsingleton ((datumPair D0).H1 ⊗[B0] p.asIdeal.ResidueField) := by
    intro p
    exact D0.subsingleton_pairH1_tensor_of_fibreWitness hW0 p.asIdeal.ResidueField
  obtain ⟨h1, hfinite, hprojective⟩ :=
    BasicOpenCocycleDatum.descentRigidEngine hfg D0 hpi hfib
  have hpair : Subsingleton (datumPair D0).H1 :=
    (subsingleton_datumPair_h1_iff D0).mpr h1
  have hrank : forall p : PrimeSpectrum (B0 : Type u),
      Module.rankAtStalk (Sheaf.HModule D0.sheaf 0) p = 1 := by
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
    exact BasicOpenCocycleDatum.rankAtStalk_hModule_zero_eq_one D0 (n := genus C) hpi
      (chi_moduleKSheaf C) hfib p (hdegree p)
  let Q := Sheaf.HModule D0.sheaf 0
  letI : Module.Finite (B0 : Type u) Q := hfinite
  letI : Module.Projective (B0 : Type u) Q := hprojective
  let e : B ⊗[B0] Q ≃ₗ[B]
      Sheaf.HModule (D0.baseChange (B' := B)).sheaf 0 :=
    D0.datumH0BaseChange B hpair
  letI : Module.Finite B (B ⊗[B0] Q) := by infer_instance
  letI : Module.Projective B (B ⊗[B0] Q) := by infer_instance
  refine {
    h1_vanishing := D0.datum_subsingleton_h1_baseChange B hpair
    h0_finite := Module.Finite.equiv e
    h0_projective := Module.Projective.of_equiv e
    h0_rank_one := ?_ }
  intro p
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange]
  exact hrank (p.comap (algebraMap (B0 : Type u) B))

end RankOneFamilyCertificates

end AlgebraicGeometry
