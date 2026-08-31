/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeAdaptationFibreRegular
import AlgebraicJacobian.Picard.DivSchemeFibrePointRead
import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseFibreCore
import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseGenerator
import AlgebraicJacobian.Picard.DivisorFamilyZarKit

/-!
# Pulled pointwise-seed equations on residue fibres

This file identifies the germ of the pulled presentation equation associated to the
pointwise generator seed with the canonical residue-fibre window reading.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- The raw residue-fibre pullback of a generator seed's local equations. Its regularity comes
directly from the seed's fibre-regularity clause, without a divisor adaptation or certificate. -/
noncomputable def residueFibreLocalEquations (D : ThetaGeneratorSeed C R pi a K)
    (hD : D.IsGenerator) (p : PrimeSpectrum R) :
    (relCurve C p.asIdeal.ResidueField).LocalEquations :=
  (D.localEquations hD).pullback (relCurveMap C R p.asIdeal.ResidueField)
    (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self
      _ _ fun z => D.germ_self_pullbackEqn_mem_nonZeroDivisors hD p z)

end ThetaGeneratorSeed

namespace PointwiseAchiever

section SeedContext

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftPulledDegree :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

noncomputable local instance instIsIntegralRelCurvePulledDegree
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePulledDegree
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePulledDegree
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePulledDegree
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

local notation "RZ" => seedChartRing C hpi g r1 r2 b1 b2 i j

set_option maxHeartbeats 8000000 in
-- The dependent seed, local-equation cover, and residue-field germ elaborate together.
set_option synthInstance.maxHeartbeats 800000 in
/-- The pulled local equation of the pointwise generator seed reads, at the canonical
residue-fibre point, as the compared pointwise window vector. -/
theorem germ_pullbackEqn_pointwiseGeneratorSeed_eq_pointwiseFibreReadGerm
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (z : relCurve C RZ) :
    let p := relCurveBasePoint C RZ z
    let K := p.asIdeal.ResidueField
    let zK := relCurveResiduePoint C RZ z
    let D := pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn
    let hD := isGenerator_pointwiseGeneratorSeed
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn
    ((relCurve C K).presheaf.germ
        (((D.localEquations hD).cover.pullback (relCurveMap C RZ K)).opens zK) zK
        (((D.localEquations hD).cover.pullback
          (relCurveMap C RZ K)).mem_opens zK)).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C RZ K) (D.localEquations hD) zK) =
      pointwiseFibreReadGerm C hpi g r1 r2 b1 b2 i j z
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z) := by
  dsimp only
  let p := relCurveBasePoint C RZ z
  let K := p.asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let D := pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn
  let hD := isGenerator_pointwiseGeneratorSeed
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn
  have hbase : (relCurveMap C RZ K).base zK = z := by
    simpa only [K, p, zK] using relCurveMap_relCurveResiduePoint C RZ z
  have hzPiece : zK ∈ (relCurve C K).basicOpen
      (relPinnedSectionsMap C RZ K pi (D.side z) (D.h z)) := by
    rw [relPinnedSectionsMap_basicOpen]
    change (relCurveMap C RZ K).base zK ∈ (relCurve C RZ).basicOpen (D.h z)
    rw [hbase]
    exact D.mem_basicOpen z
  have hzSide : zK ∈ relPinnedChart C K pi (D.side z) := by
    change zK ∈ relPinnedChart C K pi
      (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
    simpa only [K, p, zK] using relCurveResiduePoint_mem_relPinnedChart C RZ
      (π := pi) (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
      (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
  have hpull := D.germ_self_pullbackEqn_eq_germ_relPinnedSectionsMap_of_map_eq
    hD p zK z hbase hzPiece hzSide
  rw [hpull]
  convert germ_relPinnedSectionsMap_relThetaResSide_windowEquiv_at_relCurveResiduePoint
    C RZ (π := pi) (windowM_choice pi hpi g)
    (relThetaPairH1_windowM C pi hpi g)
    (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
    (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
    (pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z) using 1 <;> rfl

set_option maxHeartbeats 8000000 in
-- The residue-field germ, theta trivialization, and valuation dictionaries elaborate
-- simultaneously in this coefficient comparison.
set_option synthInstance.maxHeartbeats 800000 in
/-- A residue-fibre local-equation system whose self-germ is the pointwise seed reading
has the same coefficient as the universal fibre divisor at the canonical residue point. -/
theorem coeffAt_presentationDivisor_eq_divUniversalSeedFibreDivisor_of_germ_eq
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (d : (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).LocalEquations)
    (hgerm :
      ((relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).presheaf.germ
        (d.cover.opens (relCurveResiduePoint C RZ z)) (relCurveResiduePoint C RZ z)
        (d.cover.mem_opens (relCurveResiduePoint C RZ z))).hom
        (d.eqn (relCurveResiduePoint C RZ z)) =
      pointwiseFibreReadGerm C hpi g r1 r2 b1 b2 i j z
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z)) :
    coeffAt hzg (Scheme.presentationDivisor
        (relCurveBasePoint C RZ z).asIdeal.ResidueField d.presentation) =
      coeffAt hzg (divUniversalSeedFibreDivisor
        C hpi g r1 r2 b1 b2 i j hO hchi (relCurveBasePoint C RZ z)) := by
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let M := windowM_choice pi hpi g
  let v := pointwiseSectionVector C hpi g r1 r2 b1 b2 i j hO hchi z
  let s : relThetaSections C K pi M :=
    relThetaWindowEquiv C K pi M (relThetaPairH1_windowM C pi hpi g)
      (windowCompare RZ K v)
  have hzK : zK ∈ relPinnedChart C K pi
      (pointwiseSide C hpi g r1 r2 b1 b2 i j z) := by
    simpa only [K, zK] using relCurveResiduePoint_mem_relPinnedChart C RZ
      (π := pi) (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
      (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
  obtain ⟨hr, hzero⟩ := pointwiseSectionVector_fibreCoefficient_eq_zero
    C hpi g r1 r2 b1 b2 i j hO hchi z hzg
  have hphi : divFamPhi C K pi M (relThetaPairH1_windowM C pi hpi g)
      (windowCompare RZ K v) =
        (thetaFieldShiftUnit C K pi M : (relCurve C K).functionField) *
          thetaFieldRead C K pi M s := by
    rfl
  have ht : thetaFieldRead C K pi M s ≠ 0 := by
    intro ht0
    apply hr
    rw [hphi, ht0, mul_zero]
  let t : (relCurve C K).functionFieldˣ := Units.mk0 _ ht
  have hphiU : Units.mk0
      (divFamPhi C K pi M (relThetaPairH1_windowM C pi hpi g)
        (windowCompare RZ K v)) hr = thetaFieldShiftUnit C K pi M * t := by
    apply Units.ext
    exact hphi
  have hzero' := hzero
  change coeffAt hzg
      ((windowN C K hpi g - divUniversalSeedFibreDivisor
          C hpi g r1 r2 b1 b2 i j hO hchi (relCurveBasePoint C RZ z)) +
        Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0
            (divFamPhi C K pi M (relThetaPairH1_windowM C pi hpi g)
              (windowCompare RZ K v)) hr)) = 0 at hzero'
  rw [hphiU, Scheme.divOf_mul,
    ← divOf_thetaFieldShiftUnit C K pi M] at hzero'
  change coeffAt hzg
      ((windowTransportDivisor C K pi M - divUniversalSeedFibreDivisor
          C hpi g r1 r2 b1 b2 i j hO hchi (relCurveBasePoint C RZ z)) +
        ((thetaFieldDivisor C K pi M - windowTransportDivisor C K pi M) +
          Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K)) t)) = 0 at hzero'
  simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub] at hzero'
  have hbalance : coeffAt hzg (thetaFieldDivisor C K pi M) +
      coeffAt hzg (Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K)) t) =
        coeffAt hzg (divUniversalSeedFibreDivisor
          C hpi g r1 r2 b1 b2 i j hO hchi (relCurveBasePoint C RZ z)) := by
    omega
  have hgermSide :
      ((relCurve C K).presheaf.germ (d.cover.opens zK) zK
        (d.cover.mem_opens zK)).hom (d.eqn zK) =
      ((relCurve C K).presheaf.germ (relPinnedChart C K pi
          (pointwiseSide C hpi g r1 r2 b1 b2 i j z)) zK hzK).hom
        (relThetaResSide M (pointwiseSide C hpi g r1 r2 b1 b2 i j z) le_rfl s) := by
    simpa only [K, zK, M, v, s, pointwiseFibreReadGerm] using hgerm
  obtain ⟨w, hw⟩ := exists_unit_germ_relThetaResSide_eq C K pi M
    (pointwiseSide C hpi g r1 r2 b1 b2 i j z) le_rfl hzK
  have helem : d.presentation.elem zK =
      Units.map (algebraMap ((relCurve C K).presheaf.stalk zK)
        (relCurve C K).functionField).toMonoidHom w *
        ((thetaFieldPresentation C K pi M).elem zK * t) := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map]
    rw [Scheme.LocalEquations.presentation_elem_val,
      Scheme.germ_generic_eq_algebraMap_germ
        (d.cover.genericPoint_mem_opens zK) (d.cover.mem_opens zK) (d.eqn zK),
      hgermSide, hw s, map_mul,
      algebraMap_germ_thetaFieldGluedEquiv_eq C K pi M s zK]
    rfl
  have helem' : d.presentation.elem zK =
      ((thetaFieldPresentation C K pi M).elem zK * t) *
        Units.map (algebraMap ((relCurve C K).presheaf.stalk zK)
          (relCurve C K).functionField).toMonoidHom w := by
    rw [helem, mul_comm]
  rw [Scheme.coeffAt_presentationDivisor, helem',
    Scheme.toAdd_ordZ_mul_unitsMap_stalk K hzg,
    map_mul, toAdd_mul,
    ← Scheme.coeffAt_presentationDivisor K (thetaFieldPresentation C K pi M) hzg,
    ← Scheme.CurveDivisor.coeffAt_divOf
      (relCurve C K ↘ Spec (CommRingCat.of K)) t hzg]
  simpa only [thetaFieldDivisor] using hbalance

set_option maxHeartbeats 8000000 in
-- The raw residue pullback and the pointwise germ bridge carry the dependent residue-field tower.
set_option synthInstance.maxHeartbeats 800000 in
/-- The certificate-free residue-fibre pullback of the pointwise generator seed has the universal
fibre-divisor coefficient at the canonical residue point. -/
theorem coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    coeffAt hzg (Scheme.presentationDivisor
        (relCurveBasePoint C RZ z).asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
          (isGenerator_pointwiseGeneratorSeed
            C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
          (relCurveBasePoint C RZ z)).presentation)) =
      coeffAt hzg (divUniversalSeedFibreDivisor
        C hpi g r1 r2 b1 b2 i j hO hchi (relCurveBasePoint C RZ z)) := by
  apply coeffAt_presentationDivisor_eq_divUniversalSeedFibreDivisor_of_germ_eq
    C hpi g r1 r2 b1 b2 i j hO hchi z hzg
  change
    ((relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).presheaf.germ
      ((((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)).cover.pullback
          (relCurveMap C RZ
            (relCurveBasePoint C RZ z).asIdeal.ResidueField)).opens
        (relCurveResiduePoint C RZ z)) (relCurveResiduePoint C RZ z)
      (((((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)).cover.pullback
          (relCurveMap C RZ
            (relCurveBasePoint C RZ z).asIdeal.ResidueField)).mem_opens
        (relCurveResiduePoint C RZ z)))).hom
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField)
        ((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
          (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn))
        (relCurveResiduePoint C RZ z)) = _
  exact germ_pullbackEqn_pointwiseGeneratorSeed_eq_pointwiseFibreReadGerm
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn z

set_option maxHeartbeats 8000000 in
-- Reindexing transports the residue field, point, and both divisor coefficients dependently.
set_option synthInstance.maxHeartbeats 800000 in
/-- The certificate-free pointwise-seed presentation and the universal fibre divisor have equal
coefficients at every closed point of every residue fibre. -/
theorem coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_at
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ) {x : relCurve C p.asIdeal.ResidueField}
    (hxg : x ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    coeffAt hxg (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
          (isGenerator_pointwiseGeneratorSeed
            C hpi g r1 r2 b1 b2 i j hO hchi hrdn) p).presentation)) =
      coeffAt hxg (divUniversalSeedFibreDivisor
        C hpi g r1 r2 b1 b2 i j hO hchi p) := by
  generalize hz : (relCurveMap C RZ p.asIdeal.ResidueField).base x = z
  have hp : relCurveBasePoint C RZ z = p :=
    hz ▸ relCurveBasePoint_relCurveMap_residueField C RZ p x
  have hxcast : Eq.ndrec
      (motive := fun q : PrimeSpectrum RZ => relCurve C q.asIdeal.ResidueField)
      (relCurveResiduePoint C RZ z) hp = x := by
    subst z
    exact relCurveResiduePoint_map_cast C RZ p x
  clear hz
  subst p
  have hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) := by
    simpa only [hxcast] using hxg
  subst x
  exact
    coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn z hzg

set_option maxHeartbeats 8000000 in
-- Extensionality ranges over the dependently indexed closed points of the residue curve.
set_option synthInstance.maxHeartbeats 800000 in
/-- On every residue fibre, the certificate-free pointwise-seed presentation divisor is the
universal fibre divisor. -/
theorem presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed_eq
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ) :
    Scheme.presentationDivisor p.asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
          (isGenerator_pointwiseGeneratorSeed
            C hpi g r1 r2 b1 b2 i j hO hchi hrdn) p).presentation) =
      divUniversalSeedFibreDivisor C hpi g r1 r2 b1 b2 i j hO hchi p := by
  refine CurveDivisor.ext_coeffAt (fun x hxg => ?_)
  exact
    coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_at
      C hpi g r1 r2 b1 b2 i j hO hchi hrdn p hxg

set_option maxHeartbeats 8000000 in
-- The equality carries the full pointwise seed data, so keep instance synthesis scoped here.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every certificate-free pointwise-seed residue presentation has the prescribed degree `g`. -/
theorem deg_presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ) :
    CurveDivisor.deg p.asIdeal.ResidueField
        (Scheme.presentationDivisor p.asIdeal.ResidueField
          ((ThetaGeneratorSeed.residueFibreLocalEquations
            (pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)
            (isGenerator_pointwiseGeneratorSeed
              C hpi g r1 r2 b1 b2 i j hO hchi hrdn) p).presentation)) = (g : ℤ) := by
  rw [presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed_eq
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn p]
  exact (divUniversalSeedFibreDivisor_spec C hpi g r1 r2 b1 b2 i j hO hchi p).2.1

set_option maxHeartbeats 8000000 in
-- The germ comparison elaborates the dependent residue-point and chart transports.
set_option synthInstance.maxHeartbeats 800000 in
/-- Off the diagonal, the pulled pointwise-generator equation still reads as the compared
window vector; `gamma` controls the curve Euler characteristic and `g` the divisor degree. -/
theorem germ_pullbackEqn_pointwiseGeneratorSeed_eq_pointwiseFibreReadGerm_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hchi)
    (z : relCurve C RZ) :
    let p := relCurveBasePoint C RZ z
    let K := p.asIdeal.ResidueField
    let zK := relCurveResiduePoint C RZ z
    let D := pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn
    let hD := isGenerator_pointwiseGeneratorSeed_at
      C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn
    ((relCurve C K).presheaf.germ
        (((D.localEquations hD).cover.pullback (relCurveMap C RZ K)).opens zK) zK
        (((D.localEquations hD).cover.pullback
          (relCurveMap C RZ K)).mem_opens zK)).hom
        (Scheme.LocalEquations.pullbackEqn
          (relCurveMap C RZ K) (D.localEquations hD) zK) =
      pointwiseFibreReadGerm C hpi g r1 r2 b1 b2 i j z
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hchi z) := by
  dsimp only
  let p := relCurveBasePoint C RZ z
  let K := p.asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let D := pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn
  let hD := isGenerator_pointwiseGeneratorSeed_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn
  have hbase : (relCurveMap C RZ K).base zK = z := by
    simpa only [K, p, zK] using relCurveMap_relCurveResiduePoint C RZ z
  have hzPiece : zK ∈ (relCurve C K).basicOpen
      (relPinnedSectionsMap C RZ K pi (D.side z) (D.h z)) := by
    rw [relPinnedSectionsMap_basicOpen]
    change (relCurveMap C RZ K).base zK ∈ (relCurve C RZ).basicOpen (D.h z)
    rw [hbase]
    exact D.mem_basicOpen z
  have hzSide : zK ∈ relPinnedChart C K pi (D.side z) := by
    change zK ∈ relPinnedChart C K pi
      (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
    simpa only [K, p, zK] using relCurveResiduePoint_mem_relPinnedChart C RZ
      (π := pi) (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
      (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
  have hpull := D.germ_self_pullbackEqn_eq_germ_relPinnedSectionsMap_of_map_eq
    hD p zK z hbase hzPiece hzSide
  rw [hpull]
  convert germ_relPinnedSectionsMap_relThetaResSide_windowEquiv_at_relCurveResiduePoint
    C RZ (π := pi) (windowM_choice pi hpi g)
    (relThetaPairH1_windowM C pi hpi g)
    (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
    (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
    (pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hchi z) using 1 <;> rfl

set_option maxHeartbeats 8000000 in
-- The coefficient comparison normalizes stalk units and residue-point transports.
set_option synthInstance.maxHeartbeats 800000 in
/-- The coefficient comparison underlying the pulled-degree calculation with independent
curve parameter `gamma` and divisor degree `g`. -/
theorem coeffAt_presentationDivisor_eq_divUniversalSeedFibreDivisor_of_germ_eq_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (d : (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).LocalEquations)
    (hgerm :
      ((relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).presheaf.germ
        (d.cover.opens (relCurveResiduePoint C RZ z)) (relCurveResiduePoint C RZ z)
        (d.cover.mem_opens (relCurveResiduePoint C RZ z))).hom
        (d.eqn (relCurveResiduePoint C RZ z)) =
      pointwiseFibreReadGerm C hpi g r1 r2 b1 b2 i j z
        (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
        (pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hchi z)) :
    coeffAt hzg (Scheme.presentationDivisor
        (relCurveBasePoint C RZ z).asIdeal.ResidueField d.presentation) =
      coeffAt hzg (divUniversalSeedFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j hgamma hchi (relCurveBasePoint C RZ z)) := by
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let M := windowM_choice pi hpi g
  let v := pointwiseSectionVector_at C hpi g r1 r2 b1 b2 i j hgamma hchi z
  let s : relThetaSections C K pi M :=
    relThetaWindowEquiv C K pi M (relThetaPairH1_windowM C pi hpi g)
      (windowCompare RZ K v)
  have hzK : zK ∈ relPinnedChart C K pi
      (pointwiseSide C hpi g r1 r2 b1 b2 i j z) := by
    simpa only [K, zK] using relCurveResiduePoint_mem_relPinnedChart C RZ
      (π := pi) (pointwiseSide C hpi g r1 r2 b1 b2 i j z)
      (pointwiseSide_mem C hpi g r1 r2 b1 b2 i j z)
  obtain ⟨hr, hzero⟩ := pointwiseSectionVector_fibreCoefficient_eq_zero_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi z hzg
  have hphi : divFamPhi C K pi M (relThetaPairH1_windowM C pi hpi g)
      (windowCompare RZ K v) =
        (thetaFieldShiftUnit C K pi M : (relCurve C K).functionField) *
          thetaFieldRead C K pi M s := by
    rfl
  have ht : thetaFieldRead C K pi M s ≠ 0 := by
    intro ht0
    apply hr
    rw [hphi, ht0, mul_zero]
  let t : (relCurve C K).functionFieldˣ := Units.mk0 _ ht
  have hphiU : Units.mk0
      (divFamPhi C K pi M (relThetaPairH1_windowM C pi hpi g)
        (windowCompare RZ K v)) hr = thetaFieldShiftUnit C K pi M * t := by
    apply Units.ext
    exact hphi
  have hzero' := hzero
  change coeffAt hzg
      ((windowN C K hpi g - divUniversalSeedFibreDivisor_at
          C hpi g r1 r2 b1 b2 i j hgamma hchi (relCurveBasePoint C RZ z)) +
        Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0
            (divFamPhi C K pi M (relThetaPairH1_windowM C pi hpi g)
              (windowCompare RZ K v)) hr)) = 0 at hzero'
  rw [hphiU, Scheme.divOf_mul,
    ← divOf_thetaFieldShiftUnit C K pi M] at hzero'
  change coeffAt hzg
      ((windowTransportDivisor C K pi M - divUniversalSeedFibreDivisor_at
          C hpi g r1 r2 b1 b2 i j hgamma hchi (relCurveBasePoint C RZ z)) +
        ((thetaFieldDivisor C K pi M - windowTransportDivisor C K pi M) +
          Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K)) t)) = 0 at hzero'
  simp only [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_sub] at hzero'
  have hbalance : coeffAt hzg (thetaFieldDivisor C K pi M) +
      coeffAt hzg (Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K)) t) =
        coeffAt hzg (divUniversalSeedFibreDivisor_at
          C hpi g r1 r2 b1 b2 i j hgamma hchi (relCurveBasePoint C RZ z)) := by
    omega
  have hgermSide :
      ((relCurve C K).presheaf.germ (d.cover.opens zK) zK
        (d.cover.mem_opens zK)).hom (d.eqn zK) =
      ((relCurve C K).presheaf.germ (relPinnedChart C K pi
          (pointwiseSide C hpi g r1 r2 b1 b2 i j z)) zK hzK).hom
        (relThetaResSide M (pointwiseSide C hpi g r1 r2 b1 b2 i j z) le_rfl s) := by
    simpa only [K, zK, M, v, s, pointwiseFibreReadGerm] using hgerm
  obtain ⟨w, hw⟩ := exists_unit_germ_relThetaResSide_eq C K pi M
    (pointwiseSide C hpi g r1 r2 b1 b2 i j z) le_rfl hzK
  have helem : d.presentation.elem zK =
      Units.map (algebraMap ((relCurve C K).presheaf.stalk zK)
        (relCurve C K).functionField).toMonoidHom w *
        ((thetaFieldPresentation C K pi M).elem zK * t) := by
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map]
    rw [Scheme.LocalEquations.presentation_elem_val,
      Scheme.germ_generic_eq_algebraMap_germ
        (d.cover.genericPoint_mem_opens zK) (d.cover.mem_opens zK) (d.eqn zK),
      hgermSide, hw s, map_mul,
      algebraMap_germ_thetaFieldGluedEquiv_eq C K pi M s zK]
    rfl
  have helem' : d.presentation.elem zK =
      ((thetaFieldPresentation C K pi M).elem zK * t) *
        Units.map (algebraMap ((relCurve C K).presheaf.stalk zK)
          (relCurve C K).functionField).toMonoidHom w := by
    rw [helem, mul_comm]
  rw [Scheme.coeffAt_presentationDivisor, helem',
    Scheme.toAdd_ordZ_mul_unitsMap_stalk K hzg,
    map_mul, toAdd_mul,
    ← Scheme.coeffAt_presentationDivisor K (thetaFieldPresentation C K pi M) hzg,
    ← Scheme.CurveDivisor.coeffAt_divOf
      (relCurve C K ↘ Spec (CommRingCat.of K)) t hzg]
  simpa only [thetaFieldDivisor] using hbalance

set_option maxHeartbeats 8000000 in
-- Expanding the pulled local equations retains the full dependent residue-fibre data.
set_option synthInstance.maxHeartbeats 800000 in
/-- The residue-fibre presentation has the off-diagonal universal fibre-divisor coefficient
at the canonical residue point. -/
theorem
  coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_param
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hchi)
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    coeffAt hzg (Scheme.presentationDivisor
        (relCurveBasePoint C RZ z).asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)
          (isGenerator_pointwiseGeneratorSeed_at
            C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)
          (relCurveBasePoint C RZ z)).presentation)) =
      coeffAt hzg (divUniversalSeedFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j hgamma hchi (relCurveBasePoint C RZ z)) := by
  apply coeffAt_presentationDivisor_eq_divUniversalSeedFibreDivisor_of_germ_eq_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi z hzg
  change
    ((relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).presheaf.germ
      ((((pointwiseGeneratorSeed_at
        C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn).localEquations
          (isGenerator_pointwiseGeneratorSeed_at
            C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)).cover.pullback
              (relCurveMap C RZ
                (relCurveBasePoint C RZ z).asIdeal.ResidueField)).opens
        (relCurveResiduePoint C RZ z)) (relCurveResiduePoint C RZ z)
      (((((pointwiseGeneratorSeed_at
        C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn).localEquations
          (isGenerator_pointwiseGeneratorSeed_at
            C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)).cover.pullback
              (relCurveMap C RZ
                (relCurveBasePoint C RZ z).asIdeal.ResidueField)).mem_opens
        (relCurveResiduePoint C RZ z)))).hom
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField)
        ((pointwiseGeneratorSeed_at
          C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn).localEquations
            (isGenerator_pointwiseGeneratorSeed_at
              C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn))
        (relCurveResiduePoint C RZ z)) = _
  exact germ_pullbackEqn_pointwiseGeneratorSeed_eq_pointwiseFibreReadGerm_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn z

set_option maxHeartbeats 8000000 in
-- Reindexing the residue point across its base-prime equality requires dependent transport.
set_option synthInstance.maxHeartbeats 800000 in
/-- Reindexed off-diagonal coefficient equality at every closed residue-fibre point. -/
theorem
  coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_param_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hchi)
    (p : PrimeSpectrum RZ) {x : relCurve C p.asIdeal.ResidueField}
    (hxg : x ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    coeffAt hxg (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)
          (isGenerator_pointwiseGeneratorSeed_at
            C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn) p).presentation)) =
      coeffAt hxg (divUniversalSeedFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j hgamma hchi p) := by
  generalize hz : (relCurveMap C RZ p.asIdeal.ResidueField).base x = z
  have hp : relCurveBasePoint C RZ z = p :=
    hz ▸ relCurveBasePoint_relCurveMap_residueField C RZ p x
  have hxcast : Eq.ndrec
      (motive := fun q : PrimeSpectrum RZ => relCurve C q.asIdeal.ResidueField)
      (relCurveResiduePoint C RZ z) hp = x := by
    subst z
    exact relCurveResiduePoint_map_cast C RZ p x
  clear hz
  subst p
  have hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) := by
    simpa only [hxcast] using hxg
  subst x
  exact
    coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_param
      C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn z hzg

set_option maxHeartbeats 8000000 in
-- Divisor extensionality instantiates the coefficient theorem at every non-generic point.
set_option synthInstance.maxHeartbeats 800000 in
/-- The residue presentation divisor equals the universal fibre divisor at independent
curve and divisor parameters. -/
theorem presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hchi)
    (p : PrimeSpectrum RZ) :
    Scheme.presentationDivisor p.asIdeal.ResidueField
        ((ThetaGeneratorSeed.residueFibreLocalEquations
          (pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)
          (isGenerator_pointwiseGeneratorSeed_at
            C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn) p).presentation) =
      divUniversalSeedFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j hgamma hchi p := by
  refine CurveDivisor.ext_coeffAt (fun x hxg => ?_)
  exact (
  coeffAt_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_param_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn p hxg)

set_option maxHeartbeats 8000000 in
-- The degree rewrite elaborates the universal fibre-divisor specification at this fibre.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every off-diagonal pointwise-seed residue presentation has divisor degree `g`. -/
theorem deg_presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hrdn : PointwiseSeedRDNAt C hpi g r1 r2 b1 b2 i j hgamma hchi)
    (p : PrimeSpectrum RZ) :
    CurveDivisor.deg p.asIdeal.ResidueField
        (Scheme.presentationDivisor p.asIdeal.ResidueField
          ((ThetaGeneratorSeed.residueFibreLocalEquations
            (pointwiseGeneratorSeed_at C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn)
            (isGenerator_pointwiseGeneratorSeed_at
              C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn) p).presentation)) = (g : ℤ) := by
  rw [presentationDivisor_residueFibreLocalEquations_pointwiseGeneratorSeed_eq_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi hrdn p]
  exact (divUniversalSeedFibreDivisor_spec_at
    C hpi g r1 r2 b1 b2 i j hgamma hchi p).2.1

set_option maxHeartbeats 8000000 in
-- The pulled-equation definition and the pointwise germ bridge carry the full dependent
-- residue-field tower.
set_option synthInstance.maxHeartbeats 800000 in
/-- The presentation divisor of any pulled adaptation of the pointwise generator seed has
the universal fibre-divisor coefficient at the canonical residue point. -/
theorem coeffAt_pulledEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (A : DivisorAdaptation C RZ pi
      ((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)))
    (hproj : ∀ q : A.index, Module.Projective RZ (A.colength q)) :
    coeffAt hzg (Scheme.presentationDivisor
        (relCurveBasePoint C RZ z).asIdeal.ResidueField
        ((A.pulledEquations
          (relCurveBasePoint C RZ z).asIdeal.ResidueField hproj).presentation)) =
      coeffAt hzg (divUniversalSeedFibreDivisor
        C hpi g r1 r2 b1 b2 i j hO hchi (relCurveBasePoint C RZ z)) := by
  apply coeffAt_presentationDivisor_eq_divUniversalSeedFibreDivisor_of_germ_eq
    C hpi g r1 r2 b1 b2 i j hO hchi z hzg
  change
    ((relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).presheaf.germ
      ((((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)).cover.pullback
          (relCurveMap C RZ
            (relCurveBasePoint C RZ z).asIdeal.ResidueField)).opens
        (relCurveResiduePoint C RZ z)) (relCurveResiduePoint C RZ z)
      (((((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)).cover.pullback
          (relCurveMap C RZ
            (relCurveBasePoint C RZ z).asIdeal.ResidueField)).mem_opens
        (relCurveResiduePoint C RZ z)))).hom
      (Scheme.LocalEquations.pullbackEqn
        (relCurveMap C RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField)
        ((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
          (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn))
        (relCurveResiduePoint C RZ z)) = _
  exact germ_pullbackEqn_pointwiseGeneratorSeed_eq_pointwiseFibreReadGerm
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn z

set_option maxHeartbeats 8000000 in
-- Reindexing an arbitrary residue-fibre point through the total curve transports the
-- residue field, the point, and both divisor coefficients dependently.
set_option synthInstance.maxHeartbeats 800000 in
/-- The pulled pointwise-seed presentation and the universal fibre divisor have equal
coefficients at every closed point of every residue fibre. -/
theorem coeffAt_pulledEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_at
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ)
    (A : DivisorAdaptation C RZ pi
      ((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)))
    (hproj : ∀ q : A.index, Module.Projective RZ (A.colength q))
    {x : relCurve C p.asIdeal.ResidueField}
    (hxg : x ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    coeffAt hxg (Scheme.presentationDivisor p.asIdeal.ResidueField
        ((A.pulledEquations p.asIdeal.ResidueField hproj).presentation)) =
      coeffAt hxg (divUniversalSeedFibreDivisor
        C hpi g r1 r2 b1 b2 i j hO hchi p) := by
  generalize hz : (relCurveMap C RZ p.asIdeal.ResidueField).base x = z
  have hp : relCurveBasePoint C RZ z = p :=
    hz ▸ relCurveBasePoint_relCurveMap_residueField C RZ p x
  have hxcast : Eq.ndrec
      (motive := fun q : PrimeSpectrum RZ => relCurve C q.asIdeal.ResidueField)
      (relCurveResiduePoint C RZ z) hp = x := by
    subst z
    exact relCurveResiduePoint_map_cast C RZ p x
  clear hz
  subst p
  have hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) := by
    simpa only [hxcast] using hxg
  subst x
  exact coeffAt_pulledEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn z hzg A hproj

set_option maxHeartbeats 8000000 in
-- Divisor extensionality expands the adapted pulled equations at each residue point.
set_option synthInstance.maxHeartbeats 800000 in
/-- On every residue fibre, the pulled pointwise-seed presentation divisor is the
universal fibre divisor. -/
theorem presentationDivisor_pulledEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ)
    (A : DivisorAdaptation C RZ pi
      ((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)))
    (hproj : ∀ q : A.index, Module.Projective RZ (A.colength q)) :
    Scheme.presentationDivisor p.asIdeal.ResidueField
        ((A.pulledEquations p.asIdeal.ResidueField hproj).presentation) =
      divUniversalSeedFibreDivisor C hpi g r1 r2 b1 b2 i j hO hchi p := by
  refine CurveDivisor.ext_coeffAt (fun x hxg => ?_)
  exact coeffAt_pulledEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor_at
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn p A hproj hxg

set_option maxHeartbeats 8000000 in
-- The degree calculation combines the pulled presentation equality with the fibre specification.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every pulled pointwise-seed presentation divisor has the prescribed fibre degree
`g`; this supplies the degree gate in the divisor-adaptation certificate. -/
theorem deg_presentationDivisor_pulledEquations_pointwiseGeneratorSeed
    (hrdn : PointwiseSeedRDN C hpi g r1 r2 b1 b2 i j hO hchi)
    (p : PrimeSpectrum RZ)
    (A : DivisorAdaptation C RZ pi
      ((pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn).localEquations
        (isGenerator_pointwiseGeneratorSeed C hpi g r1 r2 b1 b2 i j hO hchi hrdn)))
    (hproj : ∀ q : A.index, Module.Projective RZ (A.colength q)) :
    CurveDivisor.deg p.asIdeal.ResidueField
        (Scheme.presentationDivisor p.asIdeal.ResidueField
          ((A.pulledEquations p.asIdeal.ResidueField hproj).presentation)) = (g : ℤ) := by
  rw [presentationDivisor_pulledEquations_pointwiseGeneratorSeed_eq_divUniversalSeedFibreDivisor
    C hpi g r1 r2 b1 b2 i j hO hchi hrdn p A hproj]
  exact (divUniversalSeedFibreDivisor_spec C hpi g r1 r2 b1 b2 i j hO hchi p).2.1

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
