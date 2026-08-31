/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeAdaptationFibreRegular
import AlgebraicJacobian.Picard.DivSchemeCertZarConfine
import AlgebraicJacobian.Picard.DivSchemeFibrePoint
import AlgebraicJacobian.Picard.DivisorFamilyFieldDegree

/-!
# Finite support fibres without a coordinate change

The residue-field support of a regular divisor family on a relative curve is finite.
This is the chart-free part of `DivSchemeCertZarFibreAvoid`: it uses only the
meromorphic presentation of local equations and the residue-fibre comparison.  In
particular its dependency closure contains neither `P1Aut` nor a field-size hypothesis.

The seed-level endpoint is the input for choosing an arbitrary affine neighbourhood of
the finite fibre before spreading that neighbourhood over a basic open of the base.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme ThetaGeneratorSeed

namespace Scheme.LocalEquations

/-- A regular local-equation system on a smooth integral quasi-compact curve over a
field has finite support. -/
private theorem supportLocus_finite_on_curve_aff
    (K : Type u) [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (d : X.LocalEquations) : d.supportLocus.Finite := by
  let T : Set {x : X // x ≠ genericPoint X} :=
    {p | Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) p.2
      (d.presentation.elem p.1) ≠ 1}
  have hT : T.Finite := d.presentation.ordZ_elem_support_finite K
  refine (hT.image Subtype.val).subset ?_
  intro x hx
  have hxg : x ≠ genericPoint X := by
    intro h
    subst x
    have hnot := (d.mem_supportLocus_iff_not_isUnit_germ
      (d.cover.mem_opens (genericPoint X))).mp hx
    apply hnot
    exact isUnit_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp
      (d.regular (genericPoint X) (genericPoint X)
        (d.cover.mem_opens (genericPoint X))))
  refine ⟨⟨x, hxg⟩, ?_, rfl⟩
  change Scheme.ordZ (X ↘ Spec (CommRingCat.of K)) hxg
    (d.presentation.elem x) ≠ 1
  intro hord
  have hnot := (d.mem_supportLocus_iff_not_isUnit_germ
    (d.cover.mem_opens x)).mp hx
  apply hnot
  exact (Scheme.isUnit_germ_iff_ordZ_eq_one K
    (d.cover.genericPoint_mem_opens x) (d.eqn x)
    (d.presentation.elem x) (d.presentation_elem_val x)
    (d.cover.mem_opens x) hxg).mpr hord

section ResidueFibre

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]

/-- The residue-field base change maps onto the corresponding topological fibre of the
relative curve. -/
private theorem range_relCurveMap_residueField_aff (p : PrimeSpectrum R) :
    Set.range (relCurveMap C R p.asIdeal.ResidueField).base =
      {z : relCurve C R | relCurveBasePoint C R z = p} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact relCurveBasePoint_relCurveMap_residueField C R p x
  · intro hz
    let z' : relCurve C p.asIdeal.ResidueField :=
      Eq.ndrec
        (motive := fun q : PrimeSpectrum R => relCurve C q.asIdeal.ResidueField)
        (relCurveResiduePoint C R z) hz
    refine ⟨z', ?_⟩
    exact (relCurveMap_residueField_cast C R hz
      (relCurveResiduePoint C R z)).trans
      (relCurveMap_relCurveResiduePoint C R z)

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- If a local-equation system pulls back to a regular system on the residue curve,
then its support fibre is finite. -/
theorem fibre_supportLocus_finite_of_pullback_support_eq_aff
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (dK : (relCurve C p.asIdeal.ResidueField).LocalEquations)
    (hsupport : dK.supportLocus =
      (relCurveMap C R p.asIdeal.ResidueField).base ⁻¹' d.supportLocus) :
    (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite := by
  letI : SmoothOfRelativeDimension 1
      (relCurve C p.asIdeal.ResidueField ↘
        Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instSmoothOfRelativeDimensionBaseChange C p.asIdeal.ResidueField
  letI : IsIntegral (relCurve C p.asIdeal.ResidueField) :=
    instIsIntegralBaseChange C p.asIdeal.ResidueField
  letI : QuasiCompact
      (relCurve C p.asIdeal.ResidueField ↘
        Spec (CommRingCat.of p.asIdeal.ResidueField)) :=
    instQuasiCompactBaseChange C p.asIdeal.ResidueField
  have hfinite := supportLocus_finite_on_curve_aff p.asIdeal.ResidueField dK
  have heq :
      ((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩ d.supportLocus =
        (relCurveMap C R p.asIdeal.ResidueField).base '' dK.supportLocus := by
    ext x
    constructor
    · rintro ⟨hxp, hxd⟩
      change relCurveBasePoint C R x = p at hxp
      have hxrange :
          x ∈ Set.range (relCurveMap C R p.asIdeal.ResidueField).base := by
        rw [range_relCurveMap_residueField_aff C R p]
        exact hxp
      obtain ⟨z, rfl⟩ := hxrange
      refine ⟨z, ?_, rfl⟩
      rw [hsupport]
      exact hxd
    · rintro ⟨z, hz, rfl⟩
      constructor
      · change relCurveBasePoint C R
          ((relCurveMap C R p.asIdeal.ResidueField).base z) = p
        exact relCurveBasePoint_relCurveMap_residueField C R p z
      · rw [hsupport] at hz
        exact hz
  rw [heq]
  exact hfinite.image (relCurveMap C R p.asIdeal.ResidueField).base

/-- Own-member regularity of the residue-field pullback is enough to make the
support fibre finite. -/
theorem fibre_supportLocus_finite_of_forall_self_aff
    (d : (relCurve C R).LocalEquations) (p : PrimeSpectrum R)
    (hself : ∀ z : relCurve C p.asIdeal.ResidueField,
      ((relCurve C p.asIdeal.ResidueField).presheaf.germ
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).opens z) z
        ((d.cover.pullback
          (relCurveMap C R p.asIdeal.ResidueField)).mem_opens z)).hom
        (pullbackEqn (relCurveMap C R p.asIdeal.ResidueField) d z) ∈
          nonZeroDivisors
            ((relCurve C p.asIdeal.ResidueField).presheaf.stalk z)) :
    (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      d.supportLocus).Finite := by
  let hreg := germ_pullbackEqn_mem_nonZeroDivisors_of_forall_self
    (relCurveMap C R p.asIdeal.ResidueField) d hself
  exact fibre_supportLocus_finite_of_pullback_support_eq_aff C R d p
    (d.pullback (relCurveMap C R p.asIdeal.ResidueField) hreg)
    (supportLocus_pullback (relCurveMap C R p.asIdeal.ResidueField) d hreg)

end ResidueFibre

end Scheme.LocalEquations

namespace ThetaGeneratorSeed

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {R : Type u} [CommRing R] [Algebra k R] [IsNoetherianRing R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : Nat}
variable {K : Submodule R (relThetaSections C R pi a)}

/-- A generator seed has finite support on every residue fibre, without a coordinate
change or a cardinality assumption on the ground field. -/
theorem fibre_supportLocus_finite_aff
    (D : ThetaGeneratorSeed C R pi a K) (hD : D.IsGenerator)
    (p : PrimeSpectrum R) :
    (((relCurve C R) ↘ Spec (.of R)).base ⁻¹' {p} ∩
      (D.localEquations hD).supportLocus).Finite :=
  Scheme.LocalEquations.fibre_supportLocus_finite_of_forall_self_aff
    C R (D.localEquations hD) p
    (fun z => D.germ_self_pullbackEqn_mem_nonZeroDivisors hD p z)

end ThetaGeneratorSeed

end AlgebraicGeometry
