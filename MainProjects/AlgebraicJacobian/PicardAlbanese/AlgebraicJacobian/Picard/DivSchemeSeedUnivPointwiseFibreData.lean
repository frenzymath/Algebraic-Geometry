/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseFlat
import AlgebraicJacobian.Picard.DivSchemeRedesignGermDvd

/-!
# Fibre-achiever data for the pointwise seed

This file extracts the two seed-specific inputs to the generic fibre germ-divisibility
theorem: the fibre-window pole bound and the coefficient equality achieved by the chosen
pointwise vector.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section SeedContext

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftPointwiseFibreData :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

noncomputable local instance instIsIntegralRelCurvePointwiseFibreData
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseFibreData
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseFibreData
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwiseFibreData
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

/-- The pole divisor used by the pointwise achiever on the residue fibre at `z`. -/
noncomputable def pointwiseFibrePoleDivisor (z : relCurve C RZ) :
    (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).CurveDivisor :=
  windowN C (relCurveBasePoint C RZ z).asIdeal.ResidueField hπ g -
    divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ
      (relCurveBasePoint C RZ z)

set_option maxHeartbeats 2400000 in
-- The seed divisor specification reconstructs the residue-field tower at `z`.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The universal fibre window lies under the pointwise achiever's pole divisor. -/
theorem divUniversalFibreKM_le_pointwiseFibrePoleDivisor
    (z : relCurve C RZ) :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j
        (relCurveBasePoint C RZ z).asIdeal.ResidueField ≤
      Scheme.divisorSections (relCurveBasePoint C RZ z).asIdeal.ResidueField
        (pointwiseFibrePoleDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) ⊤ :=
  le_of_eq (divUniversalSeedFibreDivisor_spec
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ (relCurveBasePoint C RZ z)).2.2.1

set_option maxHeartbeats 4800000 in
-- Transporting the chosen achiever payload to the pointwise vector is dependent on `z`.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The compared pointwise vector is the fibre achiever, including its nonvanishing and
coefficient equality at the canonical residue point. -/
theorem pointwiseSectionVector_fibreAchieverData
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
    let A := pointwiseFibrePoleDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
    ∃ hr : divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)
        (windowCompare RZ K
          (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)) ≠ 0,
      coeffAt hzg
          (A + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
            (Units.mk0 (divFamPhi C K π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g)
              (windowCompare RZ K
                (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))) hr))
        = (Scheme.baseDivisorAt K (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) A
          ⟨relCurveResiduePoint C RZ z, hzg⟩ : ℤ) := by
  dsimp only
  obtain ⟨hsec_ne, hach⟩ :=
    (pointwiseAchiever C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg).choose_spec.2.2.2
  have hsec_eq := pointwiseSectionVector_achieves
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg
  rw [hsec_eq]
  exact ⟨hsec_ne, hach⟩

set_option maxHeartbeats 4800000 in
-- The pointwise residue-field tower is reconstructed in both input theorems.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The compared pointwise achiever has zero residual coefficient at the canonical
residue-fibre point. -/
theorem pointwiseSectionVector_fibreCoefficient_eq_zero
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
    let A := pointwiseFibrePoleDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
    ∃ hr : divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)
        (windowCompare RZ K
          (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)) ≠ 0,
      coeffAt hzg
          (A + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
            (Units.mk0 (divFamPhi C K π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g)
              (windowCompare RZ K
                (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))) hr)) = 0 := by
  dsimp only
  obtain ⟨hr, hcoeff⟩ := pointwiseSectionVector_fibreAchieverData
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg
  refine ⟨hr, hcoeff.trans ?_⟩
  simpa only [pointwiseFibrePoleDivisor] using
    divUniversalSeedFibreDivisor_residual_baseDivisorAt_eq_zero
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ (relCurveBasePoint C RZ z) hzg

/-! ## Decoupled fibre-achiever data -/

/-- The pointwise achiever's pole divisor at divisor degree `g` and curve parameter
`gamma ≤ g`. -/
noncomputable def pointwiseFibrePoleDivisor_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).CurveDivisor :=
  windowN C (relCurveBasePoint C RZ z).asIdeal.ResidueField hπ g -
    divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ
      (relCurveBasePoint C RZ z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The universal fibre window lies under the decoupled pointwise pole divisor. -/
theorem divUniversalFibreKM_le_pointwiseFibrePoleDivisor_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j
        (relCurveBasePoint C RZ z).asIdeal.ResidueField ≤
      Scheme.divisorSections (relCurveBasePoint C RZ z).asIdeal.ResidueField
        (pointwiseFibrePoleDivisor_at
          C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) ⊤ :=
  le_of_eq (divUniversalSeedFibreDivisor_spec_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ (relCurveBasePoint C RZ z)).2.2.1

set_option maxHeartbeats 4800000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise vector carries the fibre-achiever nonvanishing and coefficient
equality. -/
theorem pointwiseSectionVector_fibreAchieverData_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
    let A := pointwiseFibrePoleDivisor_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z
    ∃ hr : divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)
        (windowCompare RZ K
          (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)) ≠ 0,
      coeffAt hzg
          (A + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
            (Units.mk0 (divFamPhi C K π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g)
              (windowCompare RZ K
                (pointwiseSectionVector_at
                  C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))) hr))
        = (Scheme.baseDivisorAt K (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) A
          ⟨relCurveResiduePoint C RZ z, hzg⟩ : ℤ) := by
  dsimp only
  obtain ⟨hsec_ne, hach⟩ :=
    (pointwiseAchiever_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg).choose_spec.2.2.2
  have hsec_eq := pointwiseSectionVector_achieves_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg
  rw [hsec_eq]
  exact ⟨hsec_ne, hach⟩

set_option maxHeartbeats 4800000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise achiever has zero residual coefficient at the canonical
residue-fibre point. -/
theorem pointwiseSectionVector_fibreCoefficient_eq_zero_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
    let A := pointwiseFibrePoleDivisor_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z
    ∃ hr : divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)
        (windowCompare RZ K
          (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)) ≠ 0,
      coeffAt hzg
          (A + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
            (Units.mk0 (divFamPhi C K π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g)
              (windowCompare RZ K
                (pointwiseSectionVector_at
                  C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))) hr)) = 0 := by
  dsimp only
  obtain ⟨hr, hcoeff⟩ := pointwiseSectionVector_fibreAchieverData_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg
  refine ⟨hr, hcoeff.trans ?_⟩
  simpa only [pointwiseFibrePoleDivisor_at] using
    divUniversalSeedFibreDivisor_residual_baseDivisorAt_eq_zero_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ (relCurveBasePoint C RZ z) hzg

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
