/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseFibreData
import AlgebraicJacobian.Picard.DivSchemeRedesignHinjChart
import AlgebraicJacobian.Picard.DivSchemeRedesignCarvePin
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeRelKit

/-!
# Core residue-fibre divisibility for the pointwise seed

This file clears both denominators in the closed-point fibre argument: first the chart
denominator introduced by passing from a fibre stalk to its affine chart, then the base
denominator introduced by the residue-field tensor product.
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

noncomputable local instance instOverCleftPointwiseFibre :
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

noncomputable local instance instIsIntegralRelCurvePointwiseFibre
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseFibre
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseFibre
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwiseFibre
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

set_option maxHeartbeats 500000 in
-- The residue-field tower and dependent germ target exceed the default elaboration budget.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The germ at the canonical residue-fibre point of the reading of a compared window
vector. -/
noncomputable def pointwiseFibreReadGerm
    (z : relCurve C RZ)
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    (x : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField).presheaf.stalk
      (relCurveResiduePoint C RZ z) := by
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let hzK := relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
  exact ((relCurve C K).presheaf.germ (relPinnedChart C K π b) zK hzK).hom
      (relThetaResSide (windowM_choice π hπ g) b le_rfl
        (relThetaWindowEquiv C K π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) (windowCompare RZ K x)))

set_option maxHeartbeats 8000000 in
-- Applying the achiever theorem reconstructs the full seed and residue-field towers.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Nonzero compared universal-window readings are divisible by the pointwise achiever in
the residue-fibre stalk. -/
theorem pointwiseFibreReadGerm_dvd_of_ne
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    {xψ : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hxψ : xψ ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule)
    (hxψzero : windowCompare RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField xψ ≠ 0) :
    pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz
        (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) ∣
      pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz xψ := by
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let A := pointwiseFibrePoleDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
  have hTA : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K ≤
      Scheme.divisorSections K A ⊤ := by
    simpa only [K, A] using divUniversalFibreKM_le_pointwiseFibrePoleDivisor
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
  obtain ⟨hsec_ne, hach⟩ :=
    pointwiseSectionVector_fibreAchieverData
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg
  have hψ_ne : divFamPhi C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) (windowCompare RZ K xψ) ≠ 0 := by
    intro hzero
    apply hxψzero
    exact (divFamPhi_injective C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g)) (by simpa using hzero)
  have hψmem := divFamPhi_windowCompare_mem_divUniversalFibreKM
    C hπ g r₁ r₂ b₁ b₂ i j K hxψ
  unfold pointwiseFibreReadGerm
  apply germ_relThetaResSide_windowEquiv_dvd_of_achiever
    K C π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
      hTA
      (windowCompare RZ K
        (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))
      (windowCompare RZ K xψ) hsec_ne hψ_ne hψmem b le_rfl
      (relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz) hzg
      hach

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Nonzero universal-window readings are divisible by the decoupled pointwise achiever in
the residue-fibre stalk. -/
theorem pointwiseFibreReadGerm_dvd_of_ne_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    {xψ : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hxψ : xψ ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule)
    (hxψzero : windowCompare RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField xψ ≠ 0) :
    pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz
        (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) ∣
      pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz xψ := by
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let A := pointwiseFibrePoleDivisor_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z
  have hTA : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K ≤
      Scheme.divisorSections K A ⊤ := by
    simpa only [K, A] using divUniversalFibreKM_le_pointwiseFibrePoleDivisor_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z
  obtain ⟨hsec_ne, hach⟩ :=
    pointwiseSectionVector_fibreAchieverData_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg
  have hψ_ne : divFamPhi C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) (windowCompare RZ K xψ) ≠ 0 := by
    intro hzero
    apply hxψzero
    exact (divFamPhi_injective C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g)) (by simpa using hzero)
  have hψmem := divFamPhi_windowCompare_mem_divUniversalFibreKM
    C hπ g r₁ r₂ b₁ b₂ i j K hxψ
  unfold pointwiseFibreReadGerm
  apply germ_relThetaResSide_windowEquiv_dvd_of_achiever
    K C π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
      hTA
      (windowCompare RZ K
        (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))
      (windowCompare RZ K xψ) hsec_ne hψ_ne hψmem b le_rfl
      (relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz) hzg
      hach

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
