/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignPointwiseAchiever

/-!
# A uniform pointwise section for the redesigned universal seed

At a non-generic point of the residue-field fibre, the redesigned seed must use the
landed base-divisor achiever.  At the generic point of a vertical fibre there is no
closed-point achiever statement to apply; a nonzero compared window vector is enough,
and its germ is a unit.

This file makes that dichotomy into one vector-valued choice.  It records only the
properties independent of the eventual basic-open cutter: membership in the universal
first window, membership of the corresponding theta section in `divUniversalSeedK`,
and nonvanishing after comparison with the residue field.  The local-principality/RD-N
step can therefore choose its cutter later without reusing the older arbitrary seed
section.
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
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftPointwiseSection :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
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

noncomputable local instance instIsIntegralRelCurvePointwiseSection
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseSection
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseSection
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwiseSection
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurvePointwiseSection
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurvePointwiseSection
    (L : Type u) [Field L] [Algebra k L] :
    Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j
local notation "HM" => ↥(Scheme.divisorSections k
  (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The redesigned pointwise vector.  At a closed fibre point it is the chosen
base-divisor achiever; at a fibre-generic point it is any nonzero compared vector. -/
noncomputable def pointwiseSectionVector
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) : RZ ⊗[k] HM := by
  classical
  exact if hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) then
    (pointwiseAchiever C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg).choose
  else
    (exists_sec_windowCompare_ne_zero_seedPrime C hπ g r₁ r₂ b₁ b₂ i j hO hχ
      (relCurveBasePoint C RZ z)).choose

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The selected vector lies in the first universal window. -/
theorem pointwiseSectionVector_mem
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) :
    pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z ∈
      (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule := by
  classical
  unfold pointwiseSectionVector
  split
  · exact (pointwiseAchiever C hπ g r₁ r₂ b₁ b₂ i j hO hχ z ‹_›).choose_spec.1
  · exact (exists_sec_windowCompare_ne_zero_seedPrime
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ (relCurveBasePoint C RZ z)).choose_spec.1

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The selected vector stays nonzero after comparison with the residue field of the
base point of `z`. -/
theorem windowCompare_pointwiseSectionVector_ne_zero
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) :
    windowCompare RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField
      (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) ≠ 0 := by
  classical
  unfold pointwiseSectionVector
  split
  · exact (pointwiseAchiever C hπ g r₁ r₂ b₁ b₂ i j hO hχ z ‹_›).choose_spec.2.2.1
  · exact (exists_sec_windowCompare_ne_zero_seedPrime
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ (relCurveBasePoint C RZ z)).choose_spec.2.1

/-- The theta section associated to the redesigned pointwise vector. -/
noncomputable def pointwiseSection
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) :
    relThetaSections C RZ π (windowM_choice π hπ g) :=
  relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g)
    (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The redesigned pointwise section belongs to the universal seed submodule. -/
theorem pointwiseSection_mem
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) :
    pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z ∈
      divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j := by
  classical
  unfold pointwiseSection pointwiseSectionVector
  split
  · exact (pointwiseAchiever C hπ g r₁ r₂ b₁ b₂ i j hO hχ z ‹_›).choose_spec.2.1
  · exact (exists_sec_windowCompare_ne_zero_seedPrime
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ (relCurveBasePoint C RZ z)).choose_spec.2.2

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- In the non-generic branch, the chosen vector is the first component of the full
achiever witness; its remaining payload is available from `pointwiseAchiever`. -/
theorem pointwiseSectionVector_achieves
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z =
      (pointwiseAchiever C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg).choose := by
  simp only [pointwiseSectionVector, dif_pos hzg]

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The redesigned pointwise vector at curve parameter `gamma ≤ g`. -/
noncomputable def pointwiseSectionVector_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) : RZ ⊗[k] HM := by
  classical
  exact if hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) then
    (pointwiseAchiever_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg).choose
  else
    (exists_sec_windowCompare_ne_zero_seedPrime_at C hπ g r₁ r₂ b₁ b₂ i j
      hgamma hχ (relCurveBasePoint C RZ z)).choose

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise vector lies in the first universal window. -/
theorem pointwiseSectionVector_mem_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z ∈
      (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule := by
  classical
  unfold pointwiseSectionVector_at
  split
  · exact (pointwiseAchiever_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z ‹_›).choose_spec.1
  · exact (exists_sec_windowCompare_ne_zero_seedPrime_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ
        (relCurveBasePoint C RZ z)).choose_spec.1

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise vector remains nonzero over the residue field of its base
point. -/
theorem windowCompare_pointwiseSectionVector_ne_zero_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    windowCompare RZ (relCurveBasePoint C RZ z).asIdeal.ResidueField
      (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) ≠ 0 := by
  classical
  unfold pointwiseSectionVector_at
  split
  · exact (pointwiseAchiever_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z ‹_›).choose_spec.2.2.1
  · exact (exists_sec_windowCompare_ne_zero_seedPrime_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ
        (relCurveBasePoint C RZ z)).choose_spec.2.1

/-- The theta section attached to the decoupled pointwise vector. -/
noncomputable def pointwiseSection_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    relThetaSections C RZ π (windowM_choice π hπ g) :=
  relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g)
    (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise section lies in the universal seed submodule. -/
theorem pointwiseSection_mem_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z ∈
      divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j := by
  classical
  unfold pointwiseSection_at pointwiseSectionVector_at
  split
  · exact (pointwiseAchiever_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z ‹_›).choose_spec.2.1
  · exact (exists_sec_windowCompare_ne_zero_seedPrime_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ
        (relCurveBasePoint C RZ z)).choose_spec.2.2

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- In the non-generic branch, the decoupled pointwise vector is the chosen achiever. -/
theorem pointwiseSectionVector_achieves_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :
    pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z =
      (pointwiseAchiever_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg).choose := by
  simp only [pointwiseSectionVector_at, dif_pos hzg]

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
