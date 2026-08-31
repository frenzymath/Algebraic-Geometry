/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeRedesignGenericTotalStalk
import AlgebraicJacobian.Picard.DivSchemeRedesignPointwiseSection

/-!
# Local generation by the pointwise section on fibre-generic points

The pointwise universal section is chosen to have nonzero residue-field
comparison at every total point. If the residue point is generic in its fibre,
the existing total-stalk reflection theorem makes its reading germ a unit.
Consequently that germ generates every universal-seed reading germ.

This closes the generic branch of the pointwise local-generation argument. It
makes no assertion about the closed branch, where lifting fibre divisibility to
the total stalk requires the separate ideal-purity input.
-/

set_option autoImplicit false
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

noncomputable local instance instOverCleftPointwiseGeneric :
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

noncomputable local instance instIsIntegralRelCurvePointwiseGeneric
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseGeneric
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseGeneric
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

set_option maxHeartbeats 1600000 in
-- The residue-field tower through `seedChartRing` and the dependent stalk germ
-- require more synthesis work than Lean's defaults allow.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- At a fibre-generic residue point, the selected pointwise section locally
generates every reading from the universal seed. This is the generic branch in
the exact germ-ideal shape consumed by the seed-level RD-N reduction. -/
theorem germ_relThetaResSide_mem_span_pointwiseSection_of_residuePoint_generic
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) (b : Bool)
    (hz : z ∈ relPinnedChart C RZ π b)
    (hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄
    (_hψ : ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :
    ((relCurve C RZ).presheaf.germ (relPinnedChart C RZ π b) z hz).hom
        (relThetaResSide (windowM_choice π hπ g) b le_rfl ψ)
      ∈ Ideal.span {
        ((relCurve C RZ).presheaf.germ (relPinnedChart C RZ π b) z hz).hom
          (relThetaResSide (windowM_choice π hπ g) b le_rfl
            (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))} := by
  have hu : IsUnit
      (((relCurve C RZ).presheaf.germ (relPinnedChart C RZ π b) z hz).hom
        (relThetaResSide (windowM_choice π hπ g) b le_rfl
          (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))) := by
    exact isUnit_total_germ_of_residuePoint_generic C RZ π
      (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) z b hz
      (windowCompare_pointwiseSectionVector_ne_zero
        C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) hzg
  rw [Ideal.span_singleton_eq_top.mpr hu]
  exact Submodule.mem_top

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Fibre-generic germ generation for the pointwise section at curve parameter
`gamma ≤ g`. -/
theorem germ_relThetaResSide_mem_span_pointwiseSection_of_residuePoint_generic_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) (b : Bool)
    (hz : z ∈ relPinnedChart C RZ π b)
    (hzg : relCurveResiduePoint C RZ z =
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄
    (_hψ : ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) :
    ((relCurve C RZ).presheaf.germ (relPinnedChart C RZ π b) z hz).hom
        (relThetaResSide (windowM_choice π hπ g) b le_rfl ψ)
      ∈ Ideal.span {
        ((relCurve C RZ).presheaf.germ (relPinnedChart C RZ π b) z hz).hom
          (relThetaResSide (windowM_choice π hπ g) b le_rfl
            (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))} := by
  have hu : IsUnit
      (((relCurve C RZ).presheaf.germ (relPinnedChart C RZ π b) z hz).hom
        (relThetaResSide (windowM_choice π hπ g) b le_rfl
          (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))) := by
    exact isUnit_total_germ_of_residuePoint_generic C RZ π
      (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) z b hz
      (windowCompare_pointwiseSectionVector_ne_zero_at
        C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) hzg
  rw [Ideal.span_singleton_eq_top.mpr hu]
  exact Submodule.mem_top

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
