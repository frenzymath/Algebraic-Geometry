/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseFibreCore
import AlgebraicJacobian.Picard.DivSchemeRedesignHsubChartPin

/-!
# The affine fibre cofactor for the pointwise seed

This file converts pointwise achiever divisibility in the residue-fibre stalk into an
affine fibre-chart cofactor, expressed through the chart-ring base-change equivalence.
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

noncomputable local instance instOverCleftPointwiseFibreLocal :
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

noncomputable local instance instIsIntegralRelCurvePointwiseFibreLocal
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseFibreLocal
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseFibreLocal
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwiseFibreLocal
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

set_option maxHeartbeats 2400000 in
-- The zero/nonzero split retains the dependent residue-field germ type.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The pointwise achiever generates every universal-window reading in the residue-fibre
stalk. -/
theorem fibre_germ_mem_span_pointwiseSectionVector_local
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    {xψ : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hxψ : xψ ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule) :
    pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz xψ ∈
      Ideal.span {pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz
        (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)} := by
  by_cases hxψzero : windowCompare RZ
      (relCurveBasePoint C RZ z).asIdeal.ResidueField xψ = 0
  · unfold pointwiseFibreReadGerm
    simp [hxψzero]
  exact Ideal.mem_span_singleton.mpr
    (pointwiseFibreReadGerm_dvd_of_ne
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg b hz hxψ hxψzero)

set_option maxHeartbeats 8000000 in
-- This clears the fibre-stalk denominator and transports two dependent readings through
-- the chart base-change equivalence.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Fibre-germ generation supplies an affine fibre-chart cofactor, already written as
base-changed total-chart readings. -/
theorem exists_fibre_chart_cofactor_pointwiseSectionVector
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    {xψ : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hxψ : xψ ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule) :
    let p := relCurveBasePoint C RZ z
    let K := p.asIdeal.ResidueField
    let zK := relCurveResiduePoint C RZ z
    let hzK := relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
    let qK := (isAffineOpen_relPinnedChart C K π b).primeIdealOf ⟨zK, hzK⟩
    let v := pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z
    ∃ d : Γ(relCurve C K, relPinnedChart C K π b), d ∉ qK.asIdeal ∧
      d * (relPinnedTermBaseChangeAlg C RZ K π b).toLinearMap
          ((1 : K) ⊗ₜ[RZ] relThetaResSide (windowM_choice π hπ g) b le_rfl
            (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) xψ)) ∈
        Ideal.span {(relPinnedTermBaseChangeAlg C RZ K π b).toLinearMap
          ((1 : K) ⊗ₜ[RZ] relThetaResSide (windowM_choice π hπ g) b le_rfl
            (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) v))} := by
  dsimp only
  let hzK : relCurveResiduePoint C RZ z ∈
      relPinnedChart C (relCurveBasePoint C RZ z).asIdeal.ResidueField π b :=
    relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
  let qK := (isAffineOpen_relPinnedChart C
    (relCurveBasePoint C RZ z).asIdeal.ResidueField π b).primeIdealOf
      ⟨relCurveResiduePoint C RZ z, hzK⟩
  have hgerm := fibre_germ_mem_span_pointwiseSectionVector_local
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg b hz hxψ
  unfold pointwiseFibreReadGerm at hgerm
  obtain ⟨d, hdqK, hdmem⟩ :=
    IsAffineOpen.exists_notMem_primeIdealOf_mul_mem_span_singleton_of_germ_mem_span
      (isAffineOpen_relPinnedChart C
        (relCurveBasePoint C RZ z).asIdeal.ResidueField π b) hzK hgerm
  refine ⟨d, ?_, ?_⟩
  · simpa only [qK] using hdqK
  · have hxBC := relPinnedTermBaseChangeAlg_reading_windowEquiv_field
      C hπ g r₁ r₂ b₁ b₂ i j
        (relCurveBasePoint C RZ z).asIdeal.ResidueField b xψ
    have hsecBC := relPinnedTermBaseChangeAlg_reading_windowEquiv_field
      C hπ g r₁ r₂ b₁ b₂ i j
        (relCurveBasePoint C RZ z).asIdeal.ResidueField b
          (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdmem
    apply Ideal.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    calc
      _ = d * _ := congrArg (d * ·) hxBC
      _ = _ * c := hc
      _ = _ := congrArg (· * c) hsecBC.symm

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise achiever generates every universal-window reading in the
residue-fibre stalk. -/
theorem fibre_germ_mem_span_pointwiseSectionVector_local_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    {xψ : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hxψ : xψ ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule) :
    pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz xψ ∈
      Ideal.span {pointwiseFibreReadGerm C hπ g r₁ r₂ b₁ b₂ i j z b hz
        (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)} := by
  by_cases hxψzero : windowCompare RZ
      (relCurveBasePoint C RZ z).asIdeal.ResidueField xψ = 0
  · unfold pointwiseFibreReadGerm
    simp [hxψzero]
  exact Ideal.mem_span_singleton.mpr
    (pointwiseFibreReadGerm_dvd_of_ne_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg b hz hxψ hxψzero)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Decoupled fibre-germ generation supplies an affine fibre-chart cofactor, expressed as
base-changed total-chart readings. -/
theorem exists_fibre_chart_cofactor_pointwiseSectionVector_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzg : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField))
    (b : Bool) (hz : z ∈ relPinnedChart C RZ π b)
    {xψ : RZ ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hxψ : xψ ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule) :
    let p := relCurveBasePoint C RZ z
    let K := p.asIdeal.ResidueField
    let zK := relCurveResiduePoint C RZ z
    let hzK := relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
    let qK := (isAffineOpen_relPinnedChart C K π b).primeIdealOf ⟨zK, hzK⟩
    let v := pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z
    ∃ d : Γ(relCurve C K, relPinnedChart C K π b), d ∉ qK.asIdeal ∧
      d * (relPinnedTermBaseChangeAlg C RZ K π b).toLinearMap
          ((1 : K) ⊗ₜ[RZ] relThetaResSide (windowM_choice π hπ g) b le_rfl
            (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) xψ)) ∈
        Ideal.span {(relPinnedTermBaseChangeAlg C RZ K π b).toLinearMap
          ((1 : K) ⊗ₜ[RZ] relThetaResSide (windowM_choice π hπ g) b le_rfl
            (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) v))} := by
  dsimp only
  let hzK : relCurveResiduePoint C RZ z ∈
      relPinnedChart C (relCurveBasePoint C RZ z).asIdeal.ResidueField π b :=
    relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
  let qK := (isAffineOpen_relPinnedChart C
    (relCurveBasePoint C RZ z).asIdeal.ResidueField π b).primeIdealOf
      ⟨relCurveResiduePoint C RZ z, hzK⟩
  have hgerm := fibre_germ_mem_span_pointwiseSectionVector_local_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg b hz hxψ
  unfold pointwiseFibreReadGerm at hgerm
  obtain ⟨d, hdqK, hdmem⟩ :=
    IsAffineOpen.exists_notMem_primeIdealOf_mul_mem_span_singleton_of_germ_mem_span
      (isAffineOpen_relPinnedChart C
        (relCurveBasePoint C RZ z).asIdeal.ResidueField π b) hzK hgerm
  refine ⟨d, ?_, ?_⟩
  · simpa only [qK] using hdqK
  · have hxBC := relPinnedTermBaseChangeAlg_reading_windowEquiv_field
      C hπ g r₁ r₂ b₁ b₂ i j
        (relCurveBasePoint C RZ z).asIdeal.ResidueField b xψ
    have hsecBC := relPinnedTermBaseChangeAlg_reading_windowEquiv_field
      C hπ g r₁ r₂ b₁ b₂ i j
        (relCurveBasePoint C RZ z).asIdeal.ResidueField b
          (pointwiseSectionVector_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdmem
    apply Ideal.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    calc
      _ = d * _ := congrArg (d * ·) hxBC
      _ = _ * c := hc
      _ = _ := congrArg (· * c) hsecBC.symm

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
