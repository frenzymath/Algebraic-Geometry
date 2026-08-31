/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwiseFibreLocal

/-!
# Residue-fibre descent for the pointwise seed

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

noncomputable local instance instOverCleftPointwiseFibreWrapper :
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

noncomputable local instance instIsIntegralRelCurvePointwiseFibreWrapper
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseFibreWrapper
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseFibreWrapper
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwiseFibreWrapper
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
theorem fibre_germ_mem_span_pointwiseSectionVector
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
  exact fibre_germ_mem_span_pointwiseSectionVector_local
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg b hz hxψ

set_option maxHeartbeats 8000000 in
-- This assembles the seed equivalence, two affine point primes, and both denominator
-- clearing steps in the dependent residue-field tower.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Fibre-stalk divisibility of the pointwise achiever gives the denominator-cleared
containment modulo the contracted base prime required by the flat-quotient bridge. -/
theorem pointwiseSeedFibreContainment :
    PointwiseSeedFibreContainment
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ := by
  intro z hzg ψ hψ
  let b : Bool := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z
  let hz : z ∈ relPinnedChart C RZ π b := by
    simpa only [b] using pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let hzK : zK ∈ relPinnedChart C K π b :=
    relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
  let q := (isAffineOpen_relPinnedChart C RZ π b).primeIdealOf ⟨z, hz⟩
  let qK := (isAffineOpen_relPinnedChart C K π b).primeIdealOf ⟨zK, hzK⟩
  let e := relPinnedTermBaseChangeAlg C RZ K π b
  let xψ : ↥(divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule :=
    (divUniversalSeedKEquiv C π hπ g r₁ r₂ b₁ b₂ i j).symm ⟨ψ, hψ⟩
  have hxψeq : relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) (xψ : _) = ψ := by
    exact congrArg Subtype.val
      ((divUniversalSeedKEquiv C π hπ g r₁ r₂ b₁ b₂ i j).apply_symm_apply
        ⟨ψ, hψ⟩)
  obtain ⟨d, hdqK, hdmem⟩ :=
    exists_fibre_chart_cofactor_pointwiseSectionVector
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ z hzg b hz xψ.property
  have hlocal : ∃ d : Γ(relCurve C K, relPinnedChart C K π b),
      d ∉ qK.asIdeal ∧
      d * e.toLinearMap ((1 : K) ⊗ₜ[RZ]
          relThetaResSide (windowM_choice π hπ g) b le_rfl ψ) ∈
        Ideal.span {e.toLinearMap ((1 : K) ⊗ₜ[RZ]
          relThetaResSide (windowM_choice π hπ g) b le_rfl
            (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))} := by
    refine ⟨d, ?_, ?_⟩
    · simpa only [qK] using hdqK
    · have hxRead := congrArg
        (fun θ => e.toLinearMap ((1 : K) ⊗ₜ[RZ]
          relThetaResSide (windowM_choice π hπ g) b le_rfl θ)) hxψeq
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdmem
      apply Ideal.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      calc
        _ = d * e.toLinearMap ((1 : K) ⊗ₜ[RZ]
            relThetaResSide (windowM_choice π hπ g) b le_rfl
              (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) (xψ : _))) :=
          congrArg (d * ·) hxRead.symm
        _ = e.toLinearMap ((1 : K) ⊗ₜ[RZ]
            relThetaResSide (windowM_choice π hπ g) b le_rfl
              (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g)
                (pointwiseSectionVector C hπ g r₁ r₂ b₁ b₂ i j hO hχ z))) * c := hc
        _ = _ := rfl
  have hqcompat : ∀ a : Γ(relCurve C RZ, relPinnedChart C RZ π b),
      e.toLinearMap ((1 : K) ⊗ₜ[RZ] a) ∈ qK.asIdeal ↔ a ∈ q.asIdeal := by
    intro a
    have hone : (relPinnedTermBaseChangeAlg C RZ K π b).toLinearMap
        ((1 : K) ⊗ₜ[RZ] a) = relPinnedSectionsMap C RZ K π b a :=
      relPinnedTermBaseChangeAlg_one_tmul C RZ K π b a
    rw [show e.toLinearMap ((1 : K) ⊗ₜ[RZ] a) =
      relPinnedSectionsMap C RZ K π b a from hone]
    have hbase : (relCurveMap C RZ K) zK = z := by
      simpa only [K, zK] using relCurveMap_relCurveResiduePoint C RZ z
    let hzbase : (relCurveMap C RZ K) zK ∈ relPinnedChart C RZ π b := by
      change zK ∈ relCurveMap C RZ K ⁻¹ᵁ relPinnedChart C RZ π b
      rw [relCurveMap_preimage_relPinnedChart C RZ (π := π) b K]
      exact hzK
    let zbase : relPinnedChart C RZ π b :=
      ⟨(relCurveMap C RZ K) zK, hzbase⟩
    have hraw := relPinnedSectionsMap_mem_primeIdealOf_iff
      C RZ K (π := π) b hzK a
    have h : relPinnedSectionsMap C RZ K π b a ∈ qK.asIdeal ↔
        a ∈ ((isAffineOpen_relPinnedChart C RZ π b).primeIdealOf zbase).asIdeal := by
      simpa only [qK, zK, zbase] using hraw
    have hpoint : zbase = ⟨z, hz⟩ := Subtype.ext hbase
    have hprime :
        ((isAffineOpen_relPinnedChart C RZ π b).primeIdealOf zbase).asIdeal =
          q.asIdeal := by
      simpa only [q] using congrArg
        (fun w => ((isAffineOpen_relPinnedChart C RZ π b).primeIdealOf w).asIdeal)
        hpoint
    rw [hprime] at h
    exact h
  have hdesc := exists_notMem_mul_mem_sup_map_of_fibre_local
    (s := (relCurveBasePoint C RZ z).asIdeal) q.asIdeal e qK.asIdeal hqcompat hlocal
  simpa only [b, hz, q] using hdesc

set_option maxHeartbeats 2400000 in
-- This corollary packages the completed fibre descent for the existing flat-quotient
-- Nakayama bridge.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Flatness of the two chart-reading quotients now implies the closed-point RD-N branch,
with no separate fibre-containment hypothesis. -/
theorem pointwiseSeedClosedRDN_of_flat_chartReadIdeal_quotient
    (hflat : ∀ b : Bool,
      Module.Flat RZ
        (Γ(relCurve C RZ, relPinnedChart C RZ π b) ⧸
          chartReadIdeal (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)) :
    PointwiseSeedClosedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ :=
  pointwiseSeedClosedRDN_of_flat_chartReadIdeal_quotient_of_fibreContainment
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ hflat
      (pointwiseSeedFibreContainment C hπ g r₁ r₂ b₁ b₂ i j hO hχ)

/-! ## Decoupled residue-fibre descent -/

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled pointwise achiever generates every universal-window reading in the
residue-fibre stalk. -/
theorem fibre_germ_mem_span_pointwiseSectionVector_at {gamma : ℕ}
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
  exact fibre_germ_mem_span_pointwiseSectionVector_local_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg b hz hxψ

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Fibre-stalk divisibility of the decoupled pointwise achiever gives the
denominator-cleared containment required by the flat-quotient bridge. -/
theorem pointwiseSeedFibreContainment_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    PointwiseSeedFibreContainmentAt
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ := by
  intro z hzg ψ hψ
  let b : Bool := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z
  let hz : z ∈ relPinnedChart C RZ π b := by
    simpa only [b] using pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z
  let K := (relCurveBasePoint C RZ z).asIdeal.ResidueField
  let zK := relCurveResiduePoint C RZ z
  let hzK : zK ∈ relPinnedChart C K π b :=
    relCurveResiduePoint_mem_relPinnedChart C RZ (π := π) b hz
  let q := (isAffineOpen_relPinnedChart C RZ π b).primeIdealOf ⟨z, hz⟩
  let qK := (isAffineOpen_relPinnedChart C K π b).primeIdealOf ⟨zK, hzK⟩
  let e := relPinnedTermBaseChangeAlg C RZ K π b
  let xψ : ↥(divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule :=
    (divUniversalSeedKEquiv C π hπ g r₁ r₂ b₁ b₂ i j).symm ⟨ψ, hψ⟩
  have hxψeq : relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) (xψ : _) = ψ := by
    exact congrArg Subtype.val
      ((divUniversalSeedKEquiv C π hπ g r₁ r₂ b₁ b₂ i j).apply_symm_apply
        ⟨ψ, hψ⟩)
  obtain ⟨d, hdqK, hdmem⟩ :=
    exists_fibre_chart_cofactor_pointwiseSectionVector_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z hzg b hz xψ.property
  have hlocal : ∃ d : Γ(relCurve C K, relPinnedChart C K π b),
      d ∉ qK.asIdeal ∧
      d * e.toLinearMap ((1 : K) ⊗ₜ[RZ]
          relThetaResSide (windowM_choice π hπ g) b le_rfl ψ) ∈
        Ideal.span {e.toLinearMap ((1 : K) ⊗ₜ[RZ]
          relThetaResSide (windowM_choice π hπ g) b le_rfl
            (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))} := by
    refine ⟨d, ?_, ?_⟩
    · simpa only [qK] using hdqK
    · have hxRead := congrArg
        (fun θ => e.toLinearMap ((1 : K) ⊗ₜ[RZ]
          relThetaResSide (windowM_choice π hπ g) b le_rfl θ)) hxψeq
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdmem
      apply Ideal.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      calc
        _ = d * e.toLinearMap ((1 : K) ⊗ₜ[RZ]
            relThetaResSide (windowM_choice π hπ g) b le_rfl
              (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) (xψ : _))) :=
          congrArg (d * ·) hxRead.symm
        _ = e.toLinearMap ((1 : K) ⊗ₜ[RZ]
            relThetaResSide (windowM_choice π hπ g) b le_rfl
              (relThetaWindowEquiv C RZ π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g)
                (pointwiseSectionVector_at
                  C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z))) * c := hc
        _ = _ := rfl
  have hqcompat : ∀ a : Γ(relCurve C RZ, relPinnedChart C RZ π b),
      e.toLinearMap ((1 : K) ⊗ₜ[RZ] a) ∈ qK.asIdeal ↔ a ∈ q.asIdeal := by
    intro a
    have hone : (relPinnedTermBaseChangeAlg C RZ K π b).toLinearMap
        ((1 : K) ⊗ₜ[RZ] a) = relPinnedSectionsMap C RZ K π b a :=
      relPinnedTermBaseChangeAlg_one_tmul C RZ K π b a
    rw [show e.toLinearMap ((1 : K) ⊗ₜ[RZ] a) =
      relPinnedSectionsMap C RZ K π b a from hone]
    have hbase : (relCurveMap C RZ K) zK = z := by
      simpa only [K, zK] using relCurveMap_relCurveResiduePoint C RZ z
    let hzbase : (relCurveMap C RZ K) zK ∈ relPinnedChart C RZ π b := by
      change zK ∈ relCurveMap C RZ K ⁻¹ᵁ relPinnedChart C RZ π b
      rw [relCurveMap_preimage_relPinnedChart C RZ (π := π) b K]
      exact hzK
    let zbase : relPinnedChart C RZ π b :=
      ⟨(relCurveMap C RZ K) zK, hzbase⟩
    have hraw := relPinnedSectionsMap_mem_primeIdealOf_iff
      C RZ K (π := π) b hzK a
    have h : relPinnedSectionsMap C RZ K π b a ∈ qK.asIdeal ↔
        a ∈ ((isAffineOpen_relPinnedChart C RZ π b).primeIdealOf zbase).asIdeal := by
      simpa only [qK, zK, zbase] using hraw
    have hpoint : zbase = ⟨z, hz⟩ := Subtype.ext hbase
    have hprime :
        ((isAffineOpen_relPinnedChart C RZ π b).primeIdealOf zbase).asIdeal =
          q.asIdeal := by
      simpa only [q] using congrArg
        (fun w => ((isAffineOpen_relPinnedChart C RZ π b).primeIdealOf w).asIdeal)
        hpoint
    rw [hprime] at h
    exact h
  have hdesc := exists_notMem_mul_mem_sup_map_of_fibre_local
    (s := (relCurveBasePoint C RZ z).asIdeal) q.asIdeal e qK.asIdeal hqcompat hlocal
  simpa only [b, hz, q] using hdesc

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Flat chart-reading quotients imply the decoupled closed-point RD-N branch. -/
theorem pointwiseSeedClosedRDNAt_of_flat_chartReadIdeal_quotient {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hflat : ∀ b : Bool,
      Module.Flat RZ
        (Γ(relCurve C RZ, relPinnedChart C RZ π b) ⧸
          chartReadIdeal (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b)) :
    PointwiseSeedClosedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ :=
  pointwiseSeedClosedRDNAt_of_flat_chartReadIdeal_quotient_of_fibreContainment
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ hflat
      (pointwiseSeedFibreContainment_at
        C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ)

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
