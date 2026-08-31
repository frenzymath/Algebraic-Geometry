/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivPointwise
import AlgebraicJacobian.Picard.DivSchemeRedesignFibreToStalkFlat
import AlgebraicJacobian.Picard.DivSchemeRedesignChartReadIdeal

/-!
# The flat-quotient reduction for the pointwise seed

This file joins the two completed sides of the non-generic point argument.

* The chosen pointwise section is the fibre achiever, hence its reading divides every
  universal-window reading in the stalk of the residue-field fibre.
* If the genuine chart-reading quotient is flat over the seed base, the fibre-to-stalk
  Nakayama theorem lifts a denominator-cleared fibre containment to local generation in
  the total chart, which is exactly the input for pointwise RD-N.

The remaining geometric transport is kept explicit: fibre-stalk divisibility must be
converted to the denominator-cleared containment modulo the contracted base prime used by
`FibreToStalkFlat`.  This is the precise bridge between the two bullets; neither finite-window
projectivity nor equality of reading ideals supplies it by itself.
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

noncomputable local instance instOverCleftPointwiseFlat :
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

noncomputable local instance instIsIntegralRelCurvePointwiseFlat
    (L : Type u) [Field L] [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwiseFlat
    (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwiseFlat
    (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwiseFlat
    (L : Type u) [Field L] [Algebra k L] :
    LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

/-! ## Finite generation of the genuine reading ideal -/

set_option linter.unusedSectionVars false in
/-- The genuine chart-reading ideal is finitely generated whenever the seed window is finite
over the base.  Its scalar-extension presentation is `chartReadIdealMap`. -/
theorem chartReadIdeal_fg_of_finite
    {R : Type u} [CommRing R] [Algebra k R]
    (K : Submodule R (relThetaSections C R π (windowM_choice π hπ g)))
    [Module.Finite R ↥K] (b : Bool) : (chartReadIdeal K b).FG := by
  rw [← range_chartReadIdealMap K b, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map (chartReadIdealMap K b)

/-! ## The exact fibre-containment input -/

set_option maxHeartbeats 2400000 in
-- The dependent pointwise chart and contracted-prime types exceed the default budget.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The denominator-cleared form of fibre-local divisibility needed by the flat-quotient
Nakayama lift.  The fibre achiever proves the corresponding statement after mapping to the
stalk of the residue-field fibre.  The remaining base-change transport must turn that germ
statement into this containment modulo the contracted base prime. -/
abbrev PointwiseSeedFibreContainment : Prop :=
  ∀ (z : relCurve C RZ),
    relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) →
    ∀ ⦃ψ : relThetaSections C RZ π (windowM_choice π hπ g)⦄,
      ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
      ∃ r : Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)),
        r ∉ ((isAffineOpen_relPinnedChart C RZ π
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
              ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩).asIdeal ∧
        r * relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ ∈
          Ideal.span {relThetaResSide (windowM_choice π hπ g)
              (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
              (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)} ⊔
            Ideal.map
              (algebraMap RZ Γ(relCurve C RZ,
                relPinnedChart C RZ π
                  (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)))
              (Ideal.comap
                (algebraMap RZ Γ(relCurve C RZ,
                  relPinnedChart C RZ π
                    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)))
                ((isAffineOpen_relPinnedChart C RZ π
                    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
                  ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩).asIdeal)

set_option maxHeartbeats 2400000 in
-- The flat quotient, ideal-span induction, and pointwise support type elaborate together.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- If the two genuine chart-reading quotients are flat over the seed base, the only
remaining input for the non-generic RD-N branch is the denominator-cleared fibre
containment above.  The proof extends that containment from the window readings to their
genuine chart ideal and applies the fibre-to-stalk Nakayama bridge. -/
theorem pointwiseSeedClosedRDN_of_flat_chartReadIdeal_quotient_of_fibreContainment
    (hflat : ∀ b : Bool,
      Module.Flat RZ
        (Γ(relCurve C RZ, relPinnedChart C RZ π b) ⧸
          chartReadIdeal (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))
    (hfibre : PointwiseSeedFibreContainment
      C hπ g r₁ r₂ b₁ b₂ i j hO hχ) :
    PointwiseSeedClosedRDN C hπ g r₁ r₂ b₁ b₂ i j hO hχ := by
  intro z hzg
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  let b : Bool := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z
  let hz : z ∈ relPinnedChart C RZ π b := by
    simpa only [b] using pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z
  let B : Type u := Γ(relCurve C RZ, relPinnedChart C RZ π b)
  let J : Ideal B :=
    chartReadIdeal (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
  let q : PrimeSpectrum B :=
    (isAffineOpen_relPinnedChart C RZ π b).primeIdealOf ⟨z, hz⟩
  let e : B := relThetaResSide (windowM_choice π hπ g) b le_rfl
    (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z)
  let I : Ideal B := Ideal.span {e} ⊔
    Ideal.map (algebraMap RZ B) (Ideal.comap (algebraMap RZ B) q.asIdeal)
  haveI : Module.Flat RZ (B ⧸ J) := by
    simpa only [B, J] using hflat b
  have hJfg : J.FG := by
    simpa only [J, B] using chartReadIdeal_fg_of_finite
      C hπ g (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
  have he : e ∈ J := by
    change relThetaResSide (windowM_choice π hπ g) b le_rfl
        (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) ∈
      Ideal.span (Set.range
        (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))
    exact Ideal.subset_span
      ⟨⟨pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z,
        pointwiseSection_mem C hπ g r₁ r₂ b₁ b₂ i j hO hχ z⟩, rfl⟩
  have hgen : ∀ x : J, ∃ r : B, r ∉ q.asIdeal ∧ r * (x : B) ∈ I := by
    intro x
    refine Submodule.span_induction
      (p := fun y _ => ∃ r : B, r ∉ q.asIdeal ∧ r * y ∈ I) ?_ ?_ ?_ ?_ x.2
    · rintro y ⟨ψ, rfl⟩
      obtain ⟨r, hr, hry⟩ := hfibre z hzg ψ.2
      refine ⟨r, ?_, ?_⟩
      · simpa only [q, b, B] using hr
      · change r * relThetaResSide (windowM_choice π hπ g) b le_rfl
            (ψ : relThetaSections C RZ π (windowM_choice π hπ g)) ∈ I
        simpa only [I, e, q, b, B] using hry
    · refine ⟨1, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top, ?_⟩
      simpa only [one_mul] using I.zero_mem
    · rintro y₁ y₂ _ _ ⟨r₁, hr₁, hy₁⟩ ⟨r₂, hr₂, hy₂⟩
      refine ⟨r₁ * r₂, fun h => (q.isPrime.mem_or_mem h).elim hr₁ hr₂, ?_⟩
      have h₁ : r₂ * (r₁ * y₁) ∈ I := I.mul_mem_left r₂ hy₁
      have h₂ : r₁ * (r₂ * y₂) ∈ I := I.mul_mem_left r₁ hy₂
      convert I.add_mem h₁ h₂ using 1
      all_goals ring
    · rintro c y _ ⟨r, hr, hy⟩
      refine ⟨r, hr, ?_⟩
      convert I.mul_mem_left c hy using 1
      all_goals ring
  have hlocal : ∀ x : J, ∃ r : B, r ∉ q.asIdeal ∧
      r * (x : B) ∈ Ideal.span ({e} : Set B) := by
    apply FibreToStalkFlat.exists_notMem_mul_mem_span_singleton_of_fibre_of_flat_quotient
      (R := RZ) q J hJfg e he
    intro x
    simpa only [I] using hgen x
  apply notMem_support_chartColengthModule_of_forall_exists_notMem_mul_read_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
    (pointwiseSection C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) hz
  intro ψ hψ
  have hread : relThetaResSide (windowM_choice π hπ g) b le_rfl ψ ∈ J := by
    change relThetaResSide (windowM_choice π hπ g) b le_rfl ψ ∈
      Ideal.span (Set.range
        (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))
    exact Ideal.subset_span ⟨⟨ψ, hψ⟩, rfl⟩
  exact hlocal ⟨_, hread⟩

/-! ## Decoupled flat-quotient bridge -/

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The denominator-cleared fibre containment for divisor degree `g` and curve parameter
`gamma ≤ g`. -/
abbrev PointwiseSeedFibreContainmentAt {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) : Prop :=
  ∀ (z : relCurve C RZ),
    relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField) →
    ∀ {ψ : relThetaSections C RZ π (windowM_choice π hπ g)},
      ψ ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j →
      ∃ r : Γ(relCurve C RZ,
          relPinnedChart C RZ π (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)),
        r ∉ ((isAffineOpen_relPinnedChart C RZ π
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
              ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩).asIdeal ∧
        r * relThetaResSide (windowM_choice π hπ g)
            (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl ψ ∈
          Ideal.span {relThetaResSide (windowM_choice π hπ g)
              (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z) le_rfl
              (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)} ⊔
            Ideal.map
              (algebraMap RZ Γ(relCurve C RZ,
                relPinnedChart C RZ π
                  (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)))
              (Ideal.comap
                (algebraMap RZ Γ(relCurve C RZ,
                  relPinnedChart C RZ π
                    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)))
                ((isAffineOpen_relPinnedChart C RZ π
                    (pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z)).primeIdealOf
                  ⟨z, pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z⟩).asIdeal)

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- Flat chart-reading quotients lift decoupled fibre containment to the closed-point
RD-N branch. -/
theorem pointwiseSeedClosedRDNAt_of_flat_chartReadIdeal_quotient_of_fibreContainment
    {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hflat : ∀ b : Bool,
      Module.Flat RZ
        (Γ(relCurve C RZ, relPinnedChart C RZ π b) ⧸
          chartReadIdeal (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))
    (hfibre : PointwiseSeedFibreContainmentAt
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ) :
    PointwiseSeedClosedRDNAt C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ := by
  intro z hzg
  haveI := finite_divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j
  let b : Bool := pointwiseSide C hπ g r₁ r₂ b₁ b₂ i j z
  let hz : z ∈ relPinnedChart C RZ π b := by
    simpa only [b] using pointwiseSide_mem C hπ g r₁ r₂ b₁ b₂ i j z
  let B : Type u := Γ(relCurve C RZ, relPinnedChart C RZ π b)
  let J : Ideal B :=
    chartReadIdeal (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
  let q : PrimeSpectrum B :=
    (isAffineOpen_relPinnedChart C RZ π b).primeIdealOf ⟨z, hz⟩
  let e : B := relThetaResSide (windowM_choice π hπ g) b le_rfl
    (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z)
  let I : Ideal B := Ideal.span {e} ⊔
    Ideal.map (algebraMap RZ B) (Ideal.comap (algebraMap RZ B) q.asIdeal)
  haveI : Module.Flat RZ (B ⧸ J) := by
    simpa only [B, J] using hflat b
  have hJfg : J.FG := by
    simpa only [J, B] using chartReadIdeal_fg_of_finite
      C hπ g (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
  have he : e ∈ J := by
    change relThetaResSide (windowM_choice π hπ g) b le_rfl
        (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) ∈
      Ideal.span (Set.range
        (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))
    exact Ideal.subset_span
      ⟨⟨pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z,
        pointwiseSection_mem_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z⟩, rfl⟩
  have hgen : ∀ x : J, ∃ r : B, r ∉ q.asIdeal ∧ r * (x : B) ∈ I := by
    intro x
    refine Submodule.span_induction
      (p := fun y _ => ∃ r : B, r ∉ q.asIdeal ∧ r * y ∈ I) ?_ ?_ ?_ ?_ x.2
    · rintro y ⟨ψ, rfl⟩
      obtain ⟨r, hr, hry⟩ := hfibre z hzg ψ.2
      refine ⟨r, ?_, ?_⟩
      · simpa only [q, b, B] using hr
      · change r * relThetaResSide (windowM_choice π hπ g) b le_rfl
            (ψ : relThetaSections C RZ π (windowM_choice π hπ g)) ∈ I
        simpa only [I, e, q, b, B] using hry
    · refine ⟨1, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top, ?_⟩
      simpa only [one_mul] using I.zero_mem
    · rintro y₁ y₂ _ _ ⟨r₁, hr₁, hy₁⟩ ⟨r₂, hr₂, hy₂⟩
      refine ⟨r₁ * r₂, fun h => (q.isPrime.mem_or_mem h).elim hr₁ hr₂, ?_⟩
      have h₁ : r₂ * (r₁ * y₁) ∈ I := I.mul_mem_left r₂ hy₁
      have h₂ : r₁ * (r₂ * y₂) ∈ I := I.mul_mem_left r₁ hy₂
      convert I.add_mem h₁ h₂ using 1
      all_goals ring
    · rintro c y _ ⟨r, hr, hy⟩
      refine ⟨r, hr, ?_⟩
      convert I.mul_mem_left c hy using 1
      all_goals ring
  have hlocal : ∀ x : J, ∃ r : B, r ∉ q.asIdeal ∧
      r * (x : B) ∈ Ideal.span ({e} : Set B) := by
    apply FibreToStalkFlat.exists_notMem_mul_mem_span_singleton_of_fibre_of_flat_quotient
      (R := RZ) q J hJfg e he
    intro x
    simpa only [I] using hgen x
  apply notMem_support_chartColengthModule_of_forall_exists_notMem_mul_read_mem_span
    (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b
    (pointwiseSection_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) hz
  intro ψ hψ
  have hread : relThetaResSide (windowM_choice π hπ g) b le_rfl ψ ∈ J := by
    change relThetaResSide (windowM_choice π hπ g) b le_rfl ψ ∈
      Ideal.span (Set.range
        (chartReadMap (divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j) b))
    exact Ideal.subset_span ⟨⟨ψ, hψ⟩, rfl⟩
  exact hlocal ⟨_, hread⟩

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
