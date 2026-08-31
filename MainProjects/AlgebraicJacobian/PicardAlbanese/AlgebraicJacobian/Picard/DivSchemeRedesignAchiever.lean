/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivBridge
import AlgebraicJacobian.RiemannRoch.BaseDivisorSpan

/-!
# G-4 redesign brick 2 — the relative achiever at a fibre point (DD-4 seed redesign)

The key new construction of the DD-4 seed redesign (`informal/spec-dd4-redesign.md` §1.2,
landing note I-0289): the seed's `sec z` must be a **relative achiever** — its `κ(p)`-fibre
reading must cut *exactly* the fibre base divisor `d_p` at `z` (minimal vanishing, order
equal to the base-divisor order), not merely be non-vanishing (the defect I-0288 isolated
in the old `windowCompare ≠ 0` section).

The achiever-lift obstruction (I-0258/0260) **dissolves through a surjection, not a rigid
reduction**: the fibre window is the `κ(p)`-span of the `Φ`-read fibre comparisons of the
universal window vectors (`divUniversalFibreKM_eq_span`, `DivSchemeSeedUnivRes.lean:376`),
so — by the achiever-purity keystone `Scheme.exists_achiever_of_span` (`BaseDivisorSpan.lean`,
the ultrametric span-minimality lemma) — the base multiplicity of the fibre window at any
closed point is already **achieved by one of the readings** `Φ(ρ_{κ(p)} x)`.  That single
reading is the fibre reading of the relative seed section `relThetaWindowEquiv … x ∈
divUniversalSeedK`.  I-0258's "a single window vector need not reduce to a *chosen* `f_p`"
is true but irrelevant: we need *some* achiever, and the span already contains one.

* `exists_achiever_relThetaWindowEquiv_mem_divUniversalSeedK` — **the core lemma** (general
  field point `K` of the tower `R_{I,J} → R_Z → K`): for any pole bound `A` with the fibre
  window inside `H⁰(𝒪(A))` and nonzero, and any closed point `z`, there is a universal
  window vector `x` whose window image lies in `divUniversalSeedK`, whose fibre comparison
  is non-vanishing, and whose `Φ`-read **achieves** the base multiplicity of the fibre
  window relative to `A` at `z`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The achiever lift at a general field point of the tower `R_{I,J} → R_Z → K` -/

section Achiever

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftAchiever : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

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
variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r₁ g r₂ i j) K]
  [IsScalarTower k (PairChartRing k g r₁ g r₂ i j) K]
  [Algebra (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower k (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower (PairChartRing k g r₁ g r₂ i j)
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack).
noncomputable local instance instIsIntegralRelCurveAchiever (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveAchiever (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveAchiever (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveAchiever (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveAchiever (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveAchiever (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 1000000 in
-- base-changed tautological towers over the pair chart ring drive the `divUniversalFibreKM`
-- span rewrite and the `divFamPhi` injectivity defeq past the defaults (recorded hatch)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **The relative achiever lift** (redesign brick 2, `informal/spec-dd4-redesign.md` §1.2):
at a field point `K` of the tower `R_{I,J} → R_Z → K`, given any pole bound `A` under which
the fibre window `divUniversalFibreKM` sits inside `H⁰(𝒪(A))` and is nonzero, and any closed
point `z`, some universal window vector `x ∈ divUniversalFstWindow` has

* its window image `relThetaWindowEquiv … x` in `divUniversalSeedK` (a relative seed
  section, by definition of `divUniversalSeedK`);
* a non-vanishing fibre comparison `windowCompare R_Z K x ≠ 0`;
* a `Φ`-read `Φ(windowCompare R_Z K x)` that **achieves** the base multiplicity of the
  fibre window relative to `A` at `z`: `(A + div Φ(…))_z = bd(divUniversalFibreKM)_z`.

This is the achiever the seed's `sec z` needs (dissolving I-0288's `hle` razor at `z`),
built by the *surjection lift* — `divUniversalFibreKM_eq_span` presents the fibre window as
the `κ(p)`-span of the readings, and `Scheme.exists_achiever_of_span` (the ultrametric
span-minimality keystone) locates an achiever *among* the readings. -/
theorem exists_achiever_relThetaWindowEquiv_mem_divUniversalSeedK
    {A : (relCurve C K).CurveDivisor}
    (hA : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
      ≤ Scheme.divisorSections K A ⊤)
    (hne : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K ≠ ⊥)
    {z : ↥(relCurve C K)} (hz : z ≠ genericPoint (relCurve C K)) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j ∧
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x ≠ 0 ∧
      ∃ hr : divFamPhi C K π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
          (windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x) ≠ 0,
        coeffAt hz (A + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
            (Units.mk0 (divFamPhi C K π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g)
                (windowCompare
                  (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
                  K x)) hr))
          = (Scheme.baseDivisorAt K (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) A
              ⟨z, hz⟩ : ℤ) := by
  classical
  -- the fibre window is the `K`-span of the `Φ`-read fibre comparisons of the window
  have hspan := divUniversalFibreKM_eq_span C hπ g r₁ r₂ b₁ b₂ i j K
  rw [hspan] at hA hne ⊢
  -- the span is nonzero, so it has a nonzero element
  have hT := (Submodule.ne_bot_iff _).mp hne
  -- the achiever of the span is achieved *on the spanning set* (ultrametric minimality)
  obtain ⟨f, hfS, hf, hach⟩ := Scheme.exists_achiever_of_span K hA hT hz
  -- unpack the achiever as a `Φ`-read of a universal window vector `x` (β-reduce the image)
  obtain ⟨x, hxW, hxf⟩ := hfS
  simp only at hxf
  refine ⟨x, hxW, Submodule.mem_map_of_mem hxW, ?_, ?_⟩
  · -- the fibre comparison is nonzero (`Φ` sends it to the nonzero achiever)
    intro h0
    exact hf (by rw [← hxf, h0, map_zero])
  · -- the `Φ`-read achieves the base multiplicity at `z`
    have hr : divFamPhi C K π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
        (windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x) ≠ 0 := by
      rw [hxf]; exact hf
    refine ⟨hr, ?_⟩
    have hunit : Units.mk0 (divFamPhi C K π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g)
          (windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x)) hr
        = Units.mk0 f hf := Units.ext hxf
    rw [hunit]
    exact hach

end Achiever

/-! ## The seed-prime instantiation: the relative achiever cutting `d_p` at every `κ(p)` -/

section SeedPrime

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftAchieverSeedPrime : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

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

noncomputable local instance instIsIntegralRelCurveAchieverSeedPrime (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveAchieverSeedPrime (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveAchieverSeedPrime (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveAchieverSeedPrime (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveAchieverSeedPrime (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveAchieverSeedPrime (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 2400000 in
-- the seed-base residue-field tower `k → R_{I,J} → R_Z → κ(p)` drives the five `κ(p)`
-- tower instances of the achiever core past the defaults (the recorded escape hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **The seed-prime relative achiever** (redesign brick 2, the deliverable the revised
`seedUniv.sec` consumes, `informal/spec-dd4-redesign.md` §1.2): at every prime `p` of the
seed base ring `R_Z`, for any closed point `z` of the fibre curve `relCurve C κ(p)` (with
`divUniversalFibreKM … κ(p)` nonzero), some universal window vector `x` has

* its window image `relThetaWindowEquiv … x` in `divUniversalSeedK` (a relative seed
  section);
* a non-vanishing fibre comparison `windowCompare R_Z κ(p) x ≠ 0`;
* a `Φ`-read that **achieves `d_p` at `z`** — cuts exactly the fibre base divisor:
  `((N − d_p) + div Φ(windowCompare R_Z κ(p) x))_z = bd(divUniversalFibreKM)_z`,
  minimal vanishing at `z`, the order equal to the base-divisor order.

This is exactly what the old `windowCompare ≠ 0` section lacked (I-0288): the reading is
not merely non-zero but a *relative achiever* at `z`, so `z` is never an extra zero and
I-0288's razor `hle` holds at `z`.  Instantiates the general achiever lift at `K := κ(p)`,
`A := N − d_p`, discharging the pole-bound hypothesis by the fibre-divisor window equality
`divUniversalSeedFibreDivisor_spec`. -/
theorem exists_relThetaWindowEquiv_mem_divUniversalSeedK_achieves_seedPrime
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    (hne : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField ≠ ⊥)
    {z : ↥(relCurve C p.asIdeal.ResidueField)}
    (hz : z ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j ∧
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField x ≠ 0 ∧
      ∃ hr : divFamPhi C p.asIdeal.ResidueField π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g)
          (windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            p.asIdeal.ResidueField x) ≠ 0,
        coeffAt hz ((windowN C p.asIdeal.ResidueField hπ g
              - divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p)
            + Scheme.divOf (relCurve C p.asIdeal.ResidueField
                ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))
                (Units.mk0 (divFamPhi C p.asIdeal.ResidueField π (windowM_choice π hπ g)
                    (relThetaPairH1_windowM C π hπ g)
                    (windowCompare
                      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
                      p.asIdeal.ResidueField x)) hr))
          = (Scheme.baseDivisorAt p.asIdeal.ResidueField
              (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField)
              (windowN C p.asIdeal.ResidueField hπ g
                - divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p)
              ⟨z, hz⟩ : ℤ) := by
  -- the fibre window is exactly `H⁰(𝒪(N − d_p))` at `κ(p)` (the fibre-divisor equality)
  have hA : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
      ≤ Scheme.divisorSections p.asIdeal.ResidueField
          (windowN C p.asIdeal.ResidueField hπ g
            - divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p) ⊤ :=
    le_of_eq (divUniversalSeedFibreDivisor_spec C hπ g r₁ r₂ b₁ b₂ i j hO hχ p).2.2.1
  -- apply the general achiever lift at `K := κ(p)`, `A := N − d_p`
  exact exists_achiever_relThetaWindowEquiv_mem_divUniversalSeedK
    C hπ g r₁ r₂ b₁ b₂ i j p.asIdeal.ResidueField hA hne hz

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- The seed-prime achiever at independent curve parameter `gamma ≤ g`. -/
theorem exists_relThetaWindowEquiv_mem_divUniversalSeedK_achieves_seedPrime_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    (hne : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField ≠ ⊥)
    {z : ↥(relCurve C p.asIdeal.ResidueField)}
    (hz : z ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j ∧
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField x ≠ 0 ∧
      ∃ hr : divFamPhi C p.asIdeal.ResidueField π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g)
          (windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            p.asIdeal.ResidueField x) ≠ 0,
        coeffAt hz ((windowN C p.asIdeal.ResidueField hπ g
              - divUniversalSeedFibreDivisor_at
                  C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p)
            + Scheme.divOf (relCurve C p.asIdeal.ResidueField
                ↘ Spec (CommRingCat.of p.asIdeal.ResidueField))
                (Units.mk0 (divFamPhi C p.asIdeal.ResidueField π (windowM_choice π hπ g)
                    (relThetaPairH1_windowM C π hπ g)
                    (windowCompare
                      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
                      p.asIdeal.ResidueField x)) hr))
          = (Scheme.baseDivisorAt p.asIdeal.ResidueField
              (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField)
              (windowN C p.asIdeal.ResidueField hπ g
                - divUniversalSeedFibreDivisor_at
                    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p)
              ⟨z, hz⟩ : ℤ) := by
  have hA : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
      ≤ Scheme.divisorSections p.asIdeal.ResidueField
          (windowN C p.asIdeal.ResidueField hπ g
            - divUniversalSeedFibreDivisor_at
                C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p) ⊤ :=
    le_of_eq (divUniversalSeedFibreDivisor_spec_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p).2.2.1
  exact exists_achiever_relThetaWindowEquiv_mem_divUniversalSeedK
    C hπ g r₁ r₂ b₁ b₂ i j p.asIdeal.ResidueField hA hne hz

end SeedPrime

end AlgebraicGeometry
