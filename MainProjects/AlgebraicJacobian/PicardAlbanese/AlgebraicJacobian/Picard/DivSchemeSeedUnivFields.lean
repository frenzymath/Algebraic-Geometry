/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivRead

/-!
# G-4 — the universal seed fibre divisor at every seed-base prime (I-0247 step (a))

The `d_q` input of the universal-seed achiever lift, made available at **every** prime of
the seed base ring `R_Z = DivCarveChartRing k A B g r₁ r₂ b₁ b₂ i j` (not only at primes
of the pair chart ring).  Every residue field `κ(p)` of `R_Z` kills the carve ideal over
the pair chart ring — the kill law `divCarveIdeal_le_ker_of_tower` fires through the
canonical tower `R_{I,J} → R_Z → κ(p)` — so the κ-assembly keystone
`existsUnique_effective_divisor_divUniversalFibre` applies at every `κ(p)`:

* `existsUnique_effective_divisor_divUniversalFibre_seedPrime` — the unique effective
  degree-`g` divisor cutting both fibre windows, at `κ(p)` for every `p : Spec R_Z`;
* `divUniversalSeedFibreDivisor` / `_spec` / `_unique` — the named fibre divisor `d_p`
  at every seed-base point, the effective degree-`g` divisor the achiever consumes.
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

/-! ## The seed fibre divisor at every prime of `R_Z` -/

section SeedFibreDivisor

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedFields : C.left.Over (Spec (.of k)) :=
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

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack).
noncomputable local instance instIsIntegralRelCurveSeedFields (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSeedFields (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSeedFields (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSeedFields (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSeedFields (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveSeedFields (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

set_option synthInstance.maxHeartbeats 800000 in
-- the canonical residue-field tower `k → R_{I,J} → R_Z → κ(p)` exceeds the default
-- search budget and the project-default pending depth (the recorded
-- `divUniversal_carve_residueField` escape hatch, one step longer)
set_option maxSynthPendingDepth 8 in
include hO hχ in
/-- **The seed-base κ(p) assembly**: at every prime `p` of the seed base ring `R_Z`, the
universal fibre windows at the residue field `κ(p)` cut a **unique effective divisor of
degree `g`** with both window equalities — the fibre divisor `d_p` of the universal seed.
Every `κ(p)` kills the carve ideal over the pair chart ring by the kill law
`divCarveIdeal_le_ker_of_tower` fired through the canonical tower `R_{I,J} → R_Z → κ(p)`,
so the κ-assembly keystone applies. -/
theorem existsUnique_effective_divisor_divUniversalFibre_seedPrime
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃! D : (relCurve C p.asIdeal.ResidueField).CurveDivisor,
      0 ≤ D ∧ CurveDivisor.deg p.asIdeal.ResidueField D = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g - D) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g
              + windowS C p.asIdeal.ResidueField hπ g - D) ⊤ :=
  existsUnique_effective_divisor_divUniversalFibre C hπ g r₁ r₂ b₁ b₂ i j
    p.asIdeal.ResidueField hO hχ
    (divCarveIdeal_le_ker_of_tower k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      p.asIdeal.ResidueField)

set_option synthInstance.maxHeartbeats 800000 in
-- the canonical residue-field tower `k → R_{I,J} → R_Z → κ(p)` escape hatch
set_option maxSynthPendingDepth 8 in
include hO hχ in
/-- **The universal seed fibre divisor** `d_p` at a seed-base point: the unique effective
degree-`g` divisor cutting both fibre windows at `κ(p)`. -/
noncomputable def divUniversalSeedFibreDivisor
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    (relCurve C p.asIdeal.ResidueField).CurveDivisor :=
  (existsUnique_effective_divisor_divUniversalFibre_seedPrime
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ p).exists.choose

set_option synthInstance.maxHeartbeats 800000 in
-- the canonical residue-field tower `k → R_{I,J} → R_Z → κ(p)` escape hatch
set_option maxSynthPendingDepth 8 in
include hO hχ in
/-- The defining property of the universal seed fibre divisor: effective, of degree `g`,
cutting both fibre windows. -/
theorem divUniversalSeedFibreDivisor_spec
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    0 ≤ divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p ∧
      CurveDivisor.deg p.asIdeal.ResidueField
          (divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p) = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g
              - divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g + windowS C p.asIdeal.ResidueField hπ g
              - divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p) ⊤ :=
  (existsUnique_effective_divisor_divUniversalFibre_seedPrime
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ p).exists.choose_spec

set_option maxHeartbeats 2400000 in
-- The residue-field tower and transported window facts exceed the default budgets.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- **The universal fibre window has no residual base multiplicity.**  At every closed
point of the residue fibre, the exact window description
`K_M(p) = H⁰(𝒪(N - d_p))` and the transported normalization theorem force the base
multiplicity relative to `N - d_p` to vanish. -/
theorem divUniversalSeedFibreDivisor_residual_baseDivisorAt_eq_zero
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    {z : relCurve C p.asIdeal.ResidueField}
    (hzg : z ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    (Scheme.baseDivisorAt p.asIdeal.ResidueField
      (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField)
      (windowN C p.asIdeal.ResidueField hπ g
        - divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p)
      ⟨z, hzg⟩ : ℤ) = 0 := by
  have hχp : Sheaf.chi ((relCurve C p.asIdeal.ResidueField).moduleKSheaf
      p.asIdeal.ResidueField) = 1 - (g : ℤ) :=
    chi_relCurve_baseField C p.asIdeal.ResidueField g hχ
  have hspec := divUniversalSeedFibreDivisor_spec
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ p
  rw [hspec.2.2.1]
  exact baseDivisorAt_window_residual_eq_zero g
    (h0_relCurve_baseField C p.asIdeal.ResidueField) hχp
    (windowN C p.asIdeal.ResidueField hπ g)
    (fun D' hD' => subsingleton_h1_windowN_sub
      C p.asIdeal.ResidueField hπ g hO hχ hχp D' hD')
    (two_mul_genus_le_deg_windowN
      C p.asIdeal.ResidueField hπ g hO hχ)
    (divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p)
    hspec.1 hspec.2.1 hzg

set_option synthInstance.maxHeartbeats 800000 in
-- the canonical residue-field tower `k → R_{I,J} → R_Z → κ(p)` escape hatch
set_option maxSynthPendingDepth 8 in
include hO hχ in
/-- **Uniqueness** of the universal seed fibre divisor: any effective degree-`g` divisor
cutting both fibre windows at `κ(p)` is `divUniversalSeedFibreDivisor`. -/
theorem divUniversalSeedFibreDivisor_unique
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    {D : (relCurve C p.asIdeal.ResidueField).CurveDivisor} (h0D : 0 ≤ D)
    (hdeg : CurveDivisor.deg p.asIdeal.ResidueField D = (g : ℤ))
    (hKM : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
      = Scheme.divisorSections p.asIdeal.ResidueField
          (windowN C p.asIdeal.ResidueField hπ g - D) ⊤)
    (hK' : divUniversalFibreK' C hπ g r₁ r₂ b₂ i j p.asIdeal.ResidueField
      = Scheme.divisorSections p.asIdeal.ResidueField
          (windowN C p.asIdeal.ResidueField hπ g + windowS C p.asIdeal.ResidueField hπ g
            - D) ⊤) :
    D = divUniversalSeedFibreDivisor C hπ g r₁ r₂ b₁ b₂ i j hO hχ p :=
  (existsUnique_effective_divisor_divUniversalFibre_seedPrime
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ p).unique ⟨h0D, hdeg, hKM, hK'⟩
    (divUniversalSeedFibreDivisor_spec C hπ g r₁ r₂ b₁ b₂ i j hO hχ p)

set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- The decoupled seed-base κ(p) assembly. -/
theorem existsUnique_effective_divisor_divUniversalFibre_seedPrime_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    ∃! D : (relCurve C p.asIdeal.ResidueField).CurveDivisor,
      0 ≤ D ∧ CurveDivisor.deg p.asIdeal.ResidueField D = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g - D) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g
              + windowS C p.asIdeal.ResidueField hπ g - D) ⊤ :=
  existsUnique_effective_divisor_divUniversalFibre_at C hπ g r₁ r₂ b₁ b₂ i j
    p.asIdeal.ResidueField hgamma hχ
    (divCarveIdeal_le_ker_of_tower k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j
      p.asIdeal.ResidueField)

set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- The universal seed fibre divisor at curve parameter `gamma ≤ g`. -/
noncomputable def divUniversalSeedFibreDivisor_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    (relCurve C p.asIdeal.ResidueField).CurveDivisor :=
  (existsUnique_effective_divisor_divUniversalFibre_seedPrime_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p).exists.choose

set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- Effective degree and two-window specification of the decoupled seed fibre divisor. -/
theorem divUniversalSeedFibreDivisor_spec_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) :
    0 ≤ divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p ∧
      CurveDivisor.deg p.asIdeal.ResidueField
          (divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p)
        = (g : ℤ) ∧
      divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g
              - divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p) ⊤ ∧
      divUniversalFibreK' C hπ g r₁ r₂ b₂ i j p.asIdeal.ResidueField
        = Scheme.divisorSections p.asIdeal.ResidueField
            (windowN C p.asIdeal.ResidueField hπ g + windowS C p.asIdeal.ResidueField hπ g
              - divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p) ⊤ :=
  (existsUnique_effective_divisor_divUniversalFibre_seedPrime_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p).exists.choose_spec

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
/-- The decoupled universal fibre window has no residual base multiplicity. -/
theorem divUniversalSeedFibreDivisor_residual_baseDivisorAt_eq_zero_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    {z : relCurve C p.asIdeal.ResidueField}
    (hzg : z ≠ genericPoint (relCurve C p.asIdeal.ResidueField)) :
    (Scheme.baseDivisorAt p.asIdeal.ResidueField
      (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField)
      (windowN C p.asIdeal.ResidueField hπ g
        - divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p)
      ⟨z, hzg⟩ : ℤ) = 0 := by
  have hχp : Sheaf.chi ((relCurve C p.asIdeal.ResidueField).moduleKSheaf
      p.asIdeal.ResidueField) = 1 - (gamma : ℤ) :=
    chi_relCurve_baseField C p.asIdeal.ResidueField gamma hχ
  have hspec := divUniversalSeedFibreDivisor_spec_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p
  rw [hspec.2.2.1]
  exact baseDivisorAt_window_residual_eq_zero (gamma := gamma) g
    (h0_relCurve_baseField C p.asIdeal.ResidueField) hχp
    (windowN C p.asIdeal.ResidueField hπ g)
    (fun D' hD' => subsingleton_h1_windowN_sub_at
      C p.asIdeal.ResidueField hπ g hχp D' hD' hgamma)
    (two_mul_degree_le_deg_windowN C p.asIdeal.ResidueField hπ g)
    (divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p)
    hspec.1 hspec.2.1 hzg (hgamma := hgamma)

set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
/-- Uniqueness of the decoupled universal seed fibre divisor. -/
theorem divUniversalSeedFibreDivisor_unique_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    {D : (relCurve C p.asIdeal.ResidueField).CurveDivisor} (h0D : 0 ≤ D)
    (hdeg : CurveDivisor.deg p.asIdeal.ResidueField D = (g : ℤ))
    (hKM : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField
      = Scheme.divisorSections p.asIdeal.ResidueField
          (windowN C p.asIdeal.ResidueField hπ g - D) ⊤)
    (hK' : divUniversalFibreK' C hπ g r₁ r₂ b₂ i j p.asIdeal.ResidueField
      = Scheme.divisorSections p.asIdeal.ResidueField
          (windowN C p.asIdeal.ResidueField hπ g + windowS C p.asIdeal.ResidueField hπ g
            - D) ⊤) :
    D = divUniversalSeedFibreDivisor_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p :=
  (existsUnique_effective_divisor_divUniversalFibre_seedPrime_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p).unique ⟨h0D, hdeg, hKM, hK'⟩
    (divUniversalSeedFibreDivisor_spec_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ p)

/-! ## The window-level Nakayama neighbourhood (I-0247 step (c)) -/

set_option maxHeartbeats 2400000 in
-- the seed-base residue-field tower `k → R_{I,J} → R_Z → κ(p)` drives the `windowCompare`
-- defeq and the base-changed basis instance chain past the defaults; the huge chart-ring
-- type is re-elaborated at each `⊗ₜ`/`windowCompare` occurrence (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option linter.unusedSectionVars false in
/-- **The fibre-nonvanishing neighbourhood of a window vector** (I-0247 step (c), the
`Module.exists_forall_tmul_residueField_ne_zero` step transported to the `windowCompare`
spelling): if the fibre comparison of a window vector `x` is nonzero at a seed-base prime
`p`, then some coordinate `f ∉ p` of `x` (in the free window `R_Z ⊗[k] H_M`, basis
`b₁.baseChange`) survives, and the fibre comparison stays nonzero at **every** prime of
`D(f)`.  This is the base-locus source of the seed's `hfib` clause — the reading bridge
`relPinnedSectionsMap_relThetaResSide_ne_zero` consumes exactly `windowCompare … ≠ 0`. -/
theorem exists_forall_windowCompare_ne_zero
    (x : TensorProduct k
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    (hx : windowCompare
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        p.asIdeal.ResidueField x ≠ 0) :
    ∃ f, f ∉ p.asIdeal ∧
      ∀ q : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j),
        f ∉ q.asIdeal →
        windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            q.asIdeal.ResidueField x ≠ 0 := by
  have hx' : (x ⊗ₜ[DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j]
        (1 : p.asIdeal.ResidueField)) ≠ 0 :=
    fun h => hx ((tmul_one_eq_zero_iff_windowCompare _ p.asIdeal.ResidueField x).mp h)
  -- the free window `R_Z ⊗[k] H_M` has the `R_Z`-basis `b₁.baseChange` (reindexed to
  -- `Type u` by `ULift`, the universe of `Module.exists_forall_tmul_residueField_ne_zero`)
  obtain ⟨f, hf, hfq⟩ := Module.exists_forall_tmul_residueField_ne_zero
    ((Module.Basis.baseChange
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) b₁).reindex
      Equiv.ulift.symm) x p hx'
  exact ⟨f, hf, fun q hq h0 =>
    hfq q hq ((tmul_one_eq_zero_iff_windowCompare _ q.asIdeal.ResidueField x).mpr h0)⟩

/-! ## The `hfib`-body producer (I-0247 the hfib route) -/

set_option maxHeartbeats 1200000 in
-- the seed-base residue-field tower `k → R_Z → κ(p)` and the fibre-curve reading bridge
-- drive the `relThetaWindowEquiv`/`relPinnedSectionsMap` defeq past the defaults
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option linter.unusedSectionVars false in
/-- **The seed `hfib`-body producer** (I-0247, the hfib route): for a seed section of the
window-equivalence form `relThetaWindowEquiv … x`, the compared side component is nonzero
on any pinned chart of the fibre curve at `κ(p)` whose basic sub-open (the piece witness)
is nonempty, as soon as the fibre comparison `windowCompare … x` is nonzero — exactly the
nonvanishing clause of `ThetaGeneratorSeed.isGenerator_of_fibre_ne_zero`.  Composes the
reading bridge `relPinnedSectionsMap_relThetaResSide_ne_zero` (a window vector with
nonzero fibre comparison has nonzero compared side component on a nonempty pinned chart)
with the derivation of chart-nonemptiness from the piece-witness `basicOpen u ≠ ⊥`. -/
theorem relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero
    (a : ℕ) (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)) (b : Bool)
    (x : TensorProduct k
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (hx : windowCompare
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        p.asIdeal.ResidueField x ≠ 0)
    (u : Γ(relCurve C p.asIdeal.ResidueField,
      relPinnedChart C p.asIdeal.ResidueField π b))
    (hne : (relCurve C p.asIdeal.ResidueField).basicOpen u ≠ ⊥) :
    relPinnedSectionsMap C
        (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
        p.asIdeal.ResidueField π b
        (relThetaResSide a b le_rfl
          (relThetaWindowEquiv C
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            π a hH1 x)) ≠ 0 :=
  relPinnedSectionsMap_relThetaResSide_ne_zero C
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
    p.asIdeal.ResidueField π a hH1 b hx
    (fun heq => hne (le_bot_iff.mp
      (heq ▸ (relCurve C p.asIdeal.ResidueField).basicOpen_le u)))

end SeedFibreDivisor

end AlgebraicGeometry
