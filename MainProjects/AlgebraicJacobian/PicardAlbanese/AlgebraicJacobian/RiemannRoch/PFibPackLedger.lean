/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.PFibPack

/-!
# P-fib-N, ledger form — the pack hypotheses discharged by DD-0 names

The consistency instantiation of `RiemannRoch/PFibPack.lean` (worksheet
`informal/w4-g4-worksheet.md` §1.4) at the pack's OWN field ledger: with
`N = M·F`, `S = s·F`, `β = windowBound`, the whole audited hypothesis bundle of
`existsUnique_effective_divisor_of_carve_pack` is discharged by the DD-0 ledger names —

* `hvan`  ↦ `windowBound_spec` (verbatim: the threshold IS the DAT-0a bound),
* `hNdeg` ↦ `two_mul_genus_le_M_mul_windowδ`,
* `hSdeg` ↦ `two_mul_genus_le_S_mul_windowδ`,
* `hβS`   ↦ `windowS_spec` (`b + 2g ≤ (s−1)·δ ≤ s·δ`),
* `hβN`   ↦ `windowBound_add_two_mul_genus_le_M_sub_S_mul` (verbatim),

re-deriving P-fib's keystone `existsUnique_effective_divisor_of_carve`
(`RiemannRoch/PFib.lean`) through the pack.  This is a smoke test that the pack
interface is instantiable, and the template for the fibrewise consumer (W4-G4 §1.5,
DDR-8), where the same five slots are filled by the TRANSPORTED N-pack instead
(`WindowFieldTransport.lean`: `subsingleton_h1_windowN_sub` +
`subsingleton_hModule_one_of_normalization`/`subsingleton_hModule_one_of_witness` for
`hvan`, `deg_windowN`-arithmetic for the budgets).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite TopologicalSpace

attribute [local instance] AlgebraicGeometry.Scheme.functionFieldOverModule
  AlgebraicGeometry.Scheme.overModule

namespace AlgebraicGeometry

open Scheme

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
  (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-- **P-fib through the pack** (ledger form, the DDR-2-style consistency check): at the
ledger windows `N = M·F`, `S = s·F` and threshold `β = windowBound`, the pack keystone
`existsUnique_effective_divisor_of_carve_pack` re-derives P-fib's
`existsUnique_effective_divisor_of_carve` verbatim — every pack hypothesis is a DD-0
ledger name. -/
theorem existsUnique_effective_divisor_of_carve_of_pack
    (g : ℕ) (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (KM : Submodule K Y.functionField)
    (hKM : KM ≤ divisorSections K (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)
    (hKMrank : Module.finrank K ↥KM + g
      = Sheaf.h0 (Y.divisorSheaf K (windowM_choice π hπ g • fiberWeilDivisor π)))
    (K' : Submodule K Y.functionField)
    (hK' : K' ≤ divisorSections K
      ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)
    (hK'rank : Module.finrank K ↥K' + g
      = Sheaf.h0 (Y.divisorSheaf K
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π)))
    (hcarve : ∀ h ∈ divisorSections K (windowS_choice π hπ g • fiberWeilDivisor π) ⊤,
      ∀ f ∈ KM, h * f ∈ K') :
    ∃! D : Y.CurveDivisor, 0 ≤ D ∧ CurveDivisor.deg K D = (g : ℤ) ∧
      KM = divisorSections K (windowM_choice π hπ g • fiberWeilDivisor π - D) ⊤ ∧
      K' = divisorSections K
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π - D) ⊤ := by
  have hdegF : CurveDivisor.deg K (fiberWeilDivisor π) = windowδ π :=
    deg_fiberWeilDivisor_windowδ π
  have hdegM : CurveDivisor.deg K (windowM_choice π hπ g • fiberWeilDivisor π)
      = (windowM_choice π hπ g : ℤ) * windowδ π := by
    rw [Scheme.CurveDivisor.deg_nsmul' K, hdegF]
  have hdegS : CurveDivisor.deg K (windowS_choice π hπ g • fiberWeilDivisor π)
      = (windowS_choice π hπ g : ℤ) * windowδ π := by
    rw [Scheme.CurveDivisor.deg_nsmul' K, hdegF]
  have hsplit : (windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π
      = windowM_choice π hπ g • fiberWeilDivisor π
        + windowS_choice π hπ g • fiberWeilDivisor π := add_nsmul _ _ _
  rw [hsplit] at hK' hK'rank
  simp only [hsplit]
  refine existsUnique_effective_divisor_of_carve_pack g hO hχ
    (windowM_choice π hπ g • fiberWeilDivisor π)
    (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowBound π hπ) (fun W hW => windowBound_spec π hπ W hW)
    ?_ ?_ ?_ ?_ KM hKM hKMrank K' hK' hK'rank hcarve
  · rw [hdegM]
    exact two_mul_genus_le_M_mul_windowδ π hπ g hO hχ
  · rw [hdegS]
    exact two_mul_genus_le_S_mul_windowδ π hπ g hO hχ
  · rw [hdegS]
    have hspec := windowS_spec π hπ g
    have hδ0 := windowδ_nonneg π
    have hexp : ((windowS_choice π hπ g : ℤ) - 1) * windowδ π
        = (windowS_choice π hπ g : ℤ) * windowδ π - windowδ π := by ring
    linarith
  · rw [hdegM, hdegS]
    exact windowBound_add_two_mul_genus_le_M_sub_S_mul π hπ g

end AlgebraicGeometry
