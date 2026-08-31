/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowPencilExact
import AlgebraicJacobian.Picard.DivSchemeHighWindowPersistence

/-!
# Exact high-window relations on universal divisor fibres

The transported canonical theta pencil and the window ledger discharge every
hypothesis of the abstract field-level exactness theorem.  Consequently, on
each field-valued carve-chart fibre, the complete kernel of multiplication

`H^0(O(S))^(basis) -> H^0(O(N + (n+1)S - D))`

is the range of the finite Koszul boundary from
`H^0(O(N + nS - D))`, uniformly in `n`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxRecDepth 8000

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section UniversalFibre

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowPencilFibre :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↑(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↑(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowPencilFibre :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowPencilFibre :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowPencilFibre :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowPencilFibre :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowPencilFibre :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowPencilFibre :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j ≤
    RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
variable {ι : Type v} [Fintype ι]

local notation "Dᵤ" => divUniversalFibreDivisor
  C hpi g r1 r2 b1 b2 i j K hO hchi hker

local notation "v₀" => thetaFieldShiftUnit C K pi (windowS_choice pi hpi g) *
  thetaFieldPencilFstUnit C K pi (windowS_choice pi hpi g)

local notation "v₁" => thetaFieldShiftUnit C K pi (windowS_choice pi hpi g) *
  thetaFieldPencilSndUnit C K pi (windowS_choice pi hpi g)

set_option maxHeartbeats 1600000 in
-- Unfolding the transported windows and the universal fibre divisor is elaboration-heavy.
/-- The complete multiplication-kernel presentation on every universal divisor
fibre and at every high-window stage. -/
theorem ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_windowN
    (hb : 0 < windowBound pi hpi) (n : ℕ)
    (b : Module.Basis ι K
      ↑(Scheme.divisorSections K (windowS C K hpi g) ⊤)) :
    LinearMap.ker
        (Scheme.finiteMulMap
          (Scheme.divisorSections K (windowS C K hpi g) ⊤)
          (Scheme.divisorSections K
            (windowN C K hpi g + (n + 1) • windowS C K hpi g - Dᵤ) ⊤) b) =
      LinearMap.range
        (Scheme.highWindowMulKoszulBoundary
          (windowN C K hpi g) (windowS C K hpi g) Dᵤ n b) := by
  have hspec := divUniversalFibreDivisor_spec
    C hpi g r1 r2 b1 b2 i j K hO hchi hker
  apply Scheme.ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_of_pair
    g (windowN C K hpi g) (windowS C K hpi g) Dᵤ
      ((windowA_choice pi hpi : ℤ) * windowδ pi + (g : ℤ))
      (fun W hW => subsingleton_h1_of_windowA_le_deg C K hpi g
        (chi_relCurve_baseField C K g hchi) W hW)
      (by
        rw [deg_windowS]
        exact two_mul_genus_le_S_mul_windowδ pi hpi g hO hchi)
      (by
        rw [deg_windowS, deg_windowN]
        have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul pi hpi hb g
        linarith)
      hspec.2.1 n b v₀ v₁
  · simpa only [windowS] using windowTransportPencilFst_mem C K pi
      (windowS_choice pi hpi g)
  · simpa only [windowS] using windowTransportPencilSnd_mem C K pi
      (windowS_choice pi hpi g)
  · simpa only [windowS] using windowTransportPencil_basepointFree C K pi
      (windowS_choice pi hpi g)

set_option maxHeartbeats 1600000 in
-- The canonical fibre-window abbreviation contains the full divisor-family parameters.
/-- The preceding exactness theorem in the canonical
`divUniversalFibreHighWindow` spelling. -/
theorem divUniversalFibreHighWindow_ker_finiteMulMap_eq_range_koszul
    (hb : 0 < windowBound pi hpi) (n : ℕ)
    (b : Module.Basis ι K
      ↑(Scheme.divisorSections K (windowS C K hpi g) ⊤)) :
    LinearMap.ker
        (Scheme.finiteMulMap
          (Scheme.divisorSections K (windowS C K hpi g) ⊤)
          (divUniversalFibreHighWindow
            C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1)) b) =
      LinearMap.range
        (Scheme.highWindowMulKoszulBoundary
          (windowN C K hpi g) (windowS C K hpi g) Dᵤ n b) := by
  simpa only [divUniversalFibreHighWindow] using
    ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_windowN
      C hpi g r1 r2 b1 b2 i j K hO hchi hker hb n b

set_option maxHeartbeats 1600000 in
/-- The complete multiplication-kernel presentation at divisor degree `g` and
independent curve parameter `gamma ≤ g`. -/
theorem ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_windowN_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j ≤
      RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : ℕ)
    (b : Module.Basis ι K
      ↑(Scheme.divisorSections K (windowS C K hpi g) ⊤)) :
    LinearMap.ker
        (Scheme.finiteMulMap
          (Scheme.divisorSections K (windowS C K hpi g) ⊤)
          (Scheme.divisorSections K
            (windowN C K hpi g + (n + 1) • windowS C K hpi g -
              divUniversalFibreDivisor_at
                C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma) ⊤) b) =
      LinearMap.range
        (Scheme.highWindowMulKoszulBoundary
          (windowN C K hpi g) (windowS C K hpi g)
          (divUniversalFibreDivisor_at
            C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma) n b) := by
  have hspec := divUniversalFibreDivisor_spec_at
    C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma
  apply Scheme.ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_of_pair
    g (windowN C K hpi g) (windowS C K hpi g)
      (divUniversalFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma)
      ((windowA_choice pi hpi : ℤ) * windowδ pi + (gamma : ℤ))
      (fun W hW => subsingleton_h1_of_windowA_le_deg C K hpi gamma
        (chi_relCurve_baseField C K gamma hχgamma) W hW)
      (by
        rw [deg_windowS]
        exact two_mul_degree_le_S_mul_windowδ pi hpi g)
      (by
        rw [deg_windowS, deg_windowN]
        have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul
          pi hpi (windowBound_pos pi hpi) g
        have hcast : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
        linarith)
      hspec.2.1 n b v₀ v₁
  · simpa only [windowS] using windowTransportPencilFst_mem C K pi
      (windowS_choice pi hpi g)
  · simpa only [windowS] using windowTransportPencilSnd_mem C K pi
      (windowS_choice pi hpi g)
  · simpa only [windowS] using windowTransportPencil_basepointFree C K pi
      (windowS_choice pi hpi g)

set_option maxHeartbeats 1600000 in
/-- The off-diagonal exactness theorem in the canonical high-window spelling. -/
theorem divUniversalFibreHighWindow_ker_finiteMulMap_eq_range_koszul_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j ≤
      RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (n : ℕ)
    (b : Module.Basis ι K
      ↑(Scheme.divisorSections K (windowS C K hpi g) ⊤)) :
    LinearMap.ker
        (Scheme.finiteMulMap
          (Scheme.divisorSections K (windowS C K hpi g) ⊤)
          (divUniversalFibreHighWindow_at
            C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma (n + 1)) b) =
      LinearMap.range
        (Scheme.highWindowMulKoszulBoundary
          (windowN C K hpi g) (windowS C K hpi g)
          (divUniversalFibreDivisor_at
            C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma) n b) := by
  simpa only [divUniversalFibreHighWindow_at] using
    ker_finiteMulMap_eq_range_highWindowMulKoszulBoundary_windowN_at
      C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma n b

end UniversalFibre

end AlgebraicGeometry
