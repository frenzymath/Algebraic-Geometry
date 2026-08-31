/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa

/-!
# G-4 -- persistence of the universal second fibre window under multiplication

At a field point of a pair chart which kills the carve ideal, the P-fib pack identifies
the two universal fibre windows with

`K_M = H^0(O(N - D))` and `K' = H^0(O(N + S - D))`

for the same effective degree-`g` divisor `D`.  The first equality also identifies `D`
with the base divisor of `K_M` relative to `N`; the pack BPF-span theorem therefore says
that multiplication by the full `S`-window spans all of `K'`.

The main theorem is parameterized by the five abstract P-fib ledger hypotheses.  The
second theorem discharges them from the transported-window ledger whenever
`0 < windowBound`; no relative chart ideal or total-space flatness claim is made here.
-/

set_option autoImplicit false
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

section SecondWindow

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftSecondWindow : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k ((windowS_choice pi hpi g • fiberWeilDivisor pi)
    + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]

noncomputable local instance instIsIntegralRelCurveSecondWindow (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) :=
  instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSecondWindow (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSecondWindow (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSecondWindow (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSecondWindow (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveSecondWindow (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
  (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
    ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hchi hker in
/-- **Field-level second-window persistence, abstract pack form.**  Under the five
P-fib ledger hypotheses at the transported divisors `N` and `S`, the products of the
full multiplier window with the first universal fibre window span the second universal
fibre window. -/
theorem divUniversalFibre_mulSpan_eq_of_pack
    (beta : Int)
    (hvan : forall W : (relCurve C K).CurveDivisor,
      beta ≤ CurveDivisor.deg K W →
        Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K W) 1))
    (hNdeg : 2 * (g : Int) ≤ CurveDivisor.deg K (windowN C K hpi g))
    (hSdeg : 2 * (g : Int) ≤ CurveDivisor.deg K (windowS C K hpi g))
    (hbetaS : beta + 2 * (g : Int) ≤ CurveDivisor.deg K (windowS C K hpi g))
    (hbetaN : beta + 2 * (g : Int) + CurveDivisor.deg K (windowS C K hpi g)
      ≤ CurveDivisor.deg K (windowN C K hpi g)) :
    Scheme.mulSpan K (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreKM C hpi g r1 r2 b1 i j K)
      = divUniversalFibreK' C hpi g r1 r2 b2 i j K := by
  classical
  have hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 :=
    h0_relCurve_baseField C K
  have hchiK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : Int) :=
    chi_relCurve_baseField C K g hchi
  have hKMle := divUniversalFibreKM_le C hpi g r1 r2 b1 i j K
  have hKMrank := finrank_divUniversalFibreKM_add C hpi g r1 r2 b1 i j K hchi
  have hK'le := divUniversalFibreK'_le C hpi g r1 r2 b2 i j K
  have hK'rank := finrank_divUniversalFibreK'_add C hpi g r1 r2 b2 i j K hchi
  have hcarve := divUniversalFibre_carve C hpi g r1 r2 b1 b2 i j K hker
  have hpack := existsUnique_effective_divisor_of_carve_pack g hOK hchiK
    (windowN C K hpi g) (windowS C K hpi g) beta hvan hNdeg hSdeg hbetaS hbetaN
    (divUniversalFibreKM C hpi g r1 r2 b1 i j K) hKMle hKMrank
    (divUniversalFibreK' C hpi g r1 r2 b2 i j K) hK'le hK'rank hcarve
  obtain ⟨D, hD0, hDdeg, hKMeq, hK'eq⟩ := hpack.exists

  have hSdeg0 : 0 ≤ CurveDivisor.deg K (windowS C K hpi g) := by omega
  have hNnorm : forall D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : Int) →
        Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K
          (windowN C K hpi g - D')) 1) := by
    intro D' hD'
    refine hvan _ ?_
    rw [Scheme.CurveDivisor.deg_sub' K]
    omega

  have hrN : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hpi g)) : Int)
      = CurveDivisor.deg K (windowN C K hpi g) + 1 - (g : Int) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hvan _ (by omega)), hchiK]
    ring
  have hKMne : ∃ f ∈ divUniversalFibreKM C hpi g r1 r2 b1 i j K, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    rw [hbot, finrank_bot] at hKMrank
    omega

  have hDbase : D = Scheme.baseDivisor K
      (divUniversalFibreKM C hpi g r1 r2 b1 i j K) (windowN C K hpi g) hKMne := by
    refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
    rw [Scheme.coeffAt_baseDivisor K hKMne hx, hKMeq]
    exact (baseDivisorAt_window_normalization g hOK hchiK
      (windowN C K hpi g) hNnorm hNdeg D hD0 hDdeg hx).symm

  have hbpf : forall (x : relCurve C K) (hx : x ≠ genericPoint (relCurve C K)),
      ∃ (f : (relCurve C K).functionField)
        (_ : f ∈ divUniversalFibreKM C hpi g r1 r2 b1 i j K) (hf : f ≠ 0),
        coeffAt hx ((windowN C K hpi g - D)
          + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
    intro x hx
    rw [hDbase]
    exact Scheme.exists_achiever_baseDivisor_sub K hKMle hKMne hx

  have hDg : CurveDivisor.deg K D ≤ (g : Int) := by omega
  have hKMsub : divUniversalFibreKM C hpi g r1 r2 b1 i j K
      ≤ Scheme.divisorSections K (windowN C K hpi g - D) ⊤ := hKMeq.le
  have hcrank : Module.finrank K
        ↥(divUniversalFibreKM C hpi g r1 r2 b1 i j K) + 0
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hpi g - D)) := by
    rw [hKMeq, finrank_divisorSections_top]
    omega
  have hspan := mulSpan_eq_divisorSections_of_basepointFree_pack
    g hOK hchiK (windowN C K hpi g) (windowS C K hpi g) beta hvan
      hSdeg hbetaS hbetaN D hD0 hDg
      (divUniversalFibreKM C hpi g r1 r2 b1 i j K) hKMsub 0 (Nat.zero_le g) hcrank hbpf
  exact hspan.trans hK'eq.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hO hchi hker in
/-- **Field-level second-window persistence at a positive transported ledger bound.**
The abstract pack hypotheses are discharged by the existing `windowA` witness and the
transported `N`/`S` degree budgets. -/
theorem divUniversalFibre_mulSpan_eq_of_windowBound_pos
    (hb : 0 < windowBound pi hpi) :
    Scheme.mulSpan K (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreKM C hpi g r1 r2 b1 i j K)
      = divUniversalFibreK' C hpi g r1 r2 b2 i j K := by
  refine divUniversalFibre_mulSpan_eq_of_pack C hpi g r1 r2 b1 b2 i j K hchi hker
    ((windowA_choice pi hpi : Int) * windowδ pi + (g : Int)) ?_ ?_ ?_ ?_ ?_
  · intro W hW
    exact subsingleton_h1_of_windowA_le_deg C K hpi g
      (chi_relCurve_baseField C K g hchi) W hW
  · exact two_mul_genus_le_deg_windowN C K hpi g hO hchi
  · rw [deg_windowS]
    exact two_mul_genus_le_S_mul_windowδ pi hpi g hO hchi
  · rw [deg_windowS]
    have hbudget := windowA_add_three_mul_genus_le_S_mul pi hpi hb g
    linarith
  · rw [deg_windowS, deg_windowN]
    have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul pi hpi hb g
    linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hker in
/-- **Decoupled field-level second-window persistence, abstract pack form.**  The
Grassmannian corank and recovered divisor have degree `g`, while Riemann--Roch is
normalized by the independent curve parameter `gamma ≤ g`. -/
theorem divUniversalFibre_mulSpan_eq_of_pack_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (beta : ℤ)
    (hvan : ∀ W : (relCurve C K).CurveDivisor,
      beta ≤ CurveDivisor.deg K W →
        Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K W) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K (windowN C K hpi g))
    (hSdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K (windowS C K hpi g))
    (hbetaS : beta + 2 * (g : ℤ) ≤ CurveDivisor.deg K (windowS C K hpi g))
    (hbetaN : beta + 2 * (g : ℤ) + CurveDivisor.deg K (windowS C K hpi g)
      ≤ CurveDivisor.deg K (windowN C K hpi g)) :
    Scheme.mulSpan K (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreKM C hpi g r1 r2 b1 i j K)
      = divUniversalFibreK' C hpi g r1 r2 b2 i j K := by
  classical
  have hOK : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 :=
    h0_relCurve_baseField C K
  have hchiK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (gamma : ℤ) :=
    chi_relCurve_baseField C K gamma hχgamma
  have hKMle := divUniversalFibreKM_le C hpi g r1 r2 b1 i j K
  have hKMrank := finrank_divUniversalFibreKM_add_at
    C hpi g r1 r2 b1 i j K hχgamma
  have hK'le := divUniversalFibreK'_le C hpi g r1 r2 b2 i j K
  have hK'rank := finrank_divUniversalFibreK'_add_at
    C hpi g r1 r2 b2 i j K hχgamma
  have hcarve := divUniversalFibre_carve C hpi g r1 r2 b1 b2 i j K hker
  have hpack := existsUnique_effective_divisor_of_carve_pack g hOK hchiK
    (windowN C K hpi g) (windowS C K hpi g) beta hvan hNdeg hSdeg hbetaS hbetaN
    (divUniversalFibreKM C hpi g r1 r2 b1 i j K) hKMle hKMrank
    (divUniversalFibreK' C hpi g r1 r2 b2 i j K) hK'le hK'rank hcarve hgamma
  obtain ⟨D, hD0, hDdeg, hKMeq, hK'eq⟩ := hpack.exists

  have hrN : (Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hpi g)) : ℤ)
      = CurveDivisor.deg K (windowN C K hpi g) + 1 - (gamma : ℤ) := by
    rw [h0_eq_deg_add_chi_of_subsingleton_hModule_one _ (hvan _ (by omega)), hchiK]
    ring

  have hNnorm : ∀ D' : (relCurve C K).CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
        Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K
          (windowN C K hpi g - D')) 1) := by
    intro D' hD'
    refine hvan _ ?_
    rw [Scheme.CurveDivisor.deg_sub' K]
    omega

  have hKMne : ∃ f ∈ divUniversalFibreKM C hpi g r1 r2 b1 i j K, f ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot (fun hbot => ?_)
    rw [hbot, finrank_bot] at hKMrank
    have hcast : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
    omega

  have hDbase : D = Scheme.baseDivisor K
      (divUniversalFibreKM C hpi g r1 r2 b1 i j K) (windowN C K hpi g) hKMne := by
    refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
    rw [Scheme.coeffAt_baseDivisor K hKMne hx, hKMeq]
    exact (baseDivisorAt_window_normalization g hOK hchiK
      (windowN C K hpi g) hNnorm hNdeg D hD0 hDdeg hx hgamma).symm

  have hbpf : ∀ (x : relCurve C K) (hx : x ≠ genericPoint (relCurve C K)),
      ∃ (f : (relCurve C K).functionField)
        (_ : f ∈ divUniversalFibreKM C hpi g r1 r2 b1 i j K) (hf : f ≠ 0),
        coeffAt hx ((windowN C K hpi g - D)
          + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
    intro x hx
    rw [hDbase]
    exact Scheme.exists_achiever_baseDivisor_sub K hKMle hKMne hx

  have hDg : CurveDivisor.deg K D ≤ (g : ℤ) := hDdeg.le
  have hKMsub : divUniversalFibreKM C hpi g r1 r2 b1 i j K
      ≤ Scheme.divisorSections K (windowN C K hpi g - D) ⊤ := hKMeq.le
  have hcrank : Module.finrank K
        ↥(divUniversalFibreKM C hpi g r1 r2 b1 i j K) + 0
      = Sheaf.h0 ((relCurve C K).divisorSheaf K (windowN C K hpi g - D)) := by
    rw [hKMeq, finrank_divisorSections_top]
    omega
  have hspan := mulSpan_eq_divisorSections_of_basepointFree_pack
    g hOK hchiK (windowN C K hpi g) (windowS C K hpi g) beta hvan
      hSdeg hbetaS hbetaN D hD0 hDg
      (divUniversalFibreKM C hpi g r1 r2 b1 i j K) hKMsub 0 (Nat.zero_le g)
      hcrank hbpf hgamma
  exact hspan.trans hK'eq.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hker in
/-- **Decoupled field-level second-window persistence.**  The normalized ledger
supplies the degree-`g` budgets uniformly, and `gamma ≤ g` pays for the independent
Euler-characteristic term in the vanishing threshold. -/
theorem divUniversalFibre_mulSpan_eq_of_windowBound_pos_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hb : 0 < windowBound pi hpi) :
    Scheme.mulSpan K (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreKM C hpi g r1 r2 b1 i j K)
      = divUniversalFibreK' C hpi g r1 r2 b2 i j K := by
  refine divUniversalFibre_mulSpan_eq_of_pack_at C hpi g r1 r2 b1 b2 i j K
    hker hgamma hχgamma
    ((windowA_choice pi hpi : ℤ) * windowδ pi + (gamma : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro W hW
    exact subsingleton_h1_of_windowA_le_deg C K hpi gamma
      (chi_relCurve_baseField C K gamma hχgamma) W hW
  · exact two_mul_degree_le_deg_windowN C K hpi g
  · rw [deg_windowS]
    exact two_mul_degree_le_S_mul_windowδ pi hpi g
  · rw [deg_windowS]
    have hbudget := windowA_add_three_mul_genus_le_S_mul pi hpi hb g
    have hcast : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
    linarith
  · rw [deg_windowS, deg_windowN]
    have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul pi hpi hb g
    have hcast : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
    linarith

end SecondWindow

end AlgebraicGeometry
