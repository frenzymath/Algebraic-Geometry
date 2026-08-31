/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivSecondWindow
import AlgebraicJacobian.Picard.DivisorFamilyEpsMono

/-!
# Persistence at every high divisor-scheme window

The two Grassmannian windows recover an effective degree-`g` divisor `D` on every
field fibre.  The same multiplication argument is not confined to those first two
windows: after replacing `N` by `N + n * S`, the degree budgets only improve.  Thus
the full `S`-window carries `H^0(O(N + n*S - D))` onto the next stage for every `n`.

This is the field-level persistence input for an eventual relative saturation or
direct-limit construction.  It does not itself construct the relative high-window
modules over the carve-chart ring.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

section Pack

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- Multiplication persistence is uniform in the high-window index.  The hypotheses
are exactly the abstract P-fib window pack at `N` and `S`; at `N + n • S` all degree
and normalization inequalities follow from the original ones. -/
theorem mulSpan_divisorSections_highWindow_of_pack
    (g : ℕ) (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (g : ℤ))
    (N S : Y.CurveDivisor) (β : ℤ)
    (hvan : ∀ W : Y.CurveDivisor, β ≤ CurveDivisor.deg K W →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hSdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K S)
    (hβS : β + 2 * (g : ℤ) ≤ CurveDivisor.deg K S)
    (hβN : β + 2 * (g : ℤ) + CurveDivisor.deg K S ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D)
    (hDdeg : CurveDivisor.deg K D = (g : ℤ)) (n : ℕ) :
    Scheme.mulSpan K (divisorSections K S ⊤)
        (divisorSections K (N + n • S - D) ⊤) =
      divisorSections K (N + (n + 1) • S - D) ⊤ := by
  classical
  let Nn : Y.CurveDivisor := N + n • S
  have hSdeg0 : 0 ≤ CurveDivisor.deg K S := by omega
  have hNndeg : CurveDivisor.deg K Nn =
      CurveDivisor.deg K N + (n : ℤ) * CurveDivisor.deg K S := by
    dsimp [Nn]
    rw [CurveDivisor.deg_add, Scheme.CurveDivisor.deg_nsmul']
  have hβNn : β + 2 * (g : ℤ) + CurveDivisor.deg K S ≤
      CurveDivisor.deg K Nn := by
    rw [hNndeg]
    have hn : 0 ≤ (n : ℤ) * CurveDivisor.deg K S :=
      mul_nonneg (Int.natCast_nonneg n) hSdeg0
    omega
  have hNnDeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K Nn := by
    rw [hNndeg]
    have hn : 0 ≤ (n : ℤ) * CurveDivisor.deg K S :=
      mul_nonneg (Int.natCast_nonneg n) hSdeg0
    omega
  have hNnNorm : ∀ D' : Y.CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
        Subsingleton (Sheaf.HModule (Y.divisorSheaf K (Nn - D')) 1) := by
    intro D' hD'
    apply hvan
    rw [Scheme.CurveDivisor.deg_sub' K, hNndeg]
    have hn : 0 ≤ (n : ℤ) * CurveDivisor.deg K S :=
      mul_nonneg (Int.natCast_nonneg n) hSdeg0
    omega
  let T : Submodule K Y.functionField := divisorSections K (Nn - D) ⊤
  have hTne : ∃ f ∈ T, f ≠ 0 :=
    exists_mem_ne_zero_of_window_normalization g hχ Nn hNnNorm hNnDeg D hDdeg rfl
  have hTD : T ≤ divisorSections K Nn ⊤ := by
    refine Scheme.divisorSections_mono K ?_ ⊤
    refine Scheme.CurveDivisor.le_iff_coeffAt.mpr fun x hx => ?_
    rw [Scheme.CurveDivisor.coeffAt_sub]
    have hDx := Scheme.CurveDivisor.le_iff_coeffAt.mp hD0 x hx
    rw [Scheme.CurveDivisor.coeffAt_zero] at hDx
    omega
  have hbase : Scheme.baseDivisor K T Nn hTne = D :=
    baseDivisor_window_normalization g hO hχ Nn hNnNorm hNnDeg D hD0 hDdeg rfl hTne
  have hbpf : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      ∃ (f : Y.functionField) (_ : f ∈ T) (hf : f ≠ 0),
        coeffAt hx ((Nn - D)
          + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
    intro x hx
    have h := Scheme.exists_achiever_baseDivisor_sub K hTD hTne hx
    rwa [hbase] at h
  have hspan := mulSpan_eq_divisorSections_of_basepointFree_pack
    g hO hχ Nn S β hvan hSdeg hβS hβNn D hD0 hDdeg.le T
      (by exact le_rfl) 0 (Nat.zero_le g) (by
        simpa only [Nat.add_zero, T] using
          (finrank_divisorSections_top K (Nn - D))) hbpf
  simpa only [T, Nn, add_nsmul, one_nsmul, add_assoc] using hspan

/-- Multiplication persistence with independent divisor degree `g` and curve parameter
`gamma ≤ g`.  All pole and corank budgets remain keyed by `g`. -/
theorem mulSpan_divisorSections_highWindow_of_pack_at
    (g : ℕ) {gamma : ℕ} (hgamma : gamma ≤ g)
    (hO : Sheaf.h0 (Y.moduleKSheaf K) = 1)
    (hχ : Sheaf.chi (Y.moduleKSheaf K) = 1 - (gamma : ℤ))
    (N S : Y.CurveDivisor) (β : ℤ)
    (hvan : ∀ W : Y.CurveDivisor, β ≤ CurveDivisor.deg K W →
      Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1))
    (hNdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K N)
    (hSdeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K S)
    (hβS : β + 2 * (g : ℤ) ≤ CurveDivisor.deg K S)
    (hβN : β + 2 * (g : ℤ) + CurveDivisor.deg K S ≤ CurveDivisor.deg K N)
    (D : Y.CurveDivisor) (hD0 : 0 ≤ D)
    (hDdeg : CurveDivisor.deg K D = (g : ℤ)) (q : ℕ) :
    Scheme.mulSpan K (divisorSections K S ⊤)
        (divisorSections K (N + q • S - D) ⊤) =
      divisorSections K (N + (q + 1) • S - D) ⊤ := by
  classical
  let Nq : Y.CurveDivisor := N + q • S
  have hSdeg0 : 0 ≤ CurveDivisor.deg K S := by omega
  have hNqdeg : CurveDivisor.deg K Nq =
      CurveDivisor.deg K N + (q : ℤ) * CurveDivisor.deg K S := by
    dsimp [Nq]
    rw [CurveDivisor.deg_add, Scheme.CurveDivisor.deg_nsmul']
  have hβNq : β + 2 * (g : ℤ) + CurveDivisor.deg K S ≤
      CurveDivisor.deg K Nq := by
    rw [hNqdeg]
    have hq : 0 ≤ (q : ℤ) * CurveDivisor.deg K S :=
      mul_nonneg (Int.natCast_nonneg q) hSdeg0
    omega
  have hNqDeg : 2 * (g : ℤ) ≤ CurveDivisor.deg K Nq := by
    rw [hNqdeg]
    have hq : 0 ≤ (q : ℤ) * CurveDivisor.deg K S :=
      mul_nonneg (Int.natCast_nonneg q) hSdeg0
    omega
  have hNqNorm : ∀ D' : Y.CurveDivisor,
      CurveDivisor.deg K D' ≤ 2 * (g : ℤ) →
        Subsingleton (Sheaf.HModule (Y.divisorSheaf K (Nq - D')) 1) := by
    intro D' hD'
    apply hvan
    rw [Scheme.CurveDivisor.deg_sub' K, hNqdeg]
    have hq : 0 ≤ (q : ℤ) * CurveDivisor.deg K S :=
      mul_nonneg (Int.natCast_nonneg q) hSdeg0
    omega
  let T : Submodule K Y.functionField := divisorSections K (Nq - D) ⊤
  have hTne : ∃ f ∈ T, f ≠ 0 :=
    exists_mem_ne_zero_of_window_normalization_at
      g hgamma hχ Nq hNqNorm hNqDeg D hDdeg rfl
  have hTD : T ≤ divisorSections K Nq ⊤ := by
    refine Scheme.divisorSections_mono K ?_ ⊤
    refine Scheme.CurveDivisor.le_iff_coeffAt.mpr fun x hx => ?_
    rw [Scheme.CurveDivisor.coeffAt_sub]
    have hDx := Scheme.CurveDivisor.le_iff_coeffAt.mp hD0 x hx
    rw [Scheme.CurveDivisor.coeffAt_zero] at hDx
    omega
  have hbase : Scheme.baseDivisor K T Nq hTne = D :=
    baseDivisor_window_normalization_at
      g hgamma hO hχ Nq hNqNorm hNqDeg D hD0 hDdeg rfl hTne
  have hbpf : ∀ (x : Y) (hx : x ≠ genericPoint Y),
      ∃ (f : Y.functionField) (_ : f ∈ T) (hf : f ≠ 0),
        coeffAt hx ((Nq - D)
          + Scheme.divOf (Y ↘ Spec (CommRingCat.of K)) (Units.mk0 f hf)) = 0 := by
    intro x hx
    have h := Scheme.exists_achiever_baseDivisor_sub K hTD hTne hx
    rwa [hbase] at h
  have hspan := mulSpan_eq_divisorSections_of_basepointFree_pack
    g hO hχ Nq S β hvan hSdeg hβS hβNq D hD0 hDdeg.le T
      (by exact le_rfl) 0 (Nat.zero_le g) (by
        simpa only [Nat.add_zero, T] using
          (finrank_divisorSections_top K (Nq - D))) hbpf hgamma
  simpa only [T, Nq, add_nsmul, one_nsmul, add_assoc] using hspan

end Pack

section UniversalFibre

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowPersistence :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi)
      + (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r1 g r2 i j) K]
  [IsScalarTower k (PairChartRing k g r1 g r2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowPersistence :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowPersistence :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowPersistence :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowPersistence :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveHighWindowPersistence :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveHighWindowPersistence :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
  (hker : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
    ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))

/-- The canonical high-window fibre cut out by the universal divisor recovered from
the first two Grassmannian windows. -/
noncomputable def divUniversalFibreHighWindow (n : ℕ) :
    Submodule K (relCurve C K).functionField :=
  Scheme.divisorSections K
    (windowN C K hpi g + n • windowS C K hpi g
      - divUniversalFibreDivisor C hpi g r1 r2 b1 b2 i j K hO hchi hker) ⊤

include hO hchi hker in
/-- Stage zero is the first universal fibre window. -/
theorem divUniversalFibreHighWindow_zero :
    divUniversalFibreHighWindow C hpi g r1 r2 b1 b2 i j K hO hchi hker 0 =
      divUniversalFibreKM C hpi g r1 r2 b1 i j K := by
  rw [divUniversalFibreHighWindow, zero_nsmul, add_zero]
  exact (divUniversalFibreDivisor_spec
    C hpi g r1 r2 b1 b2 i j K hO hchi hker).2.2.1.symm

include hO hchi hker in
/-- Stage one is the second universal fibre window. -/
theorem divUniversalFibreHighWindow_one :
    divUniversalFibreHighWindow C hpi g r1 r2 b1 b2 i j K hO hchi hker 1 =
      divUniversalFibreK' C hpi g r1 r2 b2 i j K := by
  rw [divUniversalFibreHighWindow, one_nsmul]
  exact (divUniversalFibreDivisor_spec
    C hpi g r1 r2 b1 b2 i j K hO hchi hker).2.2.2.symm

set_option maxHeartbeats 1600000 in
-- Instantiating the abstract pack unfolds both transported window dictionaries.
/-- Every canonical high fibre window is generated from its predecessor by the full
multiplier window. -/
theorem divUniversalFibreHighWindow_mulSpan_eq_of_windowBound_pos
    (hb : 0 < windowBound pi hpi) (n : ℕ) :
    Scheme.mulSpan K (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreHighWindow
          C hpi g r1 r2 b1 b2 i j K hO hchi hker n) =
      divUniversalFibreHighWindow
        C hpi g r1 r2 b1 b2 i j K hO hchi hker (n + 1) := by
  rw [divUniversalFibreHighWindow, divUniversalFibreHighWindow]
  have hspec := divUniversalFibreDivisor_spec
    C hpi g r1 r2 b1 b2 i j K hO hchi hker
  refine mulSpan_divisorSections_highWindow_of_pack
    g (h0_relCurve_baseField C K) (chi_relCurve_baseField C K g hchi)
      (windowN C K hpi g) (windowS C K hpi g)
      ((windowA_choice pi hpi : ℤ) * windowδ pi + (g : ℤ)) ?_
      (two_mul_genus_le_deg_windowN C K hpi g hO hchi) ?_ ?_ ?_
      (divUniversalFibreDivisor C hpi g r1 r2 b1 b2 i j K hO hchi hker)
      hspec.1 hspec.2.1 n
  · intro W hW
    exact subsingleton_h1_of_windowA_le_deg C K hpi g
      (chi_relCurve_baseField C K g hchi) W hW
  · rw [deg_windowS]
    exact two_mul_genus_le_S_mul_windowδ pi hpi g hO hchi
  · rw [deg_windowS]
    have hbudget := windowA_add_three_mul_genus_le_S_mul pi hpi hb g
    linarith
  · rw [deg_windowS, deg_windowN]
    have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul pi hpi hb g
    linarith

/-! ## Decoupled high-window fibre -/

/-- The canonical high-window fibre at divisor degree `g` and independent curve
parameter `gamma ≤ g`. -/
noncomputable def divUniversalFibreHighWindow_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (q : ℕ) : Submodule K (relCurve C K).functionField :=
  Scheme.divisorSections K
    (windowN C K hpi g + q • windowS C K hpi g
      - divUniversalFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma) ⊤

/-- Stage zero of the decoupled high-window fibre is the first universal window. -/
theorem divUniversalFibreHighWindow_zero_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K)) :
    divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma 0 =
      divUniversalFibreKM C hpi g r1 r2 b1 i j K := by
  rw [divUniversalFibreHighWindow_at, zero_nsmul, add_zero]
  exact (divUniversalFibreDivisor_spec_at
    C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma).2.2.1.symm

/-- Stage one of the decoupled high-window fibre is the second universal window. -/
theorem divUniversalFibreHighWindow_one_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K)) :
    divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma 1 =
      divUniversalFibreK' C hpi g r1 r2 b2 i j K := by
  rw [divUniversalFibreHighWindow_at, one_nsmul]
  exact (divUniversalFibreDivisor_spec_at
    C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma).2.2.2.symm

set_option maxHeartbeats 1600000 in
/-- Every decoupled high fibre window is generated from its predecessor by the full
multiplier window. -/
theorem divUniversalFibreHighWindow_mulSpan_eq_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (hkerGamma : divCarveIdeal k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
      ≤ RingHom.ker (algebraMap (PairChartRing k g r1 g r2 i j) K))
    (q : ℕ) :
    Scheme.mulSpan K (Scheme.divisorSections K (windowS C K hpi g) ⊤)
        (divUniversalFibreHighWindow_at
          C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma q) =
      divUniversalFibreHighWindow_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma (q + 1) := by
  rw [divUniversalFibreHighWindow_at, divUniversalFibreHighWindow_at]
  have hspec := divUniversalFibreDivisor_spec_at
    C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma
  refine mulSpan_divisorSections_highWindow_of_pack_at
    g hgamma (h0_relCurve_baseField C K) (chi_relCurve_baseField C K gamma hχgamma)
      (windowN C K hpi g) (windowS C K hpi g)
      ((windowA_choice pi hpi : ℤ) * windowδ pi + (gamma : ℤ)) ?_
      (two_mul_degree_le_deg_windowN C K hpi g) ?_ ?_ ?_
      (divUniversalFibreDivisor_at
        C hpi g r1 r2 b1 b2 i j K hgamma hχgamma hkerGamma)
      hspec.1 hspec.2.1 q
  · intro W hW
    exact subsingleton_h1_of_windowA_le_deg C K hpi gamma
      (chi_relCurve_baseField C K gamma hχgamma) W hW
  · rw [deg_windowS]
    exact two_mul_degree_le_S_mul_windowδ pi hpi g
  · rw [deg_windowS]
    have hbudget := windowA_add_three_mul_genus_le_S_mul
      pi hpi (windowBound_pos pi hpi) g
    have hcast : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
    linarith
  · rw [deg_windowS, deg_windowN]
    have hbudget := windowA_add_three_mul_genus_add_S_le_M_mul
      pi hpi (windowBound_pos pi hpi) g
    have hcast : (gamma : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgamma
    linarith

end UniversalFibre

end AlgebraicGeometry
