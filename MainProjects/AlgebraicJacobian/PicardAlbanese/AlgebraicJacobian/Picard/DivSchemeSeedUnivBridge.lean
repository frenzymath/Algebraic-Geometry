/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFields

/-!
# G-4 — the fibre-read bridge: realizing fibre-window data by relative seed sections

The bridge closing I-0254 wall A (the universal-seed achiever lift): the two fibre-read
dictionaries — `divUniversalSeedK` over `R_Z` (the `thetaFieldRead`/`relThetaWindowEquiv`
window identification) and `divUniversalFibreKM` over `κ(p)` (the `divFamPhi` fibre
dictionary) — are bridged **at the span level** through the landed seam
`divUniversalFibreKM_eq_span` (I-0247's real seam,
`Picard/DivSchemeSeedUnivRes.lean`).

Rather than re-derive a pointwise base-change naturality square (the `thetaFieldRead ↔
divFamPhi` reading bridge, which the Explore sweep flagged as unbridged), we observe that
`divUniversalFibreKM_eq_span` already presents the fibre window as the `κ(p)`-span of the
`Φ`-read fibre comparisons of the universal window vectors.  A **nonzero** fibre window is
therefore not the trivial span, so *some* window vector `x ∈ divUniversalFstWindow`
survives the fibre comparison (`windowCompare R_Z κ(p) x ≠ 0`).  Its window image
`relThetaWindowEquiv … x` is the relative seed section (it lies in `divUniversalSeedK` by
definition), and its nonzero fibre comparison feeds the seed's `hfib` clause through
`exists_forall_windowCompare_ne_zero` (Brick 2) and
`relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero` (Brick 3).

* `exists_windowCompare_ne_zero_of_divUniversalFibreKM_ne_bot` — **the bridge** (general
  field point `K` of the tower `R_{I,J} → R_Z → K`): a nonzero fibre window is spanned by
  a surviving comparison, so there is a window vector `x ∈ divUniversalFstWindow` with
  `windowCompare R_Z K x ≠ 0`, whose window image lies in `divUniversalSeedK`;
* `divUniversalFibreKM_eq_bot_iff` — the clean bidirectional form (the fibre window is
  trivial iff every window vector dies in the fibre comparison);
* `exists_relThetaWindowEquiv_mem_divUniversalSeedK_windowCompare_ne_zero_seedPrime` — the
  **seed-prime instantiation** at `p : Spec R_Z`, `K := κ(p)`: consumes the fibre achiever
  `f ∈ divUniversalFibreKM … κ(p)`, `f ≠ 0` (from `divUniversalSeedFibreDivisor_spec`) and
  produces the relative seed section together with the `windowCompare` nonvanishing that
  Bricks 2 → 3 turn into `hfib`.
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

/-! ## The bridge at a general field point of the tower `R_{I,J} → R_Z → K` -/

section Bridge

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedBridge : C.left.Over (Spec (.of k)) :=
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
noncomputable local instance instIsIntegralRelCurveSeedBridge (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSeedBridge (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSeedBridge (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSeedBridge (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSeedBridge (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveSeedBridge (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 1000000 in
-- base-changed tautological towers over the pair chart ring drive the `divUniversalFibreKM`
-- span rewrite and the `divFamPhi` injectivity defeq past the defaults (recorded hatch)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **The fibre window is trivial iff every window vector dies in the fibre comparison.**
Immediate from the seam `divUniversalFibreKM_eq_span`: the fibre window is the `K`-span of
the `Φ`-read fibre comparisons of the universal window vectors, and a span is trivial iff
all of its generators vanish (`divFamPhi` is injective, so a `Φ`-read vanishes iff the
underlying comparison does). -/
theorem divUniversalFibreKM_eq_bot_iff :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K = ⊥ ↔
      ∀ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
        windowCompare
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x = 0 := by
  rw [divUniversalFibreKM_eq_span C hπ g r₁ r₂ b₁ b₂ i j K, Submodule.span_eq_bot]
  constructor
  · intro h x hx
    have hFx : divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)
        (windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x) = 0 :=
      h _ (Set.mem_image_of_mem _ hx)
    exact divFamPhi_injective C K π (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) (hFx.trans (map_zero _).symm)
  · rintro h _ ⟨x, hx, rfl⟩
    simp only [h x hx, map_zero]

set_option maxHeartbeats 1000000 in
-- base-changed tautological towers over the pair chart ring drive the `divUniversalFibreKM`
-- span rewrite and the `windowCompare`/`relThetaWindowEquiv` defeq past the defaults
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **The bridge** (I-0254 wall A, span level): if the fibre window `divUniversalFibreKM`
at a field point `K` of the tower `R_{I,J} → R_Z → K` is nonzero, then some universal
window vector `x ∈ divUniversalFstWindow` survives the fibre comparison
(`windowCompare R_Z K x ≠ 0`) and its window image `relThetaWindowEquiv … x` is a relative
seed section (it lies in `divUniversalSeedK`).  This realizes fibre-window data by a
relative seed section without a pointwise `thetaFieldRead ↔ divFamPhi` naturality square:
the seam `divUniversalFibreKM_eq_span` already carries the base change, and a nonzero span
must have a nonzero generator. -/
theorem exists_windowCompare_ne_zero_of_divUniversalFibreKM_ne_bot
    (hne : divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K ≠ ⊥) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x ≠ 0 ∧
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j := by
  by_contra hcon
  refine hne ((divUniversalFibreKM_eq_bot_iff C hπ g r₁ r₂ b₁ b₂ i j K).mpr (fun x hx => ?_))
  by_contra hx0
  exact hcon ⟨x, hx, hx0, Submodule.mem_map_of_mem hx⟩

end Bridge

/-! ## The seed-prime instantiation (I-0254 wall A, at every `p : Spec R_Z`) -/

section SeedPrime

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedPrimeBridge : C.left.Over (Spec (.of k)) :=
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

noncomputable local instance instIsIntegralRelCurveSeedPrimeBridge (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSeedPrimeBridge (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSeedPrimeBridge (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSeedPrimeBridge (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveSeedPrimeBridge (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveSeedPrimeBridge (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

set_option maxHeartbeats 2400000 in
-- the seed-base residue-field tower `k → R_{I,J} → R_Z → κ(p)` drives the `windowCompare`
-- and `divUniversalFibreKM` defeq/instance chains past the defaults (recorded hatch)
set_option synthInstance.maxHeartbeats 800000 in
set_option maxSynthPendingDepth 8 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **The seed-prime fibre-read bridge** (I-0254 wall A): at every prime `p` of the seed
base ring `R_Z`, a fibre achiever `f ∈ divUniversalFibreKM … κ(p)` with `f ≠ 0` (from
`divUniversalSeedFibreDivisor_spec`) is realized by a relative seed section: there is a
universal window vector `x ∈ divUniversalFstWindow` with `windowCompare R_Z κ(p) x ≠ 0`
whose window image `sec := relThetaWindowEquiv … x` lies in `divUniversalSeedK`.  The
nonvanishing `windowCompare R_Z κ(p) x ≠ 0` feeds Brick 2
(`exists_forall_windowCompare_ne_zero`) → Brick 3
(`relPinnedSectionsMap_relThetaResSide_windowEquiv_ne_zero`) → the seed's `hfib`. -/
theorem exists_relThetaWindowEquiv_mem_divUniversalSeedK_windowCompare_ne_zero_seedPrime
    (p : PrimeSpectrum (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j))
    {f : (relCurve C p.asIdeal.ResidueField).functionField}
    (hf : f ∈ divUniversalFibreKM C hπ g r₁ r₂ b₁ i j p.asIdeal.ResidueField)
    (hf0 : f ≠ 0) :
    ∃ x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule,
      windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          p.asIdeal.ResidueField x ≠ 0 ∧
      relThetaWindowEquiv C
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g) x
        ∈ divUniversalSeedK C π hπ g r₁ r₂ b₁ b₂ i j :=
  exists_windowCompare_ne_zero_of_divUniversalFibreKM_ne_bot
    C hπ g r₁ r₂ b₁ b₂ i j p.asIdeal.ResidueField
    (fun hbot => hf0 (by rwa [hbot, Submodule.mem_bot] at hf))

end SeedPrime

end AlgebraicGeometry
