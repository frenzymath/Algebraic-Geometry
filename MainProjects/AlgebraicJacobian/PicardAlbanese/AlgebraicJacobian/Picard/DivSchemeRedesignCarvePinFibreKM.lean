/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignReadingBridgeDivFam
import AlgebraicJacobian.Picard.DivSchemeRedesignCarvePin

/-!
# DD-4 — the carve pin, step 2 (a): the chart reading of the fibre seed ↔ `divUniversalFibreKM`

Instantiates the `Φ`-form submodule germ bridge
(`exists_unit_map_germGenericLinear_range_chartReadMap_relThetaWindowEquiv`,
`DivSchemeRedesignReadingBridgeDivFam.lean`) at the **universal fibre seed** and folds the
`Φ`-reading through `divUniversalFibreKM_eq_span` (`DivSchemeSeedUnivRes.lean:376`) so the
right-hand side is the fibre window `divUniversalFibreKM` itself — the corank-`g` object
(`finrank_divUniversalFibreKM_add`, `DivSchemeSeedUnivAssembleKappa.lean:207`).

The fibre seed is `map (relThetaWindowEquiv …) W_κ` with
`W_κ = span K (windowCompare R_Z K '' divUniversalFstWindow)` — exactly the compared window
that step 1's transport `relPinnedTermBaseChangeAlg_reading_windowEquiv` produces when the
base-changed chart reading `f_V ⊗ κ(p)` is moved to compared-window fibre readings.  So this
identifies the function-field image of that base-changed reading range with the fibre window,
up to a fixed function-field unit — the corank-`g` pin the carve consumes.  Built over a
general field `K` of the tower (the residue-field synthesis enters only at instantiation).

* `exists_unit_map_germGenericLinear_range_chartReadMap_divUniversalFibreKM` — the bridge to
  `divUniversalFibreKM`.
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

namespace ThetaGeneratorSeed

section CarvePinFibreKM

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftFibreKM : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

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
noncomputable local instance instIsIntegralRelCurveFibreKM (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveFibreKM (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveFibreKM (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveFibreKM (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

/-- The universal fibre seed: the compared window `W_κ = span K (windowCompare '' K_univ)`,
read into the pinned chart of the fibre curve.  This is the base change (over `R_Z`) of the
chart reading of `divUniversalSeedK`, spelled at the field point `K` through step 1's window
transport. -/
noncomputable abbrev divUniversalFibreSeedW :
    Submodule K (K ⊗[k] ↥(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :=
  Submodule.span K
    (windowCompare (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K ''
      SetLike.coe (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule)

set_option maxHeartbeats 1000000 in
-- the compared-window span rewrite through `divUniversalFibreKM_eq_span` over the base-changed
-- tautological towers exceeds the default whnf budget (the recorded `SeedUnivRes` hatch class)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **The fibre window is `Φ`-read by the chart reading of the fibre seed** (`map divFamPhi`
form): the `Φ`-reading of the compared window `W_κ` is exactly `divUniversalFibreKM`. -/
theorem map_divFamPhi_divUniversalFibreSeedW :
    Submodule.map (divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g))
        (divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K)
      = divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K := by
  rw [divUniversalFibreSeedW, Submodule.map_span, ← Set.image_comp,
    divUniversalFibreKM_eq_span C hπ g r₁ r₂ b₁ b₂ i j K]
  rfl

set_option maxHeartbeats 1000000 in
-- the fibre-seed chart reading, its germ into the function field, and the compared-window
-- span all elaborate over the base-changed towers past the default whnf budget
set_option synthInstance.maxHeartbeats 400000 in
/-- **Carve pin, step 2 (a)**: the chart base ideal `N_V` of the universal fibre seed
`map (relThetaWindowEquiv …) W_κ`, read into the function field, is a fixed function-field
unit multiple of the fibre window `divUniversalFibreKM` — the corank-`g` object.  Composes the
`Φ`-form germ bridge with `map_divFamPhi_divUniversalFibreSeedW`. -/
theorem exists_unit_map_germGenericLinear_range_chartReadMap_divUniversalFibreKM (b : Bool)
    (hηV : genericPoint (relCurve C K) ∈ relPinnedChart C K π b) :
    ∃ u : (relCurve C K).functionFieldˣ,
      Submodule.map (Scheme.germGenericLinear K hηV)
          (LinearMap.range (chartReadMap
            (Submodule.map (relThetaWindowEquiv C K π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g)).toLinearMap
              (divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K)) b))
        = Submodule.map (Scheme.mulLinear K (u : (relCurve C K).functionField))
            (divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K) := by
  obtain ⟨u, hu⟩ := exists_unit_map_germGenericLinear_range_chartReadMap_relThetaWindowEquiv
    C K π (windowM_choice π hπ g) b hηV (relThetaPairH1_windowM C π hπ g)
    (divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K)
  exact ⟨u, hu.trans (congrArg (Submodule.map (Scheme.mulLinear K (u : _)))
    (map_divFamPhi_divUniversalFibreSeedW C hπ g r₁ r₂ b₁ b₂ i j K))⟩

end CarvePinFibreKM

end ThetaGeneratorSeed

end AlgebraicGeometry
