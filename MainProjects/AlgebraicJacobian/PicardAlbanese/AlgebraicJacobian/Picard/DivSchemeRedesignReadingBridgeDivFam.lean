/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignReadingBridge

/-!
# DD-4 — the submodule germ bridge in `Φ`-form: chart reading ↔ `divFamPhi`

Threads the submodule germ bridge `exists_unit_map_germGenericLinear_range_chartReadMap`
(`DivSchemeRedesignReadingBridge.lean`, `1a99fc598`) — which reads the chart base ideal
`N_V` into the function field as a unit multiple of the `thetaFieldRead` reading — through
the dictionary factorization

  `divFamPhi C K π a hH1 = mulLinear (thetaFieldShiftUnit) ∘ thetaFieldRead ∘ relThetaWindowEquiv`

(`DivisorFamilyFieldDictionary.lean:286`), producing the identification of `N_V` (for the
**window seed** `map (relThetaWindowEquiv …) W`) with the `Φ`-reading `map (divFamPhi …) W`,
again up to a fixed function-field unit.

Since `divUniversalFibreKM_eq_span` (`DivSchemeSeedUnivRes.lean:376`) presents the fibre
window `divUniversalFibreKM` as exactly a `map (divFamPhi …)` of the universal window, this
is the section→function-field identification the carve pin (steps 2–3) consumes: the
chart-reading image of the seed, read into the function field, is a unit multiple of the
fibre window.  Like the germ bridge itself it is built over a general field `K` (no `κ(p)`
tower), so it stays outside the residue-field instance minefield.

* `exists_unit_map_germGenericLinear_range_chartReadMap_relThetaWindowEquiv` — the bridge in
  `Φ`-form.  The threaded unit is `u₀ · (thetaFieldShiftUnit)⁻¹`, the germ-bridge unit `u₀`
  corrected by the class-comparison shift unit of `Φ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

namespace ThetaGeneratorSeed

section ReadingBridgeDivFam

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftReadingDivFam : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

set_option linter.unusedSectionVars false in
/-- Multiplication by two function-field units, applied to a submodule as a `Submodule.map`
of the product unit — `mulLinear` is a monoid map into the endomorphism ring. -/
private lemma map_mulLinear_map_mulLinear
    (u v : (relCurve C K).functionFieldˣ)
    (X : Submodule K (relCurve C K).functionField) :
    Submodule.map (Scheme.mulLinear K (u : (relCurve C K).functionField))
        (Submodule.map (Scheme.mulLinear K (v : (relCurve C K).functionField)) X)
      = Submodule.map (Scheme.mulLinear K
          ((u * v : (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)) X := by
  rw [← Submodule.map_comp]
  refine congrFun (congrArg _ (LinearMap.ext fun s => ?_)) X
  simp only [LinearMap.comp_apply, Scheme.mulLinear_apply, Units.val_mul, mul_assoc]

set_option maxHeartbeats 800000 in
-- elaborating the `divFamPhi` / `relThetaWindowEquiv` window-tensor readings and the
-- `germGenericLinear` chart reading in one statement exceeds the default whnf budget
set_option synthInstance.maxHeartbeats 400000 in
/-- **The submodule germ bridge, `Φ`-form**: for the window seed `map (relThetaWindowEquiv) W`
its chart base ideal `N_V = range (chartReadMap …)`, read into the function field by
`germGenericLinear`, is a fixed function-field unit multiple of the `Φ`-reading
`map (divFamPhi …) W`.  Composes the germ bridge (unit `u₀`) with the dictionary
factorization `divFamPhi = mulLinear (thetaFieldShiftUnit) ∘ thetaFieldRead ∘
relThetaWindowEquiv`, so the threaded unit is `u₀ · (thetaFieldShiftUnit)⁻¹`.  Combined with
`divUniversalFibreKM_eq_span` this identifies the chart-reading image of the seed with the
fibre window `divUniversalFibreKM`, up to that unit — the identification the carve pin
consumes. -/
theorem exists_unit_map_germGenericLinear_range_chartReadMap_relThetaWindowEquiv (b : Bool)
    (hηV : genericPoint (relCurve C K) ∈ relPinnedChart C K π b)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (W : Submodule K (K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))) :
    ∃ u : (relCurve C K).functionFieldˣ,
      Submodule.map (Scheme.germGenericLinear K hηV)
          (LinearMap.range (chartReadMap
            (Submodule.map (relThetaWindowEquiv C K π a hH1).toLinearMap W) b))
        = Submodule.map (Scheme.mulLinear K (u : (relCurve C K).functionField))
            (Submodule.map (divFamPhi C K π a hH1) W) := by
  obtain ⟨u₀, hu₀⟩ := exists_unit_map_germGenericLinear_range_chartReadMap C K π a b hηV
    (Submodule.map (relThetaWindowEquiv C K π a hH1).toLinearMap W)
  refine ⟨u₀ * (thetaFieldShiftUnit C K π a)⁻¹, ?_⟩
  -- `A`: fold `thetaFieldRead ∘ relThetaWindowEquiv` into a single `Submodule.map`
  have hA : Submodule.map (thetaFieldRead C K π a)
        (Submodule.map (relThetaWindowEquiv C K π a hH1).toLinearMap W)
      = Submodule.map ((thetaFieldRead C K π a).comp
          (relThetaWindowEquiv C K π a hH1).toLinearMap) W :=
    (Submodule.map_comp _ _ _).symm
  -- `B`: `divFamPhi` is `mulLinear (thetaFieldShiftUnit)` after that same composite
  have hB : Submodule.map (divFamPhi C K π a hH1) W
      = Submodule.map (Scheme.mulLinear K
            ((thetaFieldShiftUnit C K π a : (relCurve C K).functionFieldˣ) :
              (relCurve C K).functionField))
          (Submodule.map ((thetaFieldRead C K π a).comp
            (relThetaWindowEquiv C K π a hH1).toLinearMap) W) :=
    Submodule.map_comp _ _ W
  rw [hu₀, hA, hB, map_mulLinear_map_mulLinear,
    show u₀ * (thetaFieldShiftUnit C K π a)⁻¹ * thetaFieldShiftUnit C K π a = u₀ from by group]

end ReadingBridgeDivFam

end ThetaGeneratorSeed

end AlgebraicGeometry
