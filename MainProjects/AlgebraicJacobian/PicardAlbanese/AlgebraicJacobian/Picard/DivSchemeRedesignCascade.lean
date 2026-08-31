/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignHsubChartPin
import AlgebraicJacobian.Curve.BaseFieldTransition

/-!
# DD-4 redesign cascade — discharging `hη` (the pinned chart contains the generic point)

The carve pin `hsub_chart` (`DivSchemeRedesignHsubChartPin.lean`, I-0299) is landed modulo two
threaded hypotheses: `hχ` (the genus condition `χ = 1 − g`, campaign-provided) and `hη`, the
geometric nonemptiness fact that at *every* field extension `L` of `k` the generic point of the
residue-fibre curve `relCurve C L` lies in the pinned chart `relPinnedChart C L π b`.  This file
discharges `hη` unconditionally, so `hsub_chart` becomes unconditional bar `hχ` (I-0299 residual
1).

## The nonemptiness route (I-0299 residual 1)

`relPinnedChart C L π b` is the preimage `p₁ ⁻¹ᵁ (fiberTwoCover π).V_b` of a chart of the base
two-cover under the first projection `p₁ = (fst C (overSpec k L)).left : relCurve C L ⟶ C.left`
(`Scheme.AffineTwoCover.pullbackProd`).  Since:

* `p₁` is **surjective** — it is the base change of the surjective field-extension structure map
  `Spec L ⟶ Spec k` along `C.hom`, and surjectivity is stable under base change
  (`surjective_fst_left_overSpec`, mirroring `Over.surjective_snd_left`); and
* `relCurve C L` is **integral** (`instIsIntegralBaseChange`), so its generic point maps to the
  generic point of the integral base `C.left` (`genericPoint_eq_of_surjective`), which lies in
  *both* base charts `fiberChart₀ π ⊓ fiberChart₁ π` (`genericPoint_mem_preimage_inf`, from `π`
  dominant);

the generic point of `relCurve C L` lies in `p₁ ⁻¹ᵁ (fiberTwoCover π).V_b = relPinnedChart C L π b`
for *either* side `b`.  This closes I-0299 residual 1 with no new geometry — a clean
generic-point-in-nonempty-open argument riding on the landed base-change surjectivity stack.

The remaining `hsub_chart` obligation `hχ` is the campaign-fixed genus/χ fact; and the
chart→piece localization (I-0299 residual 2) plus the flat wiring / RD-N (I-0289) are the
downstream cascade steps toward the concrete `seedUniv'`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite

namespace AlgebraicGeometry

section Heta

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  [IsIntegral C.left]
variable (π : C.left ⟶ P1 k) [IsFinite π] [IsDominant π]

-- The residue-fibre curve is integral at every field extension (base-change transport),
-- so `genericPoint (relCurve C L)` and its `IrreducibleSpace` are available; mirrors the
-- `instIsIntegralRelCurveHsub` local instance of `DivSchemeRedesignHsubChartPin`.
noncomputable local instance instIsIntegralRelCurveCascade (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  [IsIntegral C.left] in
/-- **The first projection is surjective** (the base change of `Spec L ⟶ Spec k`): the
first projection `(fst C (overSpec k L)).left : relCurve C L ⟶ C.left` is surjective because
it is the base change, along `C.hom`, of the structure map `overSpec k L ⟶ Spec k`
(`= Spec.map (algebraMap k L)`, surjective by `surjective_specMap_algHom` since both spectra
are one-point spaces), and surjectivity is stable under base change.  The `.flip` of the
product pullback square (`Over.isPullback_left`) exhibits the first projection as that base
change — the first-projection twin of `Over.surjective_snd_left`. -/
theorem surjective_fst_left_overSpec (L : Type u) [Field L] [Algebra k L] :
    Surjective (fst C (overSpec k L)).left :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (Over.isPullback_left C (overSpec k L)).flip
    (surjective_specMap_algHom (Algebra.ofId k L))

omit [IsProper C.hom] in
/-- **`hη` discharge** (I-0299 residual 1): at every field extension `L` of `k`, the generic
point of the residue-fibre curve `relCurve C L` lies in the pinned chart
`relPinnedChart C L π b`, for either side `b`.  This is the exact hypothesis threaded through
the carve pin `hsub_chart`; discharging it makes `hsub_chart` unconditional bar the genus
condition `hχ`.

Proof: `relPinnedChart C L π b = p₁ ⁻¹ᵁ (fiberTwoCover π).V_b` for the first projection
`p₁ = (fst C (overSpec k L)).left`.  `p₁` is surjective (`surjective_fst_left_overSpec`) and
`relCurve C L` is integral, so `p₁` maps the generic point of `relCurve C L` to the generic
point of `C.left` (`genericPoint_eq_of_surjective`).  The latter lies in both base charts
(`genericPoint_mem_preimage_inf`, `π` dominant), hence its `p₁`-preimage contains the generic
point of `relCurve C L`. -/
theorem genericPoint_mem_relPinnedChart (b : Bool) (L : Type u) [Field L] [Algebra k L] :
    genericPoint (relCurve C L) ∈ relPinnedChart C L π b := by
  haveI : Surjective (fst C (overSpec k L)).left := surjective_fst_left_overSpec C L
  have hgen : (fst C (overSpec k L)).left.base (genericPoint (relCurve C L))
      = genericPoint C.left := genericPoint_eq_of_surjective _
  have hmem : genericPoint C.left ∈ fiberChart₀ π ⊓ fiberChart₁ π :=
    genericPoint_mem_preimage_inf π
  cases b with
  | false =>
    change genericPoint (relCurve C L)
      ∈ (fst C (overSpec k L)).left ⁻¹ᵁ (fiberTwoCover π).V₀
    rw [Scheme.Hom.mem_preimage, hgen, fiberTwoCover_V₀]
    exact hmem.1
  | true =>
    change genericPoint (relCurve C L)
      ∈ (fst C (overSpec k L)).left ⁻¹ᵁ (fiberTwoCover π).V₁
    rw [Scheme.Hom.mem_preimage, hgen, fiberTwoCover_V₁]
    exact hmem.2

end Heta

end AlgebraicGeometry
