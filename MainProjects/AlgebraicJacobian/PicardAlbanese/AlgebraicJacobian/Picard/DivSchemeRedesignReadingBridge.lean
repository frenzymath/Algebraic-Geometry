/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignHinjChart
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssemble

/-!
# DD-4 — the submodule germ bridge: chart reading ↔ function-field reading

Upgrades the germ **divisibility** bridge `germ_relThetaResSide_dvd_iff_ord_le`
(`DivSchemeUnivFibreHdiv.lean`, `15d9eb465`) to a `K`-**linear submodule** identification,
over the fibre curve `relCurve C K` at *any* field extension `K/k`.  No residue-field
`κ(p)` tower is needed at this level — that enters only when the identification is
base-changed inside the carve pin (steps 2–3), so the whole bridge is built over a general
field `K` and stays outside the `κ(p)` instance minefield.

The reading of a pinned-chart section into the function field is mathlib's
`Scheme.germGenericLinear K hη` (`s ↦ germ_η s`, `K`-linear).  Composed with the
side-uniform chart component `relThetaResSide a b le_rfl`, it agrees — up to a **fixed**
unit `u` of the function field (the chart-transition unit; the trivializing element of the
theta presentation is `1` at the generic point) — with the function-field reading
`thetaFieldRead`:

* `exists_unit_germGenericLinear_relThetaResSide_eq` — the pointwise identity
  `germ_η (relThetaResSide a b _ s) = u · thetaFieldRead s`, the reading identification;
* `exists_unit_germGenericLinear_comp_relThetaResSide` — its `LinearMap` form;
* `exists_unit_map_germGenericLinear_range_chartReadMap` — **the submodule bridge**: the
  chart base-ideal range `N_V = range (chartReadMap W b)`, read into the function field, is
  the unit multiple `u · thetaFieldRead(W)` of the function-field reading of `W`.  This is
  the `κ`-linear submodule identification the carve pin consumes (via
  `divUniversalFibreKM_eq_span`), replacing the earlier divisibility-only bridge.
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

section ReadingBridge

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The reading identification, pointwise**: on the fibre curve `relCurve C K`, the germ
at the generic point `η` of the side component `relThetaResSide a b hV s` (the reading of a
theta section into the pinned chart `Γ(V)`, read on into the function field via
`germGenericLinear`) equals a **fixed** function-field unit `u` — independent of `s` — times
the function-field reading `thetaFieldRead s`.  The unit `u` is the chart-transition unit of
`exists_unit_germ_relThetaResSide_eq`; the trivializing element `elem η` is `1` at `η`
(`thetaFieldPresentation_elem_genericPoint`), so it drops out.  This is the equality upgrade
of the divisibility bridge `germ_relThetaResSide_dvd_iff_ord_le`. -/
theorem exists_unit_germGenericLinear_relThetaResSide_eq (b : Bool)
    {V : (relCurve C K).Opens} (hV : V ≤ relPinnedChart C K π b)
    (hηV : genericPoint (relCurve C K) ∈ V) :
    ∃ u : (relCurve C K).functionFieldˣ, ∀ (s : relThetaSections C K π a),
      Scheme.germGenericLinear K hηV (relThetaResSide a b hV s)
        = (u : (relCurve C K).functionField) * thetaFieldRead C K π a s := by
  obtain ⟨w, hw⟩ := exists_unit_germ_relThetaResSide_eq C K π a b hV hηV
  refine ⟨w, fun s => ?_⟩
  have hgl : ((relCurve C K).presheaf.germ
        (⊤ ⊓ (thetaFieldPointedCover C K π).opens (genericPoint (relCurve C K)))
        (genericPoint (relCurve C K))
        ⟨trivial, (thetaFieldPointedCover C K π).mem_opens (genericPoint (relCurve C K))⟩).hom
        ((thetaFieldGluedEquiv C K π a s).val (genericPoint (relCurve C K)))
      = thetaFieldRead C K π a s := by
    rw [germ_generic_eq_algebraMap_germ
        (⟨trivial, (thetaFieldPointedCover C K π).mem_opens (genericPoint (relCurve C K))⟩ :
          genericPoint (relCurve C K)
            ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens (genericPoint (relCurve C K)))
        (⟨trivial, (thetaFieldPointedCover C K π).mem_opens (genericPoint (relCurve C K))⟩ :
          genericPoint (relCurve C K)
            ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens (genericPoint (relCurve C K))),
      algebraMap_germ_thetaFieldGluedEquiv_eq C K π a s (genericPoint (relCurve C K)),
      thetaFieldPresentation_elem_genericPoint, Units.val_one, one_mul]
  change ((relCurve C K).presheaf.germ V (genericPoint (relCurve C K)) hηV).hom
      (relThetaResSide a b hV s) = _
  rw [hw s, hgl]

/-- **The reading identification, `LinearMap` form**: the composite reading
`germGenericLinear K hη ∘ relThetaResSide a b le_rfl : relThetaSections → functionField`
is `u · thetaFieldRead` (multiplication by a fixed function-field unit), as `K`-linear
maps. -/
theorem exists_unit_germGenericLinear_comp_relThetaResSide (b : Bool)
    (hηV : genericPoint (relCurve C K) ∈ relPinnedChart C K π b) :
    ∃ u : (relCurve C K).functionFieldˣ,
      (Scheme.germGenericLinear K hηV).comp (relThetaResSide a b le_rfl)
        = (Scheme.mulLinear K (u : (relCurve C K).functionField)).comp
            (thetaFieldRead C K π a) := by
  obtain ⟨u, hu⟩ :=
    exists_unit_germGenericLinear_relThetaResSide_eq C K π a b le_rfl hηV
  refine ⟨u, LinearMap.ext fun s => ?_⟩
  simp only [LinearMap.comp_apply, Scheme.mulLinear_apply]
  exact hu s

/-- **The submodule germ bridge** (the `κ`-linear submodule identification): the range of
the chart reading map `chartReadMap W b` — the chart base ideal `N_V = ⟨relThetaResSide b ψ :
ψ ∈ W⟩ ⊆ Γ(V)` — read into the function field by `germGenericLinear`, is the unit multiple
`u · thetaFieldRead(W)` of the function-field reading of `W`.  Over the fibre curve
`relCurve C K` at any field `K`, this identifies the two `K`-subspaces (the chart-section
reading and the function-field reading) up to a fixed function-field unit — the equality
upgrade, at the submodule level, of the divisibility bridge
`germ_relThetaResSide_dvd_iff_ord_le`.  Combined with `divUniversalFibreKM_eq_span` it feeds
the carve pin. -/
theorem exists_unit_map_germGenericLinear_range_chartReadMap (b : Bool)
    (hηV : genericPoint (relCurve C K) ∈ relPinnedChart C K π b)
    (W : Submodule K (relThetaSections C K π a)) :
    ∃ u : (relCurve C K).functionFieldˣ,
      Submodule.map (Scheme.germGenericLinear K hηV)
          (LinearMap.range (chartReadMap W b))
        = Submodule.map (Scheme.mulLinear K (u : (relCurve C K).functionField))
            (Submodule.map (thetaFieldRead C K π a) W) := by
  obtain ⟨u, hu⟩ := exists_unit_germGenericLinear_comp_relThetaResSide C K π a b hηV
  refine ⟨u, ?_⟩
  have hrange : LinearMap.range (chartReadMap W b)
      = Submodule.map (relThetaResSide a b le_rfl) W := by
    simp only [chartReadMap, LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange, ← Submodule.map_comp, hu, Submodule.map_comp]

end ReadingBridge

end ThetaGeneratorSeed

end AlgebraicGeometry
