/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignHinjChart
import AlgebraicJacobian.Picard.DivSchemeRedesignFreeFlat

/-!
# DD-4 redesign — the chart-level free-codomain flat (consuming `hsub_chart`)

The chart-level analogue of `forall_flat_colength_quotient_of_hsub`
(`Picard/DivSchemeRedesignJFlat.lean`), reduced to the **free-codomain** flattening keystone
`Module.Flat.quotient_range_of_forall_rTensor_residueField_injective_free`
(`Picard/DivSchemeRedesignFreeFlat.lean`).

At the chart `V = relPinnedChart C R π b` (`le_rfl`, `h z`-free) the reading map is
`f_V = chartReadMap K b : ↥K → Γ(relCurve C R, V)`.  The codomain `Γ(V)` is `Module.Free R`
(`free_relSections`), but of **infinite rank**, so the landed finite `(c4)` keystone
(`SlicingFlatKernel`, `[Module.Finite R N]`) does not apply.  The free-codomain keystone does:
its fibre input is exactly the landed carve pin `hsub_chart`
(`Picard/DivSchemeRedesignHsubChartPin.lean`) — at every base prime `p`, the residue fibre of
the chart base-ideal inclusion `N_V = range (chartReadMap K b) ↪ Γ(V)` is injective — applied
to the submodule inclusion `(range (chartReadMap K b)).subtype` (whose range is `N_V`).

This lands `Module.Flat R (Γ(V) ⧸ N_V)`, the exact chart-level `hflat` shape RD-N and the
non-circular certificate consume (`Γ(V) ⧸ J` where `J = ⟨read ψ : ψ ∈ K⟩`).  The
piece-level `hflat` follows by localizing to `D(h z) ⊆ V` after `h z` is chosen (I-0299
residual 2), keeping the anti-circular ordering.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

/-- **Freeness of the pinned chart sections over the test ring**: `Γ(C_R, Vᵢᴿ)` is the free
base change `R ⊗[k] Γ(C, Vᵢ)` (`free_relSections`).  (The `Free` companion of the landed
`flat_sections_relPinnedChart`, needed as the free codomain of `chartReadMap`.) -/
theorem free_sections_relPinnedChart (C : Over (Spec (.of k))) (R : Type u) [CommRing R]
    [Algebra k R] (π : C.left ⟶ P1 k) [IsFinite π] (b : Bool) :
    Module.Free R Γ(relCurve C R, relPinnedChart C R π b) := by
  cases b
  · exact free_relSections C R (fiberChart₀ π)
      (isAffineOpen_preimage_chartOpen π 0).isCompact
      (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
  · exact free_relSections C R (fiberChart₁ π)
      (isAffineOpen_preimage_chartOpen π 1).isCompact
      (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated

namespace ThetaGeneratorSeed

/-- **Brick 1 at the chart level, from the carve pin `hsub_chart`**: the chart base-ideal
colength `Γ(V) ⧸ N_V` is `R`-flat, where `V = relPinnedChart C R π b`,
`N_V = range (chartReadMap K b)` is the image of the side reading of `K`, and the fibre
input `hsub_chart` is the carve fibre non-collapse (`N_V ⊗ κ(p) ↪ Γ(V) ⊗ κ(p)` injective at
every base prime `p`).  This is the chart-level analogue of `forall_flat_colength_quotient_of_hsub`
(`DivSchemeRedesignJFlat`), reduced to the **free-codomain** `(c4)` keystone
`Module.Flat.quotient_range_of_forall_rTensor_residueField_injective_free`: the codomain
`Γ(V)` is `Module.Free R` (`free_sections_relPinnedChart`) but infinite-rank, so the finite
`SlicingFlatKernel` keystone does not apply; the free-codomain one does, fed `hsub_chart` as
the residue-fibre injectivity of the submodule inclusion `N_V ↪ Γ(V)`. -/
theorem forall_flat_colength_quotient_of_hsub_free
    (K : Submodule R (relThetaSections C R π a)) (b : Bool) [Module.Finite R ↥K]
    (hsub_chart : ∀ p : PrimeSpectrum R, Function.Injective
      ((LinearMap.range (chartReadMap K b)).subtype.rTensor p.asIdeal.ResidueField)) :
    Module.Flat R
      (Γ(relCurve C R, relPinnedChart C R π b) ⧸ LinearMap.range (chartReadMap K b)) := by
  haveI : Module.Free R Γ(relCurve C R, relPinnedChart C R π b) :=
    free_sections_relPinnedChart C R π b
  haveI : Module.Finite R ↥(LinearMap.range (chartReadMap K b)) := by
    rw [Module.Finite.iff_fg, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map (chartReadMap K b)
  have h := Module.Flat.quotient_range_of_forall_rTensor_residueField_injective_free
    (LinearMap.range (chartReadMap K b)).subtype hsub_chart
  rwa [Submodule.range_subtype] at h

end ThetaGeneratorSeed

end AlgebraicGeometry
