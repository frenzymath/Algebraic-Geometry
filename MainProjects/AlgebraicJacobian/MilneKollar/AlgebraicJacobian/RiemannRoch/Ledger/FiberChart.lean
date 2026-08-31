/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.MapToP1
import AlgebraicJacobian.RiemannRoch.Ledger.FinitenessP1
import AlgebraicJacobian.RiemannRoch.Ledger.DivisorSheafZero

/-!
# The pinned two-chart cover of a map to the projective line, and its fiber coordinate

For a scheme `Y` with a morphism `π : Y ⟶ ℙ¹`, the two chart preimages
`V₀ = π⁻¹ D₊(X₀)`, `V₁ = π⁻¹ D₊(X₁)` cover `Y` (`preimage_chartOpen_sup`, already in
`Ledger/MapToP1.lean`) and their **overlap is a basic open**: it is `Y.basicOpen t₀` for the
pulled-back chart coordinate `t₀ = π^* (X₁/X₀) ∈ Γ(Y, V₀)`.  That single identification is
what turns the two-cover Čech `H¹` of a twisted divisor sheaf into a quotient of lattices in
the function field, and it is the geometric input of the fibrewise large-twist vanishing
(`Ledger/FiberVanishing.lean`).

## Provenance

This is the **cover half** of AJCR `RiemannRoch/FiberTwist.lean` (its `section Cover` plus the
three regularity lemmas of `section Main`), ported with bodies unchanged.  The port deliberately
stops before AJCR's `fiberDivisor`/`fiberTwist`/`fiberCocycle`/`classDeg_fiberTwist`, which
present the same fiber as a `LocalEquations` and compute its **Picard class**.  AJC has neither
`Scheme.PointedCover` nor `Scheme.LocalEquations` nor `CechPic`, and that class-side material is
what pulls AJCR's fourteen-file `Picard.*` presentation cone (and `AlgebraicJacobian.Challenge`)
into the import closure.  Measured against the vanishing chain, none of it is load-bearing: the
`H¹` argument uses `fiberChart₀`, `fiberChart₁`, `fiberCoord`,
`preimage_inf_eq_basicOpen_fiberCoord`, `genericPoint_mem_preimage_inf` and the two germ lemmas,
and nothing else from that file.  See the `Ledger/FiberVanishing.lean` docstring for how the
class-transport role AJCR gives `classDeg` is played in AJC by the already-landed
`Ledger/DegreeVanishing.lean` instead.

## Main declarations

* `AlgebraicGeometry.fiberChart₀`, `AlgebraicGeometry.fiberChart₁` — the chart preimages.
* `AlgebraicGeometry.fiberCoord` — the pulled-back chart-0 coordinate `t₀`.
* `AlgebraicGeometry.preimage_inf_eq_basicOpen_fiberCoord` — `V₀ ⊓ V₁ = Y.basicOpen t₀`.
* `AlgebraicGeometry.isUnit_fiberCoord_res_inf` — `t₀` is a unit on the overlap.
* `AlgebraicGeometry.genericPoint_mem_preimage_inf` — for `π` dominant on an integral `Y`, the
  generic point lies in the overlap.  This is what makes every section module below nonzero.
* `AlgebraicGeometry.germ_fiberCoord_ne_zero`,
  `AlgebraicGeometry.germ_fiberCoord_mem_nonZeroDivisors` — regularity of `t₀` on `V₀`.
-/

set_option autoImplicit false
/- Scheme-theoretic unification (mixing `P1 K` with `Proj 𝒜`, `Γ(Y, U)` with functor
applications) needs defeq checks through semireducible definitions, as in mathlib's own
algebraic-geometry files. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

/-! ## The pinned cover and its coordinate

These constructions depend only on the morphism `π`; the integrality hypotheses enter with the
regularity of the coordinate in the next section. -/

section Cover

variable {K : Type u} [Field K] {Y : Scheme.{u}} (π : Y ⟶ P1 K)

/-- The standard grading of `K[X₀, X₁]`, the graded ring underlying `P1 K`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) K

/-- The chart-0 preimage `V₀ = π⁻¹ D₊(X₀)`. -/
@[reducible] noncomputable def fiberChart₀ : Y.Opens := π ⁻¹ᵁ P1.chartOpen K 0

/-- The chart-1 preimage `V₁ = π⁻¹ D₊(X₁)`. -/
@[reducible] noncomputable def fiberChart₁ : Y.Opens := π ⁻¹ᵁ P1.chartOpen K 1

/-- The **pulled-back chart-0 coordinate** `t₀ = π* (X₁/X₀) ∈ Γ(Y, V₀)`: the image under
`π`'s section map of the chart-0 coordinate of `ℙ¹`. The two-cover overlap is the basic
open of `t₀` (`preimage_inf_eq_basicOpen_fiberCoord`). -/
noncomputable def fiberCoord : Γ(Y, fiberChart₀ π) :=
  (π.app (P1.chartOpen K 0)).hom ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1))

/-- **The two-cover overlap is the basic open of `t₀`**: obtained from
`Scheme.preimage_basicOpen` together with the `ℙ¹`-side identification
`P1.basicOpen_awayToSection_chartCoord`. -/
theorem preimage_inf_eq_basicOpen_fiberCoord :
    fiberChart₀ π ⊓ fiberChart₁ π = Y.basicOpen (fiberCoord π) := by
  have h : π ⁻¹ᵁ ((P1 K).basicOpen
        ((Proj.awayToSection 𝒜 (X 0)).hom (P1.chartCoord K 0 1)))
      = Y.basicOpen (fiberCoord π) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord K 0 1, Scheme.Hom.preimage_inf] at h
  exact h

/-- **The overlap-unit certificate.** The restriction of `t₀` to the overlap `V₀ ⊓ V₁` is a
unit: every point of the overlap lies in `Y.basicOpen t₀`. -/
theorem isUnit_fiberCoord_res_inf :
    IsUnit ((Y.presheaf.map (homOfLE
        (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom
      (fiberCoord π)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro w hw
  rw [Y.presheaf.germ_res_apply]
  refine (Y.mem_basicOpen (fiberCoord π) w hw.1).mp ?_
  rw [← preimage_inf_eq_basicOpen_fiberCoord π]
  exact hw

end Cover

/-! ## Regularity of the coordinate on the chart -/

section Regularity

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  (π : Y ⟶ P1 K) [IsDominant π]

/-- The standard grading of `K[X₀, X₁]`, the graded ring underlying `P1 K`. -/
local notation "𝒜" => homogeneousSubmodule (Fin 2) K

/-- The generic point of `Y` lies in the two-cover overlap: since `π` is dominant, the
`ℙ¹`-overlap `D₊(X₀X₁)` (nonempty as the range of its affine chart) meets the range of `π`,
so its `π`-preimage is a nonempty open of the irreducible `Y`. -/
theorem genericPoint_mem_preimage_inf :
    genericPoint Y ∈ fiberChart₀ π ⊓ fiberChart₁ π := by
  have hP1 : (↑(P1.chartOpen K 0 ⊓ P1.chartOpen K 1) : Set (P1 K)).Nonempty := by
    rw [P1.chartOpen_inf]
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of
        (Away 𝒜 ((X 0 : MvPolynomial (Fin 2) K) * X 1)))) := inferInstance
    refine ⟨(Proj.awayι 𝒜 _ (P1.X_mul_X_mem K) two_pos).base z, ?_⟩
    rw [← Proj.opensRange_awayι 𝒜 _ (P1.X_mul_X_mem K) two_pos]
    exact ⟨z, rfl⟩
  have hne : (↑(π ⁻¹ᵁ (P1.chartOpen K 0 ⊓ P1.chartOpen K 1)) : Set Y).Nonempty := by
    obtain ⟨p, hp⟩ :=
      π.denseRange.inter_open_nonempty _ (P1.chartOpen K 0 ⊓ P1.chartOpen K 1).isOpen hP1
    obtain ⟨y, hy⟩ := hp.2
    refine ⟨y, ?_⟩
    change π.base y ∈ (P1.chartOpen K 0 ⊓ P1.chartOpen K 1 : (P1 K).Opens)
    rw [(hy : π.base y = p)]
    exact hp.1
  rw [← Scheme.Hom.preimage_inf]
  exact genericPoint_mem_of_nonempty hne

/-- The germ of the pulled-back coordinate at any point of `V₀` is nonzero: it maps, under
the domain stalk's embedding into the function field, to the germ at `η`, which is a **unit**
(the generic point lies in `Y.basicOpen t₀`). -/
theorem germ_fiberCoord_ne_zero {y : Y} (hy : y ∈ fiberChart₀ π) :
    (Y.presheaf.germ (fiberChart₀ π) y hy).hom (fiberCoord π) ≠ 0 := by
  have hη : genericPoint Y ∈ fiberChart₀ π := (genericPoint_mem_preimage_inf π).1
  have hunit : IsUnit ((Y.presheaf.germ (fiberChart₀ π) (genericPoint Y) hη).hom
      (fiberCoord π)) := by
    refine (Y.mem_basicOpen (fiberCoord π) (genericPoint Y) hη).mp ?_
    rw [← preimage_inf_eq_basicOpen_fiberCoord π]
    exact genericPoint_mem_preimage_inf π
  intro hzero
  have key := germ_generic_eq_algebraMap_germ (X := Y) hη hy (fiberCoord π)
  rw [hzero, map_zero] at key
  rw [key] at hunit
  exact not_isUnit_zero hunit

/-- The germ of `t₀` at a point of `V₀` is a nonzerodivisor of the domain stalk. -/
theorem germ_fiberCoord_mem_nonZeroDivisors {y : Y} (hy : y ∈ fiberChart₀ π) :
    (Y.presheaf.germ (fiberChart₀ π) y hy).hom (fiberCoord π)
      ∈ nonZeroDivisors (Y.presheaf.stalk y) :=
  mem_nonZeroDivisors_iff_ne_zero.mpr (germ_fiberCoord_ne_zero π hy)

end Regularity

end AlgebraicGeometry
