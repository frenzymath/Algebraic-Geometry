/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeMulBaseChange
import AlgebraicJacobian.RiemannRoch.AnnihilatorKernel

/-!
# A finite presentation of a multiplication span

The universal second-window argument produces an equality of function-field
subspaces written as `Scheme.mulSpan`.  Its relative multiplication map is a
finite component sum indexed by a basis of the multiplier window.  This file
identifies those two presentations over a field.

For finite-dimensional `U` and any subspace `T` of a function field, the map

`(x_i)_i |-> sum_i b_i * x_i`

has range exactly `mulSpan K U T`.  Consequently, any equality
`mulSpan K U T = W` gives a surjection onto `W`.  This is the field-linear
piece needed before conjugating the universal relative multiplication map by
the boundary-basis and function-field reading equivalences.
-/

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.functionFieldOverModule

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsIntegral X]
variable {ι : Type v} [Fintype ι]

/-- The finite basis-indexed product map whose image is a multiplication span. -/
noncomputable def Scheme.finiteMulMap
    (U T : Submodule K X.functionField) (b : Module.Basis ι K U) :
    (ι → T) →ₗ[K] X.functionField := by
  classical
  exact finiteComponentSum fun i =>
    (Scheme.mulLinear K (b i : X.functionField)).comp T.subtype

@[simp]
theorem Scheme.finiteMulMap_apply
    (U T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (x : ι → T) :
    Scheme.finiteMulMap U T b x =
      ∑ i, (b i : X.functionField) * (x i : X.functionField) := by
  classical
  simp only [Scheme.finiteMulMap, finiteComponentSum, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Scheme.mulLinear_apply,
    Submodule.subtype_apply]

/-- The range of the finite basis-indexed product map is exactly the span of
all products of elements of the two subspaces. -/
theorem Scheme.range_finiteMulMap
    (U T : Submodule K X.functionField) (b : Module.Basis ι K U) :
    LinearMap.range (Scheme.finiteMulMap U T b) = Scheme.mulSpan K U T := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.finiteMulMap_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Scheme.mul_mem_mulSpan K (b i).property (x i).property
  · rw [Scheme.mulSpan, Submodule.span_le]
    rintro _ ⟨h, hh, f, hf, rfl⟩
    let hU : U := ⟨h, hh⟩
    let fT : T := ⟨f, hf⟩
    let x : ι → T := fun i => (b.repr hU i) • fT
    refine ⟨x, ?_⟩
    rw [Scheme.finiteMulMap_apply]
    change (∑ i, (b i : X.functionField) *
      ((b.repr hU i) • (fT : X.functionField))) = h * f
    have hterm : ∀ i,
        (b i : X.functionField) * ((b.repr hU i) • (fT : X.functionField)) =
          ((b.repr hU i) • (b i : X.functionField)) * (fT : X.functionField) := by
      intro i
      rw [Scheme.functionFieldOverModule_smul_def,
        Scheme.functionFieldOverModule_smul_def]
      ring
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    have hb : (∑ i, (b.repr hU i) • (b i : X.functionField)) = h := by
      calc
        (∑ i, (b.repr hU i) • (b i : X.functionField)) =
            ((∑ i, (b.repr hU i) • b i : U) : X.functionField) := by
          symm
          simpa only [Submodule.coe_smul] using
            (Submodule.coe_sum U (fun i => (b.repr hU i) • b i) Finset.univ)
        _ = h := by rw [b.sum_repr]
    rw [hb]

/-- The finite product map corestricted to a specified multiplication span. -/
noncomputable def Scheme.finiteMulMapTo
    (U T W : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hW : Scheme.mulSpan K U T = W) : (ι → T) →ₗ[K] W :=
  (Scheme.finiteMulMap U T b).codRestrict W fun x => by
    rw [← hW, ← Scheme.range_finiteMulMap U T b]
    exact LinearMap.mem_range_self _ x

/-- If a target subspace is the multiplication span, the finite product map
corestricted to that subspace is surjective. -/
theorem Scheme.finiteMulMapTo_surjective
    (U T W : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hW : Scheme.mulSpan K U T = W) :
    Function.Surjective (Scheme.finiteMulMapTo U T W b hW) := by
  classical
  rw [← LinearMap.range_eq_top]
  ext w
  constructor
  · exact fun _ => trivial
  · intro _
    rw [LinearMap.mem_range]
    have hw : (w : X.functionField) ∈ LinearMap.range (Scheme.finiteMulMap U T b) := by
      rw [Scheme.range_finiteMulMap, hW]
      exact w.property
    obtain ⟨x, hx⟩ := hw
    exact ⟨x, Subtype.ext hx⟩

end AlgebraicGeometry
