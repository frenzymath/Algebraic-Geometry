/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeMulSpanMap

/-!
# The finite Koszul boundary for a multiplication window

Let `b : ι → U` be a finite multiplier basis.  If `L` is a preceding
window and multiplication by `b i` sends `L` into the current window `T`,
then a pair-indexed family `z : ι × ι → L` gives the usual row-minus-column
relation

`κ(z)_i = ∑ j, b_j z_(i,j) - b_j z_(j,i)`.

The construction below is deliberately generic.  Its image is visibly killed
by the finite component multiplication map; the converse inclusion is the
actual high-window/Gotzmann syzygy theorem and is recorded at the end of this
file as the remaining interface.
-/

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-! ## A generic rows-minus-columns boundary -/

variable {R L M N : Type u} [CommRing R]
variable [AddCommGroup L] [Module R L]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {ι : Type v} [Fintype ι]

/-- The alternating rows-minus-columns boundary attached to a family of
`R`-linear maps `step i : L → M`.

The two occurrences of `step` have the same multiplier index, while the
outer index is the row of the resulting finite product.  This is the finite
Koszul boundary used for multiplication syzygies.
-/
noncomputable def finiteKoszulBoundary (step : ι → L →ₗ[R] M) :
    (ι × ι → L) →ₗ[R] (ι → M) := by
  classical
  refine
    { toFun := fun z i =>
        ∑ j, (step j (z (i, j)) - step j (z (j, i)))
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    funext i
    change
      (∑ j, (step j ((x + y) (i, j)) - step j ((x + y) (j, i)))) =
        (∑ j, (step j (x (i, j)) - step j (x (j, i)))) +
          ∑ j, (step j (y (i, j)) - step j (y (j, i)))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Pi.add_apply, map_add]
    abel
  · intro r x
    funext i
    change
      (∑ j, (step j ((r • x) (i, j)) - step j ((r • x) (j, i)))) =
        r • (∑ j, (step j (x (i, j)) - step j (x (j, i))))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Pi.smul_apply, map_smul, smul_sub]

@[simp]
theorem finiteKoszulBoundary_apply (step : ι → L →ₗ[R] M)
    (z : ι × ι → L) (i : ι) :
    finiteKoszulBoundary step z i =
      ∑ j, (step j (z (i, j)) - step j (z (j, i))) := rfl

/-! ## Composition with a finite component sum -/

/-- The component sum kills the rows-minus-columns boundary whenever the
component maps commute pairwise.  This is the substantive finite-stage
syzygy direction (`range ≤ kernel`).
-/
theorem finiteComponentSum_comp_finiteKoszulBoundary_eq_zero
    (row : ι → M →ₗ[R] N) (step : ι → L →ₗ[R] M)
    (hcomm : ∀ (i j : ι) (z : L),
      row i (step j z) = row j (step i z)) :
    (finiteComponentSum row).comp (finiteKoszulBoundary step) = 0 := by
  classical
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, finiteComponentSum, LinearMap.sum_apply,
    LinearMap.proj_apply, finiteKoszulBoundary_apply]
  simp_rw [map_sum, map_sub, Finset.sum_sub_distrib]
  change
    (∑ i, ∑ j, row i (step j (z (i, j)))) -
        ∑ i, ∑ j, row i (step j (z (j, i))) = 0
  have hswap :
      (∑ i, ∑ j, row i (step j (z (j, i)))) =
        ∑ i, ∑ j, row i (step j (z (i, j))) := by
    calc
      (∑ i, ∑ j, row i (step j (z (j, i)))) =
          ∑ i, ∑ j, row j (step i (z (j, i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hcomm i j (z (j, i))
      _ = ∑ j, ∑ i, row j (step i (z (j, i))) := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, row i (step j (z (i, j))) := by
        rfl
  rw [hswap, sub_self]

/-- Range form of the preceding composition identity. -/
theorem range_finiteKoszulBoundary_le_ker_finiteComponentSum
    (row : ι → M →ₗ[R] N) (step : ι → L →ₗ[R] M)
    (hcomm : ∀ (i j : ι) (z : L),
      row i (step j z) = row j (step i z)) :
    LinearMap.range (finiteKoszulBoundary step) ≤
      LinearMap.ker (finiteComponentSum row) := by
  rintro _ ⟨z, rfl⟩
  apply LinearMap.mem_ker.mpr
  have hz := LinearMap.congr_fun
    (finiteComponentSum_comp_finiteKoszulBoundary_eq_zero row step hcomm) z
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz

/-! ## Conjugacy of the boundary -/

section Conjugacy

variable {L' M' : Type u}
variable [AddCommGroup L'] [Module R L']
variable [AddCommGroup M'] [Module R M']

/-- Pointwise conjugacy of the indexed steps conjugates the complete finite
Koszul boundary.  This separates the finite-product bookkeeping from the
geometric comparison of the individual multiplication steps. -/
theorem piCongrRight_comp_finiteKoszulBoundary_of_conjugate
    (step : ι → L →ₗ[R] M) (step' : ι → L' →ₗ[R] M')
    (eL : L ≃ₗ[R] L') (eM : M ≃ₗ[R] M')
    (hstep : ∀ (i : ι) (x : L), eM (step i x) = step' i (eL x)) :
    (LinearEquiv.piCongrRight fun _ : ι => eM).toLinearMap.comp
        (finiteKoszulBoundary step) =
      (finiteKoszulBoundary step').comp
        (LinearEquiv.piCongrRight fun _ : ι × ι => eL).toLinearMap := by
  classical
  apply LinearMap.ext
  intro z
  funext i
  change eM (finiteKoszulBoundary step z i) =
    finiteKoszulBoundary step' (fun q => eL (z q)) i
  simp only [finiteKoszulBoundary_apply, map_sum, map_sub]
  apply Finset.sum_congr rfl
  intro j _
  rw [hstep, hstep]

end Conjugacy

/-! ## Scalar extension of the boundary -/

section BaseChange

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Scalar extension of the finite Koszul boundary commutes with the canonical
finite-product tensor equivalences.  This is the bridge that identifies the
base-changed relative boundary with the boundary formed directly in a fibre.
-/
theorem piRightHom_comp_baseChange_finiteKoszulBoundary
    (step : ι → L →ₗ[R] M) :
    (TensorProduct.piRightHom R S S (fun _ : ι => M)).comp
        (LinearMap.baseChange S (finiteKoszulBoundary step)) =
      (finiteKoszulBoundary (fun i => LinearMap.baseChange S (step i))).comp
        (TensorProduct.piRightHom R S S (fun _ : ι × ι => L)) := by
  classical
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
  | tmul a z =>
      ext i
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
        TensorProduct.piRightHom_tmul, finiteKoszulBoundary_apply]
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [TensorProduct.tmul_sub]

/-- After transporting the target finite product, the range of the
base-changed boundary is exactly the range of the fibrewise boundary. -/
theorem range_piRightHom_comp_baseChange_finiteKoszulBoundary
    (step : ι → L →ₗ[R] M) :
    LinearMap.range
        ((TensorProduct.piRightHom R S S (fun _ : ι => M)).comp
          (LinearMap.baseChange S (finiteKoszulBoundary step))) =
      LinearMap.range
        (finiteKoszulBoundary (fun i => LinearMap.baseChange S (step i))) := by
  classical
  rw [piRightHom_comp_baseChange_finiteKoszulBoundary]
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨z, rfl⟩
    let e := TensorProduct.piRight R S S (fun _ : ι × ι => L)
    refine ⟨e.symm z, ?_⟩
    simp only [LinearMap.comp_apply]
    have he : TensorProduct.piRightHom R S S (fun _ : ι × ι => L) (e.symm z) = z := by
      change e (e.symm z) = z
      exact e.apply_symm_apply z
    rw [he]

end BaseChange

/-! ## A finite-dimensional equality criterion -/

section Finrank

variable {k₀ A V W : Type u} [Field k₀]
variable [AddCommGroup A] [Module k₀ A]
variable [AddCommGroup V] [Module k₀ V] [FiniteDimensional k₀ V]
variable [AddCommGroup W] [Module k₀ W]

/-- Over a field, the easy inclusion `range κ ≤ ker μ` is an equality as soon
as the Koszul range has at least the dimension of the multiplication kernel.
Thus the reverse syzygy theorem is reduced to its genuine Gotzmann rank input.
-/
theorem ker_finiteComponentSum_eq_range_finiteKoszulBoundary_of_finrank_le
    (row : ι → V →ₗ[k₀] W) (step : ι → A →ₗ[k₀] V)
    (hcomm : ∀ (i j : ι) (z : A),
      row i (step j z) = row j (step i z))
    (hfin : Module.finrank k₀ (LinearMap.ker (finiteComponentSum row)) ≤
      Module.finrank k₀ (LinearMap.range (finiteKoszulBoundary step))) :
    LinearMap.ker (finiteComponentSum row) =
      LinearMap.range (finiteKoszulBoundary step) := by
  symm
  exact Submodule.eq_of_le_of_finrank_le
    (range_finiteKoszulBoundary_le_ker_finiteComponentSum row step hcomm) hfin

end Finrank

/-! ## The multiplication-window specialization -/

attribute [local instance] Scheme.overModule Scheme.functionFieldOverModule

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsIntegral X]
variable {ι : Type v} [Fintype ι]

/-- Multiplication by the `i`-th multiplier basis vector, corestricted to the
current window `T`.  The hypothesis records the only geometric input needed
to form this map.
-/
noncomputable def Scheme.finiteMulStepTo
    (U L T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T)
    (i : ι) : L →ₗ[K] T :=
  ((Scheme.mulLinear K (b i : X.functionField)).comp L.subtype).codRestrict T
    (fun z => by
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
        Scheme.mulLinear_apply] using hmul i z)

omit [Fintype ι] in
@[simp]
theorem Scheme.finiteMulStepTo_apply
    (U L T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T)
    (i : ι) (z : L) :
    ((Scheme.finiteMulStepTo U L T b hmul i z : T) : X.functionField) =
      (b i : X.functionField) * (z : X.functionField) := by
  rfl

/-- The finite Koszul boundary for the multiplication window `U · L ⊆ T`. -/
noncomputable def Scheme.finiteMulKoszulBoundary
    (U L T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T) :
    (ι × ι → L) →ₗ[K] (ι → T) :=
  finiteKoszulBoundary (fun i => Scheme.finiteMulStepTo U L T b hmul i)

/-- The finite product map kills the multiplication Koszul boundary. -/
theorem Scheme.finiteMulMap_comp_finiteMulKoszulBoundary_eq_zero
    (U L T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T) :
    (Scheme.finiteMulMap U T b).comp
        (Scheme.finiteMulKoszulBoundary U L T b hmul) = 0 := by
  apply finiteComponentSum_comp_finiteKoszulBoundary_eq_zero
  intro i j z
  change
    (b i : X.functionField) *
          ((b j : X.functionField) * (z : X.functionField)) =
      (b j : X.functionField) *
          ((b i : X.functionField) * (z : X.functionField))
  ring

/-- Range form of `finiteMulMap_comp_finiteMulKoszulBoundary_eq_zero`. -/
theorem Scheme.range_finiteMulKoszulBoundary_le_ker_finiteMulMap
    (U L T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T) :
    LinearMap.range (Scheme.finiteMulKoszulBoundary U L T b hmul) ≤
      LinearMap.ker (Scheme.finiteMulMap U T b) := by
  exact range_finiteKoszulBoundary_le_ker_finiteComponentSum
    (row := fun i =>
      (Scheme.mulLinear K (b i : X.functionField)).comp T.subtype)
    (step := fun i => Scheme.finiteMulStepTo U L T b hmul i) (by
      intro i j z
      change
        (b i : X.functionField) *
              ((b j : X.functionField) * (z : X.functionField)) =
          (b j : X.functionField) *
              ((b i : X.functionField) * (z : X.functionField))
      ring)

/-- A finite-dimensional rank lower bound upgrades the multiplication
Koszul inclusion to the exact kernel presentation.  This is the direct
consumer interface for a fieldwise Gotzmann dimension calculation. -/
theorem Scheme.ker_finiteMulMap_eq_range_finiteMulKoszulBoundary_of_finrank_le
    (U L T : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T)
    [FiniteDimensional K T]
    (hfin : Module.finrank K (LinearMap.ker (Scheme.finiteMulMap U T b)) ≤
      Module.finrank K
        (LinearMap.range (Scheme.finiteMulKoszulBoundary U L T b hmul))) :
    LinearMap.ker (Scheme.finiteMulMap U T b) =
      LinearMap.range (Scheme.finiteMulKoszulBoundary U L T b hmul) := by
  symm
  exact Submodule.eq_of_le_of_finrank_le
    (Scheme.range_finiteMulKoszulBoundary_le_ker_finiteMulMap U L T b hmul) hfin

/-- The same composition identity after corestricting the product map to a
specified multiplication span. -/
theorem Scheme.finiteMulMapTo_comp_finiteMulKoszulBoundary_eq_zero
    (U L T W : Submodule K X.functionField) (b : Module.Basis ι K U)
    (hmul : ∀ (i : ι) (z : L),
      (b i : X.functionField) * (z : X.functionField) ∈ T)
    (hW : Scheme.mulSpan K U T = W) :
    (Scheme.finiteMulMapTo U T W b hW).comp
        (Scheme.finiteMulKoszulBoundary U L T b hmul) = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  have hz := LinearMap.congr_fun
    (Scheme.finiteMulMap_comp_finiteMulKoszulBoundary_eq_zero
      U L T b hmul) z
  simpa only [Scheme.finiteMulMapTo, LinearMap.comp_apply,
    LinearMap.codRestrict_apply, LinearMap.zero_apply, Submodule.coe_zero] using hz

/-! ## The remaining high-window input

The following equality is intentionally left as the next theorem to prove.
It is the missing Gotzmann/syzygy statement that a
future high-window proof must establish (after any residue-field base change):

```
LinearMap.ker (Scheme.finiteMulMap U T b) =
  LinearMap.range (Scheme.finiteMulKoszulBoundary U L T b hmul)
```

For the universal high windows, the required fibrewise form is the reverse
inclusion for the corresponding residue-field maps: every kernel vector of
the multiplication map in degree `n` must be generated by these
rows-minus-columns relations from degree `n - 1`.  The results above supply
the other inclusion uniformly and are the finite-stage flatness brick used by
the later Gotzmann argument.
-/

end AlgebraicGeometry
