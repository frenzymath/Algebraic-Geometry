/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.LocalizationCocycle
import AlgebraicJacobian.Descent.UnitDescentMap

/-!
# Refinement of finite localization covers and the descent Picard class

Continuation of `AlgebraicJacobian.Algebra.LocalizationCocycle`: restricting a cover
cocycle along a refinement `τ : ι' → ι` of finite localization covers (each `f (τ i')`
invertible in the finer localization `S' i'`) transports the descent unit along the
canonical map of cover algebras (`refineAlgHom`) and does not change the Picard class of
the descended module (`IsLocalization.AwayCover.picClass_map_refine`).
-/

universe u

open TensorProduct

namespace IsLocalization.AwayCover

variable {A : Type u} [CommRing A] {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (f : ι → A)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
  [∀ i, IsLocalization.Away (f i) (S i)]
variable (T : ι → ι → Type u) [∀ i j, CommRing (T i j)] [∀ i j, Algebra A (T i j)]
  [∀ i j, IsLocalization.Away (f i * f j) (T i j)]
variable (W : ι → ι → ι → Type u) [∀ i j k, CommRing (W i j k)]
  [∀ i j k, Algebra A (W i j k)]
  [∀ i j k, IsLocalization.Away (f i * (f j * f k)) (W i j k)]

/-! ## Coboundary detection and the Picard class -/

/-- A descent unit that is a coboundary is an index-wise coboundary: if
`cocycleUnit γ = descentCoboundary β` for a unit `β` of the cover algebra, then each
`γ i j` is the quotient of the restrictions of the components of `β`. -/
theorem exists_units_of_cocycleUnit_eq_descentCoboundary {γ : ∀ i j, (T i j)ˣ}
    {β : (∀ i, S i)ˣ} (h : cocycleUnit f S T γ = Module.descentCoboundary A (∀ i, S i) β) :
    ∀ i j, (γ i j).val
      = inclRight f S T i j (β.val j)
        * inclLeft f S T i j ((β⁻¹).val i) := by
  -- Apply `piDoubleEquiv` to the value equation; the left side is `γ` index-wise
  -- (`piDoubleEquiv_cocycleUnit_val`), the right side is computed by
  -- `Module.descentCoboundary_val`, `map_mul`, `piDoubleEquiv_descentIncl₂`,
  -- `piDoubleEquiv_descentIncl₁` (with `s := β.val` resp. `(β⁻¹).val`).
  intro i j
  have h2 : piDoubleEquiv f S T ((1 : ∀ i, S i) ⊗ₜ[A] β.val)
      = fun p : ι × ι => inclRight f S T p.1 p.2 (β.val p.2) :=
    piDoubleEquiv_descentIncl₂ f S T β.val
  have h1 : piDoubleEquiv f S T ((β⁻¹).val ⊗ₜ[A] (1 : ∀ i, S i))
      = fun p : ι × ι => inclLeft f S T p.1 p.2 ((β⁻¹).val p.1) :=
    piDoubleEquiv_descentIncl₁ f S T (β⁻¹).val
  have hval : piDoubleEquiv f S T (cocycleUnit f S T γ).val
      = piDoubleEquiv f S T (Module.descentCoboundary A (∀ i, S i) β).val := by rw [h]
  rw [piDoubleEquiv_cocycleUnit_val, Module.descentCoboundary_val, map_mul, h2, h1] at hval
  exact congrFun hval (i, j)

/-- Twisting a cover cocycle by an index-wise coboundary multiplies the descent unit by
a descent coboundary. -/
theorem cocycleUnit_eq_descentCoboundary_mul {γ γ' : ∀ i j, (T i j)ˣ} (β : ∀ i, (S i)ˣ)
    (hrel : ∀ i j, (γ' i j).val
      = inclLeft f S T i j (β i).val
          * ((γ i j).val * inclRight f S T i j ((β j)⁻¹).val)) :
    cocycleUnit f S T γ'
      = Module.descentCoboundary A (∀ i, S i) (Pi.unitOf S β)⁻¹
          * cocycleUnit f S T γ := by
  -- `Units.ext`, then apply the injective `piDoubleEquiv` to both values; the left side
  -- is `γ'` index-wise (`piDoubleEquiv_cocycleUnit_val`), the right side is computed by
  -- `Module.descentCoboundary_val` (for the unit `(Pi.unitOf S β)⁻¹`, whose value is
  -- `(1 ⊗ₜ (β⁻¹-components)) * ((β-components) ⊗ₜ 1)`), `map_mul`,
  -- `piDoubleEquiv_descentIncl₁`, `piDoubleEquiv_descentIncl₂` and `hrel`.
  have h2 : piDoubleEquiv f S T ((1 : ∀ i, S i) ⊗ₜ[A] fun i => ((β i)⁻¹).val)
      = fun p : ι × ι => inclRight f S T p.1 p.2 ((β p.2)⁻¹).val :=
    piDoubleEquiv_descentIncl₂ f S T fun i => ((β i)⁻¹).val
  have h1 : piDoubleEquiv f S T ((fun i => (β i).val) ⊗ₜ[A] (1 : ∀ i, S i))
      = fun p : ι × ι => inclLeft f S T p.1 p.2 (β p.1).val :=
    piDoubleEquiv_descentIncl₁ f S T fun i => (β i).val
  have hco : (Module.descentCoboundary A (∀ i, S i) (Pi.unitOf S β)⁻¹).val
      = ((1 : ∀ i, S i) ⊗ₜ[A] fun i => ((β i)⁻¹).val)
        * ((fun i => (β i).val) ⊗ₜ[A] (1 : ∀ i, S i)) := rfl
  apply Units.ext
  apply (piDoubleEquiv f S T).injective
  rw [Units.val_mul, hco, map_mul, map_mul, piDoubleEquiv_cocycleUnit_val,
    piDoubleEquiv_cocycleUnit_val, h2, h1]
  funext p
  simp only [Pi.mul_apply]
  rw [hrel p.1 p.2]
  ring

section picClass

variable [Module.FaithfullyFlat A (∀ i, S i)]

/-- **Coboundary invariance of the Picard class**: two cover cocycles differing by an
index-wise coboundary have the same Picard class. -/
theorem picClass_eq_of_coboundary {γ γ' : ∀ i j, (T i j)ˣ}
    (hγ : IsCoverCocycle (f := f) (S := S) (W := W) γ)
    (hγ' : IsCoverCocycle (f := f) (S := S) (W := W) γ')
    (β : ∀ i, (S i)ˣ)
    (hrel : ∀ i j, (γ' i j).val
      = inclLeft f S T i j (β i).val
          * ((γ i j).val * inclRight f S T i j ((β j)⁻¹).val)) :
    (isDescentCocycle_cocycleUnit f S T W hγ').picClass
      = (isDescentCocycle_cocycleUnit f S T W hγ).picClass :=
  (Module.IsDescentCocycle.picClass_congr _ _
      (cocycleUnit_eq_descentCoboundary_mul f S T β hrel)).trans
    (Module.IsDescentCocycle.picClass_descentCoboundary_mul _
      (isDescentCocycle_cocycleUnit f S T W hγ))

end picClass

/-! ## Refinement of covers -/

section refine

variable {ι' : Type u} [Fintype ι'] [DecidableEq ι']
variable (f' : ι' → A)
variable (S' : ι' → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra A (S' i)]
  [∀ i, IsLocalization.Away (f' i) (S' i)]
variable (T' : ι' → ι' → Type u) [∀ i j, CommRing (T' i j)] [∀ i j, Algebra A (T' i j)]
  [∀ i j, IsLocalization.Away (f' i * f' j) (T' i j)]
variable (τ : ι' → ι) (hτ : ∀ i', IsUnit (algebraMap A (S' i') (f (τ i'))))

/-- The refinement map between cover algebras along an index map `τ` making each
`f (τ i')` invertible in `S' i'`. -/
noncomputable def refineAlgHom : (∀ i, S i) →ₐ[A] ∀ i', S' i' :=
  Pi.algHom _ _ fun i' =>
    (IsLocalization.Away.algHomOfIsUnit (S := S (τ i')) (S' i') (f (τ i')) (hτ i')).comp
      (Pi.evalAlgHom _ _ (τ i'))

omit [Fintype ι] [Fintype ι'] [DecidableEq ι'] in
private lemma refineAlgHom_single (i : ι) :
    refineAlgHom f S S' τ hτ (Pi.single i 1)
      = fun i' => if τ i' = i then (1 : S' i') else 0 := by
  funext i'
  change IsLocalization.Away.algHomOfIsUnit (S := S (τ i')) (S' i') (f (τ i')) (hτ i')
      (Pi.single i 1 (τ i')) = if τ i' = i then (1 : S' i') else 0
  by_cases h : τ i' = i
  · subst h
    rw [Pi.single_eq_same, map_one, if_pos rfl]
  · rw [Pi.single_eq_of_ne h, map_zero, if_neg h]

variable (hτT : ∀ i' j', IsUnit (algebraMap A (T' i' j') (f (τ i') * f (τ j'))))

/-- The refinement map on double overlaps. -/
noncomputable def refineOverlapAlgHom (i' j' : ι') : T (τ i') (τ j') →ₐ[A] T' i' j' :=
  IsLocalization.Away.algHomOfIsUnit (S := T (τ i') (τ j')) (T' i' j')
    (f (τ i') * f (τ j')) (hτT i' j')

/-- Base change of the descent unit along a refinement of covers: the descent unit of
the restricted cocycle. -/
theorem map_cocycleUnit (γ : ∀ i j, (T i j)ˣ) :
    Units.map (Algebra.TensorProduct.map (refineAlgHom f S S' τ hτ)
        (refineAlgHom f S S' τ hτ)).toRingHom.toMonoidHom (cocycleUnit f S T γ)
      = cocycleUnit f' S' T' (fun i' j' =>
          Units.map (refineOverlapAlgHom f T T' τ hτT i' j').toRingHom.toMonoidHom
            (γ (τ i') (τ j'))) := by
  -- Apply `piDoubleEquiv f' S' T'` to both sides.  The composite
  -- `piDoubleEquiv' ∘ (map h h) ∘ (piDoubleEquiv).symm` is index-wise
  -- `refineOverlapAlgHom` by the pi-ext principle (evaluate on the idempotents
  -- `Pi.single (i,j) 1`, whose preimages are `Pi.single i 1 ⊗ₜ Pi.single j 1`).
  have key : (piDoubleEquiv f' S' T').toAlgHom.comp
        ((Algebra.TensorProduct.map (refineAlgHom f S S' τ hτ) (refineAlgHom f S S' τ hτ)).comp
          (piDoubleEquiv f S T).symm.toAlgHom)
      = Pi.algHom _ _ fun p' : ι' × ι' =>
          (refineOverlapAlgHom f T T' τ hτT p'.1 p'.2).comp
            (Pi.evalAlgHom _ _ (τ p'.1, τ p'.2)) := by
    apply AlgHom.ext_of_isLocalization_pi
      (fun p : ι × ι => Submonoid.powers (f p.1 * f p.2))
    intro q
    obtain ⟨i, j⟩ := q
    change piDoubleEquiv f' S' T'
        (Algebra.TensorProduct.map (refineAlgHom f S S' τ hτ) (refineAlgHom f S S' τ hτ)
          ((piDoubleEquiv f S T).symm (Pi.single (i, j) 1)))
      = fun p' : ι' × ι' =>
          refineOverlapAlgHom f T T' τ hτT p'.1 p'.2
            ((Pi.single (i, j) 1 : ∀ p : ι × ι, T p.1 p.2) (τ p'.1, τ p'.2))
    rw [piDoubleEquiv_symm_single f S T i j, Algebra.TensorProduct.map_tmul,
      refineAlgHom_single f S S' τ hτ i, refineAlgHom_single f S S' τ hτ j,
      piDoubleEquiv_tmul f' S' T']
    funext p'
    obtain ⟨a, b⟩ := p'
    dsimp only
    by_cases hA : τ a = i
    · subst hA
      by_cases hB : τ b = j
      · subst hB
        rw [if_pos rfl, if_pos rfl, ← Algebra.TensorProduct.one_def, map_one,
          Pi.single_eq_same, map_one]
      · rw [if_neg hB, tmul_zero, map_zero,
          Pi.single_eq_of_ne (fun hh => hB (congrArg Prod.snd hh)), map_zero]
    · rw [if_neg hA, zero_tmul, map_zero,
        Pi.single_eq_of_ne (fun hh => hA (congrArg Prod.fst hh)), map_zero]
  apply Units.ext
  apply (piDoubleEquiv f' S' T').injective
  rw [piDoubleEquiv_cocycleUnit_val f' S' T']
  exact DFunLike.congr_fun key (piUnit T γ).val

variable (W' : ι' → ι' → ι' → Type u) [∀ i j k, CommRing (W' i j k)]
  [∀ i j k, Algebra A (W' i j k)]
  [∀ i j k, IsLocalization.Away (f' i * (f' j * f' k)) (W' i j k)]

include hτ in
/-- **Refinement invariance of the Picard class**: restricting a cover cocycle along a
refinement of finite localization covers does not change the Picard class of the
descended module. -/
theorem picClass_map_refine [Module.FaithfullyFlat A (∀ i, S i)]
    [Module.FaithfullyFlat A (∀ i', S' i')]
    {γ : ∀ i j, (T i j)ˣ} {γ' : ∀ i' j', (T' i' j')ˣ}
    (hγ : IsCoverCocycle (f := f) (S := S) (W := W) γ)
    (hγ' : IsCoverCocycle (f := f') (S := S') (W := W') γ')
    (hrel : ∀ i' j', γ' i' j'
      = Units.map (refineOverlapAlgHom f T T' τ hτT i' j').toRingHom.toMonoidHom
          (γ (τ i') (τ j'))) :
    (isDescentCocycle_cocycleUnit f' S' T' W' hγ').picClass
      = (isDescentCocycle_cocycleUnit f S T W hγ).picClass := by
  have h := map_cocycleUnit f S T f' S' T' τ hτ hτT γ
  have hγ'' : cocycleUnit f' S' T' γ'
      = Units.map (Algebra.TensorProduct.map (refineAlgHom f S S' τ hτ)
          (refineAlgHom f S S' τ hτ)).toRingHom.toMonoidHom (cocycleUnit f S T γ) := by
    rw [h]
    congr 1
    funext i' j'
    exact hrel i' j'
  exact (Module.IsDescentCocycle.picClass_congr _ _ hγ'').trans
    (Module.IsDescentCocycle.picClass_map (refineAlgHom f S S' τ hτ)
      (isDescentCocycle_cocycleUnit f S T W hγ))

end refine
end IsLocalization.AwayCover
