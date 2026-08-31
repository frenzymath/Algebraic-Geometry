/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RefinementInjectivity

/-!
# Coboundary descent from an arbitrary refining family

`AlgebraicJacobian.Picard.RefinementInjectivity` glues a coboundary datum from a pointed
refinement `𝒲 ≤ 𝒰` back to the pointed cover `𝒰`.  This file provides the same gluing
from an **arbitrary refining family**: opens `E k` (any index type) covering `X`, each
contained in the member `𝒰.opens (p k)` of the pointed cover at a chosen point `p k`,
carrying units `α k` that exhibit the corresponding evaluations of a unit cocycle `γ` on
`𝒰` as a coboundary.  The conclusion is that `γ` is a coboundary on `𝒰` itself, i.e. its
`H¹` class is trivial (`AlgebraicGeometry.Scheme.unitsH1_eq_one_of_family`).

This is the form of refinement injectivity consumed by the Čech–Picard dictionary
(`AlgebraicJacobian.Picard.PicAffine`), where the refining family is a *finite* family of
basic opens and the units come from faithfully flat descent; the pointed-cover statement
of `RefinementInjectivity` is the special case `κ := X`, `E := 𝒲.opens`, `p := id`.

The gluing argument is the one of `RefinementInjectivity`: the comparison sections
`α k ⋅ γ(i, p k)⁻¹` on `𝒰 i ⊓ E k` agree on overlaps by the cocycle identity and the
coboundary relation, hence glue to units `β i ∈ 𝒪ˣ(𝒰 i)` exhibiting `γ` as a coboundary.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- **Glued coboundary from a refining family.**  Let `γ` be a unit cocycle on a pointed
cover `𝒰`, and let `E : κ → X.Opens` be a family covering `X` with `E k ≤ 𝒰.opens (p k)`
for chosen points `p k`.  If units `α k ∈ 𝒪ˣ(E k)` satisfy the coboundary relation
against the evaluations `γ (p k, p l)`, then `γ` is a coboundary on `𝒰`. -/
theorem exists_coboundary_of_family {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰)
    {κ : Type*} (p : κ → X) (E : κ → X.Opens) (hle : ∀ k, E k ≤ 𝒰.opens (p k))
    (hcov : ∀ x : X, ∃ k, x ∈ E k) (α : ∀ k, Γ(X, E k)ˣ)
    (hα : ∀ k l,
      X.unitsRestrict (inf_le_left : E k ⊓ E l ≤ E k) (α k)
          * X.unitsRestrict (inf_le_inf (hle k) (hle l)) (unitsEvInf γ (p k) (p l))
        = X.unitsRestrict inf_le_right (α l)) :
    ∃ β : ∀ i, Γ(X, 𝒰.opens i)ˣ, ∀ i j,
      X.unitsRestrict (inf_le_left : 𝒰.opens i ⊓ 𝒰.opens j ≤ 𝒰.opens i) (β i)
          * unitsEvInf γ i j
        = X.unitsRestrict inf_le_right (β j) := by
  -- Step 1: for each `i`, glue the comparison sections over the cover
  -- `{𝒰 i ⊓ E k}_k` of `𝒰 i`.
  have key : ∀ i, ∃ βi : Γ(X, 𝒰.opens i)ˣ, ∀ k : κ,
      X.unitsRestrict (inf_le_left : 𝒰.opens i ⊓ E k ≤ 𝒰.opens i) βi
        = X.unitsRestrict inf_le_right (α k)
          * (X.unitsRestrict (inf_le_inf le_rfl (hle k)) (unitsEvInf γ i (p k)))⁻¹ := by
    intro i
    refine exists_unitsRestrict_eq (fun k ↦ inf_le_left)
      (fun w hw ↦ Opens.mem_iSup.mpr ?_) _ (fun k l ↦ ?_)
    · obtain ⟨k, hk⟩ := hcov w
      exact ⟨k, hw, hk⟩
    -- compatibility on `O := (𝒰 i ⊓ E k) ⊓ (𝒰 i ⊓ E l)`, from the coboundary relation
    -- for `α` and the cocycle identity for `γ` at `(i, p k, p l)`, both restricted to `O`
    have e₁ := congrArg (X.unitsRestrict
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (𝒰.opens i ⊓ E k) ⊓ (𝒰.opens i ⊓ E l) ≤ E k ⊓ E l)) (hα k l)
    have e₂ := congrArg (X.unitsRestrict
      (le_inf (le_inf (inf_le_left.trans inf_le_left)
          ((inf_le_left.trans inf_le_right).trans (hle k)))
          ((inf_le_right.trans inf_le_right).trans (hle l)) :
        (𝒰.opens i ⊓ E k) ⊓ (𝒰.opens i ⊓ E l)
          ≤ 𝒰.opens i ⊓ 𝒰.opens (p k) ⊓ 𝒰.opens (p l))) (unitsEvInf_trans γ i (p k) (p l))
    simp only [map_mul, map_inv, unitsRestrict_unitsRestrict] at e₁ e₂ ⊢
    rw [← e₁, ← e₂]
    group
  choose β hβ using key
  -- Step 2: the coboundary relation for `β` holds on the cover `{𝒰 i ⊓ 𝒰 j ⊓ E k}_k`
  -- of `𝒰 i ⊓ 𝒰 j`, hence everywhere by separation.
  refine ⟨β, fun i j ↦ ?_⟩
  refine unitsRestrict_eq_of_locally_eq
    (W := fun k ↦ 𝒰.opens i ⊓ 𝒰.opens j ⊓ E k) (fun k ↦ inf_le_left)
    (fun w hw ↦ Opens.mem_iSup.mpr ?_) _ _ (fun k ↦ ?_)
  · obtain ⟨k, hk⟩ := hcov w
    exact ⟨k, hw, hk⟩
  have e₁ := congrArg (X.unitsRestrict
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      𝒰.opens i ⊓ 𝒰.opens j ⊓ E k ≤ 𝒰.opens i ⊓ E k)) (hβ i k)
  have e₂ := congrArg (X.unitsRestrict
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      𝒰.opens i ⊓ 𝒰.opens j ⊓ E k ≤ 𝒰.opens j ⊓ E k)) (hβ j k)
  have e₃ := congrArg (X.unitsRestrict
    (inf_le_inf le_rfl (hle k) :
      𝒰.opens i ⊓ 𝒰.opens j ⊓ E k ≤ 𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens (p k)))
    (unitsEvInf_trans γ i j (p k))
  simp only [map_mul, map_inv, unitsRestrict_unitsRestrict] at e₁ e₂ e₃ ⊢
  rw [e₁, e₂, ← e₃]
  group

/-- **Triviality of an `H¹` class from a refining family**: a unit cocycle on a pointed
cover admitting a coboundary datum on a refining family is itself a coboundary, so its
`H¹` class is trivial. -/
theorem unitsH1_eq_one_of_family {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰)
    {κ : Type*} (p : κ → X) (E : κ → X.Opens) (hle : ∀ k, E k ≤ 𝒰.opens (p k))
    (hcov : ∀ x : X, ∃ k, x ∈ E k) (α : ∀ k, Γ(X, E k)ˣ)
    (hα : ∀ k l,
      X.unitsRestrict (inf_le_left : E k ⊓ E l ≤ E k) (α k)
          * X.unitsRestrict (inf_le_inf (hle k) (hle l)) (unitsEvInf γ (p k) (p l))
        = X.unitsRestrict inf_le_right (α l)) :
    γ.class = (1 : X.unitsH1 𝒰) := by
  obtain ⟨β, hβ⟩ := exists_coboundary_of_family γ p E hle hcov α hα
  rw [show (1 : X.unitsH1 𝒰) = OneCocycle.class 1 from rfl]
  refine (OneCocycle.class_eq_iff _ _).mpr
    ((OneCocycle.isCohomologous_iff_evInf _ _).mpr ⟨β, fun i j ↦ ?_⟩)
  rw [OneCocycle.one_evInf, one_mul]
  exact hβ i j

end Scheme

end AlgebraicGeometry
