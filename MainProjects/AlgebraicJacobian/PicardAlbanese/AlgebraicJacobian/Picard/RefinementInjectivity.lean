/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic

/-!
# Refinement injectivity for the unit Čech `H¹`

In degree one, Čech cohomology classes on a cover embed into those on any refinement:
for pointed covers `𝒲 ≤ 𝒰` of a scheme `X`, the restriction map
`unitsRes : X.unitsH1 𝒰 →* X.unitsH1 𝒲` is **injective**
(`AlgebraicGeometry.Scheme.unitsRes_injective`). Consequently the refinement colimit
`Scheme.CechPic` is a colimit of injections: a class `CechPic.mk 𝒰 a` is trivial iff `a`
is already trivial on `𝒰` (`CechPic.mk_eq_one_iff`), and `CechPic.mk 𝒰` is injective
(`CechPic.mk_injective`) — the classical statement `Ȟ¹(𝒰, 𝒪^*) ↪ Pic(X)`.

Mathematically: suppose the restriction to `𝒲` of a unit cocycle `γ` on `𝒰` is the
coboundary of a family of units `α z ∈ 𝒪ˣ(𝒲 z)`. The comparison sections
`α z ⋅ γ(i,z)⁻¹ ∈ 𝒪ˣ(𝒰 i ⊓ 𝒲 z)` agree on overlaps — by the cocycle identity for `γ`
and the coboundary relation for `α` — hence glue, the units presheaf being a sheaf, to a
unit `β i ∈ 𝒪ˣ(𝒰 i)`; the family `β` exhibits `γ` as a coboundary on `𝒰` itself.

This file also provides the sheaf-theoretic substrate as reusable API: gluing
(`Scheme.exists_unitsRestrict_eq`) and separation (`Scheme.unitsRestrict_eq_of_locally_eq`)
for unit sections, together with the composition law `unitsRestrict_unitsRestrict`.

Refinement injectivity is the "fiberwise cocycle glue" of the separatedness ledger
(design §4.4) in reusable form; it is consumed by brick 3 (`Over.prPullback_injective`,
`AlgebraicJacobian.Picard.Separatedness`) and by the Zariski-sheaf-on-affines corollary
of the étale-separatedness theorem (C1).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-! ## The `unitsRestrict` calculus and the sheaf property for unit sections -/

@[simp]
lemma coe_unitsRestrict {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ) :
    (X.unitsRestrict h u : Γ(X, W)) = X.presheaf.map (homOfLE h).op u :=
  rfl

/-- Restriction of unit sections is transitive. -/
@[simp]
lemma unitsRestrict_unitsRestrict {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (u : Γ(X, U)ˣ) :
    X.unitsRestrict h₂ (X.unitsRestrict h₁ u) = X.unitsRestrict (h₂.trans h₁) u := by
  ext
  simp only [coe_unitsRestrict]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- **Separation for unit sections**: two units on `V` agreeing on all members of a cover
of `V` are equal. -/
theorem unitsRestrict_eq_of_locally_eq {ι : Type*} {V : X.Opens} {W : ι → X.Opens}
    (hle : ∀ i, W i ≤ V) (hcover : V ≤ ⨆ i, W i) (s t : Γ(X, V)ˣ)
    (h : ∀ i, X.unitsRestrict (hle i) s = X.unitsRestrict (hle i) t) : s = t := by
  ext
  exact X.sheaf.eq_of_locally_eq' W V (fun i ↦ homOfLE (hle i)) hcover _ _
    (fun i ↦ congrArg Units.val (h i))

/-- **Gluing for unit sections**: a family of units on the members of a cover of `V`,
compatible on pairwise intersections, glues to a unit on `V`. (The value and the inverse
glue separately as sections; the products of the glued sections are locally `1`, hence
`1` by separation.) -/
theorem exists_unitsRestrict_eq {ι : Type*} {V : X.Opens} {W : ι → X.Opens}
    (hle : ∀ i, W i ≤ V) (hcover : V ≤ ⨆ i, W i) (u : ∀ i, Γ(X, W i)ˣ)
    (hu : ∀ i j, X.unitsRestrict (inf_le_left : W i ⊓ W j ≤ W i) (u i)
        = X.unitsRestrict (inf_le_right : W i ⊓ W j ≤ W j) (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, X.unitsRestrict (hle i) s = u i := by
  have hval : TopCat.Presheaf.IsCompatible X.sheaf.1 W (fun i ↦ ((u i : Γ(X, W i)))) :=
    fun i j ↦ congrArg Units.val (hu i j)
  have hinv : TopCat.Presheaf.IsCompatible X.sheaf.1 W
      (fun i ↦ (((u i)⁻¹ : Γ(X, W i)ˣ) : Γ(X, W i))) := by
    intro i j
    have h : X.unitsRestrict (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹
        = X.unitsRestrict (inf_le_right : W i ⊓ W j ≤ W j) (u j)⁻¹ := by
      rw [map_inv, map_inv, hu i j]
    exact congrArg Units.val h
  obtain ⟨sv, hsv, -⟩ :=
    X.sheaf.existsUnique_gluing' W V (fun i ↦ homOfLE (hle i)) hcover _ hval
  obtain ⟨si, hsi, -⟩ :=
    X.sheaf.existsUnique_gluing' W V (fun i ↦ homOfLE (hle i)) hcover _ hinv
  have hvi : sv * si = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i ↦ homOfLE (hle i)) hcover
    intro i
    rw [map_mul, hsv, hsi, map_one]
    exact Units.mul_inv _
  have hiv : si * sv = 1 := by rw [mul_comm]; exact hvi
  exact ⟨⟨sv, si, hvi, hiv⟩, fun i ↦ Units.ext (hsv i)⟩

/-! ## Refinement injectivity -/

/-- The glued coboundary: if the restriction of the cocycle `γ` on `𝒰` to a refinement
`𝒲 ≤ 𝒰` is the coboundary of `α`, then the comparison sections `α z ⋅ γ(i,z)⁻¹` on
`𝒰 i ⊓ 𝒲 z` glue to units `β i ∈ 𝒪ˣ(𝒰 i)` exhibiting `γ` as a coboundary on `𝒰`. -/
private lemma exists_glued_coboundary {𝒰 𝒲 : X.PointedCover} (h : 𝒲 ≤ 𝒰)
    (γ : X.unitsCocycle 𝒰) (α : ∀ z, Γ(X, 𝒲.opens z)ˣ)
    (hα : ∀ z z',
      X.unitsRestrict (inf_le_left : 𝒲.opens z ⊓ 𝒲.opens z' ≤ 𝒲.opens z) (α z)
          * X.unitsRestrict (inf_le_inf (h z) (h z')) (unitsEvInf γ z z')
        = X.unitsRestrict inf_le_right (α z')) :
    ∃ β : ∀ i, Γ(X, 𝒰.opens i)ˣ, ∀ i j,
      X.unitsRestrict (inf_le_left : 𝒰.opens i ⊓ 𝒰.opens j ≤ 𝒰.opens i) (β i)
          * unitsEvInf γ i j
        = X.unitsRestrict inf_le_right (β j) := by
  -- Step 1: for each `i`, glue the comparison sections over the cover
  -- `{𝒰 i ⊓ 𝒲 z}_z` of `𝒰 i`.
  have key : ∀ i, ∃ βi : Γ(X, 𝒰.opens i)ˣ, ∀ z : X,
      X.unitsRestrict (inf_le_left : 𝒰.opens i ⊓ 𝒲.opens z ≤ 𝒰.opens i) βi
        = X.unitsRestrict inf_le_right (α z)
          * (X.unitsRestrict (inf_le_inf le_rfl (h z)) (unitsEvInf γ i z))⁻¹ := by
    intro i
    refine exists_unitsRestrict_eq (fun z ↦ inf_le_left)
      (fun w hw ↦ Opens.mem_iSup.mpr ⟨w, hw, 𝒲.mem_opens w⟩) _ (fun z z' ↦ ?_)
    -- compatibility on `O := (𝒰 i ⊓ 𝒲 z) ⊓ (𝒰 i ⊓ 𝒲 z')`, from the coboundary relation
    -- for `α` and the cocycle identity for `γ` at `(i, z, z')`, both restricted to `O`
    have e₁ := congrArg (X.unitsRestrict
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (𝒰.opens i ⊓ 𝒲.opens z) ⊓ (𝒰.opens i ⊓ 𝒲.opens z')
          ≤ 𝒲.opens z ⊓ 𝒲.opens z')) (hα z z')
    have e₂ := congrArg (X.unitsRestrict
      (le_inf (le_inf (inf_le_left.trans inf_le_left)
          ((inf_le_left.trans inf_le_right).trans (h z)))
          ((inf_le_right.trans inf_le_right).trans (h z')) :
        (𝒰.opens i ⊓ 𝒲.opens z) ⊓ (𝒰.opens i ⊓ 𝒲.opens z')
          ≤ 𝒰.opens i ⊓ 𝒰.opens z ⊓ 𝒰.opens z')) (unitsEvInf_trans γ i z z')
    simp only [map_mul, map_inv, unitsRestrict_unitsRestrict] at e₁ e₂ ⊢
    rw [← e₁, ← e₂]
    group
  choose β hβ using key
  -- Step 2: the coboundary relation for `β` holds on the cover `{𝒰 i ⊓ 𝒰 j ⊓ 𝒲 z}_z`
  -- of `𝒰 i ⊓ 𝒰 j`, hence everywhere by separation.
  refine ⟨β, fun i j ↦ ?_⟩
  refine unitsRestrict_eq_of_locally_eq
    (W := fun z ↦ 𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒲.opens z) (fun z ↦ inf_le_left)
    (fun w hw ↦ Opens.mem_iSup.mpr ⟨w, hw, 𝒲.mem_opens w⟩) _ _ (fun z ↦ ?_)
  have e₁ := congrArg (X.unitsRestrict
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒲.opens z ≤ 𝒰.opens i ⊓ 𝒲.opens z)) (hβ i z)
  have e₂ := congrArg (X.unitsRestrict
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒲.opens z ≤ 𝒰.opens j ⊓ 𝒲.opens z)) (hβ j z)
  have e₃ := congrArg (X.unitsRestrict
    (inf_le_inf le_rfl (h z) :
      𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒲.opens z ≤ 𝒰.opens i ⊓ 𝒰.opens j ⊓ 𝒰.opens z))
    (unitsEvInf_trans γ i j z)
  simp only [map_mul, map_inv, unitsRestrict_unitsRestrict] at e₁ e₂ e₃ ⊢
  rw [e₁, e₂, ← e₃]
  group

/-- **Refinement injectivity in degree one**: for pointed covers `𝒲 ≤ 𝒰` of a scheme,
restriction of unit Čech `H¹` classes along the refinement is injective. -/
theorem unitsRes_injective {𝒰 𝒲 : X.PointedCover} (h : 𝒲 ≤ 𝒰) :
    Function.Injective (unitsRes (X := X) h) := by
  refine (injective_iff_map_eq_one (unitsRes h)).mpr fun a ha ↦ ?_
  induction a using Quot.ind with | _ γ =>
  rw [show (1 : X.unitsH1 𝒲) = OneCocycle.class 1 from rfl] at ha
  obtain ⟨α, hα⟩ :=
    (OneCocycle.isCohomologous_iff_evInf _ _).mp ((OneCocycle.class_eq_iff _ _).mp ha)
  -- restate the coboundary data through the `Γ`-typed interface
  have hα' : ∀ z z',
      X.unitsRestrict (inf_le_left : 𝒲.opens z ⊓ 𝒲.opens z' ≤ 𝒲.opens z) (α z)
          * X.unitsRestrict (inf_le_inf (h z) (h z')) (unitsEvInf γ z z')
        = X.unitsRestrict inf_le_right (α z') := by
    intro z z'
    have h1 := hα z z'
    rw [OneCocycle.one_evInf, one_mul] at h1
    rw [← res_unitsEvInf h γ z z']
    exact h1
  obtain ⟨β, hβ⟩ := exists_glued_coboundary h γ α hα'
  rw [show (1 : X.unitsH1 𝒰) = OneCocycle.class 1 from rfl]
  refine (OneCocycle.class_eq_iff _ _).mpr
    ((OneCocycle.isCohomologous_iff_evInf _ _).mpr ⟨β, fun i j ↦ ?_⟩)
  rw [OneCocycle.one_evInf, one_mul]
  exact hβ i j

/-! ## Consequences for the Čech Picard group -/

namespace CechPic

/-- A Picard class is trivial iff its representing `H¹` class is trivial on its own
cover: no refinement is needed. -/
@[simp]
theorem mk_eq_one_iff {𝒰 : X.PointedCover} {a : X.unitsH1 𝒰} :
    CechPic.mk 𝒰 a = 1 ↔ a = 1 := by
  constructor
  · intro h1
    rw [CechPic.one_def] at h1
    obtain ⟨𝒲, h₁, h₂, e⟩ := CechPic.mk_eq_mk_iff.mp h1
    rw [map_one] at e
    exact unitsRes_injective h₁ (by rw [e, map_one])
  · rintro rfl
    exact CechPic.mk_one 𝒰

/-- `Ȟ¹(𝒰, 𝒪^*) ↪ Pic(X)`: the Picard class of an `H¹` class on a fixed pointed cover
determines it. -/
theorem mk_injective (𝒰 : X.PointedCover) :
    Function.Injective (CechPic.mk 𝒰 : X.unitsH1 𝒰 → X.CechPic) := by
  intro a b hab
  have h1 : CechPic.mk 𝒰 (a * b⁻¹) = 1 := by
    rw [← CechPic.mk_mul_mk, ← CechPic.mk_inv, hab, mul_inv_cancel]
  rw [mk_eq_one_iff] at h1
  exact mul_inv_eq_one.mp h1

end CechPic

end Scheme

end AlgebraicGeometry
