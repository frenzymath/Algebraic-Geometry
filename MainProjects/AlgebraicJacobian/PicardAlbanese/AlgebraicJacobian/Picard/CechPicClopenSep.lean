/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.OpenImmersionUnits
import AlgebraicJacobian.Picard.RefinementInjectivity

/-!
# Separation of Čech Picard classes along a clopen partition

For a scheme `Y` partitioned by the images of finitely-or-infinitely many open
immersions `w i : Z i ⟶ Y` with pairwise disjoint ranges covering `Y` (a *clopen
partition* — each range is open with open complement), two Čech Picard classes on `Y`
agreeing on every piece agree
(`AlgebraicGeometry.Scheme.CechPic.eq_of_map_eq_of_clopen`).

Route: represent both classes on a common pointed cover refined so that the member at
`y` lies inside the piece of `y`; the ratio class pulls back to a coboundary on each
piece (`CechPic.mk_injective` — refinement injectivity), and the cobounding units
descend through the section equivalence of the open immersions
(`Scheme.Hom.unitsPreimageEquiv`) to a coboundary on `Y` itself: overlaps of members
from different pieces are empty, so only the single-piece coboundary relations matter,
and those transport across `w i` by injectivity of pullback on opens inside the range.

This is the exact clopen analogue of the projection-descent step of
`AlgebraicGeometry.Over.prPullback_injective` (`AlgebraicJacobian.Picard.Separatedness`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {ι : Type u} {Y : Scheme.{u}} {Z : ι → Scheme.{u}} (w : ∀ i, Z i ⟶ Y)
  [∀ i, IsOpenImmersion (w i)]

/-- The descent step for the clopen separation, with the piece points and the descended
units abstracted (the clopen mirror of `Over.descend_coboundary` in
`AlgebraicJacobian.Picard.Separatedness`): if the pullback to the piece `Z i` of a unit
cocycle `γ` on `𝒱` is the coboundary of `α`, and `βy, βy'` pull back to the values of
`α` at points `z, z'` over `y, y'`, then `βy, βy'` satisfy the coboundary relation for
`γ` at `(y, y')` — provided both members of the cover lie inside the range of the
piece. -/
private lemma clopen_descend_coboundary {i : ι} {𝒱 : Y.PointedCover}
    (γ : Y.unitsCocycle 𝒱)
    (α : ∀ z : Z i, Γ(Z i, (𝒱.pullback (w i)).opens z)ˣ)
    (hα : ∀ z z',
      (Z i).unitsRestrict
          (inf_le_left : (𝒱.pullback (w i)).opens z ⊓ (𝒱.pullback (w i)).opens z'
            ≤ (𝒱.pullback (w i)).opens z) (α z)
          * Scheme.unitsEvInf ((w i).pullbackUnitsCocycle γ) z z'
        = (Z i).unitsRestrict inf_le_right (α z'))
    (z z' : Z i) (y y' : Y)
    (hz : (w i).base z = y) (hz' : (w i).base z' = y')
    (hzle : (w i) ⁻¹ᵁ 𝒱.opens y ≤ (𝒱.pullback (w i)).opens z)
    (hz'le : (w i) ⁻¹ᵁ 𝒱.opens y' ≤ (𝒱.pullback (w i)).opens z')
    (hVy : 𝒱.opens y ≤ (w i).opensRange) (hVy' : 𝒱.opens y' ≤ (w i).opensRange)
    (βy : Γ(Y, 𝒱.opens y)ˣ) (βy' : Γ(Y, 𝒱.opens y')ˣ)
    (hβy : (w i).unitsAppLE (𝒱.opens y) ((w i) ⁻¹ᵁ 𝒱.opens y) le_rfl βy
      = (Z i).unitsRestrict hzle (α z))
    (hβy' : (w i).unitsAppLE (𝒱.opens y') ((w i) ⁻¹ᵁ 𝒱.opens y') le_rfl βy'
      = (Z i).unitsRestrict hz'le (α z')) :
    Y.unitsRestrict (inf_le_left : 𝒱.opens y ⊓ 𝒱.opens y' ≤ 𝒱.opens y) βy
        * Scheme.unitsEvInf γ y y'
      = Y.unitsRestrict inf_le_right βy' := by
  subst hz hz'
  -- injectivity of pullback of unit sections on the overlap, which lies in the range
  have hinj : Function.Injective ((w i).unitsAppLE
      (𝒱.opens ((w i).base z) ⊓ 𝒱.opens ((w i).base z'))
      ((w i) ⁻¹ᵁ (𝒱.opens ((w i).base z) ⊓ 𝒱.opens ((w i).base z')))
      le_rfl) :=
    (Scheme.Hom.unitsAppLE_bijective_of_le_opensRange (w i)
      (inf_le_left.trans hVy)).injective
  apply hinj
  rw [map_mul]
  -- the descended units, restricted to `w⁻¹(𝒱 y ⊓ 𝒱 y')`
  have e₁ := congrArg ((Z i).unitsRestrict
    ((w i).preimage_mono (inf_le_left : 𝒱.opens ((w i).base z) ⊓ 𝒱.opens ((w i).base z')
      ≤ 𝒱.opens ((w i).base z)))) hβy
  rw [Scheme.Hom.unitsAppLE_map, Scheme.unitsRestrict_unitsRestrict] at e₁
  have e₂ := congrArg ((Z i).unitsRestrict
    ((w i).preimage_mono (inf_le_right : 𝒱.opens ((w i).base z) ⊓ 𝒱.opens ((w i).base z')
      ≤ 𝒱.opens ((w i).base z')))) hβy'
  rw [Scheme.Hom.unitsAppLE_map, Scheme.unitsRestrict_unitsRestrict] at e₂
  -- the coboundary relation for `α`, restricted to `w⁻¹(𝒱 y ⊓ 𝒱 y')`
  have e₃ := congrArg ((Z i).unitsRestrict
    ((w i).le_preimage_inf ((w i).preimage_mono inf_le_left)
        ((w i).preimage_mono inf_le_right) :
      (w i) ⁻¹ᵁ (𝒱.opens ((w i).base z) ⊓ 𝒱.opens ((w i).base z'))
        ≤ (𝒱.pullback (w i)).opens z ⊓ (𝒱.pullback (w i)).opens z')) (hα z z')
  erw [map_mul, Scheme.unitsRestrict_unitsRestrict, Scheme.unitsRestrict_unitsRestrict,
    Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, Scheme.Hom.unitsAppLE_map] at e₃
  -- assemble
  rw [Scheme.Hom.map_unitsAppLE, Scheme.Hom.map_unitsAppLE, e₁, e₂]
  exact e₃

/-- The core of the clopen separation, at the level of `H¹` classes on an adapted
pointed cover: a class on a cover whose member at `y` lies inside the range of the piece
of `y` and whose pullback to every piece is trivial is trivial. -/
private lemma unitsH1_eq_one_of_pieces (piece : Y → ι)
    (hdisj : ∀ i j, i ≠ j → (w i).opensRange ⊓ (w j).opensRange = ⊥)
    (hpiece : ∀ y, y ∈ (w (piece y)).opensRange)
    {𝒱 : Y.PointedCover} (h𝒱 : ∀ y, 𝒱.opens y ≤ (w (piece y)).opensRange)
    (b : Y.unitsH1 𝒱) (hb : ∀ i, (w i).pullbackUnitsH1 𝒱 b = 1) :
    b = 1 := by
  induction b using Quot.ind with | _ γ =>
  -- extract the piece coboundaries
  have hstep : ∀ i : ι, ∃ α : ∀ z : Z i, Γ(Z i, (𝒱.pullback (w i)).opens z)ˣ,
      ∀ z z',
        (Z i).unitsRestrict
            (inf_le_left : (𝒱.pullback (w i)).opens z ⊓ (𝒱.pullback (w i)).opens z'
              ≤ (𝒱.pullback (w i)).opens z) (α z)
            * Scheme.unitsEvInf ((w i).pullbackUnitsCocycle γ) z z'
          = (Z i).unitsRestrict inf_le_right (α z') := by
    intro i
    have h1 : ((w i).pullbackUnitsCocycle γ).class = OneCocycle.class 1 := hb i
    obtain ⟨α, hα⟩ := (OneCocycle.isCohomologous_iff_evInf _ _).mp
      ((OneCocycle.class_eq_iff _ _).mp h1)
    refine ⟨α, fun z z' => ?_⟩
    have h2 := hα z z'
    rw [OneCocycle.one_evInf, one_mul] at h2
    exact h2
  choose α hα using hstep
  -- glue the piece coboundaries to a coboundary on `Y`
  have hglue : ∀ y : Y, ∃ βy : Γ(Y, 𝒱.opens y)ˣ,
      ∀ (i : ι) (z : Z i) (hz : (w i).base z = y)
        (hzle : (w i) ⁻¹ᵁ 𝒱.opens y ≤ (𝒱.pullback (w i)).opens z),
        (w i).unitsAppLE (𝒱.opens y) ((w i) ⁻¹ᵁ 𝒱.opens y) le_rfl βy
          = (Z i).unitsRestrict hzle (α i z) := by
    intro y
    obtain ⟨z₀, hz₀⟩ := Scheme.Hom.mem_opensRange.mp (hpiece y)
    refine ⟨(Scheme.Hom.unitsPreimageEquiv (w (piece y)) (h𝒱 y)).symm
      ((Z (piece y)).unitsRestrict
        (le_of_eq (congrArg (fun t => (w (piece y)) ⁻¹ᵁ 𝒱.opens t) hz₀.symm))
        (α (piece y) z₀)), ?_⟩
    intro i z hz hzle
    -- the piece of `y` is forced
    have hi : i = piece y := by
      by_contra hne
      have hymem : y ∈ (w i).opensRange ⊓ (w (piece y)).opensRange :=
        ⟨⟨z, hz⟩, hpiece y⟩
      rw [hdisj i (piece y) hne] at hymem
      exact hymem
    subst hi
    -- the point over `y` is forced
    have hzz₀ : z = z₀ := (w (piece y)).isOpenEmbedding.injective (by rw [hz, hz₀])
    subst hzz₀
    rw [Scheme.Hom.unitsAppLE_unitsPreimageEquiv_symm,
      Scheme.unitsRestrict_unitsRestrict]
    rfl
  choose β hβ using hglue
  -- the glued units witness the coboundary relation for `γ`
  rw [show (1 : Y.unitsH1 𝒱) = OneCocycle.class 1 from rfl,
    show (Quot.mk _ γ : Y.unitsH1 𝒱) = OneCocycle.class γ from rfl]
  refine (OneCocycle.class_eq_iff _ _).mpr
    ((OneCocycle.isCohomologous_iff_evInf _ _).mpr ⟨β, fun y y' => ?_⟩)
  rw [OneCocycle.one_evInf, one_mul]
  by_cases hp : piece y' = piece y
  · -- both members lie in one piece: descend the piece coboundary
    obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp (hpiece y)
    obtain ⟨z', hz'⟩ := Scheme.Hom.mem_opensRange.mp (hp ▸ hpiece y')
    exact clopen_descend_coboundary w γ (α (piece y)) (hα (piece y)) z z' y y' hz hz'
      (le_of_eq (congrArg (fun t => (w (piece y)) ⁻¹ᵁ 𝒱.opens t) hz.symm))
      (le_of_eq (congrArg (fun t => (w (piece y)) ⁻¹ᵁ 𝒱.opens t) hz'.symm))
      (h𝒱 y) (hp ▸ h𝒱 y') (β y) (β y')
      (hβ y (piece y) z hz
        (le_of_eq (congrArg (fun t => (w (piece y)) ⁻¹ᵁ 𝒱.opens t) hz.symm)))
      (hβ y' (piece y) z' hz'
        (le_of_eq (congrArg (fun t => (w (piece y)) ⁻¹ᵁ 𝒱.opens t) hz'.symm)))
  · -- members from different pieces do not meet
    have hss : Subsingleton Γ(Y, 𝒱.opens y ⊓ 𝒱.opens y')ˣ := by
      refine Y.subsingleton_units_of_le_bot ?_
      calc 𝒱.opens y ⊓ 𝒱.opens y'
          ≤ (w (piece y)).opensRange ⊓ (w (piece y')).opensRange :=
            inf_le_inf (h𝒱 y) (h𝒱 y')
        _ = ⊥ := hdisj (piece y) (piece y') (fun h => hp h.symm)
    exact @Subsingleton.elim _ hss _ _

/-- **Separation of Čech Picard classes along a clopen partition**: two Čech Picard
classes of `Y` with equal pullbacks to every piece of a clopen partition of `Y` are
equal. -/
theorem CechPic.eq_of_map_eq_of_clopen
    (hdisj : ∀ i j, i ≠ j → (w i).opensRange ⊓ (w j).opensRange = ⊥)
    (hcover : ∀ y : Y, ∃ i, y ∈ (w i).opensRange)
    {L L' : Y.CechPic} (h : ∀ i, CechPic.map (w i) L = CechPic.map (w i) L') :
    L = L' := by
  induction L using CechPic.ind with | _ 𝒰₁ a₁ =>
  induction L' using CechPic.ind with | _ 𝒰₂ a₂ =>
  choose piece hpiece using hcover
  -- the adapted common refinement
  set 𝒱 : Y.PointedCover :=
    ⟨fun y => (𝒰₁.opens y ⊓ 𝒰₂.opens y) ⊓ (w (piece y)).opensRange,
      fun y => ⟨⟨𝒰₁.mem_opens y, 𝒰₂.mem_opens y⟩, hpiece y⟩⟩ with h𝒱def
  have h₁ : 𝒱 ≤ 𝒰₁ := fun y => inf_le_left.trans inf_le_left
  have h₂ : 𝒱 ≤ 𝒰₂ := fun y => inf_le_left.trans inf_le_right
  have h𝒱 : ∀ y, 𝒱.opens y ≤ (w (piece y)).opensRange := fun y => inf_le_right
  rw [← CechPic.mk_unitsRes h₁ a₁, ← CechPic.mk_unitsRes h₂ a₂]
  refine congrArg (CechPic.mk 𝒱) ?_
  -- reduce to triviality of the ratio class
  have hb : ∀ i, (w i).pullbackUnitsH1 𝒱
      (unitsRes h₁ a₁ * (unitsRes h₂ a₂)⁻¹) = 1 := by
    intro i
    have hmk : CechPic.map (w i) (CechPic.mk 𝒱 (unitsRes h₁ a₁))
        = CechPic.map (w i) (CechPic.mk 𝒱 (unitsRes h₂ a₂)) := by
      rw [CechPic.mk_unitsRes h₁ a₁, CechPic.mk_unitsRes h₂ a₂]
      exact h i
    have hres := CechPic.mk_injective (𝒱.pullback (w i))
      (show CechPic.mk (𝒱.pullback (w i)) ((w i).pullbackUnitsH1 𝒱 (unitsRes h₁ a₁))
          = CechPic.mk (𝒱.pullback (w i)) ((w i).pullbackUnitsH1 𝒱 (unitsRes h₂ a₂))
        from hmk)
    rw [map_mul, map_inv, hres, mul_inv_cancel]
  have hone := unitsH1_eq_one_of_pieces w piece hdisj hpiece h𝒱
    (unitsRes h₁ a₁ * (unitsRes h₂ a₂)⁻¹) hb
  exact mul_inv_eq_one.mp hone

end Scheme

end AlgebraicGeometry
