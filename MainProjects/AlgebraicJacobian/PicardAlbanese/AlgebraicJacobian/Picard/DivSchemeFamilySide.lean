/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyTheta
import AlgebraicJacobian.Cohomology.RigidEngine4Relative

/-!
# DDR-3 infrastructure — flatness of chart sections and side-uniform theta components

The substrate of the relative local-generator construction
(`AlgebraicJacobian.Picard.DivSchemeFamily`, `informal/spec-dd-r.md` §3 item 3):

* `AlgebraicGeometry.flat_sections_basicOpen` — flatness of a section ring over the base
  descends to basic opens (`IsAffineOpen.isLocalization_basicOpen` + localization
  flatness + `Module.Flat.trans`);
* `AlgebraicGeometry.sections_mem_nonZeroDivisors_of_forall_germ`,
  `AlgebraicGeometry.exists_unit_mul_of_mutual_dvd` — germwise regularity gives
  section-level regularity, and mutual divisibility against a regular section is a unit
  ratio (the ratio-unit engine);
* `AlgebraicGeometry.relPinnedChart`, `flat_sections_relPinnedChart` — the two pinned
  charts of the relative curve indexed by a `Bool` side, with the free-base-change
  flatness `Γ(C_R, Vᵢᴿ) = R ⊗[k] Γ(C, Vᵢ)` (`free_relSections`);
* `AlgebraicGeometry.relThetaResSide`, `relThetaSideUnit`, `relThetaResSide_matching` —
  the side-uniform chart components of a global theta section (`relThetaResFst/Snd`
  packaged over the side index) and their matching through the theta cocycle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The flatness ladder: section rings of basic opens are flat over the test ring -/

section BasicOpenFlat

variable (K : Type u) [CommRing K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- **Flatness descends to basic opens**: for an affine open `V` with `Γ(X, V)` flat over
the base ring `K`, the section ring of any basic open `D(f) ⊆ V` is flat over `K` —
`Γ(X, D(f))` is a localization of `Γ(X, V)` (`IsAffineOpen.isLocalization_basicOpen`),
localizations are flat, and flatness composes along the scalar tower
`K → Γ(X, V) → Γ(X, D(f))`. -/
theorem flat_sections_basicOpen {V : X.Opens} (hV : IsAffineOpen V)
    (hflat : Module.Flat K Γ(X, V)) (f : Γ(X, V)) :
    Module.Flat K Γ(X, X.basicOpen f) := by
  haveI := hflat
  haveI := hV.isLocalization_basicOpen f
  haveI : Module.Flat Γ(X, V) Γ(X, X.basicOpen f) :=
    IsLocalization.flat _ (Submonoid.powers f)
  haveI : IsScalarTower K Γ(X, V) Γ(X, X.basicOpen f) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (X.overAlgebraMap_apply_res K (homOfLE (X.basicOpen_le f)).op r).symm
  exact Module.Flat.trans K Γ(X, V) Γ(X, X.basicOpen f)

end BasicOpenFlat

/-! ## Section-level and unit-ratio consequences of germwise regularity -/

section GermRegular

variable {X : Scheme.{u}}

/-- A section all of whose germs are nonzerodivisors is a nonzerodivisor
(sections of a sheaf inject into the product of their germs). -/
theorem sections_mem_nonZeroDivisors_of_forall_germ {W : X.Opens} {s : Γ(X, W)}
    (hreg : ∀ (y : X) (hy : y ∈ W),
      (X.presheaf.germ W y hy).hom s ∈ nonZeroDivisors (X.presheaf.stalk y)) :
    s ∈ nonZeroDivisors Γ(X, W) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro t ht
  apply TopCat.Presheaf.section_ext X.sheaf W t 0
  intro y hy
  rw [map_zero]
  have key : (X.presheaf.germ W y hy).hom t * (X.presheaf.germ W y hy).hom s = 0 := by
    rw [← map_mul, ht, map_zero]
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (hreg y hy)).mp key

/-- **Mutual divisibility against a germwise-regular section is a unit ratio**: if
`s = c₁ · t` and `t = c₂ · s` with every germ of `s` a nonzerodivisor, then `c₁` is a
unit, so `s = u · t` — the ratio-unit engine of the local-generator construction. -/
theorem exists_unit_mul_of_mutual_dvd {W : X.Opens} {s t c₁ c₂ : Γ(X, W)}
    (hreg : ∀ (y : X) (hy : y ∈ W),
      (X.presheaf.germ W y hy).hom s ∈ nonZeroDivisors (X.presheaf.stalk y))
    (h₁ : s = c₁ * t) (h₂ : t = c₂ * s) :
    ∃ u : Γ(X, W)ˣ, s = (u : Γ(X, W)) * t := by
  have hzero : (1 - c₁ * c₂) * s = 0 := by
    rw [sub_mul, one_mul, mul_assoc, ← h₂, ← h₁, sub_self]
  have hone : c₁ * c₂ = 1 := by
    have h := (mul_right_mem_nonZeroDivisors_eq_zero_iff
      (sections_mem_nonZeroDivisors_of_forall_germ hreg)).mp hzero
    rwa [sub_eq_zero, eq_comm] at h
  exact ⟨Units.mkOfMulEqOne c₁ c₂ hone, h₁⟩

end GermRegular

/-! ## The pinned chart of a side and the side-uniform theta components -/

section Sides

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsFinite π]

/-- The pinned chart of a side: `V₀ᴿ` for `false`, `V₁ᴿ` for `true`. -/
noncomputable def relPinnedChart : Bool → (relCurve C R).Opens
  | false => (relCover C R (fiberTwoCover π)).V₀
  | true => (relCover C R (fiberTwoCover π)).V₁

@[simp]
lemma relPinnedChart_false :
    relPinnedChart C R π false = (relCover C R (fiberTwoCover π)).V₀ := rfl

@[simp]
lemma relPinnedChart_true :
    relPinnedChart C R π true = (relCover C R (fiberTwoCover π)).V₁ := rfl

/-- Both pinned charts are affine. -/
lemma isAffineOpen_relPinnedChart (b : Bool) : IsAffineOpen (relPinnedChart C R π b) := by
  cases b
  · exact relCover_isAffineOpen₀ C R (fiberTwoCover π)
  · exact relCover_isAffineOpen₁ C R (fiberTwoCover π)

/-- **Flatness of the pinned chart sections over the test ring**: `Γ(C_R, Vᵢᴿ)` is the
free base change `R ⊗[k] Γ(C, Vᵢ)` (`free_relSections`), hence flat. -/
theorem flat_sections_relPinnedChart (b : Bool) :
    Module.Flat R Γ(relCurve C R, relPinnedChart C R π b) := by
  cases b
  · haveI : Module.Free R Γ(relCurve C R, relPinnedChart C R π false) :=
      free_relSections C R (fiberChart₀ π)
        (isAffineOpen_preimage_chartOpen π 0).isCompact
        (isAffineOpen_preimage_chartOpen π 0).isQuasiSeparated
    exact Module.Flat.of_free
  · haveI : Module.Free R Γ(relCurve C R, relPinnedChart C R π true) :=
      free_relSections C R (fiberChart₁ π)
        (isAffineOpen_preimage_chartOpen π 1).isCompact
        (isAffineOpen_preimage_chartOpen π 1).isQuasiSeparated
    exact Module.Flat.of_free

variable {C R π}
variable (a : ℕ)

/-- **The side-uniform chart component of a global theta section**, restricted into an
open below the pinned chart of the side: `relThetaResFst` on side `false`,
`relThetaResSnd` on side `true`. -/
noncomputable def relThetaResSide :
    ∀ (b : Bool) {W : (relCurve C R).Opens}, W ≤ relPinnedChart C R π b →
      (relThetaSections C R π a →ₗ[R] Γ(relCurve C R, W))
  | false, _, hW => relThetaResFst a (le_inf le_top hW)
  | true, _, hW => relThetaResSnd a (le_inf le_top hW)

@[simp]
lemma relThetaResSide_false {W : (relCurve C R).Opens}
    (hW : W ≤ relPinnedChart C R π false) (x : relThetaSections C R π a) :
    relThetaResSide a false hW x = (relCurve C R).resHom (le_inf le_top hW) x.val.1 := rfl

@[simp]
lemma relThetaResSide_true {W : (relCurve C R).Opens}
    (hW : W ≤ relPinnedChart C R π true) (x : relThetaSections C R π a) :
    relThetaResSide a true hW x = (relCurve C R).resHom (le_inf le_top hW) x.val.2 := rfl

/-- The side components commute with restriction. -/
lemma resHom_relThetaResSide (b : Bool) {W W' : (relCurve C R).Opens}
    (hW : W ≤ relPinnedChart C R π b) (h' : W' ≤ W) (x : relThetaSections C R π a) :
    (relCurve C R).resHom h' (relThetaResSide a b hW x)
      = relThetaResSide a b (h'.trans hW) x := by
  cases b <;> exact Scheme.resHom_resHom _ _ _

/-- **The matching unit of an ordered pair of sides** on an open below both pinned
charts: `1` on equal sides, the theta cocycle (resp. its inverse) across the charts. -/
noncomputable def relThetaSideUnit :
    ∀ (b b' : Bool) {W : (relCurve C R).Opens},
      W ≤ relPinnedChart C R π b ⊓ relPinnedChart C R π b' → Γ(relCurve C R, W)ˣ
  | false, false, _, _ => 1
  | false, true, _, hW => (relCurve C R).unitsRestrict hW (relThetaCocycle C R π a)
  | true, false, _, hW =>
      ((relCurve C R).unitsRestrict
        (le_inf (hW.trans inf_le_right) (hW.trans inf_le_left))
        (relThetaCocycle C R π a))⁻¹
  | true, true, _, _ => 1

/-- **The side matching law**: on an open below both pinned charts, the two side
components of a global theta section differ by the side matching unit
(`relThetaSections_matching` in side-uniform form). -/
lemma relThetaResSide_matching (b b' : Bool) {W : (relCurve C R).Opens}
    (hW : W ≤ relPinnedChart C R π b ⊓ relPinnedChart C R π b')
    (x : relThetaSections C R π a) :
    relThetaResSide a b (hW.trans inf_le_left) x
      = (relThetaSideUnit a b b' hW : Γ(relCurve C R, W))
        * relThetaResSide a b' (hW.trans inf_le_right) x := by
  cases b <;> cases b'
  · rw [show relThetaSideUnit a false false hW = 1 from rfl, Units.val_one, one_mul]
  · exact relThetaSections_matching a x hW
  · have key := relThetaSections_matching a x
      (le_inf (hW.trans inf_le_right) (hW.trans inf_le_left))
    change relThetaResSide a true (hW.trans inf_le_left) x
        = ↑((relCurve C R).unitsRestrict
            (le_inf (hW.trans inf_le_right) (hW.trans inf_le_left))
            (relThetaCocycle C R π a))⁻¹
          * relThetaResSide a false (hW.trans inf_le_right) x
    rw [Units.eq_inv_mul_iff_mul_eq]
    exact key.symm
  · rw [show relThetaSideUnit a true true hW = 1 from rfl, Units.val_one, one_mul]

end Sides

end AlgebraicGeometry
