/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.UnitsCocycle
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Unit sections across an open immersion

For an open immersion `w : Z ⟶ Y` and an open `V ⊆ Y` contained in the image of `w`,
pullback of sections along `w` is bijective on `V`; this file packages the resulting
transport of *unit* sections and its calculus, the substrate for decomposing Čech Picard
classes along clopen partitions (`AlgebraicJacobian.Picard.CechPicClopen`):

* `AlgebraicGeometry.Scheme.Hom.isIso_appLE_of_le_opensRange`: `Γ(Y, V) ≅ Γ(Z, w⁻¹ V)`
  for `V ≤ range w`.
* `AlgebraicGeometry.Scheme.Hom.unitsPreimageEquiv`: the unit-group form, as a `≃*`.
* the transport calculus: restriction of a transported unit is pullback
  (`unitsRestrict_unitsPreimageEquiv_symm_eq_of_unitsRestrict`,
  `unitsAppLE_unitsPreimageEquiv_symm`), and transport commutes with restriction
  (`unitsRestrict_unitsPreimageEquiv_symm`).
* `AlgebraicGeometry.Scheme.subsingleton_units_of_le_bot`: units over an empty open form
  a trivial group — the off-piece degeneration of every clopen-partition computation.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {Y Z : Scheme.{u}}

/-! ## Sections over an empty open -/

/-- Sections over an open contained in `⊥` form a subsingleton ring. -/
lemma subsingleton_sections_of_le_bot (X : Scheme.{u}) {O : X.Opens} (h : O ≤ ⊥) :
    Subsingleton Γ(X, O) := by
  have hO : O = ⊥ := le_bot_iff.mp h
  rw [hO]
  infer_instance

/-- Unit sections over an open contained in `⊥` form a trivial group. -/
lemma subsingleton_units_of_le_bot (X : Scheme.{u}) {O : X.Opens} (h : O ≤ ⊥) :
    Subsingleton Γ(X, O)ˣ := by
  haveI := X.subsingleton_sections_of_le_bot h
  exact ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

/-! ## The unit transport across an open immersion -/

namespace Hom

variable (w : Z ⟶ Y) [IsOpenImmersion w]

/-- For an open immersion `w` and an open `V` inside its image, pullback of sections is
an isomorphism onto the sections of the preimage. -/
theorem isIso_appLE_of_le_opensRange {V : Y.Opens} (hV : V ≤ w.opensRange) :
    IsIso (w.appLE V (w ⁻¹ᵁ V) le_rfl) := by
  have h : w.appLE V (w ⁻¹ᵁ V) le_rfl = w.app V := Scheme.Hom.appLE_eq_app w
  rw [h]
  exact w.isIso_app V hV

/-- The transport of unit sections across an open immersion, on an open inside the
image: `Γ(Y, V)ˣ ≃* Γ(Z, w⁻¹ V)ˣ`. -/
noncomputable def unitsPreimageEquiv {V : Y.Opens} (hV : V ≤ w.opensRange) :
    Γ(Y, V)ˣ ≃* Γ(Z, w ⁻¹ᵁ V)ˣ :=
  haveI := isIso_appLE_of_le_opensRange w hV
  Units.mapEquiv (asIso (w.appLE V (w ⁻¹ᵁ V) le_rfl)).commRingCatIsoToRingEquiv.toMulEquiv

@[simp]
lemma unitsPreimageEquiv_apply {V : Y.Opens} (hV : V ≤ w.opensRange) (u : Γ(Y, V)ˣ) :
    unitsPreimageEquiv w hV u = w.unitsAppLE V (w ⁻¹ᵁ V) le_rfl u :=
  rfl

/-- Restriction of a transported unit into the piece is pullback of the unit. -/
lemma unitsRestrict_unitsPreimageEquiv {V : Y.Opens} (hV : V ≤ w.opensRange)
    {U : Z.Opens} (e : U ≤ w ⁻¹ᵁ V) (u : Γ(Y, V)ˣ) :
    Z.unitsRestrict e (unitsPreimageEquiv w hV u) = w.unitsAppLE V U e u := by
  rw [unitsPreimageEquiv_apply]
  exact w.unitsAppLE_map le_rfl (homOfLE e).op u

/-- Pullback of an inverse transport is restriction: the fundamental computation rule
for `unitsPreimageEquiv.symm`. -/
lemma unitsAppLE_unitsPreimageEquiv_symm {V : Y.Opens} (hV : V ≤ w.opensRange)
    {U : Z.Opens} (e : U ≤ w ⁻¹ᵁ V) (v : Γ(Z, w ⁻¹ᵁ V)ˣ) :
    w.unitsAppLE V U e ((unitsPreimageEquiv w hV).symm v) = Z.unitsRestrict e v := by
  have h := unitsRestrict_unitsPreimageEquiv w hV e ((unitsPreimageEquiv w hV).symm v)
  rw [(unitsPreimageEquiv w hV).apply_symm_apply] at h
  exact h.symm

/-- Pullback of unit sections onto the full preimage of an open inside the image is
bijective. -/
lemma unitsAppLE_bijective_of_le_opensRange {V : Y.Opens} (hV : V ≤ w.opensRange) :
    Function.Bijective (w.unitsAppLE V (w ⁻¹ᵁ V) le_rfl) :=
  (unitsPreimageEquiv w hV).bijective

/-- The inverse transport commutes with restriction on the base. -/
lemma unitsRestrict_unitsPreimageEquiv_symm {V V' : Y.Opens} (hV : V ≤ w.opensRange)
    (h : V' ≤ V) (v : Γ(Z, w ⁻¹ᵁ V)ˣ) :
    Y.unitsRestrict h ((unitsPreimageEquiv w hV).symm v)
      = (unitsPreimageEquiv w (h.trans hV)).symm
          (Z.unitsRestrict (w.preimage_mono h) v) := by
  apply (unitsPreimageEquiv w (h.trans hV)).injective
  rw [(unitsPreimageEquiv w (h.trans hV)).apply_symm_apply,
    unitsPreimageEquiv_apply]
  have h₁ := w.map_unitsAppLE (le_rfl : w ⁻¹ᵁ V' ≤ w ⁻¹ᵁ V') (homOfLE h).op
    ((unitsPreimageEquiv w hV).symm v)
  rw [unitsAppLE_unitsPreimageEquiv_symm w hV
    ((le_rfl : w ⁻¹ᵁ V' ≤ w ⁻¹ᵁ V').trans
      ((TopologicalSpace.Opens.map w.base).map (homOfLE h)).le) v] at h₁
  exact h₁

end Hom

end Scheme

end AlgebraicGeometry
