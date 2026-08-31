/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RefinementInjectivity
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Sections on basic opens as algebras over global sections

Mathlib equips the sections `Γ(X, X.basicOpen g)` on a basic open of a scheme `X` with a
canonical `Γ(X, ⊤)`-algebra structure (restriction; the instance
`AlgebraicGeometry.Scheme.algebra_section_section_basicOpen`), which for affine `X` is the
`Away g` localization (`AlgebraicGeometry.isLocalization_away_of_isAffine`).  This file
provides the interface the Čech–Picard dictionary uses to move between this algebra world
and the units-of-sections calculus of `AlgebraicJacobian.Picard.RefinementInjectivity`:

* `AlgebraicGeometry.Scheme.basicRes`: restriction between sections on nested basic opens
  as a `Γ(X, ⊤)`-algebra map — for affine `X` **the** map, since any two `Γ(X, ⊤)`-algebra
  maps out of `Γ(X, X.basicOpen g)` agree (`Scheme.basicOpen_algHom_ext`);
* `AlgebraicGeometry.Scheme.unitsRestrict_unitsEvInf_self`: the diagonal values `γ(x,x)` of
  a unit Čech cocycle are `1` after any restriction — the normalization feeding the
  diagonal condition of the descent cocycle.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-! ## Restriction between basic opens as an algebra map -/

/-- Restriction of sections between nested basic opens, as a map of algebras over the
global sections.  (Both algebra structures are the canonical restriction instances.) -/
def basicRes (g h : Γ(X, ⊤)) (hle : X.basicOpen h ≤ X.basicOpen g) :
    Γ(X, X.basicOpen g) →ₐ[Γ(X, ⊤)] Γ(X, X.basicOpen h) where
  toRingHom := (X.presheaf.map (homOfLE hle).op).hom
  commutes' a := by
    change (X.presheaf.map (homOfLE hle).op).hom
        ((X.presheaf.map (homOfLE le_top).op).hom a)
      = (X.presheaf.map (homOfLE le_top).op).hom a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

@[simp]
lemma basicRes_apply (g h : Γ(X, ⊤)) (hle : X.basicOpen h ≤ X.basicOpen g)
    (s : Γ(X, X.basicOpen g)) :
    basicRes g h hle s = X.presheaf.map (homOfLE hle).op s :=
  rfl

/-- The unit-level restriction between basic opens is `basicRes` on values. -/
lemma coe_unitsRestrict_basicOpen (g h : Γ(X, ⊤)) (hle : X.basicOpen h ≤ X.basicOpen g)
    (u : Γ(X, X.basicOpen g)ˣ) :
    (X.unitsRestrict hle u : Γ(X, X.basicOpen h)) = basicRes g h hle u.val :=
  rfl

/-- Any two algebra maps over the global sections out of the sections on a basic open of
an affine scheme are equal: the source is a localization of `Γ(X, ⊤)`. -/
theorem basicOpen_algHom_ext [IsAffine X] (g : Γ(X, ⊤)) {C : Type u} [CommRing C]
    [Algebra Γ(X, ⊤) C] (φ ψ : Γ(X, X.basicOpen g) →ₐ[Γ(X, ⊤)] C) : φ = ψ :=
  (IsLocalization.algHom_subsingleton (Submonoid.powers g)).elim φ ψ

/-! ## Diagonal normalization of unit cocycles -/

/-- The diagonal value `γ(x,x)` of a unit Čech cocycle on a pointed cover is `1` after
restriction to any open contained in the member at `x`. -/
theorem unitsRestrict_unitsEvInf_self {𝒰 : X.PointedCover} (γ : X.unitsCocycle 𝒰) (x : X)
    {V : X.Opens} (hV : V ≤ 𝒰.opens x) :
    X.unitsRestrict (le_inf hV hV) (unitsEvInf γ x x) = 1 := by
  have e := congrArg
    (X.unitsRestrict (le_inf (le_inf hV hV) hV :
      V ≤ 𝒰.opens x ⊓ 𝒰.opens x ⊓ 𝒰.opens x)) (unitsEvInf_trans γ x x x)
  simp only [map_mul, unitsRestrict_unitsRestrict] at e
  exact mul_left_cancel (e.trans (mul_one _).symm)

end Scheme

end AlgebraicGeometry
