/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.TruncExpCech

/-!
# Iso-transport of the two-chart Čech coboundary subgroup

`TruncExpCech.cechCoboundaryUnits ρ₁ ρ₂ ≤ Bˣ` (`Tangent/TruncExpCech.lean`) is the
coboundary subgroup `im(ρ₁ˣ) · im(ρ₂ˣ)` of a two-chart datum of ring homomorphisms
`ρ₁ : A₁ →+* B`, `ρ₂ : A₂ →+* B`.  This file records that it is **natural in the datum**:
an isomorphism of two-chart data — ring isomorphisms `α₁, α₂, β` making both restriction
squares commute — carries coboundaries to coboundaries, so `Units.map β` restricts to an
isomorphism of the coboundary subgroups and descends to the Čech `Ȟ¹`-of-units quotients.

## Why this is here

The algebra-side ℙ¹ coboundary theory (`Picard/LaurentTwoChartCoboundary.lean` and the
`Algebra/Laurent*` files) characterises `laurentCoboundaryUnits A`, the coboundary subgroup
of the **abstract** two-chart datum `Polynomial.toLaurent`, `rightChart` on
`(LaurentPolynomial A)ˣ`.  A scheme consumer instead holds
`Scheme.twoChartCoboundaryUnits`, the coboundary subgroup of the **scheme** restriction homs
`X.resHom` on `Γ(X, V₀ ⊓ V₁)ˣ` (`Picard/TwoChartCechPicTrivial.lean`).  On the two charts of
a relative curve `ℙ¹_A` these two data are isomorphic once one identifies
`Γ(V₀), Γ(V₁), Γ(V₀ ⊓ V₁)` with `A[t], A[t], A[T;T⁻¹]` and the restrictions with the two
Laurent chart maps.  This file is the transport that turns *that identification of data*
into a transport of the *coboundary conclusion*, with no new hypothesis and no dependence
on the identifying isomorphisms being anything in particular.

`cechCoboundaryUnits` is a `sup` of two `Units.map`-ranges, so the whole content is the
naturality of a `Units.map`-range under a commuting square, done once here rather than
inlined at each application.

## Main declarations

* `TruncExpCech.cechCoboundaryUnits_map_le` — `Units.map β` sends `cechCoboundaryUnits ρ₁ ρ₂`
  into `cechCoboundaryUnits ρ₁' ρ₂'` when `β ∘ ρᵢ = ρᵢ' ∘ αᵢ`.
* `TruncExpCech.mem_cechCoboundaryUnits_map_iff` — membership transports both ways along a
  ring **isomorphism** `β` of the overlap rings (with `αᵢ` isomorphisms too): `u` is a
  coboundary iff `β u` is.
* `TruncExpCech.cechCoboundaryUnits_comap_unitsMapEquiv` — the subgroup pulls back exactly,
  so `Units.map β` induces an isomorphism of the two Čech `Ȟ¹`-of-units quotients
  (`cechCoboundaryUnitsQuotEquiv`).
-/

set_option autoImplicit false

universe u v w u' v' w'

namespace TruncExpCech

variable {A₁ : Type u} {A₂ : Type v} {B : Type w}
variable {A₁' : Type u'} {A₂' : Type v'} {B' : Type w'}
variable [CommRing A₁] [CommRing A₂] [CommRing B]
variable [CommRing A₁'] [CommRing A₂'] [CommRing B']

/-- **Coboundaries push forward along an isomorphism of two-chart data.**

If `β ∘ ρᵢ = ρᵢ' ∘ αᵢ` for `i = 1, 2` (the two restriction squares commute), then the
overlap-ring map `Units.map β` carries the coboundary subgroup of `(ρ₁, ρ₂)` into that of
`(ρ₁', ρ₂')`.  Only the two square identities are used — `β` and the `αᵢ` need not be
isomorphisms for this direction. -/
theorem cechCoboundaryUnits_map_le
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (ρ₁' : A₁' →+* B') (ρ₂' : A₂' →+* B')
    (α₁ : A₁ →+* A₁') (α₂ : A₂ →+* A₂') (β : B →+* B')
    (h₁ : β.comp ρ₁ = ρ₁'.comp α₁) (h₂ : β.comp ρ₂ = ρ₂'.comp α₂) :
    (cechCoboundaryUnits ρ₁ ρ₂).map (Units.map β.toMonoidHom) ≤
      cechCoboundaryUnits ρ₁' ρ₂' := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨v₁, v₂, rfl⟩ := mem_cechCoboundaryUnits.mp hu
  rw [map_mul]
  refine mem_cechCoboundaryUnits.mpr
    ⟨Units.map α₁.toMonoidHom v₁, Units.map α₂.toMonoidHom v₂, ?_⟩
  congr 1
  · ext
    have := RingHom.congr_fun h₁ (v₁ : A₁)
    simpa [Units.coe_map] using this.symm
  · ext
    have := RingHom.congr_fun h₂ (v₂ : A₂)
    simpa [Units.coe_map] using this.symm

/-- The reverse restriction square, obtained from the forward one by conjugating with the
inverse isomorphisms.  A helper for the `iff` transport. -/
private theorem comp_symm_of_comp
    {ρ : A₁ →+* B} {ρ' : A₁' →+* B'} {α : A₁ ≃+* A₁'} {β : B ≃+* B'}
    (h : (β : B →+* B').comp ρ = ρ'.comp (α : A₁ →+* A₁')) :
    (β.symm : B' →+* B).comp ρ' = ρ.comp (α.symm : A₁' →+* A₁) := by
  apply RingHom.ext; intro x
  have key := RingHom.congr_fun h (α.symm x)
  simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] at key
  change β.symm (ρ' x) = ρ (α.symm x)
  rw [← key, RingEquiv.symm_apply_apply]

/-- **Coboundary membership transports both ways along an isomorphism of two-chart data.**

When the vertical maps `α₁, α₂, β` are ring isomorphisms and both restriction squares
commute, `u : Bˣ` is a coboundary of `(ρ₁, ρ₂)` iff its image `Units.map β u` is a
coboundary of `(ρ₁', ρ₂')`.  This is the form a consumer transporting a *characterisation*
of coboundaries (e.g. the ℙ¹ Laurent theory) onto an isomorphic scheme datum uses. -/
theorem mem_cechCoboundaryUnits_map_iff
    (ρ₁ : A₁ →+* B) (ρ₂ : A₂ →+* B) (ρ₁' : A₁' →+* B') (ρ₂' : A₂' →+* B')
    (α₁ : A₁ ≃+* A₁') (α₂ : A₂ ≃+* A₂') (β : B ≃+* B')
    (h₁ : (β : B →+* B').comp ρ₁ = ρ₁'.comp (α₁ : A₁ →+* A₁'))
    (h₂ : (β : B →+* B').comp ρ₂ = ρ₂'.comp (α₂ : A₂ →+* A₂')) (u : Bˣ) :
    Units.map (β : B →+* B').toMonoidHom u ∈ cechCoboundaryUnits ρ₁' ρ₂'
      ↔ u ∈ cechCoboundaryUnits ρ₁ ρ₂ := by
  refine ⟨fun h => ?_, fun h =>
    cechCoboundaryUnits_map_le ρ₁ ρ₂ ρ₁' ρ₂' (α₁ : A₁ →+* A₁') (α₂ : A₂ →+* A₂')
      (β : B →+* B') h₁ h₂ (Subgroup.mem_map_of_mem _ h)⟩
  have hback := cechCoboundaryUnits_map_le ρ₁' ρ₂' ρ₁ ρ₂
    (α₁.symm : A₁' →+* A₁) (α₂.symm : A₂' →+* A₂) (β.symm : B' →+* B)
    (comp_symm_of_comp h₁) (comp_symm_of_comp h₂) (Subgroup.mem_map_of_mem _ h)
  have he : Units.map (β.symm : B' →+* B).toMonoidHom
      (Units.map (β : B →+* B').toMonoidHom u) = u := by ext; simp
  rwa [he] at hback

end TruncExpCech
