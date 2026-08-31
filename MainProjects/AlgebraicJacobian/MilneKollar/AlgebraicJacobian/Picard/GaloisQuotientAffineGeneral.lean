/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisQuotientGlue
import AlgebraicJacobian.Picard.GaloisQuotientNonVacuity

/-!
# The Galois quotient for an arbitrary affine total space (campaign `G2`, the affine case closed)

Let `L/K` be finite Galois with group `Γ = Gal(L/K)` and let `ρ` be a semilinear `Γ`-action
(`SemilinearGalAction`) on a scheme `X` over `Spec L`.  This file proves that **whenever `X`
is affine, the Galois quotient exists** — `HasGaloisQuotient ρ`, unconditionally on anything
else, with the quotient exhibited as `Spec` of the invariants of the section ring.

## What this changes about the `G2` gate

`Picard/FiniteGaloisQuotientAffine.lean` proves the quotient theorem
(`isGaloisQuotient_spec`) for the **affine model** `specSemilinearGalAction K L A`: the action
on `Spec A` coming from a `MulSemiringAction Γ A` that is `IsSemilinear K L A`.  That is a
statement about one *presentation* of an affine action, not about an arbitrary semilinear
action on an affine scheme, and the difference was load-bearing: before this file the only
declaration in the project concluding `HasGaloisQuotient` was
`hasGaloisQuotient_specF4` (`Picard/GaloisQuotientNonVacuity.lean`), a non-vacuity witness at
one explicit `𝔽₄/𝔽₂` action. The gate had **no general producer**.

It has one now, on the affine locus. `hasGaloisQuotient_of_isAffine` below is a global
`instance`: for `[IsAffine X]` the gate synthesizes with no further input.

## The two steps, and why the second is generic

* `isGaloisQuotient_congr` — **`IsGaloisQuotient` transports along an equivariant isomorphism
  over `Spec L`.**  No geometry: the three clauses of `IsGaloisQuotient` are a triangle over
  `Spec L`, an equivariance square, and a universal property, and each moves across an
  isomorphism by `pullback` bookkeeping alone.  Equivariance of `e` is genuinely used — it is
  what clause 2 is transported *by* (measured: dropping `he` leaves clause 2 unprovable).
* `hasGaloisQuotient_of_isAffine` — the affine case.  `⊤` is a `Γ`-stable open of any `X`, so
  `Picard/GaloisQuotientGlue.lean`'s layer-1 substrate applies at `U = ⊤`: `Γ(X, ⊤)` carries
  the semilinear section action (`sectionsMulSemiringAction`, `isSemilinear_sections`), which
  is exactly the affine model's input format.  Then `X.isoSpec : X ≅ Spec Γ(X, ⊤)` is
  equivariant for `ρ` against that model — from mathlib's `Scheme.isoSpec_hom_naturality`,
  the action's own section transport being `appTop` up to the identity restriction — and lies
  over `Spec L`.  Transport `isGaloisQuotient_spec` across it.

## Scope — what is *not* closed

This is the **affine** case of `G2(c)`, not `G2(c)`.  The gluing construction that
`Picard/GaloisQuotientGlue.lean`'s opening audit lays out in four layers remains open for a
**non-affine** `X`: the orbit hypothesis `OrbitsInAffineOpen` gives a stable affine cover
(`hasStableAffineCover_of_orbitsInAffineOpen`), each chart now has a quotient by this file,
and what is still missing is the `Scheme.GlueData` assembling them (layers 2–4: quotient
localization along invariant basic opens, the overlap isomorphisms, the glued base-change
isomorphism and `T`-points).  The Hironaka trap recorded in
`Picard/FiniteGaloisQuotient.lean` is untouched and still bites there: nothing below weakens
it, because an affine `X` has no room for it (`instOrbitsInAffineOpen_of_isAffine`).

Nor does this touch the seam: `Scheme.fgaPicardRepresentability` is unchanged, and no
antecedent of it is witnessed for any curve here.  The campaign consumer `J'_r` of `G2` is a
*glued* scheme, so it is precisely the non-affine case that the Picard route needs.

**And the sharpest limit, measured rather than inferred: the gate has ZERO binder sites.**
`grep -rn '\[HasGaloisQuotient' --include=*.lean AlgebraicJacobian/` returns nothing, and so
does a search for `HasGaloisQuotient.exists_quotient`; all 23 occurrences of the name are the
class, its two producers, and prose.  So "the gate is no longer inert" is a statement about the
*class*, not about the reachability of any theorem — nothing gets un-blocked today, because the
assembly step that would consume it is not yet a declaration.  What the affine case actually
buys is that the class has a general producer instead of a single-object witness, and that the
glue layers may quote a per-chart quotient instead of re-deriving one.  A reader pricing
distance to the headline should count this as removing a future obstacle, not as unblocking a
present one.

Campaign reference: `G2` of `informal/pic-representability-campaign.md`.  Sources: SGA I V.1.8,
Mumford *Abelian Varieties* §7, Milne *Jacobian Varieties* §4; the affine heart is Speiser's
theorem (`GaloisDescent.SemilinearAction.descentAlgEquiv`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicJacobian.GaloisDescent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-! ## §1. Transport along an equivariant isomorphism -/

/-- **`IsGaloisQuotient` is invariant under an equivariant isomorphism of the acted scheme.**

If `e : X ≅ X'` is a morphism over `Spec L` (`hef`) intertwining the two semilinear actions
(`he`), then `(Y, g)` is a Galois quotient of `(X', ρ')` iff it is one of `(X, ρ)`; this is the
direction that is used.

Nothing here is about schemes over a field beyond the shape of `IsGaloisQuotient`: clause 1 is
a triangle, clause 2 the equivariance square (this is where `he` is spent), and clause 3 the
universal property, which transports by composing the test morphism with `e.hom` in one
direction and `e.inv` in the other. -/
theorem isGaloisQuotient_congr {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    {f' : X' ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) (ρ' : SemilinearGalAction K L X' f')
    (e : X ≅ X') (hef : e.hom ≫ f' = f) (he : ρ.IsEquivariant ρ' e.hom)
    {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}
    (h : IsGaloisQuotient ρ' g) : IsGaloisQuotient ρ g := by
  obtain ⟨d, hover, hequiv, huniv⟩ := h
  refine ⟨d ≪≫ e.symm, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, ← hef, Iso.symm_hom,
      Iso.inv_hom_id_assoc, hover]
  · intro γ
    have hinv : e.inv ≫ (ρ.act γ).hom = (ρ'.act γ).hom ≫ e.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← he γ, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    change _ ≫ d.hom ≫ e.inv = (d.hom ≫ e.inv) ≫ _
    rw [← Category.assoc, hequiv γ, Category.assoc, Category.assoc, hinv]
  · intro T t hh hover' hequiv'
    obtain ⟨u, hu, hu2⟩ := huniv T t (hh ≫ e.hom)
      (by rw [Category.assoc, hef, hover'])
      (by
        intro γ
        rw [← Category.assoc, hequiv' γ, Category.assoc, he γ, Category.assoc])
    refine ⟨u, ?_, fun v hv => hu2 v ?_⟩
    · change _ ≫ d.hom ≫ e.inv = hh
      rw [← Category.assoc, hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change _ ≫ d.hom = hh ≫ e.hom
      have hv' : pullbackBaseChange K L g t v.1 v.2 ≫ d.hom ≫ e.inv = hh := hv
      rw [← Category.assoc] at hv'
      rw [← hv', Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ## §2. The affine case of the `G2` gate -/

/-- **The Galois quotient exists for every semilinear action on an affine scheme**, with
`Spec (Γ(X, ⊤)^Γ) ⟶ Spec K` as the quotient.

The route: `⊤` is `Γ`-stable, so the layer-1 substrate of
`Picard/GaloisQuotientGlue.lean` equips `Γ(X, ⊤)` with a semilinear `Γ`-action by ring
automorphisms over the `L`-algebra structure coming from `f` — the affine model's input format
— and `X.isoSpec` is then an equivariant isomorphism over `Spec L` from `ρ` to that model, so
`isGaloisQuotient_spec` transports by §1.

Note the shape of the equivariance step: the section transport `ρ.actApp hU γ` of the action is
`(ρ.act γ).hom.appTop` composed with an identity restriction map, so mathlib's
`Scheme.isoSpec_hom_naturality` supplies the square directly. -/
theorem exists_isGaloisQuotient_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {f : X ⟶ Spec (CommRingCat.of L)} (ρ : SemilinearGalAction K L X f)
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of K)), IsGaloisQuotient ρ g := by
  have hU : ρ.IsStableOpen ⊤ := fun _ => rfl
  letI := ρ.sectionsMulSemiringAction hU
  letI := SemilinearGalAction.sectionsAlgebra f (⊤ : X.Opens)
  letI := SemilinearGalAction.sectionsAlgebraK (K := K) f (⊤ : X.Opens)
  haveI := SemilinearGalAction.sections_isScalarTower (K := K) f (⊤ : X.Opens)
  haveI := ρ.isSemilinear_sections hU
  refine ⟨Spec (CommRingCat.of
      (SemilinearAction.invariantsSubalgebra K L (Γ(X, ⊤) : Type u))),
    Spec.map (CommRingCat.ofHom (algebraMap K
      (SemilinearAction.invariantsSubalgebra K L (Γ(X, ⊤) : Type u)))), ?_⟩
  -- the affine model at `A = Γ(X, ⊤)` has a quotient (Speiser descent)
  have hmodel := isGaloisQuotient_spec K L (Γ(X, ⊤) : Type u)
  -- `X.isoSpec` is equivariant for `ρ` against that model
  have hequiv : ρ.IsEquivariant (specSemilinearGalAction K L (Γ(X, ⊤) : Type u))
      X.isoSpec.hom := by
    intro γ
    rw [specSemilinearGalAction_act, toSpecAut_hom]
    have happ : CommRingCat.ofHom
        (MulSemiringAction.toRingHom Gal(L/K) (Γ(X, ⊤) : Type u) γ⁻¹)
        = (ρ.act γ).hom.appTop := by
      refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
      change (ρ.actApp hU (γ⁻¹)⁻¹).hom s = _
      rw [inv_inv]
      simp [SemilinearGalAction.actApp, Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [happ]
    exact (Scheme.isoSpec_hom_naturality (ρ.act γ).hom).symm
  -- and it lies over `Spec L`
  have hover : X.isoSpec.hom
      ≫ Spec.map (CommRingCat.ofHom (algebraMap L (Γ(X, ⊤) : Type u))) = f := by
    suffices h : X.isoSpec.hom ≫ Spec.map (Scheme.Hom.app f ⊤)
        ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv = f by
      simpa [SemilinearGalAction.sectionsAlgebraMapHom, Scheme.Hom.appLE,
        RingHom.algebraMap_toAlgebra] using h
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality f]
    simp
  exact isGaloisQuotient_congr ρ (specSemilinearGalAction K L (Γ(X, ⊤) : Type u))
    X.isoSpec hover hequiv hmodel

/-- **The `G2` gate, discharged on the affine locus** — a global `instance`, so
`HasGaloisQuotient ρ` synthesizes for any semilinear action on an affine scheme.

Before this, the gate's only inhabitant in the project was the single-`𝔽₄` witness
`hasGaloisQuotient_specF4`. This instance subsumes it **from any file that imports this
module** — measured, `inferInstance` closes that goal here — but *not at its own site*, which
imports only up to `StableAffineCover`; this module imports that one, so the reverse is a
cycle. It is therefore a generalisation, not a deletion, and that witness remains the producer
where it stands.

**The orbit-in-affine binder of the class costs the consumer nothing here, and that needed
an import to be true rather than merely plausible.** It is discharged by
`instOrbitsInAffineOpen_of_isAffine` (`Picard/GaloisQuotientNonVacuity.lean`) — `⊤` is an
affine open containing every orbit. That module is imported *for this reason*: measured on a
first version of this file which imported only `GaloisQuotientGlue`, the name did not resolve
(`unknown identifier`) and `inferInstance` for the orbit hypothesis **failed**, so the
sentence claiming the binder was free was false at the file that made it. With the import, the
instance below needs no orbit argument and consumers synthesize it from `[IsAffine X]` alone.

This does **not** discharge `G2(c)`: the campaign consumer `J'_r` is glued, hence non-affine,
and the Hironaka trap is exactly about that case (module docstring). -/
instance hasGaloisQuotient_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {f : X ⟶ Spec (CommRingCat.of L)} (ρ : SemilinearGalAction K L X f)
    [FiniteDimensional K L] [IsGalois K L] :
    HasGaloisQuotient ρ :=
  ⟨exists_isGaloisQuotient_of_isAffine ρ⟩

end AlgebraicJacobian.GaloisDescent
