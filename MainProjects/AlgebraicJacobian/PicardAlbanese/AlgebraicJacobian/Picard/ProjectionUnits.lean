/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Separatedness
import AlgebraicJacobian.Picard.RelPic

/-!
# The projection-descent equivalence for unit sections, packaged with naturality

For `C` proper, geometrically irreducible and geometrically reduced over a field `k` and
**any** test object `T` over `Spec k`, pullback of unit sections along the second
projection `pr : (C ⊗ T).left ⟶ T.left` over an **affine** open `V ⊆ T.left` is a group
isomorphism `Γ(T.left, V)ˣ ≅ Γ((C ⊗ T).left, pr⁻¹ V)ˣ` (the unit-group face of
`Over.isIso_appLE_snd`, `Picard/Separatedness.lean`). This file packages that isomorphism
as a reusable `MulEquiv` — `AlgebraicGeometry.Over.unitsSndEquiv` — together with its
naturality in **both** arguments:

* in the open `V` (restriction along `V' ≤ V`), `unitsSndEquiv_unitsRestrict` and its
  `symm` form `unitsSndEquiv_symm_unitsRestrict`;
* in the test object `T` (pullback along `g : T' ⟶ T`), `unitsSndEquiv_naturality`,
  resting on the base square `(C ◁ g).left ≫ (snd C T).left = (snd C T').left ≫ g.left`
  (`snd_left_naturality`) and its open-preimage form (`snd_left_preimage_naturality`).

## Consumer

The fppf coherence checks of the étale-separatedness assembly (brick ε1 of the Kleiman
2.5(1) assembly, `informal/c1-etale-separatedness-assembly.md`, "Refined design")
constantly (a) descend a unit on `(C ⊗ T).left` over a preimage open to a unit on
`T.left` and (b) verify identities between descended units by pulling back. The equiv and
its naturality lemmas make both operations first-class: `unitsSndEquiv.symm` is the
descent, and the naturality squares plus the uniqueness lemma
`unitsSndEquiv_symm_eq_of_unitsAppLE` let identities of descended units be checked
"upstairs" on the product.

## Main declarations

* `AlgebraicGeometry.Over.unitsSndEquiv` — the descent equivalence, with
  `unitsSndEquiv_apply` its element form.
* `unitsSndEquiv_symm_apply_eq_iff`, `unitsSndEquiv_symm_unitsAppLE`,
  `unitsAppLE_unitsSndEquiv_symm` — the `symm`/round-trip calculus.
* `unitsSndEquiv_unitsRestrict`, `unitsSndEquiv_symm_unitsRestrict` — naturality in the
  affine open.
* `snd_left_naturality`, `snd_left_preimage_naturality`, `unitsSndEquiv_naturality` —
  naturality in the test object.
* `unitsSndEquiv_symm_eq_of_unitsAppLE` — uniqueness of the descended unit.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

/-- **Morphism-congruence for `unitsAppLE`**: equal morphisms with the same source and
target opens act identically on unit sections. The proof arguments are propositions, so
only the morphism equality is data; after substituting it away the two sides are
definitionally equal. -/
theorem Scheme.Hom.unitsAppLE_congr_hom {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f')
    {V : Y.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V) (e' : U ≤ f' ⁻¹ᵁ V) (u : Γ(Y, V)ˣ) :
    f.unitsAppLE V U e u = f'.unitsAppLE V U e' u := by
  subst hf; rfl

variable {k : Type u} [Field k]

namespace Over

variable (C T : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-! ## The descent equivalence -/

/-- **The projection-descent equivalence for unit sections.** For an affine open
`V ⊆ T.left`, pullback of unit sections along the second projection
`(C ⊗ T).left ⟶ T.left` is a group isomorphism `Γ(T.left, V)ˣ ≅ Γ((C ⊗ T).left, pr⁻¹ V)ˣ`
— the `MulEquiv` packaging of `Over.unitsAppLE_snd_bijective`. Its inverse is the *descent*
of a unit on the product to a unit on the base. -/
noncomputable def unitsSndEquiv {V : T.left.Opens} (hV : IsAffineOpen V) :
    Γ(T.left, V)ˣ ≃* Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V)ˣ :=
  MulEquiv.ofBijective ((snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl)
    (unitsAppLE_snd_bijective C T hV)

@[simp]
lemma unitsSndEquiv_apply {V : T.left.Opens} (hV : IsAffineOpen V) (v : Γ(T.left, V)ˣ) :
    unitsSndEquiv C T hV v
      = (snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl v :=
  rfl

/-! ## The `symm`/round-trip calculus -/

/-- The descended unit is characterised by its pullback: `unitsSndEquiv.symm w = v` iff `v`
pulls back to `w`. This is the workhorse for checking identities of descended units on the
product. -/
lemma unitsSndEquiv_symm_apply_eq_iff {V : T.left.Opens} (hV : IsAffineOpen V)
    (w : Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V)ˣ) (v : Γ(T.left, V)ˣ) :
    (unitsSndEquiv C T hV).symm w = v
      ↔ (snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl v = w := by
  rw [MulEquiv.symm_apply_eq, unitsSndEquiv_apply, eq_comm]

/-- Round-trip: descending the pullback of `v` returns `v`. -/
@[simp]
lemma unitsSndEquiv_symm_unitsAppLE {V : T.left.Opens} (hV : IsAffineOpen V)
    (v : Γ(T.left, V)ˣ) :
    (unitsSndEquiv C T hV).symm
        ((snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl v) = v :=
  (unitsSndEquiv C T hV).symm_apply_apply v

/-- Round-trip: pulling back the descent of `w` returns `w`. -/
@[simp]
lemma unitsAppLE_unitsSndEquiv_symm {V : T.left.Opens} (hV : IsAffineOpen V)
    (w : Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V)ˣ) :
    (snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl
        ((unitsSndEquiv C T hV).symm w) = w :=
  (unitsSndEquiv C T hV).apply_symm_apply w

/-- **Uniqueness of the descended unit**: if `v` pulls back to `w`, then `v` *is* the
descent of `w`. The workhorse for "the descended unit is unique, so identities can be
checked upstairs". -/
theorem unitsSndEquiv_symm_eq_of_unitsAppLE {V : T.left.Opens} (hV : IsAffineOpen V)
    (v : Γ(T.left, V)ˣ) (w : Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V)ˣ)
    (h : (snd C T).left.unitsAppLE V ((snd C T).left ⁻¹ᵁ V) le_rfl v = w) :
    v = (unitsSndEquiv C T hV).symm w :=
  ((unitsSndEquiv_symm_apply_eq_iff C T hV w v).mpr h).symm

/-! ## Naturality in the affine open -/

/-- **Naturality of `unitsSndEquiv` in the open**: descending commutes with restriction
along `V' ≤ V` (both affine). This is `Scheme.Hom.map_unitsAppLE`/`unitsAppLE_map`
recast through the equivalence. -/
theorem unitsSndEquiv_unitsRestrict {V V' : T.left.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V) (v : Γ(T.left, V)ˣ) :
    unitsSndEquiv C T hV' (T.left.unitsRestrict h v)
      = (C ⊗ T).left.unitsRestrict ((snd C T).left.preimage_mono h)
          (unitsSndEquiv C T hV v) := by
  simp only [unitsSndEquiv_apply, Scheme.unitsRestrict, Scheme.Hom.map_unitsAppLE,
    Scheme.Hom.unitsAppLE_map]

/-- The `symm` form of `unitsSndEquiv_unitsRestrict`: descent commutes with restriction.
Cheaply derived from the forward form by applying the equivalence and using the
round-trips. -/
theorem unitsSndEquiv_symm_unitsRestrict {V V' : T.left.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V)
    (w : Γ((C ⊗ T).left, (snd C T).left ⁻¹ᵁ V)ˣ) :
    (unitsSndEquiv C T hV').symm
        ((C ⊗ T).left.unitsRestrict ((snd C T).left.preimage_mono h) w)
      = T.left.unitsRestrict h ((unitsSndEquiv C T hV).symm w) := by
  apply (unitsSndEquiv C T hV').injective
  rw [MulEquiv.apply_symm_apply, unitsSndEquiv_unitsRestrict C T hV hV' h,
    MulEquiv.apply_symm_apply]

end Over

/-! ## Naturality in the test object: the base square -/

namespace Over

variable (C : Over (Spec (.of k))) {T T' : Over (Spec (.of k))}

/-- **The base square of the second projection.** For `g : T' ⟶ T`, whiskering `C ◁ g` on
the product intertwines the projections: `(C ◁ g).left ≫ (snd C T).left =
(snd C T').left ≫ g.left`. This is `CartesianMonoidalCategory.whiskerLeft_snd` transported
through the `Over.forget` (`.left`). -/
theorem snd_left_naturality (g : T' ⟶ T) :
    (C ◁ g).left ≫ (snd C T).left = (snd C T').left ≫ g.left := by
  rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

/-- The open-preimage form of `snd_left_naturality`: the preimage of a base open under the
two legs of the base square agree. -/
theorem snd_left_preimage_naturality (g : T' ⟶ T) (V : T.left.Opens) :
    (C ◁ g).left ⁻¹ᵁ ((snd C T).left ⁻¹ᵁ V) = (snd C T').left ⁻¹ᵁ (g.left ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, snd_left_naturality, Scheme.Hom.comp_preimage]

end Over

/-! ## Naturality in the test object: the descent square -/

namespace Over

variable (C : Over (Spec (.of k)))
  [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
  {T T' : Over (Spec (.of k))}

/-- **Naturality of `unitsSndEquiv` in the test object.** For `g : T' ⟶ T` and an affine
open `V ⊆ T.left` whose preimage `g⁻¹ V ⊆ T'.left` is affine, descending `v` on `T` and
then pulling back along `C ◁ g` equals first pulling `v` back along `g` and then
descending on `T'`. Both sides are units over `(snd C T').left ⁻¹ᵁ (g.left ⁻¹ᵁ V)`; the
identification of source opens is the base square `snd_left_preimage_naturality`. -/
theorem unitsSndEquiv_naturality (g : T' ⟶ T) {V : T.left.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (g.left ⁻¹ᵁ V)) (v : Γ(T.left, V)ˣ) :
    unitsSndEquiv C T' hV' (g.left.unitsAppLE V (g.left ⁻¹ᵁ V) le_rfl v)
      = (C ◁ g).left.unitsAppLE ((snd C T).left ⁻¹ᵁ V)
          ((snd C T').left ⁻¹ᵁ (g.left ⁻¹ᵁ V))
          (le_of_eq (snd_left_preimage_naturality C g V).symm)
          (unitsSndEquiv C T hV v) := by
  simp only [unitsSndEquiv_apply]
  rw [Scheme.unitsAppLE_unitsAppLE, Scheme.unitsAppLE_unitsAppLE]
  exact Scheme.Hom.unitsAppLE_congr_hom (snd_left_naturality C g).symm _ _ v

end Over

end AlgebraicGeometry
