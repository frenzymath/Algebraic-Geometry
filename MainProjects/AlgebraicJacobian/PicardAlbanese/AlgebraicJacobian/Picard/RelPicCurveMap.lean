/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPicAlgebra

/-!
# Curve-transport of the relative Picard functor: pointwise laws and compatibilities

The carrier maps of the curve-direction transport live in `Picard/RelPic.lean`: for a
morphism of curve bundles `g : D ⟶ E` over `Spec k`, pullback of Čech classes along
`g ▷ T` descends to `relPicMapCurveApp g T : relPic E T →* relPic D T`, bundled as the
natural transformation `relPicMapCurve g : relPicFunctor E ⟶ relPicFunctor D` with the
strict functor laws `relPicMapCurve_id`/`relPicMapCurve_comp`.

This file completes the transport layer with the *pointwise* shapes that the étale-plus
layer (functoriality of `PicEtAff` in the curve) consumes:

* `AlgebraicGeometry.relPicMapCurveApp_id`, `AlgebraicGeometry.relPicMapCurveApp_comp`:
  the functor laws at a fixed test object.
* `AlgebraicGeometry.relPicMap_relPicMapCurveApp`: the unbundled naturality square —
  curve transport commutes with restriction along a test morphism.
* `AlgebraicGeometry.relPicAlgMap_relPicMapCurveApp`: the algebra face of the square —
  curve transport commutes with restriction along `Spec` of a `k`-algebra map, the form
  consumed over étale-cover carriers.
* `AlgebraicGeometry.relPicMapCurveApp_toUnit_comp`: a curve morphism that factors
  through the monoidal unit induces the *trivial* map of relative Picard groups — the
  pulled-back classes are pulled back from the test object, so they die in the quotient.
  This is the `picFromBase` compatibility consumed by the constant leg of the
  curve-morphism dichotomy (a morphism to a field point pulls every class into the
  base), via `cechPicMap_toUnit_whiskerRight_mem_picFromBase`.

All test-side restrictions are stated against the landed `relPicMap`/`relPicAlgMap`
interface; nothing here unfolds the quotient beyond `relPicMk`/`relPic.ind` and the
range description of `picFromBase`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {D E F : Over (Spec (.of k))}

/-! ## Pointwise functor laws -/

/-- The identity curve morphism induces the identity on relative Picard groups at every
test object: the pointwise form of `relPicMapCurve_id`. -/
theorem relPicMapCurveApp_id (T : Over (Spec (.of k))) (x : relPic E T) :
    relPicMapCurveApp (𝟙 E) T x = x := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicMapCurveApp_mk, MonoidalCategory.id_whiskerRight, Over.id_left,
      Scheme.CechPic.map_id]
    rfl

/-- A composite of curve morphisms induces the composite transport (contravariantly) at
every test object: the pointwise form of `relPicMapCurve_comp`. -/
theorem relPicMapCurveApp_comp (g : D ⟶ E) (g' : E ⟶ F) (T : Over (Spec (.of k)))
    (x : relPic F T) :
    relPicMapCurveApp (g ≫ g') T x
      = relPicMapCurveApp g T (relPicMapCurveApp g' T x) := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicMapCurveApp_mk, relPicMapCurveApp_mk, relPicMapCurveApp_mk]
    refine congrArg (relPicMk D T) ?_
    rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left,
      ← MonoidalCategory.comp_whiskerRight]

/-! ## Compatibility with test-side restriction -/

/-- Curve transport commutes with restriction along a test morphism — the unbundled form
of the naturality square of `relPicMapCurve`, by the monoidal exchange law. -/
theorem relPicMap_relPicMapCurveApp (g : D ⟶ E) {T T' : Over (Spec (.of k))}
    (t : T' ⟶ T) (x : relPic E T) :
    relPicMap D t (relPicMapCurveApp g T x)
      = relPicMapCurveApp g T' (relPicMap E t x) := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicMapCurveApp_mk, relPicMap_mk, relPicMap_mk, relPicMapCurveApp_mk]
    refine congrArg (relPicMk D T') ?_
    rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp,
      ← Scheme.CechPic.map_comp, ← Over.comp_left, ← Over.comp_left, whisker_exchange]

/-- Curve transport commutes with restriction along `Spec` of a `k`-algebra map: the
algebra face of the naturality square, in the form consumed over étale-cover carriers. -/
theorem relPicAlgMap_relPicMapCurveApp (g : D ⟶ E) {A B : Type u} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (x : relPic E (overSpec k A)) :
    relPicAlgMap D f (relPicMapCurveApp g (overSpec k A) x)
      = relPicMapCurveApp g (overSpec k B) (relPicAlgMap E f x) :=
  relPicMap_relPicMapCurveApp g (Over.overSpecMap f) x

/-! ## The constant leg: morphisms through the unit kill relative Picard classes -/

/-- Pullback of any Čech class along `toUnit D ▷ T` is pulled back from the test object:
the left unitor identifies `𝟙_ ⊗ T` with `T` over the second projection, so the whole
Picard group of `𝟙_ ⊗ T` is pulled back from `T`, and `toUnit D ▷ T` composes with the
second projection to the second projection. -/
lemma cechPicMap_toUnit_whiskerRight_mem_picFromBase (T : Over (Spec (.of k)))
    (X : ((𝟙_ (Over (Spec (.of k)))) ⊗ T).left.CechPic) :
    CechPic.map ((toUnit D ▷ T).left) X ∈ picFromBase D T := by
  have h : toUnit D ▷ T = snd D T ≫ (λ_ T).inv :=
    (Iso.eq_comp_inv _).mpr (whiskerRight_toUnit_comp_leftUnitor_hom D T)
  refine ⟨CechPic.map ((λ_ T).inv.left) X, ?_⟩
  show CechPic.map (snd D T).left (CechPic.map ((λ_ T).inv.left) X)
      = CechPic.map ((toUnit D ▷ T).left) X
  rw [← MonoidHom.comp_apply, ← Scheme.CechPic.map_comp, ← Over.comp_left, ← h]

/-- A curve morphism that factors through the monoidal unit — the scheme-theoretically
constant case — induces the trivial map of relative Picard groups: the pulled-back
classes are pulled back from the test object and die in the quotient. -/
theorem relPicMapCurveApp_toUnit_comp (e : 𝟙_ (Over (Spec (.of k))) ⟶ E)
    (T : Over (Spec (.of k))) (x : relPic E T) :
    relPicMapCurveApp (toUnit D ≫ e) T x = 1 := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicMapCurveApp_mk]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [comp_whiskerRight, Over.comp_left, Scheme.CechPic.map_comp,
      MonoidHom.comp_apply]
    exact cechPicMap_toUnit_whiskerRight_mem_picFromBase T _

end AlgebraicGeometry
