/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffTransport
import AlgebraicJacobian.Picard.RelPicCurveMap

/-!
# Functoriality of the étale plus construction in the curve

For a morphism of curve bundles `g : D ⟶ E` over `Spec k`, transport of relative Picard
classes along `g ▷ T` (the landed `relPicMapCurveApp`) descends through the étale plus
construction over the literally shared cover index: this file instantiates the
parameterized transport core (`Picard/PicEtAffTransport.lean`) at the whisker family
`fun B => (g ▷ overSpec k B).left` and packages the result as the curve-direction
functoriality of `PicEtAff`.

* `AlgebraicGeometry.curveTransportFamily g`: the whisker transport family.  Its `hom`
  field is stated for two a priori unrelated `k`-algebra structures on the test algebra
  (the scalar towers of the core's index force them to agree), so it is spelled as the
  underlying `pullback.map` of the whisker; at a shared instance it is definitionally
  `(g ▷ overSpec k B).left` (`curveTransportFamily_hom`), and the induced relative
  Picard transport is definitionally `relPicMapCurveApp`
  (`curveTransportFamily_relPicHom`).
* `AlgebraicGeometry.PicEtAff.curveMap g A : PicEtAff E A →* PicEtAff D A`: the induced
  homomorphism of étale-plus Picard groups, with the computation rule `curveMap_mk`
  (descent-class representatives transport by `relPicMapCurveApp` on the same cover),
  the `mk`-equality transport `curveMap_mk_eq_mk`, the functor laws
  `curveMap_id`/`curveMap_comp`, naturality of the unit (`curveMap_unit`), and the
  bilateral restriction squares `map_curveMap`/`mapAlg_curveMap`.

The étale-limit layer (`picEt`) consumes this interface through `curveMap_mk`,
`curveMap_unit` and the `mapAlg` square; nothing here unfolds the plus setoid beyond the
landed `mk`/`ind`/`mk_eq_mk_iff` API.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {D E F : Over (Spec (.of k))}

/-- Two `k`-algebra structures on the same ring sitting in a scalar tower over the
identity algebra `Algebra.id k` are equal — the seam that collapses the transport core's
two-sided instance index at the diagonal `kD = kE = kT = k`. -/
private lemma algebra_eq_of_tower {B : Type u} [CommRing B] (iT iD : Algebra k B)
    (tw : @IsScalarTower k k B (Algebra.id k).toSMul iT.toSMul iD.toSMul) :
    iD = iT := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  rw [@IsScalarTower.algebraMap_eq k k B _ _ _ (Algebra.id k) iT iD tw]
  rfl

/-- The whisker transport family of a curve morphism `g : D ⟶ E`: at every test algebra
`B`, pullback of Čech classes along `(g ▷ overSpec k B).left`.  The `hom` field is
stated across the two instance slots of the transport core's index; the scalar towers
collapse them (`algebra_eq_of_tower`), and at a shared instance the field is
definitionally the whisker itself (`curveTransportFamily_hom`). -/
noncomputable def curveTransportFamily (g : D ⟶ E) : RelPicTransportFamily k D E where
  hom B _ iD iE iT twD twE := by
    obtain rfl : iE = iD :=
      (algebra_eq_of_tower iT iE twE).trans (algebra_eq_of_tower iT iD twD).symm
    obtain rfl : iE = iT := algebra_eq_of_tower iT iE twE
    exact (g ▷ overSpec k B).left
  hom_snd B _ iD iE iT twD twE := by
    obtain rfl : iE = iD :=
      (algebra_eq_of_tower iT iE twE).trans (algebra_eq_of_tower iT iD twD).symm
    obtain rfl : iE = iT := algebra_eq_of_tower iT iE twE
    change (g ▷ overSpec k B).left ≫ (snd E (overSpec k B)).left
      = (snd D (overSpec k B)).left
    rw [← Over.comp_left, whiskerRight_snd]
  hom_naturality B B' _ iDB iEB iTB twDB twEB _ iDB' iEB' iTB' twDB' twEB' fD fE hf := by
    obtain rfl : iEB = iDB :=
      (algebra_eq_of_tower iTB iEB twEB).trans (algebra_eq_of_tower iTB iDB twDB).symm
    obtain rfl : iEB = iTB := algebra_eq_of_tower iTB iEB twEB
    obtain rfl : iEB' = iDB' :=
      (algebra_eq_of_tower iTB' iEB' twEB').trans
        (algebra_eq_of_tower iTB' iDB' twDB').symm
    obtain rfl : iEB' = iTB' := algebra_eq_of_tower iTB' iEB' twEB'
    obtain rfl : fD = fE := AlgHom.ext hf
    change (g ▷ overSpec k B').left ≫ (E ◁ Over.overSpecMap fD).left
      = (D ◁ Over.overSpecMap fD).left ≫ (g ▷ overSpec k B).left
    rw [← Over.comp_left, ← Over.comp_left, whisker_exchange]

/-- At a shared `k`-algebra instance, the whisker family is the whisker. -/
lemma curveTransportFamily_hom (g : D ⟶ E) (B : Type u) [CommRing B] [Algebra k B] :
    (curveTransportFamily g).hom B = (g ▷ overSpec k B).left :=
  rfl

/-- At a shared `k`-algebra instance, the relative Picard transport induced by the
whisker family is the landed curve-direction transport `relPicMapCurveApp`. -/
lemma curveTransportFamily_relPicHom (g : D ⟶ E) (B : Type u) [CommRing B]
    [Algebra k B] :
    (curveTransportFamily g).relPicHom B = relPicMapCurveApp g (overSpec k B) :=
  rfl

namespace PicEtAff

variable (A : Type u) [CommRing A] [Algebra k A]

noncomputable section

/-- **Functoriality of the étale plus construction in the curve**: a morphism of curve
bundles `g : D ⟶ E` over `Spec k` induces a homomorphism of étale-plus Picard groups
`PicEtAff E A →* PicEtAff D A` at every affine test, over the literally shared étale
cover index — descent-class representatives transport by `relPicMapCurveApp` on the same
cover. -/
def curveMap (g : D ⟶ E) : PicEtAff E A →* PicEtAff D A :=
  (curveTransportFamily g).picEtAffHom A

variable {A}

/-- The computation rule of `curveMap`: representatives transport cover-by-cover. -/
@[simp]
theorem curveMap_mk (g : D ⟶ E) (U : Algebra.EtaleCover A) (x : descentClasses E U) :
    curveMap A g (mk E U x) = mk D U ((curveTransportFamily g).descentHom U x) :=
  rfl

/-- The descent-class transport of the whisker family is `relPicMapCurveApp` on the
underlying relative Picard classes. -/
@[simp]
theorem curveTransportFamily_descentHom_coe (g : D ⟶ E) (U : Algebra.EtaleCover A)
    (x : descentClasses E U) :
    (((curveTransportFamily g).descentHom U x) : relPic D (overSpec k U.Carrier))
      = relPicMapCurveApp g (overSpec k U.Carrier)
          (x : relPic E (overSpec k U.Carrier)) :=
  rfl

/-- `curveMap` transports `mk`-equalities: representatives identified in the plus of `E`
stay identified after curve transport — the plus-level face of `descentHom_descentMap`. -/
theorem curveMap_mk_eq_mk (g : D ⟶ E) {U V : Algebra.EtaleCover A}
    {x : descentClasses E U} {y : descentClasses E V} (h : mk E U x = mk E V y) :
    mk D U ((curveTransportFamily g).descentHom U x)
      = mk D V ((curveTransportFamily g).descentHom V y) := by
  rw [← curveMap_mk, ← curveMap_mk, h]

/-- The identity curve morphism induces the identity transport. -/
theorem curveMap_id (a : PicEtAff E A) : curveMap A (𝟙 E) a = a := by
  induction a using ind with | _ U x =>
  rw [curveMap_mk]
  refine congrArg (mk E U) (Subtype.ext ?_)
  rw [curveTransportFamily_descentHom_coe]
  exact relPicMapCurveApp_id _ _

/-- A composite of curve morphisms induces the composite transport, contravariantly. -/
theorem curveMap_comp (g : D ⟶ E) (g' : E ⟶ F) (a : PicEtAff F A) :
    curveMap A (g ≫ g') a = curveMap A g (curveMap A g' a) := by
  induction a using ind with | _ U x =>
  rw [curveMap_mk, curveMap_mk, curveMap_mk]
  refine congrArg (mk D U) (Subtype.ext ?_)
  rw [curveTransportFamily_descentHom_coe, curveTransportFamily_descentHom_coe,
    curveTransportFamily_descentHom_coe]
  exact relPicMapCurveApp_comp g g' _ _

/-- Curve transport is compatible with the unit of the plus construction: on classes
pulled back to the trivial cover it is the relative Picard curve transport. -/
theorem curveMap_unit (g : D ⟶ E) (x : relPic E (overSpec k A)) :
    curveMap A g (unit E A x) = unit D A (relPicMapCurveApp g (overSpec k A) x) :=
  (curveTransportFamily g).picEtAffHom_unit x

/-- Curve transport commutes with restriction along a base extension of affine tests
(instance form). -/
theorem map_curveMap (g : D ⟶ E) (A' : Type u) [CommRing A'] [Algebra k A']
    [Algebra A A'] [IsScalarTower k A A'] (a : PicEtAff E A) :
    curveMap A' g (map E A' a) = map D A' (curveMap A g a) :=
  (curveTransportFamily g).map_picEtAffHom a

/-- **The `mapAlg` bilateral square**: curve transport commutes with restriction along an
explicit `k`-algebra map of affine tests. -/
theorem mapAlg_curveMap (g : D ⟶ E) {A' : Type u} [CommRing A'] [Algebra k A']
    (φ : A →ₐ[k] A') (a : PicEtAff E A) :
    curveMap A' g (mapAlg E φ a) = mapAlg D φ (curveMap A g a) :=
  (curveTransportFamily g).mapAlg_picEtAffHom φ a

end

end PicEtAff

end AlgebraicGeometry
