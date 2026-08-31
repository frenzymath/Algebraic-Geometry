/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorClass

/-!
# Pullback of local-equation divisors and its Picard class

For a morphism of schemes `f : Y ⟶ X` and a local-equation system `E : X.LocalEquations`
(`AlgebraicJacobian.Picard.DivisorClass`), this file constructs the pulled-back system
`E.pullback f hreg : Y.LocalEquations`, whose equations are the `f`-pullbacks of the
equations of `E`, living on the pulled-back pointed cover `E.cover.pullback f`
(`AlgebraicJacobian.Picard.UnitsCocycle`). Its Picard class is the pullback of the class
of `E`:

`(E.pullback f hreg).picClass = CechPic.map f E.picClass`.

## The regularity side-hypothesis

The naive statement — "pull the equations back and stay a `LocalEquations`" — is **false**
without a side-condition: a nonzerodivisor can pull back to a zerodivisor along a non-flat
morphism, so the `regular` field of the target need not hold. The construction therefore
takes the regularity of the *pulled-back* equations as an explicit hypothesis `hreg`: for
every point `z` of the member `(E.cover.pullback f).opens y`, the germ of the pulled-back
equation `pullbackEqn f E y` at `z` is a nonzerodivisor. This is the primitive form of the
side-condition (option (a) of the deg-D4 recon): it is exactly what a downstream user
(e.g. presenting a graph as the pullback of a diagonal) proves from the *relative-divisor*
geometry that makes the pulled equations regular, and it is discharged pointwise. A
flatness assumption on `f` is a stronger sufficient condition; it would be a corollary of
this primitive, not the primitive itself.

## Main declarations

* `AlgebraicGeometry.Scheme.LocalEquations.pullbackEqn`: the `f`-pullback of the equation
  `E.eqn (f.base y)` to the member `(E.cover.pullback f).opens y`, via `Scheme.Hom.appLE`.
* `AlgebraicGeometry.Scheme.LocalEquations.pullback`: the pulled-back local-equation system
  on `E.cover.pullback f`, under the regularity hypothesis `hreg`.
* `AlgebraicGeometry.Scheme.LocalEquations.pullback_ratioUnit`: the transition units of the
  pulled-back system are the `f`-pullbacks (`Scheme.Hom.unitsAppLE`) of the transition units
  of `E`.
* `AlgebraicGeometry.Scheme.LocalEquations.picClass_pullback`: the Picard class of the
  pulled-back system is `CechPic.map f` applied to the class of `E`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

namespace LocalEquations

variable {X Y : Scheme.{u}}

/-! ## The pulled-back equations -/

/-- The `f`-pullback of the local equation `E.eqn (f.base y)` to the member
`(E.cover.pullback f).opens y = f ⁻¹ᵁ E.cover.opens (f.base y)` of the pulled-back pointed
cover. This is the section that the pulled-back system carries on that member. -/
noncomputable def pullbackEqn (f : Y ⟶ X) (E : X.LocalEquations) (y : Y) :
    Γ(Y, (E.cover.pullback f).opens y) :=
  (f.appLE (E.cover.opens (f.base y)) ((E.cover.pullback f).opens y) le_rfl).hom
    (E.eqn (f.base y))

/-- Restriction of a pulled-back equation to a sub-open `W ≤ (E.cover.pullback f).opens y`
is the `f`-pullback of `E.eqn (f.base y)` directly to `W`. This is the ring-level naturality
of `appLE` with restriction (`Scheme.Hom.appLE_map`), packaged for the ratio computation. -/
lemma pullbackEqn_res (f : Y ⟶ X) (E : X.LocalEquations) (y : Y) {W : Y.Opens}
    (h : W ≤ (E.cover.pullback f).opens y) :
    (Y.presheaf.map (homOfLE h).op).hom (pullbackEqn f E y)
      = (f.appLE (E.cover.opens (f.base y)) W (h.trans le_rfl)).hom (E.eqn (f.base y)) := by
  rw [pullbackEqn, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-! ## The ratio equation -/

/-- The defining ratio equation of the pulled-back system on the overlap
`(E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y'`: the two pulled-back
equations differ by the `f`-pullback (`Scheme.Hom.unitsAppLE`) of the transition unit
`E.ratioUnit (f.base y) (f.base y')`. -/
lemma pullback_ratio_eq (f : Y ⟶ X) (E : X.LocalEquations) (y y' : Y) :
    (Y.presheaf.map (homOfLE (inf_le_left :
        (E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y'
          ≤ (E.cover.pullback f).opens y)).op).hom (pullbackEqn f E y)
      = ((f.unitsAppLE (E.cover.opens (f.base y) ⊓ E.cover.opens (f.base y'))
            ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y')
            (f.le_preimage_inf inf_le_left inf_le_right)
            (E.ratioUnit (f.base y) (f.base y')))
          : Γ(Y, (E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y'))
        * (Y.presheaf.map (homOfLE (inf_le_right :
            (E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y'
              ≤ (E.cover.pullback f).opens y')).op).hom (pullbackEqn f E y') := by
  have key := congrArg
    (f.appLE (E.cover.opens (f.base y) ⊓ E.cover.opens (f.base y'))
      ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y')
      (f.le_preimage_inf inf_le_left inf_le_right)).hom
    (E.eqn_restrict_eq (f.base y) (f.base y'))
  rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at key
  rw [pullbackEqn_res, pullbackEqn_res, Scheme.Hom.coe_unitsAppLE]
  exact key

/-! ## The pulled-back local-equation system -/

/-- The pullback of a local-equation system `E` along a morphism `f : Y ⟶ X`, under the
side-hypothesis `hreg` that the pulled-back equations are regular (their germs are
nonzerodivisors at every point of their member).

The equations are the `f`-pullbacks `pullbackEqn f E y` of the equations of `E`, living on
the pulled-back pointed cover `E.cover.pullback f`. Regularity is supplied by `hreg` — it is
not automatic, since pulling a nonzerodivisor back along a non-flat morphism may produce a
zerodivisor. The overlap ratios are the `f`-pullbacks of the ratios of `E`, hence units. -/
noncomputable def pullback (f : Y ⟶ X) (E : X.LocalEquations)
    (hreg : ∀ (y z : Y) (hz : z ∈ (E.cover.pullback f).opens y),
      (Y.presheaf.germ ((E.cover.pullback f).opens y) z hz).hom (pullbackEqn f E y)
        ∈ nonZeroDivisors (Y.presheaf.stalk z)) :
    Y.LocalEquations where
  cover := E.cover.pullback f
  eqn y := pullbackEqn f E y
  regular := hreg
  ratio_isUnit y y' :=
    ⟨f.unitsAppLE (E.cover.opens (f.base y) ⊓ E.cover.opens (f.base y'))
        ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y')
        (f.le_preimage_inf inf_le_left inf_le_right)
        (E.ratioUnit (f.base y) (f.base y')),
      pullback_ratio_eq f E y y'⟩

@[simp]
lemma pullback_cover (f : Y ⟶ X) (E : X.LocalEquations) (hreg) :
    (E.pullback f hreg).cover = E.cover.pullback f :=
  rfl

@[simp]
lemma pullback_eqn (f : Y ⟶ X) (E : X.LocalEquations) (hreg) (y : Y) :
    (E.pullback f hreg).eqn y = pullbackEqn f E y :=
  rfl

/-- The transition units of the pulled-back system are the `f`-pullbacks
(`Scheme.Hom.unitsAppLE`) of the transition units of `E`. -/
lemma pullback_ratioUnit (f : Y ⟶ X) (E : X.LocalEquations) (hreg) (y y' : Y) :
    (E.pullback f hreg).ratioUnit y y'
      = f.unitsAppLE (E.cover.opens (f.base y) ⊓ E.cover.opens (f.base y'))
          ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y')
          (f.le_preimage_inf inf_le_left inf_le_right)
          (E.ratioUnit (f.base y) (f.base y')) :=
  ((E.pullback f hreg).ratioUnit_unique y y' _ (pullback_ratio_eq f E y y')).symm

/-! ## The Picard class of a pullback -/

/-- The cocycle of transition units of the pulled-back system is the `f`-pullback of the
cocycle of `E` (`Scheme.Hom.pullbackUnitsCocycle`). -/
lemma pullback_unitsCocycle (f : Y ⟶ X) (E : X.LocalEquations) (hreg) :
    (E.pullback f hreg).unitsCocycle = f.pullbackUnitsCocycle E.unitsCocycle := by
  refine unitsCocycle_ext fun y y' ↦ ?_
  calc unitsEvInf (E.pullback f hreg).unitsCocycle y y'
      = f.unitsAppLE (E.cover.opens (f.base y) ⊓ E.cover.opens (f.base y'))
          ((E.cover.pullback f).opens y ⊓ (E.cover.pullback f).opens y')
          (f.le_preimage_inf inf_le_left inf_le_right)
          (E.ratioUnit (f.base y) (f.base y')) :=
        ((E.pullback f hreg).unitsCocycle_evInf y y').trans (pullback_ratioUnit f E hreg y y')
    _ = unitsEvInf (f.pullbackUnitsCocycle E.unitsCocycle) y y' := by
        rw [Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, unitsCocycle_evInf]

/-- The Picard class of a pulled-back local-equation system is `CechPic.map f` applied to
the class of `E`: pulling back the divisor pulls back its class `𝒪(D)`. -/
@[simp]
lemma picClass_pullback (f : Y ⟶ X) (E : X.LocalEquations) (hreg) :
    (E.pullback f hreg).picClass = CechPic.map f E.picClass := by
  change CechPic.mk (E.cover.pullback f) (E.pullback f hreg).unitsCocycle.class
    = CechPic.map f (CechPic.mk E.cover E.unitsCocycle.class)
  rw [CechPic.map_mk, Scheme.Hom.pullbackUnitsH1_class]
  exact congrArg (CechPic.mk (E.cover.pullback f))
    (congrArg OneCocycle.class (pullback_unitsCocycle f E hreg))

end LocalEquations

end Scheme

end AlgebraicGeometry
