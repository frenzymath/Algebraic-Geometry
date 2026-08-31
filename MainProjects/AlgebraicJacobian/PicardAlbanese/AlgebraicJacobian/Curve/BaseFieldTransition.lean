/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Curve.BaseChangeInstances
import AlgebraicJacobian.Picard.RelPicAlgebra

/-!
# The base-field transition square and its toolkit (gap G-D5(b), SB-1)

For a `k`-algebra map `φ : K₁ →ₐ[k] K₂` of field extensions of `k` and the challenge curve
`C : Over (Spec k)`, the **base-field transition** is the morphism

`π := (C ◁ Over.overSpecMap φ).left : (C ⊗ overSpec k K₂).left ⟶ (C ⊗ overSpec k K₁).left`.

This file provides the geometric toolkit for the E-iv-alg campaign
(`informal/deg-d5b-worksheet.md` §3–§4 SB-1): the *pasted pullback square* exhibiting `π` as
the base change of `Spec.map φ` along the second projection, obtained by cancellation of the
two landed squares `Over.isPullback_left C (overSpec k Kᵢ)` — the "base-field shuffle" enters
only as this square, never as a scheme isomorphism (worksheet D3).

## Main declarations

* `AlgebraicGeometry.Over.isPullback_whiskerLeft_left` — the general pasted square: for any
  `X : Over S` and any morphism `t : T' ⟶ T` of test objects, `(X ◁ t).left` is the base
  change of `t.left` along the second projections.  Stated for a general `t` so that Wave-7's
  `baseChangeIso` can re-instantiate it at arbitrary test objects (worksheet §3).
* `AlgebraicGeometry.isPullback_baseFieldTransition` — the transition square itself, with the
  bottom edge spelled `Spec.map (CommRingCat.ofHom φ.toRingHom)`.
* `AlgebraicGeometry.flat_specMap_algHom`, `surjective_specMap_algHom` (`Spec.map φ` is flat
  and surjective for `K₁` a field), and the transported instances
  `flat_baseFieldTransition`, `isAffineHom_baseFieldTransition`,
  `surjective_baseFieldTransition` on `π` via `MorphismProperty.of_isPullback`.
* `AlgebraicGeometry.genericPoint_eq_of_surjective` — a surjective morphism of irreducible
  schemes maps the generic point to the generic point; instantiated as
  `baseFieldTransition_genericPoint` for `π` (both ends are integral by
  `Curve.BaseChangeInstances`).
* `AlgebraicGeometry.Scheme.Hom.functionFieldMap` — the pullback of rational functions
  `K(Y) ⟶ K(X)` along a morphism hitting the generic point, as the stalk map at `η`, with the
  germ-naturality lemma `functionFieldMap_germ`, injectivity on integral schemes, and the
  induced map on units (`functionFieldMapUnits`).

The sections base change over this square is SB-2 (`Curve.TransitionSectionsBaseChange`); the
fiber-degree identity and E-iv-alg consume both.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-! ## The pasted pullback square -/

section PastedSquare

variable {S : Scheme.{u}}

/-- **The pasted square, general form** (stated for an arbitrary morphism of test objects so
that Wave-7 inherits it, worksheet §3): for `X : Over S` and `t : T' ⟶ T`, the square

```
(X ⊗ T').left --(X ◁ t).left--> (X ⊗ T).left
     |                               |
 (snd X T').left                (snd X T).left
     ↓                               ↓
   T'.left --------t.left--------> T.left
```

is a pullback: it is the cancellation (`IsPullback.of_right`) of the pasted composite of the
two landed squares `Over.isPullback_left X T'` and `Over.isPullback_left X T` along the
whisker-projection naturality `(X ◁ t) ≫ fst X T = fst X T'`. -/
theorem Over.isPullback_whiskerLeft_left (X : Over S) {T T' : Over S} (t : T' ⟶ T) :
    IsPullback ((X ◁ t).left) ((snd X T').left) ((snd X T).left) t.left := by
  refine IsPullback.of_right ?_ ?_ (Over.isPullback_left X T)
  · have h1 : (X ◁ t).left ≫ (fst X T).left = (fst X T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : t.left ≫ T.hom = T'.hom := Over.w t
    rw [h1, h2]
    exact Over.isPullback_left X T'
  · rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]

end PastedSquare

/-! ## The base-field transition square -/

section Transition

variable {k : Type u} [CommRing k] (C : Over (Spec (.of k)))
variable {K₁ K₂ : Type u} [CommRing K₁] [Algebra k K₁] [CommRing K₂] [Algebra k K₂]

/-- **The base-field transition square** (worksheet D3): for a `k`-algebra map
`φ : K₁ →ₐ[k] K₂`, the transition `π = (C ◁ Over.overSpecMap φ).left` is the base change of
`Spec.map φ` along the second projection of the `K₁`-curve:

```
(C ⊗ overSpec k K₂).left --π--> (C ⊗ overSpec k K₁).left
        |                                |
   (snd C _).left                   (snd C _).left
        ↓                                ↓
     Spec K₂ ------Spec.map φ-------> Spec K₁
```

Everything downstream (flatness, affineness, surjectivity of `π`, and SB-2's sections base
change) consumes this datum. -/
theorem isPullback_baseFieldTransition (φ : K₁ →ₐ[k] K₂) :
    IsPullback ((C ◁ Over.overSpecMap φ).left) ((snd C (overSpec k K₂)).left)
      ((snd C (overSpec k K₁)).left) (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  Over.isPullback_whiskerLeft_left C (Over.overSpecMap φ)

/-! ### Properties of `Spec.map φ` over a base field -/

/-- `Spec` of an algebra map out of a field is flat: every module over a field is flat. -/
theorem flat_specMap_algHom {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [CommRing K₂]
    [Algebra k K₂] (φ : K₁ →ₐ[k] K₂) :
    Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
  algebraize [φ.toRingHom]
  rw [show φ.toRingHom = algebraMap K₁ K₂ from rfl]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- `Spec` of an algebra map of fields is surjective: both prime spectra are one-point
spaces. -/
theorem surjective_specMap_algHom {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [CommRing K₂]
    [Nontrivial K₂] [Algebra k K₂] (φ : K₁ →ₐ[k] K₂) :
    Surjective (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  haveI : Nonempty (Spec (CommRingCat.of K₂)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K₂))
  haveI : Subsingleton (Spec (CommRingCat.of K₁)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K₁))
  inferInstance

/-! ### The properties transported to the transition

Each property is stable under base change, and the flipped transition square exhibits `π` as
the base change of `Spec.map φ`. -/

variable {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]

/-- **The transition is flat** — the hypothesis feeding the regularity (`hreg`) discharge of
the pulled point equations in E-iv-alg (worksheet §2 step 3). -/
instance flat_baseFieldTransition (φ : K₁ →ₐ[k] K₂) :
    Flat ((C ◁ Over.overSpecMap φ).left) :=
  MorphismProperty.of_isPullback (P := @Flat)
    (isPullback_baseFieldTransition C φ).flip (flat_specMap_algHom φ)

/-- **The transition is affine** — preimages of affine opens are affine, so the chart
`π ⁻¹ᵁ V'` of the fiber-degree identity is affine. -/
instance isAffineHom_baseFieldTransition (φ : K₁ →ₐ[k] K₂) :
    IsAffineHom ((C ◁ Over.overSpecMap φ).left) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_baseFieldTransition C φ).flip
    (isAffineHom_of_isAffine (Spec.map (CommRingCat.ofHom φ.toRingHom)))

/-- **The transition is surjective** — every closed point of the `K₁`-curve has a nonempty
fiber. -/
instance surjective_baseFieldTransition (φ : K₁ →ₐ[k] K₂) :
    Surjective ((C ◁ Over.overSpecMap φ).left) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_baseFieldTransition C φ).flip (surjective_specMap_algHom φ)

end Transition

/-! ## Generic points under surjective morphisms -/

/-- **A surjective morphism of irreducible schemes maps the generic point to the generic
point.** The image of `η_X` specializes to every point of the image, in particular to a
preimage-image of `η_Y`; conversely `η_Y` specializes to every point.  Antisymmetry in the
sober (`T0`) space `Y` concludes. -/
theorem genericPoint_eq_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨z, hz⟩ := f.surjective (genericPoint Y)
  have h0 : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have h1 : f.base (genericPoint X) ⤳ genericPoint Y := hz ▸ h0.map f.continuous
  have h2 : genericPoint Y ⤳ f.base (genericPoint X) :=
    (genericPoint_spec Y).specializes trivial
  exact (h1.antisymm h2).eq

section TransitionGenericPoint

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
  {K₁ K₂ : Type u} [Field K₁] [Algebra k K₁] [Field K₂] [Algebra k K₂]

omit [IsProper C.hom] in
/-- **The transition maps generic point to generic point**: both base-changed curves are
integral (`Curve.BaseChangeInstances`), and `π` is surjective. -/
theorem baseFieldTransition_genericPoint (φ : K₁ →ₐ[k] K₂) :
    ((C ◁ Over.overSpecMap φ).left).base (genericPoint ((C ⊗ overSpec k K₂).left))
      = genericPoint ((C ⊗ overSpec k K₁).left) :=
  genericPoint_eq_of_surjective ((C ◁ Over.overSpecMap φ).left)

end TransitionGenericPoint

/-! ## The function-field map -/

section FunctionField

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- **The pullback of rational functions** along a morphism hitting the generic point: the
stalk map of `f` at `η_X`, preceded by the identification of the stalks of `Y` at `η_Y` and
at `f(η_X)`.  For the base-field transition this is
`π^♯ : K(C_{K₁}) ⟶ K(C_{K₂})` (with `h := baseFieldTransition_genericPoint`). -/
noncomputable def Scheme.Hom.functionFieldMap (f : X ⟶ Y)
    (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫ f.stalkMap (genericPoint X)

/-- **Germ naturality of the function-field map**: pulling back the germ at `η` of a section
is the germ at `η` of the pulled-back section.  This is the seam through which the orders of
pulled-back local equations are computed (E-iv-alg step 4). -/
theorem Scheme.Hom.functionFieldMap_germ (f : X ⟶ Y)
    (h : f.base (genericPoint X) = genericPoint Y) (U : Y.Opens)
    (hη : genericPoint Y ∈ U) (hη' : genericPoint X ∈ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    (f.functionFieldMap h).hom ((Y.presheaf.germ U (genericPoint Y) hη).hom s)
      = (X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hη').hom ((f.app U).hom s) := by
  have hmem : f.base (genericPoint X) ∈ U := h ▸ hη
  have hgerm : (Y.presheaf.stalkCongr
        (Inseparable.of_eq h.symm)).hom.hom ((Y.presheaf.germ U (genericPoint Y) hη).hom s)
      = (Y.presheaf.germ U (f.base (genericPoint X)) hmem).hom s := by
    rw [TopCat.Presheaf.stalkCongr_hom, ← CommRingCat.comp_apply,
      Y.presheaf.germ_stalkSpecializes]
  rw [Scheme.Hom.functionFieldMap, CommRingCat.hom_comp, RingHom.comp_apply, hgerm]
  exact f.germ_stalkMap_apply U (genericPoint X) hmem s

/-- The function-field map of a morphism of integral schemes is injective (a ring
homomorphism of fields). -/
theorem Scheme.Hom.functionFieldMap_injective [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) = genericPoint Y) :
    Function.Injective (f.functionFieldMap h).hom :=
  RingHom.injective _

/-- The function-field map on units, `K(Y)ˣ →* K(X)ˣ` — the vocabulary in which the orders
of rational functions (`Scheme.ordZ`) are compared across the transition. -/
noncomputable def Scheme.Hom.functionFieldMapUnits (f : X ⟶ Y)
    (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionFieldˣ →* X.functionFieldˣ :=
  Units.map (f.functionFieldMap h).hom.toMonoidHom

@[simp]
lemma Scheme.Hom.coe_functionFieldMapUnits (f : X ⟶ Y)
    (h : f.base (genericPoint X) = genericPoint Y) (g : Y.functionFieldˣ) :
    (f.functionFieldMapUnits h g : X.functionField) = (f.functionFieldMap h).hom g :=
  rfl

end FunctionField

end AlgebraicGeometry
