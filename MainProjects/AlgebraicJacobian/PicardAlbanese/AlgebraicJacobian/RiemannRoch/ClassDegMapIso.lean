/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.DegreeIsoTransport

/-!
# W7-B3: the degree is invariant along scheme isomorphisms (`classDeg_map_iso`)

For an isomorphism `e : X ≅ Y` of curve bundles over one field `K`, the degree of a Čech
Picard class is preserved by the contravariant transport `Scheme.CechPic.map e.hom.left`:

`classDeg K (CechPic.map e.hom.left L) = classDeg K L`.

This is `informal/deg-d5b-worksheet.md` §3's named Wave-7 lemma **`classDeg_map_iso`** — the
lighter sibling of E-iv-alg (`RiemannRoch/DegreeBaseFieldInvariance.lean`), built by the
same ladder with the base-field transition `π` replaced by an isomorphism, so that every
leg degenerates (`informal/w7-worksheet.md` §D2-iii, brick B-3): single-point reduction
along `picClass` generators, tracked point equations, pullback presentation — and then the
fiber is a *single* point, the coefficient is `ord` of the transported uniformizer
(`= 1` by transport of the adic multiplicity along the stalk isomorphism, no colength),
and the residue degree transports along the induced isomorphism of residue fields.

## Main declarations

* `AlgebraicGeometry.classDeg_cechPicMap_of_isIso` — the scheme-level engine: for an
  isomorphism `f : W ⟶ X` over `Spec K`, `classDeg K (CechPic.map f L) = classDeg K L`.
* `AlgebraicGeometry.classDeg_map_iso` — **the W7-B3 keystone**, the worksheet's pinned
  `Over`-category form at `e : X ≅ Y` in `Over (Spec (.of K))` with the standing curve pack.

The transport legs (adic-multiplicity/`ord` transport along the stalk isomorphism,
`residueDeg_eq_of_isIso`, `overAlgebraMap_app`, and the generic pulled tracked point
system `pointPullbackEquations` with its fiber computation) live in
`RiemannRoch/DegreeIsoTransport.lean`.

Consumers: W7-B4a (`degAt` matching through B-3 + E-iv-alg) and W7-B4b (θ); EW-3 of the
Wave-7 recon is closed by this brick.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits UniqueFactorizationMonoid IsDedekindDomain

namespace AlgebraicGeometry

/-! ## The degenerate ladder: `classDeg` invariance along an isomorphism -/

section Ladder

variable (K : Type u) [Field K] {W X : Scheme.{u}}
  [W.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (W ↘ Spec (CommRingCat.of K))] [IsIntegral W]
  [QuasiCompact (W ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-- **The pulled point divisor along an isomorphism is the single preimage point**: the
divisor of the presentation of the pulled tracked point system has `K`-degree equal to the
residue degree of `x'`. -/
private theorem deg_presentationDivisor_pointPullback_of_isIso (f : W ⟶ X) [IsIso f]
    (hover : f ≫ (X ↘ Spec (CommRingCat.of K)) = W ↘ Spec (CommRingCat.of K))
    (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) :
    Scheme.CurveDivisor.deg K (Scheme.presentationDivisor K
        (pointPullbackEquations K f hgen hx').presentation)
      = (X.residueDeg K x' : ℤ) := by
  have hcoe : ⇑(Scheme.homeoOfIso (asIso f)) = ⇑f.base := by
    rw [Scheme.coe_homeoOfIso, asIso_hom]
  have hinj : Function.Injective f.base := by
    have h := (Scheme.homeoOfIso (asIso f)).injective
    rwa [hcoe] at h
  set z₀ : W := (Scheme.homeoOfIso (asIso f)).symm x' with hz₀def
  have hfz₀ : f.base z₀ = x' := by
    have h := (Scheme.homeoOfIso (asIso f)).apply_symm_apply x'
    rwa [hcoe] at h
  have hz₀ : z₀ ≠ genericPoint W := fun h => hx' (by rw [← hfz₀, h, hgen])
  have hcoeff : ∀ (z : W) (hz : z ≠ genericPoint W),
      coeffAt hz (Scheme.presentationDivisor K
          (pointPullbackEquations K f hgen hx').presentation)
        = Multiplicative.toAdd (Scheme.ordZ (W ↘ Spec (CommRingCat.of K)) hz
            ((pointPullbackEquations K f hgen hx').presentation.elem z)) :=
    fun z hz => Scheme.coeffAt_presentationDivisor K _ hz
  have hzero : ∀ (z : W) (hz : z ≠ genericPoint W), z ≠ z₀ →
      coeffAt hz (Scheme.presentationDivisor K
        (pointPullbackEquations K f hgen hx').presentation) = 0 := by
    intro z hz hne
    have hfne : f.base z ≠ x' := fun h => hne (hinj (by rw [h, hfz₀]))
    rw [hcoeff z hz, pointPullbackEquations_presentation_elem_of_ne K f hgen hx' hfne,
      map_one, toAdd_one]
  have hc1 : Multiplicative.toAdd (Scheme.ordZ (W ↘ Spec (CommRingCat.of K)) hz₀
      ((pointPullbackEquations K f hgen hx').presentation.elem z₀)) = 1 := by
    rw [pointPullbackEquations_presentation_elem_of_eq K f hgen hx' hfz₀,
      ordZ_pointPullbackUnit K f hgen hz₀ hx' hfz₀, toAdd_ofAdd]
  have hD : Scheme.presentationDivisor K
      (pointPullbackEquations K f hgen hx').presentation
      = Scheme.CurveDivisor.single hz₀ 1 := by
    refine Scheme.CurveDivisor.ext_coeffAt fun z hz => ?_
    by_cases hzz : z = z₀
    · subst hzz
      rw [hcoeff z₀ hz, hc1]
      exact (Scheme.CurveDivisor.coeffAt_single_self hz₀ 1).symm
    · rw [hzero z hz hzz]
      exact (Scheme.CurveDivisor.coeffAt_single_of_ne hz₀ hz hzz 1).symm
  rw [hD, Scheme.CurveDivisor.deg_single' K hz₀ 1, one_mul,
    residueDeg_eq_of_isIso K f hover z₀, hfz₀]

variable [Module.Finite K (Sheaf.HModule (W.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (W.moduleKSheaf K) 1)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- The single-point case: an isomorphism preserves the degree of the class of a one-point
divisor. -/
private theorem classDeg_cechPicMap_picClass_single_of_isIso (f : W ⟶ X) [IsIso f]
    (hover : f ≫ (X ↘ Spec (CommRingCat.of K)) = W ↘ Spec (CommRingCat.of K))
    (hgen : f.base (genericPoint W) = genericPoint X)
    {x' : X} (hx' : x' ≠ genericPoint X) :
    classDeg K (Scheme.CechPic.map f
        (Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single hx' 1)))
      = classDeg K (Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single hx' 1)) := by
  have h1 : Scheme.CechPic.map f
      (Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single hx' 1))
      = (pointPullbackEquations K f hgen hx').picClass := by
    rw [Scheme.CurveDivisor.picClass_single K hx']
    exact (Scheme.LocalEquations.picClass_pullback _ _ _).symm
  have h2 : (pointPullbackEquations K f hgen hx').picClass
      = Scheme.CurveDivisor.picClass K (Scheme.presentationDivisor K
          (pointPullbackEquations K f hgen hx').presentation) := by
    rw [Scheme.CurveDivisor.picClass_presentationDivisor,
      Scheme.LocalEquations.presentation_picClass]
  rw [h1, h2, classDeg_picClass, classDeg_picClass,
    deg_presentationDivisor_pointPullback_of_isIso K f hover hgen hx',
    Scheme.CurveDivisor.deg_single' K hx' 1, one_mul]

/-- **W7-B3, scheme-level engine**: the degree of a Čech Picard class is invariant under
`CechPic.map` of an isomorphism of curve bundles over `Spec K` — for every isomorphism
`f : W ⟶ X` over `Spec K` and every class `L` on `X`,

`classDeg K (CechPic.map f L) = classDeg K L`.

The E-iv-alg ladder with the transition replaced by an isomorphism: reduce along the
surjective additive class map `CurveDivisor.picClass K` to one-point divisors, present the
point class by the tracked point equations, pull the presentation back along `f`, and close
with the degenerate fiber computation (single fiber point, coefficient `1` by `ord`
transport along the stalk isomorphism, residue degree transported along the residue-field
isomorphism). -/
theorem classDeg_cechPicMap_of_isIso (f : W ⟶ X) [IsIso f]
    (hover : f ≫ (X ↘ Spec (CommRingCat.of K)) = W ↘ Spec (CommRingCat.of K))
    (L : X.CechPic) :
    classDeg K (Scheme.CechPic.map f L) = classDeg K L := by
  have hgen : f.base (genericPoint W) = genericPoint X := genericPoint_eq_of_surjective f
  obtain ⟨D, rfl⟩ := Scheme.CurveDivisor.exists_picClass_eq K L
  suffices h : ∀ g : {p : X // p ≠ genericPoint X} →₀ ℤ,
      classDeg K (Scheme.CechPic.map f (Scheme.CurveDivisor.picClass K g))
        = classDeg K (Scheme.CurveDivisor.picClass K g) from h D
  intro g
  induction g using Finsupp.induction with
  | zero =>
    change classDeg K (Scheme.CechPic.map f
      (Scheme.CurveDivisor.picClass K (0 : X.CurveDivisor)))
      = classDeg K (Scheme.CurveDivisor.picClass K (0 : X.CurveDivisor))
    rw [Scheme.CurveDivisor.picClass_zero, map_one, classDeg_one, classDeg_one]
  | single_add p b g hpg hb ih =>
    have key : ∀ D : X.CurveDivisor,
        classDeg K (Scheme.CechPic.map f (Scheme.CurveDivisor.picClass K D))
          = classDeg K (Scheme.CurveDivisor.picClass K D) →
        classDeg K (Scheme.CechPic.map f
          (Scheme.CurveDivisor.picClass K (Scheme.CurveDivisor.single p.2 b + D)))
          = classDeg K (Scheme.CurveDivisor.picClass K
            (Scheme.CurveDivisor.single p.2 b + D)) := by
      intro D hD
      rw [Scheme.CurveDivisor.picClass_add, ← Scheme.picClass_single_zpow K p.2 b,
        map_mul, map_zpow, classDeg_mul, classDeg_mul, classDeg_zpow, classDeg_zpow, hD,
        classDeg_cechPicMap_picClass_single_of_isIso K f hover hgen p.2]
    exact key g ih

end Ladder

/-! ## The keystone: the `Over`-category form -/

section Keystone

open Scheme

/-- **W7-B3 keystone (`classDeg_map_iso`)** — the `deg-d5b` worksheet §3's named Wave-7
lemma, in the pinned `Over`-category form (`informal/w7-worksheet.md` §D2 B-3): for an
isomorphism `e : X ≅ Y` of curve bundles over one field `K` and every Čech Picard class
`L` of `Y`, the contravariant transport preserves the degree,

`classDeg K (CechPic.map e.hom.left L) = classDeg K L`.

Consumed by W7-B4a (`degAt` matching) and W7-B4b (θ); closes EW-3. -/
theorem classDeg_map_iso {K : Type u} [Field K] {X Y : Over (Spec (CommRingCat.of K))}
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] [GeometricallyIrreducible X.hom]
    [SmoothOfRelativeDimension 1 Y.hom] [IsProper Y.hom] [GeometricallyIrreducible Y.hom]
    (e : X ≅ Y) (L : Y.left.CechPic) :
    letI : X.left.Over (Spec (CommRingCat.of K)) := .ofHom X.hom
    letI : Y.left.Over (Spec (CommRingCat.of K)) := .ofHom Y.hom
    haveI : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
    haveI : QuasiCompact (X.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (QuasiCompact X.hom)
    haveI : Module.Finite K (Sheaf.HModule (X.left.moduleKSheaf K) 0) :=
      moduleFinite_hModule_zero X
    haveI : Module.Finite K (Sheaf.HModule (X.left.moduleKSheaf K) 1) :=
      moduleFinite_hModule_one X
    haveI : SmoothOfRelativeDimension 1 (Y.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (SmoothOfRelativeDimension 1 Y.hom)
    haveI : QuasiCompact (Y.left ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (QuasiCompact Y.hom)
    haveI : Module.Finite K (Sheaf.HModule (Y.left.moduleKSheaf K) 0) :=
      moduleFinite_hModule_zero Y
    haveI : Module.Finite K (Sheaf.HModule (Y.left.moduleKSheaf K) 1) :=
      moduleFinite_hModule_one Y
    classDeg K (Scheme.CechPic.map e.hom.left L) = classDeg K L := by
  letI : X.left.Over (Spec (CommRingCat.of K)) := .ofHom X.hom
  letI : Y.left.Over (Spec (CommRingCat.of K)) := .ofHom Y.hom
  haveI : SmoothOfRelativeDimension 1 (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  haveI : QuasiCompact (X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact X.hom)
  haveI : Module.Finite K (Sheaf.HModule (X.left.moduleKSheaf K) 0) :=
    moduleFinite_hModule_zero X
  haveI : Module.Finite K (Sheaf.HModule (X.left.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one X
  haveI : SmoothOfRelativeDimension 1 (Y.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 Y.hom)
  haveI : QuasiCompact (Y.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  haveI : Module.Finite K (Sheaf.HModule (Y.left.moduleKSheaf K) 0) :=
    moduleFinite_hModule_zero Y
  haveI : Module.Finite K (Sheaf.HModule (Y.left.moduleKSheaf K) 1) :=
    moduleFinite_hModule_one Y
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact classDeg_cechPicMap_of_isIso K e.hom.left (Over.w e.hom) L

end Keystone

end AlgebraicGeometry
