/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtCurveMap
import AlgebraicJacobian.Curve.CurveMorphismDichotomy
import AlgebraicJacobian.RiemannRoch.DegreePullback

/-!
# Curve-functoriality of the degree-zero Picard functor (W7-F6, the EV-cor layer)

For a morphism of curve bundles `g : D ⟶ E` over `Spec k`, the curve transport
`picEtPullback g` of the étale-sheafified relative Picard functor (W7-F3) restricts to
the degree-zero subfunctor: **pullback along a curve morphism preserves degree zero at
every field point**.  This is the EV-cor corollary of the E-v campaign, obtained by the
per-field-point dodge (ratified `informal/w7-ev-worksheet.md` §2.1): at each field point
`t : overSpec k K ⟶ T` the degree of the pulled-back class collapses (via
`degAt_picEtPullback`) to the degree of an affine curve transport over `K`, which is
read on a finite separable field refinement `L` of the representative's cover and
controlled **over that field `L` independently** by the curve-morphism dichotomy
(`curveHom_isFinite_or_constant`) together with EV-main
(`classDeg_cechPicMap_eq_finrank_mul`, `n · 0 = 0`) on the finite-surjective leg and
EV-const (`cechPicMap_eq_one_of_range_eq_singleton`) on the constant leg.  The
multiplier `n` is never transported across fields.

* `AlgebraicGeometry.classDeg_cechPicMap_whiskerRight_eq_zero` — the scheme-level core:
  the whisker `(g ▷ overSpec k L).left` is a morphism of curve bundles over `L`
  (`BaseChangeInstances` + `whiskerRight_snd`), and the dichotomy over `L` kills the
  degree of the pulled-back class.
* `AlgebraicGeometry.relPicDeg_relPicMapCurveApp_eq_zero` /
  `AlgebraicGeometry.PicEtAff.degAff_curveMap_eq_zero` — the corollary descended to the
  relative Picard group at a field test, then lifted through the plus construction via
  the master equality `degAff_mk` and the `relPicAlgMap` exchange square.
* `AlgebraicGeometry.pic0Pullback g T : pic0Subgroup E T →* pic0Subgroup D T` — the
  degree-zero restriction of `picEtPullback g T` (membership by EV-cor), with the
  underlying-class equation `pic0Pullback_coe`, naturality `pic0Map_pic0Pullback` in the
  test object, and the contravariant functor laws `pic0Pullback_id`/`pic0Pullback_comp`.
* `AlgebraicGeometry.pic0PullbackNat g : pic0Functor E ⟶ pic0Functor D` — **the
  CommGrpCat-level natural transformation** (the W7-F6 deliverable consumed by the
  `functor.map` packaging), with the functor laws
  `pic0PullbackNat_id`/`pic0PullbackNat_comp` and the inclusion square
  `pic0PullbackNat_inclusion`.

The `Grp (Over (Spec k))`-level packaging of `pic0PullbackNat` (the pinned probe-C
`functor.map` construction against `JacobianData`) lives in
`AlgebraicJacobian.Picard.Pic0PullbackGrp`.  All statements take explicit per-curve
hypotheses; the frozen `functor` fields of `Challenge.lean` are discharged only at DAT-J
time, by pure instantiation.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {D E F : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 D.hom] [IsProper D.hom] [GeometricallyIrreducible D.hom]
  [SmoothOfRelativeDimension 1 E.hom] [IsProper E.hom] [GeometricallyIrreducible E.hom]

noncomputable section

/-! ## The scheme-level core: the dichotomy over each field kills pulled-back degrees

At a field extension `L` of `k`, the whisker `(g ▷ overSpec k L).left` is a morphism
between the base-changed curve bundles `(D ⊗ overSpec k L).left` and
`(E ⊗ overSpec k L).left`, each proper, smooth of relative dimension one and
geometrically irreducible over `Spec L` via its second projection
(`Curve/BaseChangeInstances.lean`).  The curve-morphism dichotomy over `L` then applies:
on the finite-surjective leg EV-main gives `classDeg = n · classDeg` and `n · 0 = 0`; on
the constant leg the pulled-back class is trivial outright. -/

/-- **The EV-cor scheme-level core**: for a morphism of curve bundles `g : D ⟶ E` over
`k` and a field extension `L` of `k`, pullback of Čech Picard classes along the whisker
`(g ▷ overSpec k L).left` preserves degree zero.  The dichotomy and the degree
multiplicativity are applied over `L` itself — the per-field-point dodge; no degree data
is transported between fields. -/
theorem classDeg_cechPicMap_whiskerRight_eq_zero (g : D ⟶ E) (L : Type u) [Field L]
    [Algebra k L] (Λ : (E ⊗ overSpec k L).left.CechPic) (hΛ : classDeg L Λ = 0) :
    classDeg L (CechPic.map (g ▷ overSpec k L).left Λ) = 0 := by
  -- the whisker commutes with the second projections
  have hw : (g ▷ overSpec k L).left ≫ (snd E (overSpec k L)).left
      = (snd D (overSpec k L)).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  -- package the fibers as curve bundles over `Spec L` and the whisker as an
  -- `Over`-morphism.  The `Over (Spec (.of L))` ascription is load-bearing: the
  -- dichotomy's instance goals project `.hom` at the base `Spec (.of L)`, so the
  -- `BaseChangeInstances` transports must be keyed at that spelling (η-defeq verdict).
  let DL : Over (Spec (CommRingCat.of L)) := Over.mk (snd D (overSpec k L)).left
  let EL : Over (Spec (CommRingCat.of L)) := Over.mk (snd E (overSpec k L)).left
  haveI : IsProper DL.hom := instIsProperSndLeft D L
  haveI : SmoothOfRelativeDimension 1 DL.hom := instSmoothOfRelativeDimensionSndLeft D L
  haveI : GeometricallyIrreducible DL.hom := instGeometricallyIrreducibleSndLeft D L
  haveI : IsProper EL.hom := instIsProperSndLeft E L
  haveI : SmoothOfRelativeDimension 1 EL.hom := instSmoothOfRelativeDimensionSndLeft E L
  haveI : GeometricallyIrreducible EL.hom := instGeometricallyIrreducibleSndLeft E L
  let hOver : DL ⟶ EL := Over.homMk (g ▷ overSpec k L).left hw
  -- the dichotomy over `L`
  rcases curveHom_isFinite_or_constant hOver with ⟨hsurj, hfin⟩ | ⟨x, hx, hrange⟩
  · -- finite-surjective leg: EV-main, `n · 0 = 0`
    haveI : Surjective (g ▷ overSpec k L).left := hsurj
    haveI : IsFinite (g ▷ overSpec k L).left := hfin
    have hgen : (g ▷ overSpec k L).left.base (genericPoint (D ⊗ overSpec k L).left)
        = genericPoint (E ⊗ overSpec k L).left :=
      genericPoint_eq_of_surjective (g ▷ overSpec k L).left
    refine (classDeg_cechPicMap_eq_finrank_mul L (g ▷ overSpec k L).left hw hgen Λ).trans
      ?_
    rw [hΛ, mul_zero]
  · -- constant leg: EV-const, the pulled-back class is trivial
    haveI : IsProper hOver.left := isProper_left hOver
    haveI : QuasiCompact hOver.left := inferInstance
    haveI : IsReduced DL.left := inferInstanceAs (IsReduced (D ⊗ overSpec k L).left)
    have h1 : CechPic.map (g ▷ overSpec k L).left Λ = 1 :=
      cechPicMap_eq_one_of_range_eq_singleton _ _ hOver hx hrange Λ
    rw [h1]
    exact classDeg_one L

/-! ## Descent to the relative Picard group and the plus construction -/

/-- **EV-cor at the relative Picard level**: the curve transport `relPicMapCurveApp`
preserves relative degree zero at every field test — pulled-back relative Picard classes
of degree zero stay degree zero. -/
theorem relPicDeg_relPicMapCurveApp_eq_zero (g : D ⟶ E) {L : Type u} [Field L]
    [Algebra k L] (y : relPic E (overSpec k L)) (hy : relPicDeg L y = 0) :
    relPicDeg L (relPicMapCurveApp g (overSpec k L) y) = 0 := by
  induction y using relPic.ind with
  | mk Λ =>
    rw [relPicDeg_relPicMk] at hy
    rw [relPicMapCurveApp_mk, relPicDeg_relPicMk]
    exact classDeg_cechPicMap_whiskerRight_eq_zero g L Λ hy

/-- **EV-cor at the étale-plus level**: the affine curve transport `PicEtAff.curveMap`
preserves degree zero of plus classes.  A representative on a cover is read on a finite
separable field refinement `L` of the cover (`degAff_mk`, the master equality); the
transported representative reads on the *same* refinement through the `relPicAlgMap`
exchange square, and the relative-Picard corollary over `L` closes. -/
theorem PicEtAff.degAff_curveMap_eq_zero (g : D ⟶ E) {K : Type u} [Field K]
    [Algebra k K] (a : PicEtAff E K) (ha : PicEtAff.degAff K a = 0) :
    PicEtAff.degAff K (PicEtAff.curveMap K g a) = 0 := by
  induction a using PicEtAff.ind with
  | _ U x =>
    -- choose a finite separable field refinement of the cover and install the tower
    obtain ⟨L, _, _, _, _, ⟨j⟩⟩ := U.exists_finiteSeparableField_algHom
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- read both degrees on the refinement through the master equality
    rw [PicEtAff.degAff_mk U x L j] at ha
    rw [PicEtAff.curveMap_mk,
      PicEtAff.degAff_mk U ((curveTransportFamily g).descentHom U x) L j,
      PicEtAff.curveTransportFamily_descentHom_coe, relPicAlgMap_relPicMapCurveApp]
    exact relPicDeg_relPicMapCurveApp_eq_zero g _ ha

/-! ## The degree-zero restriction of the curve transport -/

/-- **Curve-functoriality of the degree-zero Picard functor** (W7-F6, EV-cor): the curve
transport `picEtPullback g T` restricts to the degree-zero subgroups.  Membership is the
per-field-point dodge: at a field point `t` the degree of the pulled-back class is the
degree of an affine curve transport over the point's own field (`degAt_picEtPullback`),
killed by `degAff_curveMap_eq_zero`. -/
def pic0Pullback (g : D ⟶ E) (T : Over (Spec (.of k))) :
    pic0Subgroup E T →* pic0Subgroup D T :=
  ((picEtPullback g T).comp (pic0Subgroup E T).subtype).codRestrict (pic0Subgroup D T)
    fun lam K _ _ t => by
      change degAt (picEtPullback g T (lam : picEt E T)) t = 0
      rw [degAt_picEtPullback g (lam : picEt E T) t]
      exact PicEtAff.degAff_curveMap_eq_zero g _ (lam.2 K t)

/-- The underlying étale Picard class of a pulled-back degree-zero class is the
`picEtPullback` transport — the naturality square of the subfunctor inclusion in the
curve direction, element form. -/
@[simp]
theorem pic0Pullback_coe (g : D ⟶ E) (T : Over (Spec (.of k)))
    (lam : pic0Subgroup E T) :
    (pic0Pullback g T lam : picEt D T) = picEtPullback g T (lam : picEt E T) :=
  rfl

/-- **Naturality of `pic0Pullback` in the test object**: curve transport of degree-zero
classes commutes with restriction along a morphism of test objects (elementwise from
`pic0Map_coe` and `picEtMap_picEtPullback`). -/
theorem pic0Map_pic0Pullback (g : D ⟶ E) {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (lam : pic0Subgroup E T) :
    pic0Map D f (pic0Pullback g T lam) = pic0Pullback g T' (pic0Map E f lam) :=
  Subtype.ext (picEtMap_picEtPullback g f (lam : picEt E T))

/-- The identity curve morphism pulls back degree-zero classes identically. -/
theorem pic0Pullback_id (T : Over (Spec (.of k))) (lam : pic0Subgroup E T) :
    pic0Pullback (𝟙 E) T lam = lam :=
  Subtype.ext (picEtPullback_id T (lam : picEt E T))

variable [SmoothOfRelativeDimension 1 F.hom] [IsProper F.hom]
  [GeometricallyIrreducible F.hom]

/-- A composite of curve morphisms pulls back degree-zero classes contravariantly. -/
theorem pic0Pullback_comp (g : D ⟶ E) (g' : E ⟶ F) (T : Over (Spec (.of k)))
    (lam : pic0Subgroup F T) :
    pic0Pullback (g ≫ g') T lam = pic0Pullback g T (pic0Pullback g' T lam) :=
  Subtype.ext (picEtPullback_comp g g' T (lam : picEt F T))

/-! ## The CommGrpCat-level natural transformation -/

/-- **The curve-direction transport of the degree-zero Picard functor** (the W7-F6
deliverable): a morphism of curve bundles `g : D ⟶ E` induces a natural transformation
`pic0Functor E ⟶ pic0Functor D` of `CommGrpCat`-valued functors on the test category.
This is the transformation whose `yonedaGrp`-conjugate packages the frozen
`Jacobian.functor.map` at DAT-J time. -/
def pic0PullbackNat (g : D ⟶ E) : pic0Functor E ⟶ pic0Functor D where
  app T := CommGrpCat.ofHom (pic0Pullback g T.unop)
  naturality T T' f := by
    ext lam
    exact (pic0Map_pic0Pullback g f.unop lam).symm

/-- The components of `pic0PullbackNat` are `pic0Pullback`. -/
@[simp]
lemma pic0PullbackNat_app (g : D ⟶ E) (T : (Over (Spec (.of k)))ᵒᵖ)
    (lam : pic0Subgroup E T.unop) :
    (pic0PullbackNat g).app T lam = pic0Pullback g T.unop lam :=
  rfl

/-- The identity curve morphism bundles to the identity natural transformation. -/
theorem pic0PullbackNat_id :
    pic0PullbackNat (𝟙 E) = 𝟙 (pic0Functor E) := by
  ext T lam
  exact pic0Pullback_id T.unop lam

/-- A composite of curve morphisms bundles to the composite natural transformation,
contravariantly. -/
theorem pic0PullbackNat_comp (g : D ⟶ E) (g' : E ⟶ F) :
    pic0PullbackNat (g ≫ g') = pic0PullbackNat g' ≫ pic0PullbackNat g := by
  ext T lam
  exact pic0Pullback_comp g g' T.unop lam

/-- The curve transport of degree-zero classes is compatible with the subfunctor
inclusion into the étale-sheafified relative Picard functor (W7-F3's
`picEtPullbackNat`). -/
theorem pic0PullbackNat_inclusion (g : D ⟶ E) :
    pic0PullbackNat g ≫ pic0Inclusion D = pic0Inclusion E ≫ picEtPullbackNat g := by
  ext T lam
  rfl

end

end AlgebraicGeometry
