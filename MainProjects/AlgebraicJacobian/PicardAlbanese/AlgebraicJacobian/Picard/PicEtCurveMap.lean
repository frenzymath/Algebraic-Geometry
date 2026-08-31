/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtAffCurveMap
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# Functoriality of the étale-sheafified relative Picard functor in the curve

For a morphism of curve bundles `g : D ⟶ E` over `Spec k`, the curve-direction
transport of the étale plus construction (`AlgebraicJacobian.Picard.PicEtAffCurveMap`)
lifts componentwise through the affine-opens limit: a compatible family of plus classes
over the affine opens of a test object transports affine-open by affine-open, and the
`mapAlg` bilateral square keeps the family compatible.

* `AlgebraicGeometry.picEtPullback g T : picEt E T →* picEt D T`: the lifted
  homomorphism, with the componentwise computation rule `picEtPullback_val` and the
  contravariant functor laws `picEtPullback_id`/`picEtPullback_comp`.
* `AlgebraicGeometry.picEtAffineEquiv_picEtPullback`: at an affine test the lift is the
  affine curve transport `PicEtAff.curveMap` under the affine comparison
  (`picEtAffineEquiv`-compatibility, with the symmetric form
  `picEtPullback_picEtAffineEquiv_symm`).
* `AlgebraicGeometry.picEtMap_picEtPullback`: **naturality in the test object** — curve
  transport commutes with restriction along an arbitrary morphism of test objects.  The
  glued value of `picEtMap` is pinned by the `IsPullbackValue` characterization, which
  the transported family satisfies through the `mapAlg` square.
* `AlgebraicGeometry.picEtPullbackNat g : picEtFunctor E ⟶ picEtFunctor D`: the
  functor-level bundling as a natural transformation of `CommGrpCat`-valued functors,
  with the functor laws `picEtPullbackNat_id`/`picEtPullbackNat_comp`.
* `AlgebraicGeometry.degAt_picEtPullback`: the degree of a pulled-back class at a field
  point of the test collapses to the degree of the affine curve transport of the
  restricted class — the reduction consumed by the degree-multiplicativity campaign
  (E-v) when the `pic0` restriction of `picEtPullbackNat` is built.

Nothing here unfolds the limit carrier beyond the componentwise interface of
`AlgebraicJacobian.Picard.PicEt`, and `picEtMap` is consumed only through its
`IsPullbackValue` characterization.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] {D E F : Over (Spec (.of k))}

noncomputable section

/-! ## The componentwise lift through the affine-opens limit -/

/-- **Functoriality of the étale-sheafified relative Picard functor in the curve**: a
morphism of curve bundles `g : D ⟶ E` over `Spec k` induces a homomorphism
`picEt E T →* picEt D T` at every test object, by transporting a compatible family of
plus classes affine-open by affine-open along the affine curve transport
`PicEtAff.curveMap`; the `mapAlg` bilateral square keeps the family compatible. -/
def picEtPullback (g : D ⟶ E) (T : Over (Spec (.of k))) : picEt E T →* picEt D T where
  toFun s := ⟨fun U => PicEtAff.curveMap Γ(T.left, U.1) g (s.1 U), fun U V h => by
    rw [← PicEtAff.mapAlg_curveMap, s.compat U V h]⟩
  map_one' := picEt.ext fun U => map_one (PicEtAff.curveMap Γ(T.left, U.1) g)
  map_mul' s t := picEt.ext fun U =>
    map_mul (PicEtAff.curveMap Γ(T.left, U.1) g) (s.1 U) (t.1 U)

/-- The componentwise computation rule of `picEtPullback`. -/
@[simp]
lemma picEtPullback_val (g : D ⟶ E) (T : Over (Spec (.of k))) (s : picEt E T)
    (U : T.left.affineOpens) :
    (picEtPullback g T s).1 U = PicEtAff.curveMap Γ(T.left, U.1) g (s.1 U) :=
  rfl

/-- The identity curve morphism pulls back to the identity. -/
theorem picEtPullback_id (T : Over (Spec (.of k))) (s : picEt E T) :
    picEtPullback (𝟙 E) T s = s :=
  picEt.ext fun U => PicEtAff.curveMap_id (s.1 U)

/-- A composite of curve morphisms pulls back to the composite transport,
contravariantly. -/
theorem picEtPullback_comp (g : D ⟶ E) (g' : E ⟶ F) (T : Over (Spec (.of k)))
    (s : picEt F T) :
    picEtPullback (g ≫ g') T s = picEtPullback g T (picEtPullback g' T s) :=
  picEt.ext fun U => PicEtAff.curveMap_comp g g' (s.1 U)

/-! ## Compatibility with the affine comparison -/

section Affine

variable {A : Type u} [CommRing A] [Algebra k A]

/-- **`picEtAffineEquiv`-compatibility**: at an affine test the componentwise lift is
the affine curve transport under the affine comparison. -/
theorem picEtAffineEquiv_picEtPullback (g : D ⟶ E) (s : picEt E (overSpec k A)) :
    picEtAffineEquiv D A (picEtPullback g (overSpec k A) s)
      = PicEtAff.curveMap A g (picEtAffineEquiv E A s) := by
  rw [picEtAffineEquiv_apply, picEtAffineEquiv_apply, picEtPullback_val,
    PicEtAff.mapAlg_curveMap]
  rfl

/-- The symmetric form of the affine compatibility: the lift of the section determined
by a plus class is the section determined by the affine curve transport. -/
theorem picEtPullback_picEtAffineEquiv_symm (g : D ⟶ E) (x : PicEtAff E A) :
    picEtPullback g (overSpec k A) ((picEtAffineEquiv E A).symm x)
      = (picEtAffineEquiv D A).symm (PicEtAff.curveMap A g x) := by
  refine (picEtAffineEquiv D A).injective ?_
  rw [MulEquiv.apply_symm_apply, picEtAffineEquiv_picEtPullback,
    MulEquiv.apply_symm_apply]

end Affine

/-! ## Naturality in the test object -/

section Naturality

variable [IsProper D.hom] [GeometricallyIrreducible D.hom] [GeometricallyReduced D.hom]
variable [IsProper E.hom] [GeometricallyIrreducible E.hom] [GeometricallyReduced E.hom]

/-- **Naturality of the curve transport in the test object**: curve transport commutes
with restriction along an arbitrary morphism of test objects.  The glued value of
`picEtMap` is pinned by its `IsPullbackValue` characterization, which the transported
family satisfies through the `mapAlg` bilateral square. -/
theorem picEtMap_picEtPullback (g : D ⟶ E) {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (s : picEt E T) :
    picEtMap D f (picEtPullback g T s) = picEtPullback g T' (picEtMap E f s) := by
  refine picEt.ext fun W => ?_
  simp only [picEtMap_val, picEtPullback_val]
  refine picEtMapVal_eq_of D f (picEtPullback g T s) ?_
  intro W₀ hW₀ V hV
  rw [picEtPullback_val, ← PicEtAff.mapAlg_curveMap,
    picEtMapVal_spec E f s W W₀ hW₀ V hV, PicEtAff.mapAlg_curveMap]

/-! ## The functor-level bundling -/

/-- **The curve-direction transport of the étale-sheafified relative Picard functor**,
bundled as a natural transformation of `CommGrpCat`-valued functors on the test
category. -/
def picEtPullbackNat (g : D ⟶ E) : picEtFunctor E ⟶ picEtFunctor D where
  app T := CommGrpCat.ofHom (picEtPullback g T.unop)
  naturality T T' f := by
    ext s
    exact (picEtMap_picEtPullback g f.unop s).symm

/-- The components of `picEtPullbackNat` are `picEtPullback`. -/
@[simp]
lemma picEtPullbackNat_app (g : D ⟶ E) (T : (Over (Spec (.of k)))ᵒᵖ)
    (s : picEt E T.unop) :
    (picEtPullbackNat g).app T s = picEtPullback g T.unop s :=
  rfl

/-- The identity curve morphism bundles to the identity natural transformation. -/
theorem picEtPullbackNat_id :
    picEtPullbackNat (𝟙 E) = 𝟙 (picEtFunctor E) := by
  ext T s
  exact picEtPullback_id T.unop s

variable [IsProper F.hom] [GeometricallyIrreducible F.hom] [GeometricallyReduced F.hom]

/-- A composite of curve morphisms bundles to the composite natural transformation,
contravariantly. -/
theorem picEtPullbackNat_comp (g : D ⟶ E) (g' : E ⟶ F) :
    picEtPullbackNat (g ≫ g') = picEtPullbackNat g' ≫ picEtPullbackNat g := by
  ext T s
  exact picEtPullback_comp g g' T.unop s

end Naturality

/-! ## The degree reduction at field points -/

/-- **The degree of a pulled-back class at a field point** collapses to the degree of
the affine curve transport of the restricted class: restriction to the field point
commutes with the curve transport (naturality), and at the affine test the transport is
`PicEtAff.curveMap` (affine compatibility).  This is the reduction through which the
degree-multiplicativity campaign (E-v) controls the `pic0`-membership of pulled-back
degree-zero classes. -/
theorem degAt_picEtPullback [SmoothOfRelativeDimension 1 D.hom] [IsProper D.hom]
    [GeometricallyIrreducible D.hom] [IsProper E.hom] [GeometricallyIrreducible E.hom]
    [GeometricallyReduced E.hom] (g : D ⟶ E) {T : Over (Spec (.of k))} (s : picEt E T)
    {K : Type u} [Field K] [Algebra k K] (t : overSpec k K ⟶ T) :
    degAt (picEtPullback g T s) t
      = PicEtAff.degAff K
          (PicEtAff.curveMap K g (picEtAffineEquiv E K (picEtMap E t s))) := by
  change PicEtAff.degAff K
      (picEtAffineEquiv D K (picEtMap D t (picEtPullback g T s))) = _
  rw [picEtMap_picEtPullback g t s, picEtAffineEquiv_picEtPullback]

end

end AlgebraicGeometry
