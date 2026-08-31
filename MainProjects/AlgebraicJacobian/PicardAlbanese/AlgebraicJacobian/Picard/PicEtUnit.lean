/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtMap

/-!
# The unit of the étale sheafification: `relPicFunctor ⟶ picEtFunctor`

The Layer-2 étale Picard functor `picEt` (`AlgebraicJacobian.Picard.PicEt`,
`AlgebraicJacobian.Picard.PicEtMap`) receives the honest relative Picard functor
through a natural transformation — the **unit of the étale sheafification**
(gap G4 of `informal/zeta-c2-rigidification-recon.md`, shared prerequisite of the
global (C2) comparison and of the degree/`Pic⁰` interface):

* `AlgebraicGeometry.Over.fromSpecAffine T U`: the spectrum of the section ring of an
  affine open `U` of a test object `T`, as a test object over `T` — the bridge between
  the affine-opens indexing of `picEt` and the test-object indexing of `relPic`.  Its
  coherences: restriction (`fromSpecAffine_resAlgHom`) and naturality along an
  arbitrary test morphism (`fromSpecAffine_naturality`).
* `AlgebraicGeometry.relPicToPicEt C T`: the component at `T` — a relative Picard class
  restricts along `fromSpecAffine T U` to every affine open, and each restriction is
  sent into the plus construction by `PicEtAff.unit`; the family is compatible by
  `PicEtAff.mapAlg_unit` and the coherences.
* `AlgebraicGeometry.picEtAffineEquiv_relPicToPicEt`: **affine consistency** — on an
  affine test the component collapses through the affine comparison
  (`picEtAffineEquiv`) to the unit `PicEtAff.unit` of the plus construction, so the
  Layer-2 unit extends the affine unit.
* `AlgebraicGeometry.picEtUnit C : relPicFunctor C ⟶ picEtFunctor C`: the natural
  transformation (naturality through the `∃!`-API `picEt.IsPullbackValue` of
  `picEtMapVal`).

The (C2) comparison (`PicEtAff.unit_surjective_of_section`, recon §1.3) will upgrade
the affine components to isomorphisms over section-admitting tests; injectivity of the
affine components is the landed (C1) `PicEtAff.unit_injective`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

noncomputable section

/-! ## The affine-open test objects of a test object -/

namespace Over

/-- The spectrum of the section ring of an affine open `U ⊆ T.left`, as a test object
over `T`: the underlying morphism is `IsAffineOpen.fromSpec`, and it lies over `Spec k`
by the very definition of the section-ring algebra `Over.sectionsAlgebra`. -/
def fromSpecAffine (T : Over (Spec (.of k))) (U : T.left.affineOpens) :
    overSpec k Γ(T.left, U.1) ⟶ T :=
  Over.homMk U.2.fromSpec (by
    have h1 : Spec.map (T.hom.appLE ⊤ U.1
          (le_top.trans (Scheme.Hom.preimage_top T.hom).ge))
          ≫ (isAffineOpen_top (Spec (.of k))).fromSpec
        = U.2.fromSpec ≫ T.hom :=
      IsAffineOpen.SpecMap_appLE_fromSpec T.hom (isAffineOpen_top _) U.2 _
    have h2 : (isAffineOpen_top (Spec (.of k))).fromSpec
        = Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    change U.2.fromSpec ≫ T.hom
        = Spec.map (CommRingCat.ofHom (algebraMap k Γ(T.left, U.1)))
    rw [Over.ofHom_algebraMap_sections, Spec.map_comp, ← h2, h1])

/-- **Naturality of `fromSpecAffine`** along an arbitrary morphism of test objects:
for affine opens `W ≤ f⁻¹ V`, the section-ring pullback `Over.appLEAlgHom` intertwines
the affine-open test objects — `IsAffineOpen.SpecMap_appLE_fromSpec` in the over
category. -/
theorem fromSpecAffine_naturality {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (V : T.left.affineOpens) (W : T'.left.affineOpens) (e : W.1 ≤ f.left ⁻¹ᵁ V.1) :
    Over.overSpecMap (Over.appLEAlgHom f V.1 W.1 e) ≫ fromSpecAffine T V
      = fromSpecAffine T' W ≫ f := by
  ext : 1
  change Spec.map (CommRingCat.ofHom (Over.appLEAlgHom f V.1 W.1 e).toRingHom)
      ≫ V.2.fromSpec = W.2.fromSpec ≫ f.left
  have h : CommRingCat.ofHom (Over.appLEAlgHom f V.1 W.1 e).toRingHom
      = f.left.appLE V.1 W.1 e := rfl
  rw [h]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f.left V.2 W.2 e

/-- **Restriction coherence of `fromSpecAffine`**: the affine-open test object of a
smaller affine open factors through that of a larger one, along `Spec` of the section
restriction. -/
theorem fromSpecAffine_resAlgHom {T : Over (Spec (.of k))} {U V : T.left.affineOpens}
    (h : U.1 ≤ V.1) :
    Over.overSpecMap (Over.resAlgHom T h) ≫ fromSpecAffine T V = fromSpecAffine T U := by
  have he : U.1 ≤ (Over.Hom.left (𝟙 T)) ⁻¹ᵁ V.1 := fun x hx => by
    rw [Over.id_left]
    exact h hx
  rw [← Over.appLEAlgHom_id T V.1 U.1 he h, fromSpecAffine_naturality (𝟙 T) V U he,
    Category.comp_id]

/-- On an affine test, the affine-open test object of the top affine open is the test
itself: composing with the `ΓSpecIso` identification of the section ring with the test
algebra gives the identity. -/
theorem overSpecMap_ΓTop_fromSpecAffine_top (A : Type u) [CommRing A] [Algebra k A] :
    Over.overSpecMap (k := k) (Over.overSpecΓTopAlgEquiv k A).toAlgHom
        ≫ fromSpecAffine (overSpec k A) (overSpecTopAffine A) = 𝟙 (overSpec k A) := by
  have key : Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ≫ (isAffineOpen_top (Spec (CommRingCat.of A))).fromSpec
      = 𝟙 (Spec (CommRingCat.of A)) := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id]
  ext : 1
  exact key

end Over

/-! ## The component at a test object -/

/-- The component at a test object `T` of the unit of the étale sheafification: a
relative Picard class restricts along `Over.fromSpecAffine T U` to every affine open
`U ⊆ T.left`, and each restriction enters the plus construction through
`PicEtAff.unit`.  The family is compatible under restriction by naturality of the unit
(`PicEtAff.mapAlg_unit`) and the restriction coherence of `fromSpecAffine`. -/
def relPicToPicEt (T : Over (Spec (.of k))) : relPic C T →* picEt C T where
  toFun z :=
    ⟨fun U => PicEtAff.unit C Γ(T.left, U.1) (relPicMap C (Over.fromSpecAffine T U) z),
      fun U V h => by
        rw [PicEtAff.mapAlg_unit]
        refine congrArg (PicEtAff.unit C Γ(T.left, U.1)) ?_
        calc relPicAlgMap C (Over.resAlgHom T h)
              (relPicMap C (Over.fromSpecAffine T V) z)
            = relPicMap C (Over.overSpecMap (Over.resAlgHom T h)
                ≫ Over.fromSpecAffine T V) z :=
              (relPicMap_comp C (Over.fromSpecAffine T V)
                (Over.overSpecMap (Over.resAlgHom T h)) z).symm
          _ = relPicMap C (Over.fromSpecAffine T U) z := by
              rw [Over.fromSpecAffine_resAlgHom h]⟩
  map_one' := by
    refine picEt.ext fun U => ?_
    change PicEtAff.unit C Γ(T.left, U.1) (relPicMap C (Over.fromSpecAffine T U) 1) = 1
    rw [map_one, map_one]
  map_mul' z w := by
    refine picEt.ext fun U => ?_
    change PicEtAff.unit C Γ(T.left, U.1) (relPicMap C (Over.fromSpecAffine T U) (z * w))
      = PicEtAff.unit C Γ(T.left, U.1) (relPicMap C (Over.fromSpecAffine T U) z)
        * PicEtAff.unit C Γ(T.left, U.1) (relPicMap C (Over.fromSpecAffine T U) w)
    rw [map_mul, map_mul]

@[simp]
lemma relPicToPicEt_val (T : Over (Spec (.of k))) (z : relPic C T)
    (U : T.left.affineOpens) :
    (relPicToPicEt C T z).1 U
      = PicEtAff.unit C Γ(T.left, U.1) (relPicMap C (Over.fromSpecAffine T U) z) :=
  rfl

/-- **Affine consistency of the unit**: on an affine test `overSpec k A` the component
`relPicToPicEt` collapses, through the affine comparison `picEtAffineEquiv`, to the
unit `PicEtAff.unit` of the plus construction. -/
theorem picEtAffineEquiv_relPicToPicEt (A : Type u) [CommRing A] [Algebra k A]
    (z : relPic C (overSpec k A)) :
    picEtAffineEquiv C A (relPicToPicEt C (overSpec k A) z) = PicEtAff.unit C A z :=
  calc picEtAffineEquiv C A (relPicToPicEt C (overSpec k A) z)
      = PicEtAff.mapAlg C (Over.overSpecΓTopAlgEquiv k A).toAlgHom
          (PicEtAff.unit C Γ((overSpec k A).left, (overSpecTopAffine A).1)
            (relPicMap C (Over.fromSpecAffine (overSpec k A) (overSpecTopAffine A))
              z)) := rfl
    _ = PicEtAff.unit C A (relPicAlgMap C (Over.overSpecΓTopAlgEquiv k A).toAlgHom
          (relPicMap C (Over.fromSpecAffine (overSpec k A) (overSpecTopAffine A)) z)) :=
        PicEtAff.mapAlg_unit C _ _
    _ = PicEtAff.unit C A
          (relPicMap C (Over.overSpecMap (k := k) (Over.overSpecΓTopAlgEquiv k A).toAlgHom
            ≫ Over.fromSpecAffine (overSpec k A) (overSpecTopAffine A)) z) :=
        congrArg (PicEtAff.unit C A)
          (relPicMap_comp C (Over.fromSpecAffine (overSpec k A) (overSpecTopAffine A))
            (Over.overSpecMap (k := k) (Over.overSpecΓTopAlgEquiv k A).toAlgHom) z).symm
    _ = PicEtAff.unit C A (relPicMap C (𝟙 (overSpec k A)) z) :=
        congrArg (fun g : overSpec k A ⟶ overSpec k A =>
            PicEtAff.unit C A (relPicMap C g z))
          (Over.overSpecMap_ΓTop_fromSpecAffine_top A)
    _ = PicEtAff.unit C A z := congrArg (PicEtAff.unit C A) (relPicMap_id C z)

/-! ## The natural transformation -/

section unit

variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]

/-- Naturality of the components: restriction of the unit's image along an arbitrary
morphism of test objects is the unit's image of the restricted class.  Verified through
the `∃!`-characterization `picEt.IsPullbackValue` of the glued value of `picEtMap`,
using both coherences of `fromSpecAffine`. -/
theorem picEtMap_relPicToPicEt {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (z : relPic C T) :
    picEtMap C f (relPicToPicEt C T z) = relPicToPicEt C T' (relPicMap C f z) := by
  refine picEt.ext fun W => ?_
  rw [picEtMap_val]
  refine picEtMapVal_eq_of C f (relPicToPicEt C T z) ?_
  intro W₀ hW₀ V hV
  rw [relPicToPicEt_val, relPicToPicEt_val, PicEtAff.mapAlg_unit, PicEtAff.mapAlg_unit]
  refine congrArg (PicEtAff.unit C Γ(T'.left, W₀.1)) ?_
  calc relPicAlgMap C (Over.resAlgHom T' hW₀)
        (relPicMap C (Over.fromSpecAffine T' W) (relPicMap C f z))
      = relPicAlgMap C (Over.resAlgHom T' hW₀)
          (relPicMap C (Over.fromSpecAffine T' W ≫ f) z) := by
        rw [relPicMap_comp C f (Over.fromSpecAffine T' W) z]
    _ = relPicMap C (Over.overSpecMap (Over.resAlgHom T' hW₀)
          ≫ (Over.fromSpecAffine T' W ≫ f)) z :=
        (relPicMap_comp C (Over.fromSpecAffine T' W ≫ f)
          (Over.overSpecMap (Over.resAlgHom T' hW₀)) z).symm
    _ = relPicMap C ((Over.overSpecMap (Over.resAlgHom T' hW₀)
          ≫ Over.fromSpecAffine T' W) ≫ f) z := by
        rw [Category.assoc]
    _ = relPicMap C (Over.fromSpecAffine T' W₀ ≫ f) z := by
        rw [Over.fromSpecAffine_resAlgHom hW₀]
    _ = relPicMap C (Over.overSpecMap (Over.appLEAlgHom f V.1 W₀.1 hV)
          ≫ Over.fromSpecAffine T V) z := by
        rw [Over.fromSpecAffine_naturality f V W₀ hV]
    _ = relPicAlgMap C (Over.appLEAlgHom f V.1 W₀.1 hV)
          (relPicMap C (Over.fromSpecAffine T V) z) :=
        relPicMap_comp C (Over.fromSpecAffine T V)
          (Over.overSpecMap (Over.appLEAlgHom f V.1 W₀.1 hV)) z

/-- **The unit of the étale sheafification** (gap G4 of the (C2) recon): the natural
transformation from the honest relative Picard functor into the étale-sheafified
Layer-2 functor.  On affine tests it is the unit of the plus construction
(`picEtAffineEquiv_relPicToPicEt`); its affine components are injective by the (C1)
étale separatedness (`PicEtAff.unit_injective`), and bijective over section-admitting
tests by the (C2) comparison. -/
def picEtUnit : relPicFunctor C ⟶ picEtFunctor C where
  app T := CommGrpCat.ofHom (relPicToPicEt C T.unop)
  naturality T T' g := by
    ext z
    exact (picEtMap_relPicToPicEt C g.unop z).symm

@[simp]
lemma picEtUnit_app (T : (Over (Spec (.of k)))ᵒᵖ) (z : relPic C T.unop) :
    (picEtUnit C).app T z = relPicToPicEt C T.unop z :=
  rfl

/-- Affine consistency of the unit, natural-transformation form. -/
theorem picEtAffineEquiv_picEtUnit_app (A : Type u) [CommRing A] [Algebra k A]
    (z : relPic C (overSpec k A)) :
    picEtAffineEquiv C A ((picEtUnit C).app (op (overSpec k A)) z)
      = PicEtAff.unit C A z :=
  picEtAffineEquiv_relPicToPicEt C A z

end unit

end

end AlgebraicGeometry
