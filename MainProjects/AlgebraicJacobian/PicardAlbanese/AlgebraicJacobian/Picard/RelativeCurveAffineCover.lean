/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.RelativeTwoCover
import AlgebraicJacobian.Picard.PicEtUnit
import AlgebraicJacobian.Picard.SectionsDescent
import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# The affine-base cover of a relative curve

For a test scheme `T` over `Spec k`, pull the directed cover by all affine opens of
`T.left` back along the second projection `(C ⊗ T).left ⟶ T.left`.  Its component over an
affine open `U` is canonically the relative curve over the section ring `Γ(T, U)`.

The comparison isomorphisms are compatible with inclusions of affine opens.  These
coherences let data constructed over the affine relative curves descend through the
locally directed cover without choosing new affine charts on the total product.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

noncomputable section

attribute [local instance] Over.sectionsAlgebra

/-- The pullback of the directed affine cover of `T.left` along the relative-curve
projection `(C ⊗ T).left ⟶ T.left`. -/
abbrev relCurveAffineCover (C T : Over (Spec (.of k))) : (C ⊗ T).left.OpenCover :=
  T.left.directedAffineCover.pullback₁ (snd C T).left

/-- The pulled-back cover carries the canonical locally directed structure inherited
from the directed affine cover of the base. -/
noncomputable instance relCurveAffineCoverLocallyDirected
    (C T : Over (Spec (.of k))) :
    Scheme.Cover.LocallyDirected (relCurveAffineCover C T) :=
  Scheme.Cover.locallyDirectedPullbackCover
    T.left.directedAffineCover (snd C T).left

variable (C T : Over (Spec (.of k)))

/-- The relative curve over the section ring of an affine open and the corresponding
component of `relCurveAffineCover` are pullbacks of the same cospan. -/
theorem isPullback_relCurve_affineOpen (U : T.left.affineOpens) :
    IsPullback
      (C ◁ Over.fromSpecAffine T U).left
      ((snd C (overSpec k Γ(T.left, U.1))).left ≫ U.2.isoSpec.inv)
      (snd C T).left U.1.ι := by
  refine (Over.isPullback_whiskerLeft_snd C (Over.fromSpecAffine T U)).of_iso
    (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp [Over.fromSpecAffine]

/-- The affine relative curve `C_{Γ(T,U)}` is canonically the component over `U` of
the affine-base cover of `(C ⊗ T).left`. -/
def relCurveAffineOpenIso (U : T.left.affineOpens) :
    relCurve C Γ(T.left, U.1) ≅ (relCurveAffineCover C T).X U :=
  IsPullback.isoIsPullback _ _ (isPullback_relCurve_affineOpen C T U)
    (IsPullback.of_hasPullback (snd C T).left U.1.ι)

/-- The comparison isomorphism followed by the cover map is the relative-curve map
induced by the affine-open test object. -/
@[reassoc (attr := simp)]
theorem relCurveAffineOpenIso_hom_f (U : T.left.affineOpens) :
    (relCurveAffineOpenIso C T U).hom ≫ (relCurveAffineCover C T).f U =
      (C ◁ Over.fromSpecAffine T U).left :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

private theorem relCurveAffineOpenIso_hom_pullbackHom (U : T.left.affineOpens) :
    (relCurveAffineOpenIso C T U).hom ≫
        T.left.directedAffineCover.pullbackHom (snd C T).left U =
      (snd C (overSpec k Γ(T.left, U.1))).left ≫ U.2.isoSpec.inv :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

private theorem isoSpec_hom_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  rw [← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

private theorem isoSpec_resAlgHom (U V : T.left.affineOpens) (hUV : U.1 ≤ V.1) :
    U.2.isoSpec.hom ≫ (Over.overSpecMap (Over.resAlgHom T hUV)).left =
      T.left.homOfLE hUV ≫ V.2.isoSpec.hom := by
  have hres : (Over.overSpecMap (Over.resAlgHom T hUV)).left ≫ V.2.fromSpec =
      U.2.fromSpec :=
    congrArg CategoryTheory.Over.Hom.left
      (Over.fromSpecAffine_resAlgHom (T := T) hUV)
  rw [← cancel_mono V.2.fromSpec, Category.assoc, Category.assoc, hres,
    isoSpec_hom_fromSpec, isoSpec_hom_fromSpec, Scheme.homOfLE_ι]

private theorem resAlgHom_isoSpec_inv (U V : T.left.affineOpens) (hUV : U.1 ≤ V.1) :
    (Over.overSpecMap (Over.resAlgHom T hUV)).left ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ T.left.homOfLE hUV := by
  rw [← cancel_epi U.2.isoSpec.hom]
  calc
    U.2.isoSpec.hom ≫
          ((Over.overSpecMap (Over.resAlgHom T hUV)).left ≫ V.2.isoSpec.inv) =
        (U.2.isoSpec.hom ≫
          (Over.overSpecMap (Over.resAlgHom T hUV)).left) ≫ V.2.isoSpec.inv :=
      (Category.assoc _ _ _).symm
    _ = (T.left.homOfLE hUV ≫ V.2.isoSpec.hom) ≫ V.2.isoSpec.inv := by
      rw [isoSpec_resAlgHom T U V hUV]
    _ = T.left.homOfLE hUV := by simp
    _ = (U.2.isoSpec.hom ≫ U.2.isoSpec.inv) ≫ T.left.homOfLE hUV := by simp
    _ = U.2.isoSpec.hom ≫ (U.2.isoSpec.inv ≫ T.left.homOfLE hUV) :=
      Category.assoc _ _ _

private theorem relCurveAffineCover_trans_pullbackHom
    {U V : T.left.directedAffineCover.I₀} (hUV : U ⟶ V) :
    Scheme.Cover.trans (relCurveAffineCover C T) hUV ≫
        T.left.directedAffineCover.pullbackHom (snd C T).left V =
      T.left.directedAffineCover.pullbackHom (snd C T).left U ≫
        T.left.homOfLE (leOfHom hUV) := by
  rw [Subsingleton.elim hUV (homOfLE (leOfHom hUV))]
  change
    pullback.map _ _ _ _ (𝟙 _) (T.left.homOfLE (leOfHom hUV)) (𝟙 _)
        (by simp) (by simp [Scheme.homOfLE_ι]) ≫
        pullback.snd _ _ =
      pullback.snd _ _ ≫ T.left.homOfLE (leOfHom hUV)
  simp

/-- Restriction coherence of the affine-relative-curve comparison: restriction on
section rings followed by the comparison over `V` equals the cover transition from
the component over `U` to the component over `V`. -/
theorem relCurveAffineOpenIso_hom_trans
    {U V : T.left.directedAffineCover.I₀} (hUV : U ⟶ V) :
    (relCurveAffineOpenIso C T U).hom ≫
        Scheme.Cover.trans (relCurveAffineCover C T) hUV =
      (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
        (relCurveAffineOpenIso C T V).hom := by
  have hcurve :
      (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (C ◁ Over.fromSpecAffine T V).left =
        (C ◁ Over.fromSpecAffine T U).left := by
    rw [← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      Over.fromSpecAffine_resAlgHom]
  have hsnd :
      (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (snd C (overSpec k Γ(T.left, V.1))).left =
        (snd C (overSpec k Γ(T.left, U.1))).left ≫
          (Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  apply pullback.hom_ext
  · change
      ((relCurveAffineOpenIso C T U).hom ≫
          Scheme.Cover.trans (relCurveAffineCover C T) hUV) ≫
            (relCurveAffineCover C T).f V =
        ((C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (relCurveAffineOpenIso C T V).hom) ≫
            (relCurveAffineCover C T).f V
    calc
      ((relCurveAffineOpenIso C T U).hom ≫
            Scheme.Cover.trans (relCurveAffineCover C T) hUV) ≫
          (relCurveAffineCover C T).f V =
          (relCurveAffineOpenIso C T U).hom ≫
            (Scheme.Cover.trans (relCurveAffineCover C T) hUV ≫
              (relCurveAffineCover C T).f V) := Category.assoc _ _ _
      _ = (relCurveAffineOpenIso C T U).hom ≫
          (relCurveAffineCover C T).f U := by rw [Scheme.Cover.trans_map]
      _ = (C ◁ Over.fromSpecAffine T U).left :=
        relCurveAffineOpenIso_hom_f C T U
      _ = (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (C ◁ Over.fromSpecAffine T V).left := hcurve.symm
      _ = (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          ((relCurveAffineOpenIso C T V).hom ≫
            (relCurveAffineCover C T).f V) := by
        rw [relCurveAffineOpenIso_hom_f]
      _ = ((C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (relCurveAffineOpenIso C T V).hom) ≫
            (relCurveAffineCover C T).f V := (Category.assoc _ _ _).symm
  · change
      ((relCurveAffineOpenIso C T U).hom ≫
          Scheme.Cover.trans (relCurveAffineCover C T) hUV) ≫
            T.left.directedAffineCover.pullbackHom (snd C T).left V =
        ((C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (relCurveAffineOpenIso C T V).hom) ≫
            T.left.directedAffineCover.pullbackHom (snd C T).left V
    calc
      ((relCurveAffineOpenIso C T U).hom ≫
            Scheme.Cover.trans (relCurveAffineCover C T) hUV) ≫
          T.left.directedAffineCover.pullbackHom (snd C T).left V =
          (relCurveAffineOpenIso C T U).hom ≫
            (Scheme.Cover.trans (relCurveAffineCover C T) hUV ≫
              T.left.directedAffineCover.pullbackHom (snd C T).left V) :=
        Category.assoc _ _ _
      _ = (relCurveAffineOpenIso C T U).hom ≫
          (T.left.directedAffineCover.pullbackHom (snd C T).left U ≫
            T.left.homOfLE (leOfHom hUV)) := by
        rw [relCurveAffineCover_trans_pullbackHom C T hUV]
      _ = ((snd C (overSpec k Γ(T.left, U.1))).left ≫ U.2.isoSpec.inv) ≫
          T.left.homOfLE (leOfHom hUV) := by
        rw [← Category.assoc, relCurveAffineOpenIso_hom_pullbackHom]
      _ = (snd C (overSpec k Γ(T.left, U.1))).left ≫
          (U.2.isoSpec.inv ≫ T.left.homOfLE (leOfHom hUV)) :=
        Category.assoc _ _ _
      _ = (snd C (overSpec k Γ(T.left, U.1))).left ≫
          ((Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
            V.2.isoSpec.inv) := by
        rw [resAlgHom_isoSpec_inv T U V (leOfHom hUV)]
      _ = ((snd C (overSpec k Γ(T.left, U.1))).left ≫
          (Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left) ≫
            V.2.isoSpec.inv := (Category.assoc _ _ _).symm
      _ = ((C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (snd C (overSpec k Γ(T.left, V.1))).left) ≫ V.2.isoSpec.inv := by
        rw [hsnd]
      _ = (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          ((snd C (overSpec k Γ(T.left, V.1))).left ≫ V.2.isoSpec.inv) :=
        Category.assoc _ _ _
      _ = (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          ((relCurveAffineOpenIso C T V).hom ≫
            T.left.directedAffineCover.pullbackHom (snd C T).left V) := by
        rw [relCurveAffineOpenIso_hom_pullbackHom]
      _ = ((C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (relCurveAffineOpenIso C T V).hom) ≫
            T.left.directedAffineCover.pullbackHom (snd C T).left V :=
        (Category.assoc _ _ _).symm

/-- Inverse form of `relCurveAffineOpenIso_hom_trans`, convenient for transporting
data from a cover component to its affine relative-curve model. -/
theorem relCurveAffineOpenIso_inv_trans
    {U V : T.left.directedAffineCover.I₀} (hUV : U ⟶ V) :
    Scheme.Cover.trans (relCurveAffineCover C T) hUV ≫
        (relCurveAffineOpenIso C T V).inv =
      (relCurveAffineOpenIso C T U).inv ≫
        (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left := by
  rw [← cancel_epi (relCurveAffineOpenIso C T U).hom]
  calc
    (relCurveAffineOpenIso C T U).hom ≫
          (Scheme.Cover.trans (relCurveAffineCover C T) hUV ≫
            (relCurveAffineOpenIso C T V).inv) =
        ((relCurveAffineOpenIso C T U).hom ≫
          Scheme.Cover.trans (relCurveAffineCover C T) hUV) ≫
            (relCurveAffineOpenIso C T V).inv := (Category.assoc _ _ _).symm
    _ = ((C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left ≫
          (relCurveAffineOpenIso C T V).hom) ≫
            (relCurveAffineOpenIso C T V).inv := by
      rw [relCurveAffineOpenIso_hom_trans C T hUV]
    _ = (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left := by simp
    _ = ((relCurveAffineOpenIso C T U).hom ≫
          (relCurveAffineOpenIso C T U).inv) ≫
            (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left := by simp
    _ = (relCurveAffineOpenIso C T U).hom ≫
          ((relCurveAffineOpenIso C T U).inv ≫
            (C ◁ Over.overSpecMap (Over.resAlgHom T (leOfHom hUV))).left) :=
      Category.assoc _ _ _

end

end AlgebraicGeometry
