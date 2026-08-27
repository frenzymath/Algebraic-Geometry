/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteMorphismEmbedding
import AlgebraicJacobian.Picard.ProjectiveSpaceAffineChartAt

/-!
# Relative projective coordinate charts

A normalized homogeneous coordinate family over a field defines a morphism to
relative projective space and a canonical factor through the chart where the
normalizing coordinate is nonzero.  The corresponding affine-space map is a
closed immersion as soon as the remaining coordinates algebra-generate the
source ring.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjectiveSpace.Coordinates

variable {k B J : Type u} [Field k] [CommRing B] [Algebra k B]

/-- The structural morphism of an affine spectrum induced by its `k`-algebra
structure. -/
def specToBase : Spec (.of B) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k B))

/-- A normalized integral coordinate map paired with the structural morphism
to the base field. -/
def relativeFromSpec (i : J) (c : J → B) (hi : c i = 1) :
    Spec (.of B) ⟶ ℙ(J; Spec (.of k)) :=
  pullback.lift specToBase (fromSpec i c hi) (Subsingleton.elim _ _)

@[reassoc]
theorem relativeFromSpec_over (i : J) (c : J → B) (hi : c i = 1) :
    relativeFromSpec i c hi ≫ (ℙ(J; Spec (.of k)) ↘ Spec (.of k)) =
      specToBase := by
  rw [ProjectiveSpace.over_eq_fst]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem relativeFromSpec_toProjInt (i : J) (c : J → B) (hi : c i = 1) :
    relativeFromSpec i c hi ≫ ProjectiveSpace.toProjInt J (Spec (.of k)) =
      fromSpec i c hi := by
  rw [ProjectiveSpace.toProjInt_eq_snd]
  exact pullback.lift_snd _ _ _

/-- The normalized coordinate map factored through its relative standard
chart. -/
def toAffineChartAt (i : J) (c : J → B) (hi : c i = 1) :
    Spec (.of B) ⟶ ProjectiveSpace.affineChartAt J i (Spec (.of k)) :=
  pullback.lift (relativeFromSpec i c hi)
    (Spec.map (CommRingCat.ofHom (chartHom i c hi))) (by
      rw [relativeFromSpec_toProjInt]
      rfl)

@[reassoc]
theorem toAffineChartAt_incl (i : J) (c : J → B) (hi : c i = 1) :
    toAffineChartAt i c hi ≫
        ProjectiveSpace.affineChartAt.incl J i (Spec (.of k)) =
      relativeFromSpec i c hi :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem toAffineChartAt_specAway (i : J) (c : J → B) (hi : c i = 1) :
    toAffineChartAt i c hi ≫
        ProjectiveSpace.affineChartAt.toSpecAway J i (Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (chartHom i c hi)) :=
  pullback.lift_snd _ _ _

/-- The affine-space map classified by the complementary normalized
coordinates. -/
def affineSpecMap (i : J) (c : J → B) :
    Spec (.of B) ⟶ 𝔸({j : J // j ≠ i}; Spec (.of k)) :=
  Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k) (fun j : {j : J // j ≠ i} ↦ c j.1)).toRingHom) ≫
    (AffineSpace.SpecIso {j : J // j ≠ i} (.of k)).inv

@[reassoc]
theorem affineSpecMap_over (i : J) (c : J → B) :
    affineSpecMap (k := k) i c ≫
        (𝔸({j : J // j ≠ i}; Spec (.of k)) ↘ Spec (.of k)) =
      specToBase := by
  rw [affineSpecMap, Category.assoc, AffineSpace.SpecIso_inv_over,
    ← Spec.map_comp]
  congr 1
  ext x
  simp

@[simp]
theorem affineSpecMap_appTop_coord (i : J) (c : J → B)
    (j : {j : J // j ≠ i}) :
    (affineSpecMap (k := k) i c).appTop
        (AffineSpace.coord (Spec (.of k)) j) =
      (Scheme.ΓSpecIso (.of B)).inv (c j.1) := by
  rw [affineSpecMap, Scheme.Hom.comp_appTop]
  change (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k)
        (fun j : {j : J // j ≠ i} ↦ c j.1)).toRingHom)).appTop
        ((AffineSpace.SpecIso {j : J // j ≠ i} (.of k)).inv.appTop
          (AffineSpace.coord (Spec (.of k)) j)) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, ConcreteCategory.hom_ofHom]
  exact congrArg (fun z : B ↦ (Scheme.ΓSpecIso (.of B)).inv z)
    (MvPolynomial.aeval_X
      (R := k) (fun j : {j : J // j ≠ i} ↦ c j.1) j)

/-- Algebra generation of the complementary normalized coordinates makes the
associated affine-space map a closed immersion. -/
theorem isClosedImmersion_affineSpecMap (i : J) (c : J → B)
    (hgen : Algebra.adjoin k (Set.range fun j : {j : J // j ≠ i} ↦ c j.1) = ⊤) :
    IsClosedImmersion (affineSpecMap (k := k) i c) := by
  dsimp [affineSpecMap]
  apply MorphismProperty.comp_mem @IsClosedImmersion
  · exact IsFinite.isClosedImmersion_SpecMap_aeval_of_adjoin_eq_top
      (R := k) (A := B) (n := {j : J // j ≠ i}) _ hgen
  · infer_instance

section Finite

variable [Finite J]

/-- The chart factor pulls the affine coordinate indexed by `j` back to the
corresponding normalized homogeneous coordinate. -/
@[simp]
theorem toAffineChartAt_isoAffineSpace_appTop_coord
    (i : J) (c : J → B) (hi : c i = 1)
    (j : {j : J // j ≠ i}) :
    (toAffineChartAt i c hi ≫
        (ProjectiveSpace.affineChartAt.isoAffineSpace
          J i (Spec (.of k))).hom).appTop
        (AffineSpace.coord (Spec (.of k)) j) =
      (Scheme.ΓSpecIso (.of B)).inv (c j.1) := by
  change (toAffineChartAt i c hi ≫
      (ProjectiveSpace.affineChartAt.isoAffineSpace
        J i (Spec (.of k))).hom ≫
      AffineSpace.toSpecMvPoly {j : J // j ≠ i} (Spec (.of k))).appTop
        ((Scheme.ΓSpecIso
          (.of (MvPolynomial {j : J // j ≠ i} (ULift.{u} ℤ)))).inv (X j)) = _
  rw [ProjectiveSpace.affineChartAt.isoAffineSpace_hom_toSpecMvPoly,
    ← Category.assoc, toAffineChartAt_specAway,
    Scheme.Hom.comp_appTop]
  change (Spec.map (CommRingCat.ofHom (chartHom i c hi))).appTop
      ((ProjectiveSpace.affineChartAt.specAwayIso J i).hom.appTop
        ((Scheme.ΓSpecIso
          (.of (MvPolynomial {j : J // j ≠ i} (ULift.{u} ℤ)))).inv (X j))) = _
  simp only [ProjectiveSpace.affineChartAt.specAwayIso,
    Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  change (Spec.map (CommRingCat.ofHom (chartHom i c hi))).appTop
      ((Spec.map
        (ProjectiveSpace.AffineChartAtRing.awayAlgEquiv
          (ULift.{u} ℤ) J i).toRingEquiv.toCommRingCatIso.inv).appTop
        ((Scheme.ΓSpecIso
          (.of (MvPolynomial {j : J // j ≠ i} (ULift.{u} ℤ)))).inv (X j))) = _
  have hAway :
      (Spec.map
        (ProjectiveSpace.AffineChartAtRing.awayAlgEquiv
          (ULift.{u} ℤ) J i).toRingEquiv.toCommRingCatIso.inv).appTop
          ((Scheme.ΓSpecIso
            (.of (MvPolynomial {j : J // j ≠ i} (ULift.{u} ℤ)))).inv (X j)) =
        (Scheme.ΓSpecIso
          (.of (Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i)))).inv
            ((ProjectiveSpace.AffineChartAtRing.awayAlgEquiv
              (ULift.{u} ℤ) J i).symm (X j)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl
  have hChart (z : Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i)) :
      (Spec.map (CommRingCat.ofHom (chartHom i c hi))).appTop
          ((Scheme.ΓSpecIso
            (.of (Away (homogeneousSubmodule J (ULift.{u} ℤ)) (X i)))).inv z) =
        (Scheme.ΓSpecIso (.of B)).inv (chartHom i c hi z) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply, ConcreteCategory.hom_ofHom]
  rw [hAway,
    ProjectiveSpace.AffineChartAtRing.awayAlgEquiv_symm_X_eq_coordinates,
    hChart, chartHom_chartCoord]

/-- The canonical projective-chart factor is the affine-space map classified
by the complementary normalized coordinates. -/
theorem toAffineChartAt_isoAffineSpace_eq_affineSpecMap
    (i : J) (c : J → B) (hi : c i = 1) :
    toAffineChartAt i c hi ≫
        (ProjectiveSpace.affineChartAt.isoAffineSpace
          J i (Spec (.of k))).hom =
      affineSpecMap (k := k) i c := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc,
      ProjectiveSpace.affineChartAt.isoAffineSpace_hom_over]
    rw [ProjectiveSpace.affineChartAt.over_eq,
      ← Category.assoc, toAffineChartAt_incl,
      relativeFromSpec_over, affineSpecMap_over]
  · intro j
    rw [toAffineChartAt_isoAffineSpace_appTop_coord,
      affineSpecMap_appTop_coord]

/-- If the complementary normalized coordinates algebra-generate the source
ring, the factor through the corresponding relative projective chart is a
closed immersion. -/
theorem isClosedImmersion_toAffineChartAt
    (i : J) (c : J → B) (hi : c i = 1)
    (hgen : Algebra.adjoin k
      (Set.range fun j : {j : J // j ≠ i} ↦ c j.1) = ⊤) :
    IsClosedImmersion (toAffineChartAt (k := k) i c hi) := by
  haveI : IsClosedImmersion
      (toAffineChartAt (k := k) i c hi ≫
        (ProjectiveSpace.affineChartAt.isoAffineSpace
          J i (Spec (.of k))).hom) := by
    rw [toAffineChartAt_isoAffineSpace_eq_affineSpecMap]
    exact isClosedImmersion_affineSpecMap i c hgen
  exact IsClosedImmersion.of_comp (toAffineChartAt (k := k) i c hi)
    (ProjectiveSpace.affineChartAt.isoAffineSpace
      J i (Spec (.of k))).hom

end Finite

end AlgebraicGeometry.ProjectiveSpace.Coordinates
