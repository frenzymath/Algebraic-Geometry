/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.GrassmannianPluckerImmersion
import AlgebraicJacobian.Picard.SerreTwist

/-!
# Global immersion of the Plucker morphism

The inverse image of the standard projective open indexed by `I` is exactly
the range of the `I`-th affine Grassmannian chart. On this open, the global
Plucker morphism is therefore identified with the local immersion proved in
`GrassmannianPluckerImmersion`. Since the standard projective opens cover the
target, the global Plucker morphism is an immersion.
-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry
namespace Grassmannian

/-- The range of a Grassmannian chart localization is the principal open cut
out by its transition minor. -/
theorem chartIncl_opensRange (d r : ℕ) (I J : PluckerIndex d r) :
    (chartIncl d r I.1 J.1 I.2 J.2).opensRange =
      PrimeSpectrum.basicOpen (minorDet d r I.1 J.1 I.2 J.2) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
      (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))).opensRange = _
  exact TopologicalSpace.Opens.ext
    (PrimeSpectrum.localization_away_comap_range
      (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))
      (minorDet d r I.1 J.1 I.2 J.2))

/-- Inside one affine Grassmannian chart, the inverse image of another chart's
range is the overlap localization. -/
theorem glueChart_preimage_opensRange (d r : ℕ)
    (I J : (theGlueData d r).J) :
    (theGlueData d r).ι J ⁻¹ᵁ ((theGlueData d r).ι I).opensRange =
      (chartIncl d r J.1 I.1 J.2 I.2).opensRange := by
  have hp := IsPullback.of_isLimit ((theGlueData d r).vPullbackConeIsLimit J I)
  change (theGlueData d r).ι J ⁻¹ᵁ ((theGlueData d r).ι I).opensRange =
    ((theGlueData d r).f J I).opensRange
  rw [← Scheme.Hom.opensRange_pullbackFst]
  have hfst := hp.isoPullback_hom_fst
  change hp.isoPullback.hom ≫
      pullback.fst ((theGlueData d r).ι J) ((theGlueData d r).ι I) =
    (theGlueData d r).f J I at hfst
  have hrange :
      (hp.isoPullback.hom ≫ pullback.fst ((theGlueData d r).ι J)
        ((theGlueData d r).ι I)).opensRange =
      (pullback.fst ((theGlueData d r).ι J)
        ((theGlueData d r).ι I)).opensRange := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_of_isIso]
    simp
  rw [← hrange]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- A normalized Plucker chart pulls a standard projective open back to the
principal open defined by the corresponding maximal minor. -/
theorem pluckerChart_preimage_basicOpen (d r : ℕ)
    (I J : (theGlueData d r).J) :
    pluckerChart d r J ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I) =
      PrimeSpectrum.basicOpen (minorDet d r J.1 I.1 J.2 I.2) := by
  change ProjectiveSpace.Coordinates.fromSpec J
      (fun K : PluckerIndex d r => minorDet d r J.1 K.1 J.2 K.2)
      (minorDet_self d r J.1 J.2) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I) = _
  exact ProjectiveSpace.Coordinates.fromSpec_preimage_basicOpen J I
    (fun K : PluckerIndex d r => minorDet d r J.1 K.1 J.2 K.2)
    (minorDet_self d r J.1 J.2)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a standard projective coordinate open under the
global Plucker morphism is exactly the corresponding Grassmannian chart. -/
theorem pluckerToProj_preimage_basicOpen (d r : ℕ)
    (I : PluckerIndex d r) :
    pluckerToProj d r ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I) =
      ((theGlueData d r).ι I).opensRange := by
  ext x
  obtain ⟨J, y, rfl⟩ := (theGlueData d r).ι_jointly_surjective x
  change ((theGlueData d r).ι J ≫ pluckerToProj d r) y ∈
      Proj.basicOpen (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I) ↔
    y ∈ (theGlueData d r).ι J ⁻¹ᵁ ((theGlueData d r).ι I).opensRange
  rw [ι_pluckerToProj]
  change y ∈ pluckerChart d r J ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I) ↔
    y ∈ (theGlueData d r).ι J ⁻¹ᵁ ((theGlueData d r).ι I).opensRange
  rw [pluckerChart_preimage_basicOpen,
    glueChart_preimage_opensRange, chartIncl_opensRange]

set_option backward.isDefEq.respectTransparency false in
/-- The affine chart is canonically isomorphic to its open range in the glued
Grassmannian. -/
def pluckerChartRangeIso (d r : ℕ) (I : (theGlueData d r).J) :
    affineChart d r I.1 ≅ (((theGlueData d r).ι I).opensRange).toScheme := by
  apply IsOpenImmersion.isoOfRangeEq
    ((theGlueData d r).ι I) (((theGlueData d r).ι I).opensRange).ι
  rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι]

set_option backward.isDefEq.respectTransparency false in
/-- The absolute Plucker morphism is an immersion. -/
theorem pluckerToProj_isImmersion (d r : ℕ) :
    IsImmersion (pluckerToProj d r) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsImmersion)
    (fun I : PluckerIndex d r =>
      Proj.basicOpen (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I))
    (ProjTwist.iSup_basicOpen_X_eq_top (PluckerIndex d r))
  intro I
  let U := Proj.basicOpen
    (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) (X I)
  let V := ((theGlueData d r).ι I).opensRange
  let e : affineChart d r I.1 ≅ V.toScheme := pluckerChartRangeIso d r I
  let hpre : pluckerToProj d r ⁻¹ᵁ U = V := by
    simpa only [U, V] using pluckerToProj_preimage_basicOpen d r I
  let g : V.toScheme ⟶ U.toScheme :=
    (pluckerToProj d r).resLE U V hpre.ge
  have he : e.hom ≫ V.ι = (theGlueData d r).ι I := by
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hgfac : e.hom ≫ (g ≫ U.ι) = pluckerChart d r I := by
    rw [Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, he, ι_pluckerToProj]
  have hcomp : IsImmersion (e.hom ≫ (g ≫ U.ι)) := by
    rw [hgfac]
    exact pluckerChart_isImmersion d r I
  haveI : IsImmersion (g ≫ U.ι) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (@IsImmersion) e.hom (g ≫ U.ι)).mp hcomp
  have hg : IsImmersion g := IsImmersion.of_comp g U.ι
  let restrictionIso : Arrow.mk ((pluckerToProj d r) ∣_ U) ≅ Arrow.mk g :=
    Arrow.isoMk ((scheme d r).isoOfEq hpre) (Iso.refl _) (by
      change ((scheme d r).isoOfEq hpre).hom ≫
          ((scheme d r).homOfLE _ ≫ (pluckerToProj d r) ∣_ U) =
        ((pluckerToProj d r) ∣_ U) ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc]
      rw [show (scheme d r).homOfLE _ = ((scheme d r).isoOfEq hpre).inv by
        rw [← cancel_mono (pluckerToProj d r ⁻¹ᵁ U).ι, Scheme.homOfLE_ι,
          Scheme.isoOfEq_inv_ι], Iso.hom_inv_id, Category.id_comp])
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsImmersion)
    restrictionIso]
  exact hg

end Grassmannian
end AlgebraicGeometry
