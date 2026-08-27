/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GrassmannianCells
import AlgebraicJacobian.Picard.ProjectiveCoordinateChart

/-!
# The Plucker morphism for the absolute Grassmannian over Spec Z

This file constructs the absolute morphism from the project-local Grassmannian
to projective space. On the chart indexed by `I`, its homogeneous coordinates
are the maximal minors `P^I_K`, normalized by `P^I_I = 1`. The minor-ratio
identity from `GrassmannianCells` says that these coordinate maps agree on
chart overlaps up to multiplication by the invertible minor `P^I_J`, so they
glue to a global morphism.

The immersion proof is deliberately a separate layer. It requires identifying
the inverse image of each standard projective chart, proving that the
corresponding affine coordinate map is surjective, and reindexing the finite
coordinate type by `Fin (n + 1)` for `IsHQuasiProjective`.
-/

open CategoryTheory Limits
open MvPolynomial

noncomputable section

namespace AlgebraicGeometry
namespace Grassmannian

/-- The Plucker coordinates, indexed by the `d`-subsets of `Fin r`. -/
abbrev PluckerIndex (d r : ℕ) := {I : Finset (Fin r) // I.card = d}

/-- The normalized Plucker-coordinate morphism on the affine chart indexed by
`I`. Its coordinate at `K` is the maximal minor `P^I_K`. -/
noncomputable def pluckerChart (d r : ℕ) (I : PluckerIndex d r) :
    affineChart d r I.1 ⟶
      Proj (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) :=
  ProjectiveSpace.Coordinates.fromSpec I
    (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
    (minorDet_self d r I.1 I.2)

/-- Restricting the `I`-th Plucker chart morphism to its overlap with `J`
applies the localization map to every minor coordinate. -/
theorem chartIncl_pluckerChart (d r : ℕ) (I J : PluckerIndex d r) :
    chartIncl d r I.1 J.1 I.2 J.2 ≫ pluckerChart d r I =
      ProjectiveSpace.Coordinates.fromSpec I
        (fun K : PluckerIndex d r =>
          algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
            (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))
            (minorDet d r I.1 K.1 I.2 K.2))
        (by rw [minorDet_self, map_one]) := by
  rw [chartIncl, pluckerChart]
  exact ProjectiveSpace.Coordinates.SpecMap_fromSpec
    (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
      (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))
    I (fun K : PluckerIndex d r => minorDet d r I.1 K.1 I.2 K.2)
    (minorDet_self d r I.1 I.2)

set_option backward.isDefEq.respectTransparency false in
/-- The normalized Plucker-coordinate morphisms agree on an overlap. The two
coordinate families differ by the invertible minor `P^I_J`; this is precisely
`transitionPreMap_minorDet_mul`. -/
theorem pluckerChart_overlap (d r : ℕ) (I J : PluckerIndex d r) :
    chartIncl d r I.1 J.1 I.2 J.2 ≫ pluckerChart d r I =
      chartTransition d r I.1 J.1 I.2 J.2 ≫
        chartIncl d r J.1 I.1 J.2 I.2 ≫ pluckerChart d r J := by
  rw [chartIncl_pluckerChart, ← Category.assoc,
    chartTransition_comp_chartIncl]
  rw [pluckerChart, ProjectiveSpace.Coordinates.SpecMap_fromSpec]
  apply ProjectiveSpace.Coordinates.fromSpec_eq_of_unit_smul
    (lambda := algebraMap
      (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
      (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))
      (minorDet d r I.1 J.1 I.2 J.2))
  · exact IsLocalization.Away.algebraMap_isUnit _
  · intro K
    simpa [mul_comm] using
      (transitionPreMap_minorDet_mul d r I.1 J.1 K.1 I.2 J.2 K.2).symm

set_option backward.isDefEq.respectTransparency false in
/-- The local Plucker morphisms satisfy the compatibility equation required by
`Scheme.Cover.glueMorphisms`. -/
theorem pluckerChart_compat (d r : ℕ) (I J : (theGlueData d r).J) :
    pullback.fst ((theGlueData d r).ι I)
        ((theGlueData d r).ι J) ≫ pluckerChart d r I =
      pullback.snd ((theGlueData d r).ι I)
        ((theGlueData d r).ι J) ≫ pluckerChart d r J := by
  rw [← cancel_epi (pullbackιIso d r I J).inv]
  simp only [← Category.assoc]
  rw [pullbackιIso_inv_fst, pullbackιIso_inv_snd]
  exact pluckerChart_overlap d r I J

/-- The global absolute Plucker morphism, obtained by gluing the normalized
minor-coordinate maps on the standard Grassmannian charts. -/
noncomputable def pluckerToProj (d r : ℕ) :
    scheme d r ⟶ Proj (homogeneousSubmodule (PluckerIndex d r) (ULift ℤ)) :=
  (theGlueData d r).openCover.glueMorphisms
    (fun I => pluckerChart d r I)
    (fun I J => pluckerChart_compat d r I J)

/-- The global Plucker morphism restricts to the normalized minor-coordinate
morphism on every Grassmannian chart. -/
theorem ι_pluckerToProj (d r : ℕ) (I : (theGlueData d r).J) :
    (theGlueData d r).ι I ≫ pluckerToProj d r = pluckerChart d r I := by
  exact Scheme.Cover.ι_glueMorphisms
    (theGlueData d r).openCover
    (fun J => pluckerChart d r J)
    (fun J K => pluckerChart_compat d r J K) I

end Grassmannian
end AlgebraicGeometry
