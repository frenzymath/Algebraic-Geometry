/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageAtlas
import AlgebraicJacobian.AbelianVariety.GroupSeparated
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Affine intersections in the finite-stage Picard atlas

The exact separably closed `Pic^0` representer is a group scheme over a field, hence is
separated.  Consequently the intersection of any two affine charts in its chosen finite
atlas is itself affine.  The canonical affine overlap packaged here is the geometric input
for spreading out the finite atlas's restriction maps and gluing data.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- The finite index type of charts in the chosen atlas of the exact separably closed
`Pic^0` representer. -/
abbrev Pic0FiniteStageChartIndex :=
  { U // U ∈ (pic0FiniteStageAtlas C).charts }

instance : Finite (Pic0FiniteStageChartIndex C) :=
  (pic0FiniteStageAtlas C).finite_charts.to_subtype

/-- Pairwise intersections of charts in the chosen finite atlas of the exact separably
closed `Pic^0` representer are affine.  This uses the group structure transported from
the represented Picard functor, rather than adding separatedness as a hypothesis. -/
theorem pic0FiniteStageAtlas_inter_isAffine
    (U V : Pic0FiniteStageChartIndex C) :
    IsAffineOpen (U.1.1 ⊓ V.1.1) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : GrpObj J := (picRepDatumSepClosed C).grpObj
  haveI : IsSeparated J.hom := isSeparated_of_grpObj J
  haveI : Scheme.IsSeparated J.left := by
    constructor
    rw [← Limits.terminal.comp_from J.hom]
    infer_instance
  exact U.1.2.inf V.1.2

/-- The intersection of two chosen finite-stage charts, regarded canonically as an affine
open of the exact separably closed `Pic^0` representer. -/
noncomputable def pic0FiniteStageAffineOverlap
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0_sepClosed_representableBy (C := C)).1.left.affineOpens :=
  ⟨U.1.1 ⊓ V.1.1, pic0FiniteStageAtlas_inter_isAffine C U V⟩

@[simp]
theorem pic0FiniteStageAffineOverlap_open
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageAffineOverlap C U V).1 = U.1.1 ⊓ V.1.1 :=
  rfl

/-- The canonical affine overlap is contained in its left chart. -/
theorem pic0FiniteStageAffineOverlap_le_left
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageAffineOverlap C U V).1 ≤ U.1.1 :=
  inf_le_left

/-- The canonical affine overlap is contained in its right chart. -/
theorem pic0FiniteStageAffineOverlap_le_right
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageAffineOverlap C U V).1 ≤ V.1.1 :=
  inf_le_right

/-! ## The canonical finite affine gluing datum -/

/-- The chosen finite atlas as an actual open cover of the exact separably closed `Pic^0`
representer. -/
noncomputable def pic0SepClosedAtlasOpenCover :
    (pic0_sepClosed_representableBy (C := C)).1.left.OpenCover :=
  (pic0_sepClosed_representableBy (C := C)).1.left.openCoverOfIsOpenCover
    (fun U : Pic0FiniteStageChartIndex C => U.1.1) (by
      apply TopologicalSpace.IsOpenCover.mk
      rw [iSup_subtype'']
      exact (pic0FiniteStageAtlas C).iSup_opens)

/-- Every object of the chosen finite open cover is affine. -/
instance pic0SepClosedAtlasOpenCover_isAffine (U : Pic0FiniteStageChartIndex C) :
    IsAffine ((pic0SepClosedAtlasOpenCover C).X U) := by
  change IsAffine U.1.1.toScheme
  exact U.1.2

/-- The canonical finite affine gluing datum associated by Mathlib to the chosen open cover.
Its transition maps and triple-overlap cocycle are construction output of `gluedCover`; this
does not yet assert that the datum descends to a finite subextension. -/
noncomputable def pic0SepClosedAtlasGlueData : Scheme.GlueData :=
  (pic0SepClosedAtlasOpenCover C).gluedCover

/-- The left leg of the canonical atlas gluing, with its dependent chart indices fixed.

Keeping this projection folded as a whole avoids transporting the `HasPullback` witness
when downstream proofs compare the canonical gluing with a finite-stage gluing. -/
@[simp]
theorem pic0SepClosedAtlasGlueData_f
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasGlueData C).f U V =
      pullback.fst U.1.1.ι V.1.1.ι := by
  rfl

/-- The right leg of the canonical atlas gluing, exposed as one typed composite. -/
theorem pic0SepClosedAtlasGlueData_t_f
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasGlueData C).t U V ≫
        (pic0SepClosedAtlasGlueData C).f V U =
      pullback.snd ((pic0SepClosedAtlasOpenCover C).f U)
        ((pic0SepClosedAtlasOpenCover C).f V) := by
  change (pullbackSymmetry ((pic0SepClosedAtlasOpenCover C).f U)
      ((pic0SepClosedAtlasOpenCover C).f V)).hom ≫
      pullback.fst ((pic0SepClosedAtlasOpenCover C).f V)
        ((pic0SepClosedAtlasOpenCover C).f U) = _
  exact pullbackSymmetry_hom_comp_fst _ _

/-- The canonical affine overlap is a pullback against the atlas's own cover maps. -/
theorem pic0SepClosedAtlasOverlap_isPullback
    (U V : Pic0FiniteStageChartIndex C) :
    IsPullback
      ((pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
        (pic0FiniteStageAffineOverlap_le_left C U V))
      ((pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
        (pic0FiniteStageAffineOverlap_le_right C U V))
      ((pic0SepClosedAtlasOpenCover C).f U)
      ((pic0SepClosedAtlasOpenCover C).f V) := by
  change IsPullback _ _ U.1.1.ι V.1.1.ι
  exact isPullback_opens_inf U.1.1 V.1.1

/-- The affine overlap identified with the exact pullback object chosen by `gluedCover`. -/
noncomputable def pic0SepClosedAtlasOverlapIso
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0FiniteStageAffineOverlap C U V).1.toScheme ≅
      (pic0SepClosedAtlasGlueData C).V (U, V) :=
  (pic0SepClosedAtlasOverlap_isPullback C U V).isoPullback

/-- The typed overlap isomorphism has the canonical left projection. -/
@[reassoc]
theorem pic0SepClosedAtlasOverlapIso_hom_f
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasOverlapIso C U V).hom ≫
        (pic0SepClosedAtlasGlueData C).f U V =
      (pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
        (pic0FiniteStageAffineOverlap_le_left C U V) := by
  change (pic0SepClosedAtlasOverlap_isPullback C U V).isoPullback.hom ≫
      pullback.fst ((pic0SepClosedAtlasOpenCover C).f U)
        ((pic0SepClosedAtlasOpenCover C).f V) = _
  exact (pic0SepClosedAtlasOverlap_isPullback C U V).isoPullback_hom_fst

/-- The typed overlap isomorphism has the canonical right projection. -/
@[reassoc]
theorem pic0SepClosedAtlasOverlapIso_hom_t_f
    (U V : Pic0FiniteStageChartIndex C) :
    (pic0SepClosedAtlasOverlapIso C U V).hom ≫
        ((pic0SepClosedAtlasGlueData C).t U V ≫
          (pic0SepClosedAtlasGlueData C).f V U) =
      (pic0_sepClosed_representableBy (C := C)).1.left.homOfLE
        (pic0FiniteStageAffineOverlap_le_right C U V) := by
  rw [pic0SepClosedAtlasGlueData_t_f]
  exact (pic0SepClosedAtlasOverlap_isPullback C U V).isoPullback_hom_snd

/-- Every pairwise overlap scheme in the canonical finite gluing datum is affine. -/
instance isAffine_pic0SepClosedAtlasGlueData_V
    (U V : Pic0FiniteStageChartIndex C) :
    IsAffine ((pic0SepClosedAtlasGlueData C).V (U, V)) := by
  letI : IsAffine (U.1.1 ⊓ V.1.1).toScheme :=
    pic0FiniteStageAtlas_inter_isAffine C U V
  let h := isPullback_opens_inf U.1.1 V.1.1
  change IsAffine
    (pullback ((pic0SepClosedAtlasOpenCover C).f U)
      ((pic0SepClosedAtlasOpenCover C).f V))
  change IsAffine (pullback U.1.1.ι V.1.1.ι)
  exact IsAffine.of_isIso h.isoPullback.inv

end

end AlgebraicGeometry
