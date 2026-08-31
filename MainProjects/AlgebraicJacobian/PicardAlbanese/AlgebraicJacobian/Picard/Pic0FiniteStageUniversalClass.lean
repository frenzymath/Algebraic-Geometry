/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageOverlapRings
import AlgebraicJacobian.Descent.RepresenterData

/-!
# The universal Picard class on the finite affine atlas

The separably closed Picard representer carries one canonical universal class, obtained
from its `RepresentableBy` equivalence at the identity.  This file restricts that same
class to every chart and pairwise overlap in the chosen finite affine atlas and records
the two restriction equations.  Thus later finite-subextension descent starts from one
pinned universal element rather than independently chosen local classes.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- The separably closed representer kept as a named package.

The legacy API returns a dependent sigma; this projection is the migration boundary used by
the universal-class declarations below.  The package does not select a new representer. -/
noncomputable def pic0SepClosedRepresenterData :
    AlgebraicJacobian.RepresenterData
      (Over (Spec (.of k))) (pic0TypeFunctor C) :=
  AlgebraicJacobian.RepresenterData.ofSigma
    (pic0_sepClosed_representableBy (C := C))

/-- The universal degree-zero Picard class pinned by the separably closed
`RepresentableBy` certificate. -/
noncomputable def pic0SepClosedUniversalClass :
    pic0Subgroup C (pic0_sepClosed_representableBy (C := C)).1 :=
  (pic0SepClosedRepresenterData C).representation.homEquiv (𝟙 _)

/-- The restriction of the pinned universal class to one affine chart. -/
noncomputable def pic0FiniteStageUniversalChartClass
    (U : Pic0FiniteStageChartIndex C) :
    pic0Subgroup C (overSpec k (Pic0FiniteStageChartRing C U)) :=
  (pic0_sepClosed_representableBy (C := C)).2.homEquiv
    (Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 U.1)

/-- The restriction of the pinned universal class to one affine pairwise overlap. -/
noncomputable def pic0FiniteStageUniversalOverlapClass
    (U V : Pic0FiniteStageChartIndex C) :
    pic0Subgroup C (overSpec k (Pic0FiniteStageOverlapRing C U V)) :=
  (pic0_sepClosed_representableBy (C := C)).2.homEquiv
    (Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1
      (pic0FiniteStageAffineOverlap C U V))

private theorem pic0FiniteStageRestrictionLeft_eq_resAlgHom
    (U V : Pic0FiniteStageChartIndex C) :
    pic0FiniteStageRestrictionLeft C U V =
      Over.resAlgHom (pic0_sepClosed_representableBy (C := C)).1
        (pic0FiniteStageAffineOverlap_le_left C U V) := by
  rfl

private theorem pic0FiniteStageRestrictionRight_eq_resAlgHom
    (U V : Pic0FiniteStageChartIndex C) :
    pic0FiniteStageRestrictionRight C U V =
      Over.resAlgHom (pic0_sepClosed_representableBy (C := C)).1
        (pic0FiniteStageAffineOverlap_le_right C U V) := by
  rfl

/-- The universal chart class restricts to the universal overlap class along the left
atlas leg. -/
theorem pic0FiniteStageUniversalChartClass_restrict_left
    (U V : Pic0FiniteStageChartIndex C) :
    pic0Map C (Over.overSpecMap (pic0FiniteStageRestrictionLeft C U V))
        (pic0FiniteStageUniversalChartClass C U) =
      pic0FiniteStageUniversalOverlapClass C U V := by
  rw [pic0FiniteStageUniversalChartClass, pic0FiniteStageUniversalOverlapClass]
  calc
    _ = (pic0_sepClosed_representableBy (C := C)).2.homEquiv
        (Over.overSpecMap (pic0FiniteStageRestrictionLeft C U V) ≫
          Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 U.1) := by
      change (pic0TypeFunctor C).map
        (Over.overSpecMap (pic0FiniteStageRestrictionLeft C U V)).op
          ((pic0_sepClosed_representableBy (C := C)).2.homEquiv
            (Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 U.1)) = _
      exact ((pic0_sepClosed_representableBy (C := C)).2.homEquiv_comp
        (Over.overSpecMap (pic0FiniteStageRestrictionLeft C U V))
        (Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 U.1)).symm
    _ = _ := by
      apply congrArg (pic0_sepClosed_representableBy (C := C)).2.homEquiv
      rw [pic0FiniteStageRestrictionLeft_eq_resAlgHom]
      exact Over.fromSpecAffine_resAlgHom
        (pic0FiniteStageAffineOverlap_le_left C U V)

/-- The universal chart class restricts to the universal overlap class along the right
atlas leg. -/
theorem pic0FiniteStageUniversalChartClass_restrict_right
    (U V : Pic0FiniteStageChartIndex C) :
    pic0Map C (Over.overSpecMap (pic0FiniteStageRestrictionRight C U V))
        (pic0FiniteStageUniversalChartClass C V) =
      pic0FiniteStageUniversalOverlapClass C U V := by
  rw [pic0FiniteStageUniversalChartClass, pic0FiniteStageUniversalOverlapClass]
  calc
    _ = (pic0_sepClosed_representableBy (C := C)).2.homEquiv
        (Over.overSpecMap (pic0FiniteStageRestrictionRight C U V) ≫
          Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 V.1) := by
      change (pic0TypeFunctor C).map
        (Over.overSpecMap (pic0FiniteStageRestrictionRight C U V)).op
          ((pic0_sepClosed_representableBy (C := C)).2.homEquiv
            (Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 V.1)) = _
      exact ((pic0_sepClosed_representableBy (C := C)).2.homEquiv_comp
        (Over.overSpecMap (pic0FiniteStageRestrictionRight C U V))
        (Over.fromSpecAffine (pic0_sepClosed_representableBy (C := C)).1 V.1)).symm
    _ = _ := by
      apply congrArg (pic0_sepClosed_representableBy (C := C)).2.homEquiv
      rw [pic0FiniteStageRestrictionRight_eq_resAlgHom]
      exact Over.fromSpecAffine_resAlgHom
        (pic0FiniteStageAffineOverlap_le_right C U V)

/-- The finite atlas carries restrictions of one pinned universal Picard class, with both
overlap equations retained as data for finite-stage descent. -/
structure Pic0FiniteStageUniversalAtlasClass where
  universal : pic0Subgroup C (pic0_sepClosed_representableBy (C := C)).1
  chart : forall U : Pic0FiniteStageChartIndex C,
    pic0Subgroup C (overSpec k (Pic0FiniteStageChartRing C U))
  overlap : forall U V : Pic0FiniteStageChartIndex C,
    pic0Subgroup C (overSpec k (Pic0FiniteStageOverlapRing C U V))
  chart_eq : forall U, chart U = pic0FiniteStageUniversalChartClass C U
  overlap_eq : forall U V, overlap U V = pic0FiniteStageUniversalOverlapClass C U V
  restrict_left : forall U V,
    pic0Map C (Over.overSpecMap (pic0FiniteStageRestrictionLeft C U V)) (chart U) =
      overlap U V
  restrict_right : forall U V,
    pic0Map C (Over.overSpecMap (pic0FiniteStageRestrictionRight C U V)) (chart V) =
      overlap U V

/-- The canonical universal-class package on the chosen finite atlas. -/
noncomputable def pic0FiniteStageUniversalAtlasClass :
    Pic0FiniteStageUniversalAtlasClass C where
  universal := pic0SepClosedUniversalClass C
  chart := pic0FiniteStageUniversalChartClass C
  overlap := pic0FiniteStageUniversalOverlapClass C
  chart_eq := fun _ => rfl
  overlap_eq := fun _ _ => rfl
  restrict_left := pic0FiniteStageUniversalChartClass_restrict_left C
  restrict_right := pic0FiniteStageUniversalChartClass_restrict_right C

end

end AlgebraicGeometry
