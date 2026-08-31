/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluePackage
import AlgebraicJacobian.Descent.GluedMapData

/-!
# The finite-stage Picard glue as a scheme over its field of definition

The finite-stage glue package already contains affine algebras over its final finite
subextension `P.N.1`.  Their structure maps agree on overlaps, so they descend to the
glued scheme.  This retains the finite-stage object over `Spec P.N.1`, which is the
object-level input for the scalar-extension comparison with the separably closed atlas.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

/-! The dependent scalar towers are assembled by `P.presentation` in the package module.
This projection keeps the public map type aligned with the presentation's glue datum and
avoids rebuilding those towers in every consumer. -/
noncomputable def gluedMapData
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    AlgebraicJacobian.GluedMapData P.glueData (Spec (.of P.N.1)) :=
  P.presentation.mapData

set_option maxHeartbeats 12800000 in
-- The projection is definitionally the selected map datum.
@[simp]
theorem presentation_mapData
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    P.presentation.mapData = P.gluedMapData :=
  rfl

/-! The old wrapper stored `GluedMapData P.glueData` directly.  That repeated the
dependent glue construction at every use site.  Reuse the pinned presentation instead:
the carrier and map are now indexed by one selected value, with no producer proofs in the
consumer-facing type. -/
abbrev GluedOverData
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :=
  AlgebraicJacobian.AffineRingGluePresentation P.N.1

namespace GluedOverData

/-- The structure map carried by the selected presentation. -/
def map
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    {P : Pic0FiniteStageGluePackage C F}
    (Q : GluedOverData C P) : Q.glueData.glued ⟶ Spec (.of P.N.1) :=
  AlgebraicJacobian.AffineRingGluePresentation.map Q

/-- The selected glue as an object of the slice over its finite-stage field. -/
def «over»
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    {P : Pic0FiniteStageGluePackage C F}
    (Q : GluedOverData C P) : Over (Spec (.of P.N.1)) :=
  AlgebraicJacobian.AffineRingGluePresentation.over Q

@[simp]
theorem map_eq
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    {P : Pic0FiniteStageGluePackage C F}
    (Q : GluedOverData C P) : Q.map = Q.mapData.map :=
  rfl

/-- The chart-factor equation exposed without opening the generic map package. -/
theorem chartMap_factor
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    {P : Pic0FiniteStageGluePackage C F}
    (Q : GluedOverData C P) (U : Q.glueData.J) :
    Q.glueData.ι U ≫ Q.map = Q.mapData.chartMap U := by
  exact AlgebraicJacobian.AffineRingGluePresentation.chartMap_factor Q U

end GluedOverData

/-- The canonical finite-stage glue package, built once from `P.gluedMapData`. -/
noncomputable def gluedOverData
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) : GluedOverData C P :=
  P.presentation

/-- The structure map from the finite-stage glued scheme to its field of definition. -/
noncomputable def gluedMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    P.glueData.glued ⟶ Spec (.of P.N.1) :=
  P.presentation.map

@[simp]
theorem gluedMap_presentation
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) :
    P.gluedMap = P.presentation.map :=
  rfl

/-! The chart maps are exported as named data, rather than as an `algebraMap` expression
with instances inferred at each call site.  The carrier is a dependent tensor product, so
reconstructing its `CommRing`/`Algebra` witnesses changes the elaborated morphism even when
the printed types agree. -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 12800000 in
/-- The pinned structure map from a finite-stage chart to the field of definition. -/
noncomputable def chartBaseChangeMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    P.glueData.U U ⟶ Spec (.of P.N.1) :=
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U
  letI : Algebra P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U
  Spec.map (CommRingCat.ofHom
    (@algebraMap P.N.1
      (Pic0FiniteStageChartBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U)
      (inferInstance : CommSemiring P.N.1)
      (pic0FiniteStageChartBaseChangeRingCommRing
        C P.L P.n P.m P.relation P.M P.N U).toSemiring
      (pic0FiniteStageChartBaseChangeRingAlgebra
        C P.L P.n P.m P.relation P.M P.N U)))

@[simp]
theorem gluedMapData_chartMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U : Pic0FiniteStageChartIndex C) :
    P.gluedMapData.chartMap U = chartBaseChangeMap C P U := by
  rfl

/-- The finite-stage Picard glue, retained over the finite field `P.N.1`. -/
noncomputable def gluedOver
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F) : Over (Spec (.of P.N.1)) :=
  Over.mk P.gluedMap

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
