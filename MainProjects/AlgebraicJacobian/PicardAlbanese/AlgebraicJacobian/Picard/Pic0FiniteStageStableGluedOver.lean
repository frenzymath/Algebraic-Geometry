/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage

/-!
# A stable finite-stage gluing over its field of definition

This is the scheme-level consumer of `Pic0FiniteStageStableGluePackage`.  It projects the
already selected map and slice object from the pinned affine presentation; it does not
reconstruct chart algebras, scalar towers, or a second multicoequalizer map.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageStableGluePackage

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-! The presentation already contains the selected map datum.  Keep this name as an
abbreviation for the map datum itself, rather than wrapping the same dependent value in a
second structure.  The exact `P.presentation.glueData` index is retained in the alias. -/
abbrev GluedOverData (P : Pic0FiniteStageStableGluePackage C F) :=
  AlgebraicJacobian.GluedMapData P.presentation.glueData
    (Spec (.of P.context.triple.N.1))

namespace GluedOverData

/-- Compatibility projection for clients that used the former wrapper field. -/
abbrev mapData {P : Pic0FiniteStageStableGluePackage C F}
    (Q : GluedOverData C P) : AlgebraicJacobian.GluedMapData P.presentation.glueData
      (Spec (.of P.context.triple.N.1)) :=
  Q

/-- The exact glue datum indexed by the packaged structure map. -/
def glueData {P : Pic0FiniteStageStableGluePackage C F}
    (_Q : GluedOverData C P) : Scheme.GlueData :=
  P.presentation.glueData

/-- The structure map carried by the packaged finite-stage gluing. -/
def map {P : Pic0FiniteStageStableGluePackage C F}
    (Q : GluedOverData C P) :
    P.presentation.glueData.glued ⟶ Spec (.of P.context.triple.N.1) :=
  AlgebraicJacobian.GluedMapData.map Q

/-- The packaged gluing as an object over its finite-stage field. -/
def asOver {P : Pic0FiniteStageStableGluePackage C F}
    (Q : GluedOverData C P) : Over (Spec (.of P.context.triple.N.1)) :=
  Over.mk Q.map

@[simp]
theorem asOver_hom {P : Pic0FiniteStageStableGluePackage C F}
    (Q : GluedOverData C P) : Q.asOver.hom = Q.map :=
  rfl

@[simp]
theorem chartMap_factor {P : Pic0FiniteStageStableGluePackage C F}
    (Q : GluedOverData C P) (i : P.presentation.glueData.J) :
    P.presentation.glueData.ι i ≫ Q.map = Q.mapData.chartMap i :=
  AlgebraicJacobian.GluedMapData.chartMap_factor Q i

end GluedOverData

/-- Project the stable gluing and map without reopening their construction. -/
def gluedOverData (P : Pic0FiniteStageStableGluePackage C F) : GluedOverData C P :=
  P.presentation.mapData

/-! Compatibility names for consumers that previously projected the legacy package's
`gluedOver`.  The stable object is definitionally the selected presentation's `Over`, so
these wrappers do not reconstruct any finite-stage data. -/

noncomputable def gluedOver (P : Pic0FiniteStageStableGluePackage C F) :
    Over (Spec (.of P.context.triple.N.1)) :=
  P.gluedOverData.asOver

@[simp]
theorem gluedOverData_map (P : Pic0FiniteStageStableGluePackage C F) :
    (P.gluedOverData C).map = P.presentation.map :=
  rfl

@[simp]
theorem gluedOverData_asOver (P : Pic0FiniteStageStableGluePackage C F) :
    (P.gluedOverData C).asOver = P.presentation.over :=
  rfl

@[simp]
theorem gluedOver_hom (P : Pic0FiniteStageStableGluePackage C F) :
    P.gluedOver.hom = P.presentation.map :=
  rfl

end Pic0FiniteStageStableGluePackage

end

end AlgebraicGeometry
