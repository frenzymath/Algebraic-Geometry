/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleTransitionModels

/-!
# Stable context for finite-stage Picard gluing

`Pic0FiniteStageTransitionModelsData` fixes the chart and pair-transition models at one
finite stage.  The triple-transition producer then needs a comparison family for those
same models and produces a further finite stage.  This record keeps these dependent values
together, so gluing consumers can pass one context instead of repeatedly rebuilding the
comparison family and re-elaborating the nested tensor carriers.

The fields are ordinary data fields: no `letI` binders occur in the public type and this
file installs no global instances.
-/

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- All finite-stage data needed by the affine Picard gluing construction.

`models` fixes the common stages, presentations, maps, and pair-transition compatibilities.
`Q` fixes the scalar-extension comparison for every cyclic triple.  `triple` stores the
next finite stage of cyclic transitions together with its comparison squares.
-/
structure Pic0FiniteStageGlueContext
    (F : Type u) [Field F] [Algebra F k] [Algebra.IsAlgebraic F k] where
  models : Pic0FiniteStageTransitionModelsData C F
  Q : ∀ q : Pic0FiniteStageTripleTransitionIndex C,
    k ⊗[models.M.1]
        Pic0FiniteStageTripleTransitionModelTarget
          C models.L models.n models.m models.relation models.M models.mapM q ≃ₐ[k]
      Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2
  triple : Pic0FiniteStageTripleTransitionFamilyData
    C models.L models.n models.m models.relation models.M models.mapM Q

namespace Pic0FiniteStageGlueContext

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-! ## Transparent projections -/

def L (D : Pic0FiniteStageGlueContext C F) := D.models.L
def n (D : Pic0FiniteStageGlueContext C F) := D.models.n
def m (D : Pic0FiniteStageGlueContext C F) := D.models.m
def relation (D : Pic0FiniteStageGlueContext C F) := D.models.relation
def e (D : Pic0FiniteStageGlueContext C F) := D.models.e
def M (D : Pic0FiniteStageGlueContext C F) := D.models.M
def mapM (D : Pic0FiniteStageGlueContext C F) := D.models.mapM
def N (D : Pic0FiniteStageGlueContext C F) := D.triple.N
def thetaN (D : Pic0FiniteStageGlueContext C F) := D.triple.thetaN

/-! ## Stored compatibility certificates -/

@[simp]
theorem comparison
    (D : Pic0FiniteStageGlueContext C F)
    (q : Pic0FiniteStageMapIndex C) :
    Pic0FiniteStageTransitionModelComparison C D.L D.n D.m D.relation D.e D.M D.mapM q :=
  D.models.comparison q

@[simp]
theorem openImmersion
    (D : Pic0FiniteStageGlueContext C F)
    (i : Pic0FiniteStageRestrictionIndex C) :
    Pic0FiniteStageTransitionOpenImmersion C D.L D.n D.m D.relation D.M D.mapM i :=
  D.models.openImmersion i

@[simp]
theorem inverse
    (D : Pic0FiniteStageGlueContext C F)
    (U V : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageTransitionInverse C D.L D.n D.m D.relation D.M D.mapM U V :=
  D.models.inverse U V

set_option synthInstance.maxHeartbeats 400000 in
-- The dependent triple family unfolds two tensor-model towers in this result type.
set_option maxHeartbeats 3200000 in
@[simp]
theorem tripleComparison
    (D : Pic0FiniteStageGlueContext C F)
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    Pic0FiniteStageTripleTransitionFamilyComparison
      C D.L D.n D.m D.relation D.M D.mapM D.Q D.triple.N p (D.triple.thetaN p) :=
  D.triple.comparison p

end Pic0FiniteStageGlueContext

end

end AlgebraicGeometry
