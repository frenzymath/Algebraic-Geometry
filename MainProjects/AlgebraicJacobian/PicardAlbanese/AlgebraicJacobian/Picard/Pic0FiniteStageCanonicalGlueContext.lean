/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGlueContext
import AlgebraicJacobian.Picard.Pic0FiniteStageTransportedTripleTransitionFace

/-!
# Canonical finite-stage glue contexts

The general glue context keeps an explicit comparison family because it is useful while
assembling finite-stage data. A face consumer, however, needs the concrete comparison
family attached to the selected transition models. This module provides that boundary
without changing the legacy context: the family is fixed in the type of the triple data,
so a separately reconstructed comparison cannot silently enter a downstream statement.
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

namespace Pic0FiniteStageGlueContext

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-! ## The canonical comparison family -/

/- The family is kept behind an opaque witness so elaborating a context never unfolds the
dependent tensor-model comparison.  The witness also stores the specification equation; this
is the proof-level bridge needed by consumers that use the model-level face theorem.
-/
noncomputable opaque canonicalComparisonWitness
    (D : Pic0FiniteStageTransitionModelsData C F) :
    {Q : ∀ q : Pic0FiniteStageTripleTransitionIndex C,
      k ⊗[D.M.1] Pic0FiniteStageTripleTransitionModelTarget
          C D.L D.n D.m D.relation D.M D.mapM q ≃ₐ[k]
        Pic0FiniteStageTripleRing C q.1 q.2.1 q.2.2 //
      Q = pic0FiniteStageTripleModelComparisonFamily C D.L D.n D.m D.relation
        D.e D.M D.mapM D.comparison} :=
  ⟨pic0FiniteStageTripleModelComparisonFamily C D.L D.n D.m D.relation
      D.e D.M D.mapM D.comparison, rfl⟩

/-- The comparison family determined by one bundled transition-model datum. -/
noncomputable def canonicalComparisonFamily
    (D : Pic0FiniteStageTransitionModelsData C F) :=
  (canonicalComparisonWitness C D).1

@[simp]
theorem canonicalComparisonFamily_spec
    (D : Pic0FiniteStageTransitionModelsData C F) :
    canonicalComparisonFamily C D =
      pic0FiniteStageTripleModelComparisonFamily C D.L D.n D.m D.relation
        D.e D.M D.mapM D.comparison :=
  (canonicalComparisonWitness C D).2

/-! ## Canonical constructor -/

/-- Build a legacy-compatible context with the comparison family pinned to `D`. -/
def ofCanonical
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM (canonicalComparisonFamily C D)) :
    Pic0FiniteStageGlueContext C F :=
  { models := D
    Q := canonicalComparisonFamily C D
    triple := T }

@[simp]
theorem ofCanonical_models
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM (canonicalComparisonFamily C D)) :
    (ofCanonical C D T).models = D :=
  rfl

@[simp]
theorem ofCanonical_Q
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM (canonicalComparisonFamily C D)) :
    (ofCanonical C D T).Q = canonicalComparisonFamily C D :=
  rfl

@[simp]
theorem ofCanonical_triple
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM (canonicalComparisonFamily C D)) :
    (ofCanonical C D T).triple = T :=
  rfl

end Pic0FiniteStageGlueContext

/-! ## Canonical contexts -/

/-- A finite-stage glue context whose stored comparison family is the one determined by its
transition models.

The general `Pic0FiniteStageGlueContext` remains useful while assembling arbitrary descended
data.  Face and gluing consumers should use this wrapper: `q_spec` prevents the triple-family
certificate from being silently disconnected from the model comparison used by the face
theorem.
-/
structure Pic0FiniteStageCanonicalGlueContext
    (F : Type u) [Field F] [Algebra F k] [Algebra.IsAlgebraic F k] where
  context : Pic0FiniteStageGlueContext C F
  q_spec : context.Q =
    Pic0FiniteStageGlueContext.canonicalComparisonFamily C context.models

namespace Pic0FiniteStageCanonicalGlueContext

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-- Retain a general context after supplying the missing canonicality invariant. -/
def ofContext
    (D : Pic0FiniteStageGlueContext C F)
    (hQ : D.Q = Pic0FiniteStageGlueContext.canonicalComparisonFamily C D.models) :
    Pic0FiniteStageCanonicalGlueContext C F :=
  { context := D, q_spec := hQ }

/-! The family and its dependent triple data are accepted together at this boundary.  In
contrast to transporting a record with `hQ ▸ T`, this constructor preserves the selected
family in the context and uses the equality only for the small canonicality field. -/
def ofModelsWithComparison
    (D : Pic0FiniteStageTransitionModelsData C F)
    (Q : ∀ p : Pic0FiniteStageTripleTransitionIndex C,
      k ⊗[D.M.1]
          Pic0FiniteStageTripleTransitionModelTarget
            C D.L D.n D.m D.relation D.M D.mapM p ≃ₐ[k]
        Pic0FiniteStageTripleRing C p.1 p.2.1 p.2.2)
    (T : Pic0FiniteStageTripleTransitionFamilyData
      C D.L D.n D.m D.relation D.M D.mapM Q)
    (hQ : Q = Pic0FiniteStageGlueContext.canonicalComparisonFamily C D) :
    Pic0FiniteStageCanonicalGlueContext C F :=
  { context := { models := D, Q := Q, triple := T }
    q_spec := hQ }

/-- Bundle model and triple data without forgetting that the triple family uses the canonical
comparison attached to those models. -/
def ofModels
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM
        (Pic0FiniteStageGlueContext.canonicalComparisonFamily C D)) :
    Pic0FiniteStageCanonicalGlueContext C F :=
  { context := Pic0FiniteStageGlueContext.ofCanonical C D T
    q_spec := rfl }

/-- Forget canonicality only when calling a legacy general-context API. -/
def toGlueContext (D : Pic0FiniteStageCanonicalGlueContext C F) :
    Pic0FiniteStageGlueContext C F :=
  D.context

/-- The transition models selected by a canonical context. -/
def models (D : Pic0FiniteStageCanonicalGlueContext C F) :=
  D.context.models

/-- The triple-transition family selected by a canonical context. -/
def triple (D : Pic0FiniteStageCanonicalGlueContext C F) :=
  D.context.triple

/-- The comparison family stored by the underlying general context. -/
def Q (D : Pic0FiniteStageCanonicalGlueContext C F) :=
  D.context.Q

/-- The final finite scalar stage selected by a canonical context. -/
def N (D : Pic0FiniteStageCanonicalGlueContext C F) :=
  D.context.triple.N

/-- The descended cyclic transition family at the final scalar stage. -/
def thetaN (D : Pic0FiniteStageCanonicalGlueContext C F) :=
  D.context.triple.thetaN

@[simp]
theorem ofModels_models
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM
        (Pic0FiniteStageGlueContext.canonicalComparisonFamily C D)) :
    (ofModels C D T).models = D :=
  rfl

@[simp]
theorem ofModels_triple
    (D : Pic0FiniteStageTransitionModelsData C F)
    (T : Pic0FiniteStageTripleTransitionFamilyData C
      D.L D.n D.m D.relation D.M D.mapM
        (Pic0FiniteStageGlueContext.canonicalComparisonFamily C D)) :
    (ofModels C D T).triple = T :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Normalizing the dependent family unfolds tensor models in both comparison directions.
set_option maxHeartbeats 6400000 in
/-- The stored triple-transition certificate, normalized to the concrete comparison family
used by the model-level face theorem. -/
theorem comparison
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    Pic0FiniteStageTripleTransitionFamilyComparison C
      D.context.models.L D.context.models.n D.context.models.m
      D.context.models.relation D.context.models.M D.context.models.mapM
      (pic0FiniteStageTripleModelComparisonFamily C
        D.context.models.L D.context.models.n D.context.models.m
        D.context.models.relation D.context.models.e D.context.models.M
        D.context.models.mapM D.context.models.comparison)
      D.context.triple.N p (D.context.triple.thetaN p) := by
  rw [← Pic0FiniteStageGlueContext.canonicalComparisonFamily_spec C D.context.models,
    ← D.q_spec]
  exact D.context.triple.comparison p

set_option synthInstance.maxHeartbeats 400000 in
-- The explicit legacy square repeats the dependent source and target tensor carriers.
set_option maxHeartbeats 6400000 in
/-- The concrete comparison square expected by the legacy affine face proof, obtained from
the canonical context rather than from a separately supplied certificate. -/
theorem comparison_of_models
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    (p : Pic0FiniteStageTripleTransitionIndex C) :
    (Algebra.TensorProduct.map D.context.triple.N.1.val
        (AlgHom.id D.context.models.M.1
          (Pic0FiniteStageTripleTransitionModelTarget C
            D.context.models.L D.context.models.n D.context.models.m
            D.context.models.relation D.context.models.M D.context.models.mapM p))).comp
        ((D.context.triple.thetaN p).restrictScalars D.context.models.M.1) =
      ((pic0FiniteStageTransportedTripleTransitionOfModels C
        D.context.models.L D.context.models.n D.context.models.m
        D.context.models.relation D.context.models.e D.context.models.M
        D.context.models.mapM D.context.models.comparison
        p.1 p.2.1 p.2.2).restrictScalars D.context.models.M.1).comp
        (Algebra.TensorProduct.map D.context.triple.N.1.val
          (AlgHom.id D.context.models.M.1
            (Pic0FiniteStageTripleTransitionModelSource C
              D.context.models.L D.context.models.n D.context.models.m
              D.context.models.relation D.context.models.M D.context.models.mapM p))) := by
  change Pic0FiniteStageTripleTransitionFamilyComparison C
    D.context.models.L D.context.models.n D.context.models.m
    D.context.models.relation D.context.models.M D.context.models.mapM
    (pic0FiniteStageTripleModelComparisonFamily C
      D.context.models.L D.context.models.n D.context.models.m
      D.context.models.relation D.context.models.e D.context.models.M
      D.context.models.mapM D.context.models.comparison)
    D.context.triple.N p (D.context.triple.thetaN p)
  exact D.comparison C p

end Pic0FiniteStageCanonicalGlueContext

end

end AlgebraicGeometry
