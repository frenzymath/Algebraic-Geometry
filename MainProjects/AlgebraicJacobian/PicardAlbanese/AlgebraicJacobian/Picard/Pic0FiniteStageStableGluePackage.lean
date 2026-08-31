/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGlueDataAssembly

/-!
# Stable finite-stage gluing boundary

The historical `Pic0FiniteStageGluePackage` repeats every finite-stage witness as a
field and reconstructs the affine gluing presentation from those fields.  This facade
stores only the canonical context and derives its presentation at one opaque boundary.
Consequently every stable consumer sees the same witness-bearing presentation; a caller
cannot pair a context with an unrelated presentation that merely shares its coefficient
ring.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- A finite-stage context with a presentation derived from that context.

Unlike the legacy package, this boundary has no raw stage parameters and no
instance-producing `let` expressions in its public fields.
-/
structure Pic0FiniteStageStableGluePackage
    (F : Type u) [Field F] [Algebra F k] [Algebra.IsAlgebraic F k] where
  context : Pic0FiniteStageCanonicalGlueContext C F

namespace Pic0FiniteStageStableGluePackage

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-- Build the stable package from its canonical context.

The presentation is derived below, so this constructor cannot accept a value whose
glue datum or map is disconnected from the context. -/
noncomputable def ofContext
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    : Pic0FiniteStageStableGluePackage C F :=
  { context := D }

/-- Checked migration constructor for callers that already selected a presentation.

The equality hypothesis is intentional: the former two-field constructor accepted a
presentation sharing only the coefficient ring, which allowed unrelated glue data to be
paired with a context.  A caller can retain a selected presentation only after certifying
that it is the canonical assembly for `D`. -/
noncomputable def ofContextWithPresentation
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    (P : AlgebraicJacobian.AffineRingGluePresentation D.triple.N.1)
    (_hP : P = pic0FiniteStageAffineRingGluePresentation_of_canonical_context C D) :
    Pic0FiniteStageStableGluePackage C F :=
  { context := D }

/-! Keep the expensive canonical assembly opaque to downstream elaboration.  The witness
also retains a named equality so clients can use canonicality without unfolding the tensor
construction. -/
noncomputable opaque presentationWitness
    (P : Pic0FiniteStageStableGluePackage C F) :
    { A : AlgebraicJacobian.AffineRingGluePresentation P.context.triple.N.1 //
      A = pic0FiniteStageAffineRingGluePresentation_of_canonical_context C P.context } :=
  ⟨pic0FiniteStageAffineRingGluePresentation_of_canonical_context C P.context, rfl⟩

/-- The presentation selected by the canonical context. -/
noncomputable def presentation
    (P : Pic0FiniteStageStableGluePackage C F) :
    AlgebraicJacobian.AffineRingGluePresentation P.context.triple.N.1 :=
  (presentationWitness C P).1

/-- The stable presentation is definitionally the canonical context assembly, exposed as a
rewrite theorem instead of requiring clients to unfold the opaque witness. -/
theorem presentation_spec
    (P : Pic0FiniteStageStableGluePackage C F) :
    P.presentation = pic0FiniteStageAffineRingGluePresentation_of_canonical_context C P.context :=
  (presentationWitness C P).2

/-- Named compatibility alias for clients that need to rewrite to the canonical assembly. -/
theorem presentation_eq
    (P : Pic0FiniteStageStableGluePackage C F) :
    P.presentation = pic0FiniteStageAffineRingGluePresentation_of_canonical_context C P.context :=
  P.presentation_spec C

@[simp]
theorem ofContextWithPresentation_presentation
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    (P : AlgebraicJacobian.AffineRingGluePresentation D.triple.N.1)
    (hP : P = pic0FiniteStageAffineRingGluePresentation_of_canonical_context C D) :
    (ofContextWithPresentation C D P hP).presentation = P := by
  exact (presentation_spec C _).trans hP.symm

/-! The following accessors are ordinary definitions rather than reducible aliases.
This keeps expensive tensor carriers behind the package boundary. -/

def models (P : Pic0FiniteStageStableGluePackage C F) :
    Pic0FiniteStageTransitionModelsData C F :=
  P.context.models

def triple (P : Pic0FiniteStageStableGluePackage C F) :
    Pic0FiniteStageTripleTransitionFamilyData
      C P.context.models.L P.context.models.n P.context.models.m
      P.context.models.relation P.context.models.M P.context.models.mapM
        P.context.Q :=
  P.context.triple

def L (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.L
def n (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.n
def m (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.m
def relation (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.relation
def e (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.e
def M (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.M
def mapM (P : Pic0FiniteStageStableGluePackage C F) := P.context.models.mapM
def N (P : Pic0FiniteStageStableGluePackage C F) := P.context.triple.N
def thetaN (P : Pic0FiniteStageStableGluePackage C F) := P.context.triple.thetaN

def glueData (P : Pic0FiniteStageStableGluePackage C F) : Scheme.GlueData :=
  P.presentation.glueData

def mapData (P : Pic0FiniteStageStableGluePackage C F) :
    AlgebraicJacobian.GluedMapData P.presentation.glueData
      (Spec (.of P.context.triple.N.1)) :=
  P.presentation.mapData

def gluedMap (P : Pic0FiniteStageStableGluePackage C F) :
    P.presentation.glueData.glued ⟶ Spec (.of P.context.triple.N.1) :=
  P.presentation.map

def asOver (P : Pic0FiniteStageStableGluePackage C F) :
    Over (Spec (.of P.context.triple.N.1)) :=
  P.presentation.over

@[simp]
theorem chartMap_factor
    (P : Pic0FiniteStageStableGluePackage C F)
    (i : P.presentation.glueData.J) :
    P.presentation.glueData.ι i ≫ P.gluedMap = P.mapData.chartMap i :=
  P.presentation.chartMap_factor i

@[simp]
theorem comparison
    (P : Pic0FiniteStageStableGluePackage C F)
    (q : Pic0FiniteStageMapIndex C) :
    Pic0FiniteStageTransitionModelComparison C
      P.context.models.L P.context.models.n P.context.models.m
      P.context.models.relation P.context.models.e P.context.models.M
      P.context.models.mapM q :=
  P.context.models.comparison q

@[simp]
theorem openImmersion
    (P : Pic0FiniteStageStableGluePackage C F)
    (i : Pic0FiniteStageRestrictionIndex C) :
    Pic0FiniteStageTransitionOpenImmersion C
      P.context.models.L P.context.models.n P.context.models.m
      P.context.models.relation P.context.models.M P.context.models.mapM i :=
  P.context.models.openImmersion i

end Pic0FiniteStageStableGluePackage

end

end AlgebraicGeometry
