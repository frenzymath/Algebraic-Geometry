/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage

/-!
# Stable finite-stage gluing producer compatibility import

The stable package is now constructed from a canonical context alone; its presentation is
derived by the package boundary.  This module remains as a compatibility import for clients
that used to import a separate producer module.  `ofContextMapData` below keeps the historical
name but requires an explicit equality certificate, so an arbitrary map datum cannot be paired
with an unrelated context.
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

/-- Checked compatibility adapter for the former map-data constructor.

The map datum is accepted only when it is the presentation selected by the canonical context;
the proof is kept explicit so this adapter cannot silently discard a caller's data. -/
noncomputable def ofContextMapData
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    {G : Scheme.GlueData}
    (M : AlgebraicJacobian.GluedMapData G (Spec (.of D.triple.N.1)))
    (hM : AlgebraicJacobian.AffineRingGluePresentation.ofMapData M =
      pic0FiniteStageAffineRingGluePresentation_of_canonical_context C D) :
    Pic0FiniteStageStableGluePackage C F :=
  ofContextWithPresentation C D
    (AlgebraicJacobian.AffineRingGluePresentation.ofMapData M) hM

@[simp]
theorem ofContextMapData_context
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    {G : Scheme.GlueData}
    (M : AlgebraicJacobian.GluedMapData G (Spec (.of D.triple.N.1)))
    (hM : AlgebraicJacobian.AffineRingGluePresentation.ofMapData M =
      pic0FiniteStageAffineRingGluePresentation_of_canonical_context C D) :
    (ofContextMapData C D M hM).context = D :=
  rfl

@[simp]
theorem ofContextMapData_presentation
    (D : Pic0FiniteStageCanonicalGlueContext C F)
    {G : Scheme.GlueData}
    (M : AlgebraicJacobian.GluedMapData G (Spec (.of D.triple.N.1)))
    (hM : AlgebraicJacobian.AffineRingGluePresentation.ofMapData M =
      pic0FiniteStageAffineRingGluePresentation_of_canonical_context C D) :
    (ofContextMapData C D M hM).presentation =
      AlgebraicJacobian.AffineRingGluePresentation.ofMapData M :=
  ofContextWithPresentation_presentation C D
    (AlgebraicJacobian.AffineRingGluePresentation.ofMapData M) hM

end Pic0FiniteStageStableGluePackage

end

end AlgebraicGeometry
