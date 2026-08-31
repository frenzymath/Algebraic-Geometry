/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageEngine
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageRank
import AlgebraicJacobian.Cohomology.RankOneFamilyCertificates

/-!
# Rank-one certificates at the finite stage

The expensive engine, base-change comparison, and rank transport each live in their own opaque
declaration.  This file only packages those already checked interfaces.  The separate arbitrary
field degree law remains a downstream obligation of the divisor producer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance stageCertOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

namespace PicRankOneNoetherianStage

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
variable {P : PicRankOneLocalPresentation pi lam}

set_option maxHeartbeats 2000000 in
-- The certificate constructor only invokes opaque finite-stage interfaces.
set_option synthInstance.maxHeartbeats 800000 in
/-- Package the finite-stage rank-one cohomological certificates. -/
theorem certificates (S : PicRankOneNoetherianStage P)
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    RankOneFamilyCertificates (S.D0.baseChange S.A0) := by
  obtain ⟨h1, hfin, hproj⟩ := S.engine hpi
  exact ⟨h1, hfin, hproj, S.stageRank hpi⟩

end PicRankOneNoetherianStage

end AlgebraicGeometry
