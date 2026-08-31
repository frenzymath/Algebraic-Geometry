/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageEngine

/-!
# The finite-stage H⁰ comparison
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance stageH0OverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

namespace PicRankOneNoetherianStage

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
variable {P : PicRankOneLocalPresentation pi lam}

set_option maxHeartbeats 2000000 in
-- The dependent datum equality crosses both nested subalgebra scalar towers.
set_option synthInstance.maxHeartbeats 800000 in
-- Resolving the induced module structures needs the same enlarged synthesis budget.
/-- The stage H⁰ module becomes the presentation H⁰ module after scalar extension. -/
noncomputable def h0BaseChangeIso (S : PicRankOneNoetherianStage P) :
    P.cover.Carrier ⊗[S.A0]
        (Sheaf.HModule (S.D0.baseChange S.A0).sheaf 0) ≃ₗ[P.cover.Carrier]
      Sheaf.HModule P.datum.sheaf 0 := by
  exact ((S.D0.baseChange S.A0).datumH0BaseChange P.cover.Carrier S.hpair).trans
    (Sheaf.HModule.mapEquiv
      (eqToIso (congrArg
        (fun E : BasicOpenCocycleDatum C P.cover.Carrier pi => E.sheaf) S.hbase)) 0)

end PicRankOneNoetherianStage

end AlgebraicGeometry
