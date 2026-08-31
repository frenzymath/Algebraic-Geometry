/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageAdmissibility
import AlgebraicJacobian.Picard.Pic0RankOneDatumGluedDivisor

/-!
# A glued divisor at the finite rank-one stage

The admissibility certificate for a Noetherian rank-one stage supplies exactly the fibrewise
vanishing and degree hypotheses of the datum-level glued-divisor theorem.  This module keeps that
keystone application opaque before the divisor is transported to the presentation carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance stageGluedOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

namespace PicRankOneNoetherianStage

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
variable {P : PicRankOneLocalPresentation pi lam}

/-- The finite stage carries a glued divisor whose relative Picard class is its descended datum. -/
theorem exists_glued_divFamZarAff (S : PicRankOneNoetherianStage P)
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    ∃ F : DivFamZarAff C S.A0 (genus C),
      relPicMk C (overSpec k S.A0) F.picClass =
        relPicMk C (overSpec k S.A0)
          (S.D0.baseChange S.A0).cechPicClass := by
  letI : IsNoetherianRing S.A0 := S.hAnoeth
  have h := S.admissibility hpi
  exact (S.D0.baseChange S.A0).exists_glued_divFamZarAff_of_admissible_fibre
    hpi h.h1 h.degree

end PicRankOneNoetherianStage

end AlgebraicGeometry
