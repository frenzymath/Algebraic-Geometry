/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageH0
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorRank

/-!
# Rank one at the finite stage
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

noncomputable local instance stageRankOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

namespace PicRankOneNoetherianStage

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
variable {P : PicRankOneLocalPresentation pi lam}

set_option maxHeartbeats 2000000 in
-- Dense image of the nested coefficient map transports the presentation's rank-one law.
set_option synthInstance.maxHeartbeats 800000 in
/-- The finite-stage datum has stalk-rank-one `H⁰`. -/
theorem stageRank (S : PicRankOneNoetherianStage P)
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    ∀ p : PrimeSpectrum S.A0,
      Module.rankAtStalk (Sheaf.HModule (S.D0.baseChange S.A0).sheaf 0) p = 1 := by
  letI : IsNoetherianRing S.A0 := S.hAnoeth
  obtain ⟨-, hfin, hproj⟩ := S.engine hpi
  letI := hfin
  letI := hproj
  have hinj : Function.Injective (algebraMap S.A0 P.cover.Carrier) :=
    fun x y hxy => Subtype.ext hxy
  exact rankAtStalk_eq_one_of_injective_baseChange
    (R := S.A0) (S := P.cover.Carrier)
    (M := Sheaf.HModule (S.D0.baseChange S.A0).sheaf 0)
    (N := Sheaf.HModule P.datum.sheaf 0)
    hinj (S.h0BaseChangeIso) P.h0_rank_one

end PicRankOneNoetherianStage

end AlgebraicGeometry
