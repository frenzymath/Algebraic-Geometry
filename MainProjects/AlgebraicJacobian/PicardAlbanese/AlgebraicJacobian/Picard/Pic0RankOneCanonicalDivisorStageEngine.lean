/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneCanonicalDivisorStageData

/-!
# Rigid-engine certificates at the finite stage
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

noncomputable local instance stageEngineOverCleft :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

namespace PicRankOneNoetherianStage

variable {A : Type u} [CommRing A] [Algebra k A]
variable {lam : picDegLayer C (genus C : ℤ) (overSpec k A)}
variable {P : PicRankOneLocalPresentation pi lam}

set_option maxHeartbeats 2000000 in
-- The nested subalgebra datum makes the rigid engine expand two scalar towers.
set_option synthInstance.maxHeartbeats 800000 in
-- The same expansion requires a larger deterministic typeclass budget.
/-- The finite-stage rigid engine gives `H¹` vanishing and finite-projective `H⁰`. -/
theorem engine (S : PicRankOneNoetherianStage P)
    (hpi : pi ≫ P1.structureMap k = C.hom) :
    Subsingleton (Sheaf.HModule (S.D0.baseChange S.A0).sheaf 1) ∧
      Module.Finite S.A0 (Sheaf.HModule (S.D0.baseChange S.A0).sheaf 0) ∧
      Module.Projective S.A0 (Sheaf.HModule (S.D0.baseChange S.A0).sheaf 0) := by
  letI : IsNoetherianRing S.A0 := S.hAnoeth
  letI : Subsingleton (datumPair (S.D0.baseChange S.A0)).H1 := S.hpair
  have hfib : ∀ p : PrimeSpectrum S.A0,
      Subsingleton ((datumPair (S.D0.baseChange S.A0)).H1 ⊗[S.A0]
        p.asIdeal.ResidueField) :=
    fun _ => inferInstance
  exact datumRigidEngine (S.D0.baseChange S.A0) hpi hfib

end PicRankOneNoetherianStage

end AlgebraicGeometry
