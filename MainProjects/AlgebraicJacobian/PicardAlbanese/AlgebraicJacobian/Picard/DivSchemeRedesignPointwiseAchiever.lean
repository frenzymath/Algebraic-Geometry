/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignAchiever
import AlgebraicJacobian.Picard.DivSchemeFibrePoint
import AlgebraicJacobian.Picard.DivSchemeSeedUnivGen
import AlgebraicJacobian.Picard.DivSchemeRedesignCarvePin

/-!
# The pointwise universal achiever over the total seed curve

The seed-prime achiever is stated on a fibre curve over `κ(p)`.  The seed, however, is
chosen pointwise on the total curve over the carve ring.  This file supplies the small
reindexing bridge between the two statements: for a total point `z`, set
`p := relCurveBasePoint C RZ z` and `z_fib := relCurveResiduePoint C RZ z`, then apply the
seed-prime theorem at `(p, z_fib)`.

There is one important topological qualification.  A total point can be the generic point
of a vertical fibre, so `z_fib ≠ genericPoint (relCurve C κ(p))` is not true for every total
point.  Accordingly the main theorem takes that hypothesis explicitly, while the companion
dichotomy is unconditional and exposes the generic-fibre branch to downstream code.
The old seed is left untouched.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

namespace PointwiseAchiever

section SeedContext

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftPointwise : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

-- The fibre-curve instances used by the seed-prime theorem are reconstructed locally here
-- because its original declarations are section-local.
noncomputable local instance instIsIntegralRelCurvePointwise (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePointwise (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePointwise (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurvePointwise (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurvePointwise (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurvePointwise (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

local notation "RZ" => seedChartRing C hπ g r₁ r₂ b₁ b₂ i j

/-! ## The total-point achiever -/

-- Reconstructing the native tower `k → RZ → κ(p)` while elaborating the fibre window
-- exceeds the default instance and recursion budgets.
set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The universal first fibre window at the base point of `z` is nonzero. -/
noncomputable def pointwiseFibreWindowNonzero
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ) :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j
      (relCurveBasePoint C RZ z).asIdeal.ResidueField ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ :=
    exists_mem_ne_zero_divUniversalFibreKM_seedPrime C hπ g r₁ r₂ b₁ b₂ i j hO hχ
      (relCurveBasePoint C RZ z)
  intro hbot
  apply hf0
  rw [hbot, Submodule.mem_bot] at hf
  exact hf

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The pointwise first fibre window is nonzero at curve parameter `gamma ≤ g`. -/
noncomputable def pointwiseFibreWindowNonzero_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ) :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j
      (relCurveBasePoint C RZ z).asIdeal.ResidueField ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ :=
    exists_mem_ne_zero_divUniversalFibreKM_seedPrime_at
      C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ (relCurveBasePoint C RZ z)
  intro hbot
  apply hf0
  rw [hbot, Submodule.mem_bot] at hf
  exact hf

-- The achiever theorem reconstructs the same residue-field tower and large window types.
set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- At a non-generic residue-fibre point, choose the full landed achiever witness. -/
noncomputable def pointwiseAchiever
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C RZ)
    (hzfib : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :=
  exists_relThetaWindowEquiv_mem_divUniversalSeedK_achieves_seedPrime
    C hπ g r₁ r₂ b₁ b₂ i j hO hχ (relCurveBasePoint C RZ z)
      (pointwiseFibreWindowNonzero C hπ g r₁ r₂ b₁ b₂ i j hO hχ z) hzfib

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- The pointwise achiever at independent curve parameter `gamma ≤ g`. -/
noncomputable def pointwiseAchiever_at {gamma : ℕ}
    (hgamma : gamma ≤ g)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C RZ)
    (hzfib : relCurveResiduePoint C RZ z ≠
      genericPoint (relCurve C (relCurveBasePoint C RZ z).asIdeal.ResidueField)) :=
  exists_relThetaWindowEquiv_mem_divUniversalSeedK_achieves_seedPrime_at
    C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ (relCurveBasePoint C RZ z)
      (pointwiseFibreWindowNonzero_at C hπ g r₁ r₂ b₁ b₂ i j hgamma hχ z) hzfib

end SeedContext

end PointwiseAchiever

end AlgebraicGeometry
