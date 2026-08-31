/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivRes

/-!
# The second universal-window fibre seam

`DivSchemeSeedUnivRes` records the span normal form for the first universal
window.  The target of the multiplication span needs the corresponding second
window statement, including the boundary-basis transport used by
`divUniversalSndWindow`; this file supplies that mirror without changing the
older import graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftSndRes :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
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

local notation "RZ" => DivCarveChartRing k
  (windowS_choice π hπ g • fiberWeilDivisor π)
  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j

set_option linter.unusedSectionVars false in
/-- The coordinate second universal window is the span of the compared
tautological second kernel. -/
private theorem divUniversalSnd_toSubmodule_eq_span_aux :
    (divUniversalSnd k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.span RZ
          (windowCompare (PairChartRing k g r₁ g r₂ i j) RZ ''
            ((pairTautSnd k g r₁ r₂ i j).toSubmodule :
              Set (TensorProduct k (PairChartRing k g r₁ g r₂ i j) (Fin r₂ → k)))) := by
  letI : Algebra (PairChartRing k g r₁ g r₂ i j) RZ :=
    (divCarveChartMk k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toAlgebra
  letI : IsScalarTower k (PairChartRing k g r₁ g r₂ i j) RZ :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq k _ _
  have h1 := Module.Grassmannian.map_toSubmodule
    (divCarveChartMk k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
    (pairTautSnd k g r₁ r₂ i j)
  refine ((show (divUniversalSnd k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule = _
    from h1).trans ?_)
  rw [Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- The second universal window in the transported `H_{M+s}` ambient is
the span of the compared tautological second-kernel generators. -/
theorem divUniversalSndWindow_toSubmodule_eq_span :
    (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.span RZ
          ((fun n =>
              LinearMap.baseChange RZ
                (b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g)).toLinearMap
                (windowCompare (PairChartRing k g r₁ g r₂ i j) RZ n)) ''
            ((pairTautSnd k g r₁ r₂ i j).toSubmodule :
              Set (TensorProduct k (PairChartRing k g r₁ g r₂ i j) (Fin r₂ → k)))) := by
  have h0 : (divUniversalSndWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.map
          (LinearMap.baseChange RZ
            (b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g)).toLinearMap)
          (divUniversalSnd k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule :=
    congrAmbient_toSubmodule
      (b₂.equivFun.symm.trans (seedWindowShiftEquiv C π hπ g))
      (divUniversalSnd k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
  rw [h0, divUniversalSnd_toSubmodule_eq_span_aux
      (C := C) (π := π) hπ g r₁ r₂ b₁ b₂ i j,
    Submodule.map_span, ← Set.image_comp]
  rfl

end AlgebraicGeometry
