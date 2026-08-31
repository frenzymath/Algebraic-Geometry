/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorSheaf

/-!
# Composition of bounded-order inclusions

The inclusions between the sheaves `𝒪(D)` are functorial in the divisor
inequality.  This file records the presheaf and sheaf composition laws.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

lemma divisorPresheafLE_comp {D₀ D₁ D₂ : CurveDivisor k X}
    (h₀₁ : D₀ ≤ D₁) (h₁₂ : D₁ ≤ D₂) :
    divisorPresheafLE (le_trans h₀₁ h₁₂) =
      divisorPresheafLE h₀₁ ≫ divisorPresheafLE h₁₂ := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

lemma divisorSheafLE_comp {D₀ D₁ D₂ : CurveDivisor k X}
    (h₀₁ : D₀ ≤ D₁) (h₁₂ : D₁ ≤ D₂) :
    divisorSheafLE (le_trans h₀₁ h₁₂) =
      divisorSheafLE h₀₁ ≫ divisorSheafLE h₁₂ := by
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  simp only [Functor.map_comp]
  exact divisorPresheafLE_comp h₀₁ h₁₂

end Hartshorne
