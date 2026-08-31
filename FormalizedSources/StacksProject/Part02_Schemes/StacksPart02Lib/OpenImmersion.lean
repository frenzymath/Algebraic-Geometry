/-
Copyright (c) 2026 The StacksPart02Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart02Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Restrict

/-!
# Basic consequences of open immersions

This module packages the topological and range properties of open immersions
of schemes in the namespace used by the Stacks Part 02 development.
-/

namespace StacksPart02

open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits

universe u

/-- An open immersion of schemes is injective on the underlying points. -/
theorem scheme_openImmersion_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Function.Injective f := by
  exact f.isOpenEmbedding.isEmbedding.injective

/-- An open immersion maps open subsets to open subsets. -/
theorem scheme_openImmersion_isOpenMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpenMap f := by
  exact f.isOpenEmbedding.isOpenMap

/-- The set-theoretic image of an open immersion is its canonical open range. -/
theorem scheme_openImmersion_range_eq_opensRange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Set.range f = (f.opensRange : Set Y) := by
  rfl

/-- Every open immersion factors through the inclusion of its canonical range. -/
theorem scheme_openImmersion_factorization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.hom ≫ f.opensRange.ι = f := by
  exact f.isoOpensRange_hom_ι

/-- The composite of two open immersions is an open immersion. -/
theorem scheme_openImmersion_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) := by
  exact IsOpenImmersion.comp f g

/-- Pullback preserves open immersions along the first projection. -/
theorem scheme_openImmersion_pullback_fst
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] :
    IsOpenImmersion (pullback.fst g f) := by
  infer_instance

/-- The image of the pullback projection is the preimage of the original
open immersion's range. -/
theorem scheme_openImmersion_pullback_fst_range
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] :
    Set.range (pullback.fst g f) = g ⁻¹ᵁ f.opensRange := by
  exact IsOpenImmersion.range_pullbackFst f g

/-- Pullback preserves open immersions along the second projection. -/
theorem scheme_openImmersion_pullback_snd
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] :
    IsOpenImmersion (pullback.snd f g) := by
  infer_instance

/-- The image of the second pullback projection is the preimage of the
original open immersion's range. -/
theorem scheme_openImmersion_pullback_snd_range
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] :
    Set.range (pullback.snd f g) = g ⁻¹ᵁ f.opensRange := by
  exact IsOpenImmersion.range_pullbackSnd f g

end StacksPart02
