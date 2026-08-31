/-
Copyright (c) 2026 The StacksPart05Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart05Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# StacksPart05Lib.FormalSpaces

The formal-space chapter defines finite-type properties for morphisms of
formal algebraic spaces by testing representable maps.  Mathlib has the
corresponding properties for scheme morphisms.  This file records the
source-facing closure statements in that representable setting.  Arbitrary
formal algebraic spaces are intentionally not identified with schemes here.
-/

namespace StacksPart05Lib

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/-! ## Representable (scheme) model -/

/-- The finite-type property for a scheme morphism, matching the two clauses
in the formal-space definition: locally of finite type and quasi-compact. -/
def schemeFiniteType : MorphismProperty Scheme :=
  @LocallyOfFiniteType ⊓ @QuasiCompact

@[simp]
theorem schemeFiniteType_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeFiniteType f ↔ LocallyOfFiniteType f ∧ QuasiCompact f := Iff.rfl

/-- Composition preserves the scheme finite-type property. -/
instance schemeFiniteType_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition schemeFiniteType where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@LocallyOfFiniteType) f g hf.1 hg.1,
      MorphismProperty.comp_mem (@QuasiCompact) f g hf.2 hg.2⟩

instance schemeFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeFiniteType where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg.1,
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq hg.2⟩

instance schemeFiniteType_containsIdentities :
    MorphismProperty.ContainsIdentities schemeFiniteType where
  id_mem _X := ⟨inferInstance, inferInstance⟩

/-- Every identity scheme morphism is of finite type. -/
theorem scheme_finiteType_id (X : Scheme) : schemeFiniteType (𝟙 X) := by
  exact MorphismProperty.ContainsIdentities.id_mem X

/-! The source's composition and base-change lemmas for the representable
scheme case. -/

/-- Locally finite type is stable under composition. -/
theorem scheme_locallyOfFiniteType_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) := by
  infer_instance

/-- Locally finite type is stable under pullback on the second leg. -/
theorem scheme_locallyOfFiniteType_baseChange {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (pullback.snd f g) := by
  infer_instance

/-- Locally finite type is stable under pullback on the first leg. -/
theorem scheme_locallyOfFiniteType_baseChange_fst {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [LocallyOfFiniteType g] :
    LocallyOfFiniteType (pullback.fst f g) := by
  infer_instance

/-- The scheme finite-type property is stable under composition. -/
theorem scheme_finiteType_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [QuasiCompact f]
    [QuasiCompact g] :
    schemeFiniteType (f ≫ g) := by
  exact MorphismProperty.comp_mem schemeFiniteType f g
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩

/-- The scheme finite-type property is stable under pullback on the second leg. -/
theorem scheme_finiteType_baseChange {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    schemeFiniteType (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := schemeFiniteType) f g
    ⟨inferInstance, inferInstance⟩

/-- The scheme finite-type property is stable under pullback on the first leg. -/
theorem scheme_finiteType_baseChange_fst {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [LocallyOfFiniteType g] [QuasiCompact g] :
    schemeFiniteType (pullback.fst f g) := by
  exact MorphismProperty.pullback_fst (P := schemeFiniteType) f g
    ⟨inferInstance, inferInstance⟩

end StacksPart05Lib
