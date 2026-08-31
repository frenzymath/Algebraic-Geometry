/-
Copyright (c) 2026 The StacksPart08Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart08Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Scheme-morphism property facades

The moduli-stack chapter repeatedly asks for morphisms that are affine or
closed and of finite presentation.  Mathlib provides the individual scheme
properties and their closure theorems.  This module packages the conjunctions
used by the source; it does not assert that a moduli functor or stack is
represented by a scheme.
-/

namespace StacksPart08

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/-! ### Finite presentation -/

/-- Finite presentation for a scheme morphism: locally of finite presentation
and quasi-compact. -/
def schemeFinitePresentation : MorphismProperty Scheme :=
  @LocallyOfFinitePresentation ⊓ @QuasiCompact

@[simp]
theorem schemeFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeFinitePresentation f ↔
      LocallyOfFinitePresentation f ∧ QuasiCompact f := Iff.rfl

instance schemeFinitePresentation_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition schemeFinitePresentation where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@LocallyOfFinitePresentation) f g hf.1 hg.1,
      MorphismProperty.comp_mem (@QuasiCompact) f g hf.2 hg.2⟩

instance schemeFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq hg.1,
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq hg.2⟩

instance schemeFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeFinitePresentation where
  id_mem _ := ⟨inferInstance, inferInstance⟩

theorem schemeFinitePresentation_id (X : Scheme) :
    schemeFinitePresentation (𝟙 X) :=
  MorphismProperty.ContainsIdentities.id_mem X

theorem schemeFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation g] [QuasiCompact f] [QuasiCompact g] :
    schemeFinitePresentation (f ≫ g) := by
  exact MorphismProperty.comp_mem schemeFinitePresentation f g
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩

theorem schemeFinitePresentation_baseChange {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] :
    schemeFinitePresentation (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := schemeFinitePresentation) f g
    ⟨inferInstance, inferInstance⟩

theorem schemeFinitePresentation_baseChange_fst {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [LocallyOfFinitePresentation g] [QuasiCompact g] :
    schemeFinitePresentation (pullback.fst f g) := by
  exact MorphismProperty.pullback_fst (P := schemeFinitePresentation) f g
    ⟨inferInstance, inferInstance⟩

/-! ### Affine finite-presentation morphisms -/

/-- The affine finite-presentation property used for represented moduli pieces. -/
def schemeAffineFinitePresentation : MorphismProperty Scheme :=
  @IsAffineHom ⊓ schemeFinitePresentation

@[simp]
theorem schemeAffineFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeAffineFinitePresentation f ↔
      IsAffineHom f ∧ schemeFinitePresentation f := Iff.rfl

instance schemeAffineFinitePresentation_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition schemeAffineFinitePresentation where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@IsAffineHom) f g hf.1 hg.1,
      MorphismProperty.comp_mem schemeFinitePresentation f g hf.2 hg.2⟩

instance schemeAffineFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeAffineFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsAffineHom) sq hg.1,
      MorphismProperty.of_isPullback (P := schemeFinitePresentation) sq hg.2⟩

instance schemeAffineFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeAffineFinitePresentation where
  id_mem X := ⟨inferInstance, schemeFinitePresentation_id X⟩

theorem schemeAffineFinitePresentation_id (X : Scheme) :
    schemeAffineFinitePresentation (𝟙 X) :=
  MorphismProperty.ContainsIdentities.id_mem X

theorem schemeAffineFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsAffineHom f] [IsAffineHom g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [QuasiCompact f] [QuasiCompact g] :
    schemeAffineFinitePresentation (f ≫ g) := by
  exact MorphismProperty.comp_mem schemeAffineFinitePresentation f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem schemeAffineFinitePresentation_baseChange {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] :
    schemeAffineFinitePresentation (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := schemeAffineFinitePresentation) f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem schemeAffineFinitePresentation_baseChange_fst {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g]
    [LocallyOfFinitePresentation g] [QuasiCompact g] :
    schemeAffineFinitePresentation (pullback.fst f g) := by
  exact MorphismProperty.pullback_fst (P := schemeAffineFinitePresentation) f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

/-! ### Closed finite-presentation morphisms -/

/-- A closed immersion equipped with the finite-presentation hypotheses. -/
def schemeClosedFinitePresentation : MorphismProperty Scheme :=
  @IsClosedImmersion ⊓ schemeFinitePresentation

@[simp]
theorem schemeClosedFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeClosedFinitePresentation f ↔
      IsClosedImmersion f ∧ schemeFinitePresentation f := Iff.rfl

instance schemeClosedFinitePresentation_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition schemeClosedFinitePresentation where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@IsClosedImmersion) f g hf.1 hg.1,
      MorphismProperty.comp_mem schemeFinitePresentation f g hf.2 hg.2⟩

instance schemeClosedFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeClosedFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hg.1,
      MorphismProperty.of_isPullback (P := schemeFinitePresentation) sq hg.2⟩

instance schemeClosedFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeClosedFinitePresentation where
  id_mem X := ⟨inferInstance, schemeFinitePresentation_id X⟩

theorem schemeClosedFinitePresentation_id (X : Scheme) :
    schemeClosedFinitePresentation (𝟙 X) :=
  MorphismProperty.ContainsIdentities.id_mem X

theorem schemeClosedFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsClosedImmersion f] [IsClosedImmersion g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [QuasiCompact f] [QuasiCompact g] :
    schemeClosedFinitePresentation (f ≫ g) := by
  exact MorphismProperty.comp_mem schemeClosedFinitePresentation f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem schemeClosedFinitePresentation_baseChange {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] :
    schemeClosedFinitePresentation (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := schemeClosedFinitePresentation) f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem schemeClosedFinitePresentation_baseChange_fst {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [IsClosedImmersion g]
    [LocallyOfFinitePresentation g] [QuasiCompact g] :
    schemeClosedFinitePresentation (pullback.fst f g) := by
  exact MorphismProperty.pullback_fst (P := schemeClosedFinitePresentation) f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

/-! ### Separated finite-presentation morphisms -/

/-- A separated morphism equipped with the finite-presentation hypotheses. -/
def schemeSeparatedFinitePresentation : MorphismProperty Scheme :=
  @IsSeparated ⊓ schemeFinitePresentation

@[simp]
theorem schemeSeparatedFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeSeparatedFinitePresentation f ↔
      IsSeparated f ∧ schemeFinitePresentation f := Iff.rfl

instance schemeSeparatedFinitePresentation_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition schemeSeparatedFinitePresentation where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@IsSeparated) f g hf.1 hg.1,
      MorphismProperty.comp_mem schemeFinitePresentation f g hf.2 hg.2⟩

instance schemeSeparatedFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeSeparatedFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsSeparated) sq hg.1,
      MorphismProperty.of_isPullback (P := schemeFinitePresentation) sq hg.2⟩

instance schemeSeparatedFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeSeparatedFinitePresentation where
  id_mem X := ⟨inferInstance, schemeFinitePresentation_id X⟩

theorem schemeSeparatedFinitePresentation_id (X : Scheme) :
    schemeSeparatedFinitePresentation (𝟙 X) :=
  MorphismProperty.ContainsIdentities.id_mem X

theorem schemeSeparatedFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsSeparated f] [IsSeparated g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [QuasiCompact f] [QuasiCompact g] :
    schemeSeparatedFinitePresentation (f ≫ g) := by
  exact MorphismProperty.comp_mem schemeSeparatedFinitePresentation f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem schemeSeparatedFinitePresentation_baseChange {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] :
    schemeSeparatedFinitePresentation (pullback.snd f g) := by
  exact MorphismProperty.pullback_snd (P := schemeSeparatedFinitePresentation) f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem schemeSeparatedFinitePresentation_baseChange_fst {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g]
    [LocallyOfFinitePresentation g] [QuasiCompact g] :
    schemeSeparatedFinitePresentation (pullback.fst f g) := by
  exact MorphismProperty.pullback_fst (P := schemeSeparatedFinitePresentation) f g
    ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

end StacksPart08
