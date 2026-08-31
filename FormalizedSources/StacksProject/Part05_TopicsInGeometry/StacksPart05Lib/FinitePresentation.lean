/-
Copyright (c) 2026 The StacksPart05Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart05Lib Contributors
-/

import StacksPart05Lib.Geometry
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# StacksPart05Lib.FinitePresentation

Source-facing conjunctions for finite-presentation morphisms.  The formal-space
blueprint tests these properties on representable maps; this module packages
the corresponding scheme statements without identifying a formal space with a
scheme.
-/

namespace StacksPart05Lib

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/-! ## Finite presentation -/

/-- A scheme morphism is of finite presentation when it is locally of finite
presentation and quasi-compact. -/
def schemeFinitePresentation : MorphismProperty Scheme :=
  @LocallyOfFinitePresentation ⊓ @QuasiCompact

@[simp]
theorem schemeFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeFinitePresentation f ↔
      LocallyOfFinitePresentation f ∧ QuasiCompact f := Iff.rfl

instance schemeFinitePresentation_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeFinitePresentation where
  id_mem _ := ⟨inferInstance, inferInstance⟩
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@LocallyOfFinitePresentation) f g hf.1 hg.1,
      MorphismProperty.comp_mem (@QuasiCompact) f g hf.2 hg.2⟩

instance schemeFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso schemeFinitePresentation := by
  change MorphismProperty.RespectsIso
    (@LocallyOfFinitePresentation ⊓ @QuasiCompact)
  infer_instance

instance schemeFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback
        (P := @LocallyOfFinitePresentation) sq hg.1,
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq hg.2⟩

instance schemeFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeFinitePresentation where
  id_mem _ := ⟨inferInstance, inferInstance⟩

theorem scheme_finitePresentation_id (X : Scheme) :
    schemeFinitePresentation (𝟙 X) :=
  MorphismProperty.ContainsIdentities.id_mem X

theorem scheme_finitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : schemeFinitePresentation f)
    (hg : schemeFinitePresentation g) :
    schemeFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem schemeFinitePresentation f g hf hg

theorem scheme_finitePresentation_baseChange {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeFinitePresentation f) :
    schemeFinitePresentation (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeFinitePresentation) f g hf

theorem scheme_finitePresentation_baseChange_fst {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (hg : schemeFinitePresentation g) :
    schemeFinitePresentation (pullback.fst f g) :=
  MorphismProperty.pullback_fst (P := schemeFinitePresentation) f g hg

/-! ## Affine finite presentation -/

/-- The conjunction of affine and finite-presentation morphism properties. -/
def schemeAffineFinitePresentation : MorphismProperty Scheme :=
  @IsAffineHom ⊓ schemeFinitePresentation

@[simp]
theorem schemeAffineFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeAffineFinitePresentation f ↔
      IsAffineHom f ∧ schemeFinitePresentation f := Iff.rfl

instance schemeAffineFinitePresentation_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeAffineFinitePresentation where
  id_mem X := ⟨inferInstance, scheme_finitePresentation_id X⟩
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@IsAffineHom) f g hf.1 hg.1,
      MorphismProperty.comp_mem schemeFinitePresentation f g hf.2 hg.2⟩

instance schemeAffineFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso schemeAffineFinitePresentation := by
  change MorphismProperty.RespectsIso
    (@IsAffineHom ⊓ (@LocallyOfFinitePresentation ⊓ @QuasiCompact))
  infer_instance

instance schemeAffineFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeAffineFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsAffineHom) sq hg.1,
      MorphismProperty.of_isPullback (P := schemeFinitePresentation) sq hg.2⟩

instance schemeAffineFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeAffineFinitePresentation where
  id_mem X := ⟨inferInstance, scheme_finitePresentation_id X⟩

theorem scheme_affineFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : schemeAffineFinitePresentation f)
    (hg : schemeAffineFinitePresentation g) :
    schemeAffineFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem schemeAffineFinitePresentation f g hf hg

theorem scheme_affineFinitePresentation_baseChange {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (hf : schemeAffineFinitePresentation f) :
    schemeAffineFinitePresentation (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeAffineFinitePresentation) f g hf

theorem scheme_affineFinitePresentation_baseChange_fst {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (hg : schemeAffineFinitePresentation g) :
    schemeAffineFinitePresentation (pullback.fst f g) :=
  MorphismProperty.pullback_fst (P := schemeAffineFinitePresentation) f g hg

/-! ## Closed and separated finite presentation -/

/-- The conjunction of closed immersion and finite-presentation properties. -/
def schemeClosedFinitePresentation : MorphismProperty Scheme :=
  @IsClosedImmersion ⊓ schemeFinitePresentation

@[simp]
theorem schemeClosedFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeClosedFinitePresentation f ↔
      IsClosedImmersion f ∧ schemeFinitePresentation f := Iff.rfl

instance schemeClosedFinitePresentation_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeClosedFinitePresentation where
  id_mem X := ⟨inferInstance, scheme_finitePresentation_id X⟩
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@IsClosedImmersion) f g hf.1 hg.1,
      MorphismProperty.comp_mem schemeFinitePresentation f g hf.2 hg.2⟩

instance schemeClosedFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso schemeClosedFinitePresentation := by
  change MorphismProperty.RespectsIso
    (@IsClosedImmersion ⊓ (@LocallyOfFinitePresentation ⊓ @QuasiCompact))
  infer_instance

instance schemeClosedFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeClosedFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hg.1,
      MorphismProperty.of_isPullback (P := schemeFinitePresentation) sq hg.2⟩

instance schemeClosedFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeClosedFinitePresentation where
  id_mem X := ⟨inferInstance, scheme_finitePresentation_id X⟩

theorem scheme_closedFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : schemeClosedFinitePresentation f)
    (hg : schemeClosedFinitePresentation g) :
    schemeClosedFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem schemeClosedFinitePresentation f g hf hg

theorem scheme_closedFinitePresentation_baseChange {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (hf : schemeClosedFinitePresentation f) :
    schemeClosedFinitePresentation (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeClosedFinitePresentation) f g hf

/-- The conjunction of separated and finite-presentation properties. -/
def schemeSeparatedFinitePresentation : MorphismProperty Scheme :=
  @IsSeparated ⊓ schemeFinitePresentation

@[simp]
theorem schemeSeparatedFinitePresentation_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeSeparatedFinitePresentation f ↔
      IsSeparated f ∧ schemeFinitePresentation f := Iff.rfl

instance schemeSeparatedFinitePresentation_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeSeparatedFinitePresentation where
  id_mem X := ⟨inferInstance, scheme_finitePresentation_id X⟩
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (@IsSeparated) f g hf.1 hg.1,
      MorphismProperty.comp_mem schemeFinitePresentation f g hf.2 hg.2⟩

instance schemeSeparatedFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso schemeSeparatedFinitePresentation := by
  change MorphismProperty.RespectsIso
    (@IsSeparated ⊓ (@LocallyOfFinitePresentation ⊓ @QuasiCompact))
  infer_instance

instance schemeSeparatedFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeSeparatedFinitePresentation where
  of_isPullback sq hg :=
    ⟨MorphismProperty.of_isPullback (P := @IsSeparated) sq hg.1,
      MorphismProperty.of_isPullback (P := schemeFinitePresentation) sq hg.2⟩

instance schemeSeparatedFinitePresentation_containsIdentities :
    MorphismProperty.ContainsIdentities schemeSeparatedFinitePresentation where
  id_mem X := ⟨inferInstance, scheme_finitePresentation_id X⟩

theorem scheme_separatedFinitePresentation_comp {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : schemeSeparatedFinitePresentation f)
    (hg : schemeSeparatedFinitePresentation g) :
    schemeSeparatedFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem schemeSeparatedFinitePresentation f g hf hg

theorem scheme_separatedFinitePresentation_baseChange {X Y S : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (hf : schemeSeparatedFinitePresentation f) :
    schemeSeparatedFinitePresentation (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeSeparatedFinitePresentation) f g hf

end StacksPart05Lib
