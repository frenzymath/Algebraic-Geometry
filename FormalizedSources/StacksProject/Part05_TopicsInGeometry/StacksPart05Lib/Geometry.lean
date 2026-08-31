/-
Copyright (c) 2026 The StacksPart05Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart05Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# StacksPart05Lib.Geometry

Source-facing wrappers for the standard classes of scheme morphisms used in
the formal-space and algebraization chapters.  The Part 05 blueprint works
with formal algebraic spaces; until that category is formalized, these
properties are deliberately exposed only in the representable (scheme) model.
-/

namespace StacksPart05Lib

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/-! ## Scheme-model properties -/

def schemeProper : MorphismProperty Scheme := @IsProper

def schemeSeparated : MorphismProperty Scheme := @IsSeparated

def schemeFinite : MorphismProperty Scheme := @IsFinite

def schemeSmooth : MorphismProperty Scheme := @Smooth

def schemeEtale : MorphismProperty Scheme := @Etale

@[simp]
theorem schemeProper_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeProper f ↔ IsProper f := Iff.rfl

@[simp]
theorem schemeSeparated_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeSeparated f ↔ IsSeparated f := Iff.rfl

@[simp]
theorem schemeFinite_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeFinite f ↔ IsFinite f := Iff.rfl

@[simp]
theorem schemeSmooth_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeSmooth f ↔ Smooth f := Iff.rfl

@[simp]
theorem schemeEtale_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeEtale f ↔ Etale f := Iff.rfl

instance schemeProper_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeProper := by
  change MorphismProperty.IsMultiplicative (@IsProper)
  infer_instance

instance schemeProper_respectsIso :
    MorphismProperty.RespectsIso schemeProper := by
  change MorphismProperty.RespectsIso (@IsProper)
  infer_instance

instance schemeProper_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeProper := by
  change MorphismProperty.IsStableUnderBaseChange (@IsProper)
  infer_instance

instance schemeSeparated_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeSeparated := by
  change MorphismProperty.IsMultiplicative (@IsSeparated)
  infer_instance

instance schemeSeparated_respectsIso :
    MorphismProperty.RespectsIso schemeSeparated := by
  change MorphismProperty.RespectsIso (@IsSeparated)
  infer_instance

instance schemeSeparated_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeSeparated := by
  change MorphismProperty.IsStableUnderBaseChange (@IsSeparated)
  infer_instance

instance schemeFinite_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeFinite := by
  change MorphismProperty.IsMultiplicative (@IsFinite)
  infer_instance

instance schemeFinite_respectsIso :
    MorphismProperty.RespectsIso schemeFinite := by
  change MorphismProperty.RespectsIso (@IsFinite)
  infer_instance

instance schemeFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeFinite := by
  change MorphismProperty.IsStableUnderBaseChange (@IsFinite)
  infer_instance

instance schemeSmooth_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeSmooth where
  id_mem X := by
    change Smooth (𝟙 X)
    infer_instance
  comp_mem f g hf hg := by
    change Smooth (f ≫ g)
    exact MorphismProperty.comp_mem (@Smooth) f g hf hg

instance schemeSmooth_respectsIso :
    MorphismProperty.RespectsIso schemeSmooth := by
  change MorphismProperty.RespectsIso (@Smooth)
  exact MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro X Y f hf
    change IsIso f at hf
    letI := hf
    infer_instance)

instance schemeSmooth_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeSmooth := by
  change MorphismProperty.IsStableUnderBaseChange (@Smooth)
  infer_instance

instance schemeEtale_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeEtale := by
  change MorphismProperty.IsMultiplicative (@Etale)
  infer_instance

instance schemeEtale_respectsIso :
    MorphismProperty.RespectsIso schemeEtale := by
  change MorphismProperty.RespectsIso (@Etale)
  exact MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro X Y f hf
    change IsIso f at hf
    letI := hf
    infer_instance)

instance schemeEtale_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeEtale := by
  change MorphismProperty.IsStableUnderBaseChange (@Etale)
  infer_instance

/-! ## Closure in the scheme model -/

theorem scheme_proper_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeProper f) (hg : schemeProper g) :
    schemeProper (f ≫ g) :=
  MorphismProperty.comp_mem schemeProper f g hf hg

theorem scheme_proper_baseChange_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeProper f) :
    schemeProper (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeProper) f g hf

theorem scheme_proper_baseChange_fst_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hg : schemeProper g) :
    schemeProper (pullback.fst f g) :=
  MorphismProperty.pullback_fst (P := schemeProper) f g hg

theorem scheme_separated_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeSeparated f) (hg : schemeSeparated g) :
    schemeSeparated (f ≫ g) :=
  MorphismProperty.comp_mem schemeSeparated f g hf hg

theorem scheme_separated_baseChange_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeSeparated f) :
    schemeSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeSeparated) f g hf

theorem scheme_finite_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeFinite f) (hg : schemeFinite g) :
    schemeFinite (f ≫ g) :=
  MorphismProperty.comp_mem schemeFinite f g hf hg

theorem scheme_finite_baseChange_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeFinite f) :
    schemeFinite (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeFinite) f g hf

theorem scheme_smooth_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeSmooth f) (hg : schemeSmooth g) :
    schemeSmooth (f ≫ g) :=
  MorphismProperty.comp_mem schemeSmooth f g hf hg

theorem scheme_smooth_baseChange_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeSmooth f) :
    schemeSmooth (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeSmooth) f g hf

theorem scheme_etale_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeEtale f) (hg : schemeEtale g) :
    schemeEtale (f ≫ g) :=
  MorphismProperty.comp_mem schemeEtale f g hf hg

theorem scheme_etale_baseChange_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeEtale f) :
    schemeEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := schemeEtale) f g hf

/-! ## Standard implications -/

theorem scheme_proper_of_finite {X Y : Scheme} (f : X ⟶ Y)
    (hf : schemeFinite f) : schemeProper f := by
  change IsProper f
  letI : IsFinite f := hf
  infer_instance

theorem scheme_finite_iff_proper_and_affineHom {X Y : Scheme} (f : X ⟶ Y) :
    schemeFinite f ↔ schemeProper f ∧ IsAffineHom f := by
  change IsFinite f ↔ IsProper f ∧ IsAffineHom f
  exact IsFinite.iff_isProper_and_isAffineHom

theorem scheme_finite_iff_integral_and_locallyOfFiniteType {X Y : Scheme}
    (f : X ⟶ Y) :
    schemeFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  change IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f
  exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f

theorem scheme_finite_of_comp_of_separated {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hfg : schemeFinite (f ≫ g)) (hg : schemeSeparated g) :
    schemeFinite f := by
  change IsFinite f at *
  letI : IsFinite (f ≫ g) := hfg
  letI : IsSeparated g := hg
  exact IsFinite.of_comp f g

theorem scheme_proper_of_comp_of_separated {X Y Z : Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hfg : schemeProper (f ≫ g)) (hg : schemeSeparated g) :
    schemeProper f := by
  change IsProper f at *
  letI : IsProper (f ≫ g) := hfg
  letI : IsSeparated g := hg
  exact IsProper.of_comp f g

theorem scheme_separated_of_affineHom {X Y : Scheme} (f : X ⟶ Y)
    (hf : IsAffineHom f) : schemeSeparated f := by
  change IsSeparated f
  letI : IsAffineHom f := hf
  exact IsSeparated.of_isAffineHom f

theorem scheme_etale_iff_smoothOfRelativeDimension_zero {X Y : Scheme}
    (f : X ⟶ Y) :
    schemeEtale f ↔ SmoothOfRelativeDimension 0 f := by
  change Etale f ↔ SmoothOfRelativeDimension 0 f
  exact Etale.iff_smoothOfRelativeDimension_zero f

theorem scheme_etale_to_smooth {X Y : Scheme} (f : X ⟶ Y)
    (hf : schemeEtale f) : schemeSmooth f := by
  change Smooth f
  letI : Etale f := hf
  infer_instance

theorem scheme_etale_to_flat {X Y : Scheme} (f : X ⟶ Y)
    (hf : schemeEtale f) : Flat f := by
  letI : Etale f := hf
  infer_instance

theorem scheme_etale_to_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    (hf : schemeEtale f) : FormallyUnramified f := by
  letI : Etale f := hf
  infer_instance

end StacksPart05Lib
