/-
Copyright (c) 2026 The StacksPart05Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart05Lib Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# StacksPart05Lib.Surjectivity

The scheme-model closure properties for the surjective morphisms appearing in
the formal algebraic space chapter.
-/

namespace StacksPart05Lib

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

/-- The surjectivity property in the representable scheme model. -/
def schemeSurjective : MorphismProperty Scheme :=
  @AlgebraicGeometry.Surjective

@[simp]
theorem schemeSurjective_iff {X Y : Scheme} (f : X ⟶ Y) :
    schemeSurjective f ↔ AlgebraicGeometry.Surjective f := Iff.rfl

/-- The scheme-level wrapper is equivalent to surjectivity of the underlying
continuous map.  Keeping this bridge explicit makes the source-facing
property convenient to use without introducing a local instance. -/
theorem scheme_surjective_iff_underlying {X Y : Scheme} (f : X ⟶ Y) :
    schemeSurjective f ↔ Function.Surjective f := by
  change AlgebraicGeometry.Surjective f ↔ Function.Surjective f
  exact AlgebraicGeometry.surjective_iff f

/-! ## Term-level closure -/

/-- An isomorphism of schemes is surjective. -/
theorem scheme_surjective_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    schemeSurjective f := by
  change AlgebraicGeometry.Surjective f
  infer_instance

/-- Surjectivity of two composable scheme morphisms gives surjectivity of the
composite, with hypotheses supplied as terms. -/
theorem scheme_surjective_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeSurjective f) (hg : schemeSurjective g) :
    schemeSurjective (f ≫ g) := by
  change AlgebraicGeometry.Surjective (f ≫ g)
  letI : AlgebraicGeometry.Surjective f := hf
  letI : AlgebraicGeometry.Surjective g := hg
  infer_instance

/-- Surjectivity of a composite implies surjectivity of its second leg,
without requiring a typeclass hypothesis at the call site. -/
theorem scheme_surjective_of_comp_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : schemeSurjective (f ≫ g)) :
    schemeSurjective g := by
  letI : AlgebraicGeometry.Surjective (f ≫ g) := hfg
  exact AlgebraicGeometry.Surjective.of_comp f g

/-- If the first leg is surjective, surjectivity of a composite is equivalent
to surjectivity of the second leg. -/
theorem scheme_surjective_comp_iff_of_mem {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : schemeSurjective f) :
    schemeSurjective (f ≫ g) ↔ schemeSurjective g := by
  letI : AlgebraicGeometry.Surjective f := hf
  exact AlgebraicGeometry.Surjective.comp_iff f g

/-- Surjectivity is preserved by pullback when the base-changed map is given
as a term. -/
theorem scheme_surjective_baseChange_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hf : schemeSurjective f) :
    schemeSurjective (pullback.snd f g) := by
  change AlgebraicGeometry.Surjective (pullback.snd f g)
  letI : AlgebraicGeometry.Surjective f := hf
  infer_instance

/-- The symmetric pullback leg is surjective when its other map is. -/
theorem scheme_surjective_baseChange_fst_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (hg : schemeSurjective g) :
    schemeSurjective (pullback.fst f g) := by
  change AlgebraicGeometry.Surjective (pullback.fst f g)
  letI : AlgebraicGeometry.Surjective g := hg
  infer_instance

/-- A surjective map does not change the range of a compatible map out of its
source. -/
theorem scheme_surjective_range_eq_range_of_mem {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) (e : X ⟶ Y) (he : e ≫ g = f)
    (h : schemeSurjective e) :
    Set.range f = Set.range g := by
  letI : AlgebraicGeometry.Surjective e := h
  exact AlgebraicGeometry.range_eq_range_of_surjective f g e he

/-- A scheme morphism is surjective exactly when its underlying map has full range. -/
theorem scheme_surjective_iff_range_eq_univ {X Y : Scheme} (f : X ⟶ Y) :
    schemeSurjective f ↔ Set.range f = Set.univ := by
  constructor
  · intro h
    letI : AlgebraicGeometry.Surjective f := h
    exact AlgebraicGeometry.range_eq_univ f
  · intro h
    exact ⟨Set.range_eq_univ.mp h⟩

/-- Surjectivity is preserved by composition of scheme morphisms. -/
theorem scheme_surjective_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.Surjective g] :
    schemeSurjective (f ≫ g) := by
  exact ⟨g.surjective.comp f.surjective⟩

/-- Surjectivity of a composite implies surjectivity of its second leg. -/
theorem scheme_surjective_of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Surjective (f ≫ g)] :
    schemeSurjective g := by
  exact AlgebraicGeometry.Surjective.of_comp f g

/-- When the first leg is surjective, a composite is surjective exactly when
the second leg is surjective. -/
theorem scheme_surjective_comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Surjective f] :
    schemeSurjective (f ≫ g) ↔ schemeSurjective g := by
  change AlgebraicGeometry.Surjective (f ≫ g) ↔ AlgebraicGeometry.Surjective g
  exact AlgebraicGeometry.Surjective.comp_iff f g

/-- Surjectivity is preserved by pullback on the second leg. -/
theorem scheme_surjective_baseChange {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [AlgebraicGeometry.Surjective f] :
    schemeSurjective (pullback.snd f g) := by
  change AlgebraicGeometry.Surjective (pullback.snd f g)
  infer_instance

/-- Surjectivity is preserved by pullback on the first leg. -/
theorem scheme_surjective_baseChange_fst {X Y S : Scheme} (f : X ⟶ S)
    (g : Y ⟶ S) [AlgebraicGeometry.Surjective g] :
    schemeSurjective (pullback.fst f g) := by
  change AlgebraicGeometry.Surjective (pullback.fst f g)
  infer_instance

instance schemeSurjective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition schemeSurjective where
  comp_mem f g hf hg := by
    change AlgebraicGeometry.Surjective (f ≫ g)
    exact ⟨hg.surj.comp hf.surj⟩

instance schemeSurjective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange schemeSurjective where
  of_isPullback sq hg := by
    change AlgebraicGeometry.Surjective _
    exact MorphismProperty.of_isPullback sq hg

/-- The surjectivity property contains identities and is closed under
composition, matching the multiplicative source convention. -/
instance schemeSurjective_isMultiplicative :
    MorphismProperty.IsMultiplicative schemeSurjective where
  id_mem X := scheme_surjective_of_isIso (𝟙 X)
  comp_mem f g hf hg := scheme_surjective_comp_of_mem f g hf hg

/-- Surjectivity is invariant under replacing either endpoint by an
isomorphic scheme. -/
instance schemeSurjective_respectsIso :
    MorphismProperty.RespectsIso schemeSurjective := by
  change MorphismProperty.RespectsIso (@AlgebraicGeometry.Surjective)
  infer_instance

end StacksPart05Lib
