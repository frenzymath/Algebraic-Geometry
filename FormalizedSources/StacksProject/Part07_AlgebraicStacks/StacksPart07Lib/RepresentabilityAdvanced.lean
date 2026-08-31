/-
Copyright (c) 2026 The StacksPart07Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart07Lib Contributors
-/

import StacksPart07Lib.RepresentableMorphisms

/-!
# Further representability interfaces

The algebraic-stacks blueprint repeatedly switches between selected
represented pullbacks and arbitrary representatives.  This module exposes
those generic relative-property constructors, together with the pairwise
fibre-product form of the diagonal criterion.
-/

namespace StacksPart07Lib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe v u v' u'

/-! ### Relative-property constructors -/

/-- A relative morphism property can be checked on any represented pullback.

This is the source-facing form of the generic constructor used in the
representable-morphism lemmas (Stacks tag `02Z*`).
-/
theorem relativeMorphismProperty_of_exists {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.RespectsIso]
    {X Y : D} {f : X ⟶ Y}
    (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y),
      ∃ (b : C) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
        (_ : IsPullback fst (F.map snd) f g), P snd) :
    RelativeMorphismProperty F P f :=
  MorphismProperty.relative.of_exists h

/-- A relative property follows from the selected pullback projections. -/
theorem relativeMorphismProperty_of_snd {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.RespectsIso]
    {X Y : D} {f : X ⟶ Y} (hf : RelativeRepresentable F f)
    (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) :
    RelativeMorphismProperty F P f :=
  MorphismProperty.relative_of_snd hf h

/-- For a fully faithful test functor, a base-change-stable property of a
mapped morphism is equivalent to the original property. -/
theorem relativeMorphismProperty_map_iff {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
    [HasPullbacks C] [P.IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) :
    RelativeMorphismProperty F P (F.map f) ↔ P f :=
  MorphismProperty.relative_map_iff

/-! ### Pairwise form of the diagonal criterion -/

/-- The diagonal criterion stated directly using fibre products of maps from
test objects. -/
theorem relativeRepresentable_diag_iff_pairwise {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {X : D}
    [HasBinaryProducts C] [HasPullbacks C]
    [HasPullbacks D] [HasBinaryProducts D] [HasTerminal D]
    [F.Full] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingCospan F] :
    RelativeRepresentable F (Limits.diag X) ↔
      ∀ ⦃a b : C⦄ (g : F.obj a ⟶ X) (h : F.obj b ⟶ X),
        ∃ (c : C) (p : c ⟶ a) (q : c ⟶ b),
          IsPullback (F.map p) (F.map q) g h := by
  rw [relativeRepresentable_diag_iff]
  constructor
  · intro hdiag a b g h
    obtain ⟨c, q, fst, sq⟩ := hdiag g h
    refine ⟨c, F.preimage fst, q, ?_⟩
    simpa only [Functor.map_preimage] using sq
  · intro hdiag a g b h
    obtain ⟨c, p, q, sq⟩ := hdiag g h
    exact ⟨c, q, F.map p, sq⟩

end StacksPart07Lib
