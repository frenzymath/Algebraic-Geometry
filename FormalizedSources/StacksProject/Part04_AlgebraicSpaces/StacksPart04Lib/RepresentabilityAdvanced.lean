/-
Copyright (c) 2026 The StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import StacksPart04Lib.Representability

/-!
# Further representability interfaces

This module records the pairwise fibre-product form of the diagonal criterion
and exposes the generic relative-property constructors from Mathlib under the
source-facing names used by Part 04.
-/

namespace StacksPart04Lib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe v u v' u'

/-! ### Invariance and relative-property constructors -/

/-- Representability is unchanged after replacing the source and target by
isomorphic presheaves. -/
theorem representableTransformation_iff_of_iso {C : Type u} [Category.{v} C]
    {F F' G G' : Presheaf C} (eF : F' ≅ F) (eG : G' ≅ G)
    (a : F ⟶ G) :
    RepresentableTransformation C (eF.hom ≫ a ≫ eG.inv) ↔
      RepresentableTransformation C a := by
  constructor
  · intro h
    have h1 : RepresentableTransformation C (a ≫ eG.inv) :=
      MorphismProperty.cancel_left_of_respectsIso
        (RepresentableTransformation C) eF.hom (a ≫ eG.inv) |>.mp h
    exact MorphismProperty.cancel_right_of_respectsIso
      (RepresentableTransformation C) a eG.inv |>.mp h1
  · intro h
    have h1 : RepresentableTransformation C (a ≫ eG.inv) :=
      MorphismProperty.cancel_right_of_respectsIso
        (RepresentableTransformation C) a eG.inv |>.mpr h
    exact MorphismProperty.cancel_left_of_respectsIso
      (RepresentableTransformation C) eF.hom (a ≫ eG.inv) |>.mpr h1

/-- The relative property can be established by choosing any represented
pullback whose projection has the underlying property. -/
theorem relativeMorphismProperty_of_exists {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.RespectsIso]
    {X Y : D} {f : X ⟶ Y}
    (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y),
      ∃ (b : C) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
        (_ : IsPullback fst (F.map snd) f g), P snd) :
    RelativeMorphismProperty F P f :=
  MorphismProperty.relative.of_exists h

/-- The relative property can be established from the selected pullback
projections of a relatively representable morphism. -/
theorem relativeMorphismProperty_of_snd {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.RespectsIso]
    {X Y : D} {f : X ⟶ Y} (hf : RelativeRepresentable F f)
    (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) :
    RelativeMorphismProperty F P f :=
  MorphismProperty.relative_of_snd hf h

/-- For a fully faithful test functor and a base-change-stable property, the
relative property of a mapped morphism is equivalent to the original
property. -/
theorem relativeMorphismProperty_map_iff {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
    [HasPullbacks C] [P.IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) :
    RelativeMorphismProperty F P (F.map f) ↔ P f :=
  MorphismProperty.relative_map_iff

/-! ### The pairwise fibre-product form of the diagonal criterion -/

/-- The diagonal criterion can be stated directly in terms of pairwise
fibre products of maps from test objects.  The two projections are maps in the
test category, so this is the source-facing third clause of Stacks Tag `025W`.
-/
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

end StacksPart04Lib
