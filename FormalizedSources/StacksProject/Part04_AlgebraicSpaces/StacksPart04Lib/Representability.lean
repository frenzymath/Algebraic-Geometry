/-
Copyright (c) 2026 The StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Representable transformations

The first chapter of the Algebraic Spaces part of the Stacks Project develops
representable transformations of presheaves and properties of such
transformations (Stacks, Tags `02W9`, `02WA`, `02WB`, `025V`, `02WJ`, `02WK`,
and `02WL`).  Mathlib's `CategoryTheory.MorphismProperty.Representable` is the
abstract categorical formulation of precisely this discussion.  This module
keeps the source-facing names local to the Part 04 library while exposing the
corresponding Mathlib constructions.
-/

namespace StacksPart04Lib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe v u v' u'

/-! ### Presheaves and relative representability -/

/-- The `Type v`-valued presheaves on a category `C`.

This is the ambient category used by the Yoneda formulation of representable
transformations. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type v

/-- Relative representability of a morphism with respect to a functor.

This is an alias for `Functor.relativelyRepresentable`; it is the categorical
form of the fibre-product definition in Stacks, Tag `025V`. -/
abbrev RelativeRepresentable {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) : MorphismProperty D :=
  F.relativelyRepresentable

/-- A representable transformation between presheaves on `C`.

The Yoneda functor is used as the representing family, as in the classical
definition of a representable transformation in Stacks, Tag `02W9`. -/
abbrev RepresentableTransformation (C : Type u) [Category.{v} C] :
    MorphismProperty (Presheaf C) :=
  yoneda.relativelyRepresentable

/-- A morphism property imposed on represented pullbacks of a transformation. -/
abbrev RelativeMorphismProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (P : MorphismProperty C) :
    MorphismProperty D :=
  P.relative F

/-- The special case of `RelativeMorphismProperty` for presheaves and Yoneda. -/
abbrev PresheafMorphismProperty {C : Type u} [Category.{v} C]
    (P : MorphismProperty C) : MorphismProperty (Presheaf C) :=
  P.presheaf

/-! ### Morphisms represented by schemes -/

/-- The Yoneda transformation associated to a morphism of objects.

For a category of schemes this is the transformation usually denoted `h_f` in
the Stacks Project (Tag `02W9`). -/
abbrev morphismScheme {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    yoneda.obj X ⟶ yoneda.obj Y :=
  yoneda.map f

/-- A morphism of objects induces a representable Yoneda transformation.

The only categorical input is the existence of pullbacks in `C`. -/
theorem morphismScheme_representable {C : Type u} [Category.{v} C]
    [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    RepresentableTransformation C (morphismScheme f) := by
  exact Functor.relativelyRepresentable.map yoneda f

@[simp]
theorem morphismScheme_id {C : Type u} [Category.{v} C] {X : C} :
    morphismScheme (𝟙 X) = 𝟙 (yoneda.obj X) :=
  yoneda.map_id X

@[simp]
theorem morphismScheme_comp {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    morphismScheme (f ≫ g) = morphismScheme f ≫ morphismScheme g :=
  yoneda.map_comp f g

/-! ### Stability of representable transformations -/

/-- The composite of representable transformations is representable
(Stacks, Tag `02WA`). -/
theorem representableTransformation_comp {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (a : F ⟶ G) (b : G ⟶ H)
    (ha : RepresentableTransformation C a)
    (hb : RepresentableTransformation C b) :
    RepresentableTransformation C (a ≫ b) := by
  exact MorphismProperty.comp_mem (RepresentableTransformation C) a b ha hb

/-- Representability is preserved by a pullback of transformations
(Stacks, Tag `02WB`).

The square is written in Mathlib's order: `p` and `a'` are the two maps out of
the pullback object, `a` is the represented map, and `b` is the arbitrary base
change map. -/
theorem representableTransformation_baseChange {C : Type u} [Category.{v} C]
    {F G H K : Presheaf C} {a : F ⟶ G} {b : H ⟶ G}
    {a' : K ⟶ H} {p : K ⟶ F}
    (sq : IsPullback p a' a b)
    (ha : RepresentableTransformation C a) :
    RepresentableTransformation C a' := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ha

/-- Every isomorphism of presheaves is a representable transformation. -/
theorem representableTransformation_of_isIso {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (a : F ⟶ G) [IsIso a] :
    RepresentableTransformation C a := by
  exact Functor.relativelyRepresentable.of_isIso yoneda a

/-- The class of representable transformations contains identities and is
closed under composition (Stacks, Tag `02WA`). -/
theorem representableTransformation_isMultiplicative (C : Type u)
    [Category.{v} C] :
    (RepresentableTransformation C).IsMultiplicative :=
  Functor.relativelyRepresentable.isMultiplicative yoneda

/-- Representable transformations are stable under arbitrary base change
(Stacks, Tag `02WB`). -/
theorem representableTransformation_isStableUnderBaseChange (C : Type u)
    [Category.{v} C] :
    (RepresentableTransformation C).IsStableUnderBaseChange :=
  Functor.relativelyRepresentable.isStableUnderBaseChange yoneda

/-! ### Relative morphism properties -/

/-- A relative morphism property implies relative representability. -/
theorem relativeMorphismProperty_rep {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y : D} {f : X ⟶ Y}
    (hf : RelativeMorphismProperty F P f) :
    RelativeRepresentable F f :=
  hf.rep

/-- The defining scheme-level property of a represented pullback. -/
theorem relativeMorphismProperty_property {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y : D} {f : X ⟶ Y} (hf : RelativeMorphismProperty F P f)
    {a b : C} (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (sq : IsPullback fst (F.map snd) f g) : P snd :=
  hf.property g fst snd sq

/-- The selected pullback projection satisfies the relative morphism property. -/
theorem relativeMorphismProperty_property_snd {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y : D} {f : X ⟶ Y} (hf : RelativeMorphismProperty F P f)
    {a : C} (g : F.obj a ⟶ Y) :
    P (hf.rep.snd g) :=
  hf.property_snd g

/-- Relative morphism properties compose when the underlying scheme property
is stable under composition (Stacks, Tag `02WK`). -/
theorem relativeMorphismProperty_comp {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.IsStableUnderComposition]
    {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : RelativeMorphismProperty F P f)
    (hg : RelativeMorphismProperty F P g) :
    RelativeMorphismProperty F P (f ≫ g) := by
  exact MorphismProperty.comp_mem (RelativeMorphismProperty F P) f g hf hg

/-- Relative morphism properties are stable under base change (Stacks, Tag
`02WL`). -/
theorem relativeMorphismProperty_baseChange {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y Y' S : D} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    (hg : RelativeMorphismProperty F P g) :
    RelativeMorphismProperty F P g' := by
  exact (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback sq hg

/-! ### Comparison and diagonal criteria -/

/-- The morphism-scheme sanity check: a Yoneda morphism has a relative
morphism property exactly when the original morphism has it (Stacks, Tag
`02WJ`). -/
theorem morphismScheme_property_iff {C : Type u} [Category.{v} C]
    [HasPullbacks C] (P : MorphismProperty C)
    [P.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) :
    PresheafMorphismProperty P (morphismScheme f) ↔ P f := by
  exact MorphismProperty.relative_map_iff

/-- Relative morphism properties are monotone in the underlying scheme
property (Stacks, Tag `02YO`). -/
theorem relativeMorphismProperty_mono {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D}
    {P P' : MorphismProperty C} (h : P ≤ P') :
    RelativeMorphismProperty F P ≤ RelativeMorphismProperty F P' :=
  MorphismProperty.relative_monotone h

/-- The core (diagonal-to-point-map) criterion for relative representability,
corresponding to the first two clauses of Stacks Tag `025W`.  The explicit
preservation assumptions record the products and pullbacks used by the
categorical theorem; the blueprint's separate pairwise-fibre-product clause
is left for a later extension. -/
theorem relativeRepresentable_diag_iff {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {X : D}
    [HasBinaryProducts C] [HasPullbacks C]
    [HasPullbacks D] [HasBinaryProducts D] [HasTerminal D]
    [F.Full] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingCospan F] :
    RelativeRepresentable F (Limits.diag X) ↔
      ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), RelativeRepresentable F g :=
  Functor.relativelyRepresentable.diag_iff

/-- An isomorphism has a relative morphism property whenever the underlying
property is multiplicative (and hence contains isomorphisms). -/
theorem relativeMorphismProperty_of_isIso {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso]
    {X Y : D} (f : X ⟶ Y) [IsIso f] :
    RelativeMorphismProperty F P f := by
  letI : (P.relative F).IsMultiplicative :=
    MorphismProperty.relative_isMultiplicative P
  exact MorphismProperty.of_isIso _ f

end StacksPart04Lib
