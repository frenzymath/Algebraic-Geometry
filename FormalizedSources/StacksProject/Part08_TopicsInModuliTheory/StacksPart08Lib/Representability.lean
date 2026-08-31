/-
Copyright (c) 2026 The StacksPart08Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart08Lib Contributors
-/

import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Representability interfaces

The moduli-stack chapter uses representable transformations and relative
morphism properties as its categorical substrate.  This module exposes that
substrate through Mathlib's `Functor.relativelyRepresentable` API.  The
geometric existence and algebraicity statements in the blueprint are not
asserted here; these are source-facing, kernel-checked closure lemmas for the
representability layer.
-/

namespace StacksPart08

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe v u v' u'

/-! ### Presheaves and relative representability -/

/-- The `Type v`-valued presheaves on a category `C`. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type v

/-- Relative representability with respect to a test functor. -/
abbrev RelativeRepresentable {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) : MorphismProperty D :=
  F.relativelyRepresentable

/-- A representable transformation between presheaves on `C`. -/
abbrev RepresentableTransformation (C : Type u) [Category.{v} C] :
    MorphismProperty (Presheaf C) :=
  yoneda.relativelyRepresentable

/-- A property imposed on each represented pullback. -/
abbrev RelativeMorphismProperty {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) (P : MorphismProperty C) :
    MorphismProperty D :=
  P.relative F

/-- The relative-property construction for presheaves and Yoneda. -/
abbrev PresheafMorphismProperty {C : Type u} [Category.{v} C]
    (P : MorphismProperty C) : MorphismProperty (Presheaf C) :=
  P.presheaf

/-! ### Yoneda morphisms -/

/-- The Yoneda transformation associated to a morphism of test objects. -/
abbrev morphismScheme {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    yoneda.obj X ⟶ yoneda.obj Y :=
  yoneda.map f

/-- A Yoneda morphism is relatively representable when pullbacks exist. -/
theorem morphismScheme_representable {C : Type u} [Category.{v} C]
    [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    RepresentableTransformation C (morphismScheme f) := by
  exact Functor.relativelyRepresentable.map yoneda f

/-- Scheme-specialized form of `morphismScheme_representable`. -/
theorem scheme_morphism_representable {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RepresentableTransformation Scheme.{u} (morphismScheme f) := by
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

/-- Composition of representable transformations is representable. -/
theorem representableTransformation_comp {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (a : F ⟶ G) (b : G ⟶ H)
    (ha : RepresentableTransformation C a)
    (hb : RepresentableTransformation C b) :
    RepresentableTransformation C (a ≫ b) := by
  exact MorphismProperty.comp_mem (RepresentableTransformation C) a b ha hb

/-- Representability is preserved by a pullback of transformations. -/
theorem representableTransformation_baseChange {C : Type u} [Category.{v} C]
    {F G H K : Presheaf C} {a : F ⟶ G} {b : H ⟶ G}
    {a' : K ⟶ H} {p : K ⟶ F}
    (sq : IsPullback p a' a b)
    (ha : RepresentableTransformation C a) :
    RepresentableTransformation C a' := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ha

/-! Representability is unchanged after replacing source and target by
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

/-- Every isomorphism of presheaves is representable. -/
theorem representableTransformation_of_isIso {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (a : F ⟶ G) [IsIso a] :
    RepresentableTransformation C a := by
  exact Functor.relativelyRepresentable.of_isIso yoneda a

/-- Representable transformations form a multiplicative morphism property. -/
theorem representableTransformation_isMultiplicative (C : Type u)
    [Category.{v} C] :
    (RepresentableTransformation C).IsMultiplicative :=
  Functor.relativelyRepresentable.isMultiplicative yoneda

/-- Representable transformations are stable under arbitrary base change. -/
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

/-- The defining property of a represented pullback. -/
theorem relativeMorphismProperty_property {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y : D} {f : X ⟶ Y} (hf : RelativeMorphismProperty F P f)
    {a b : C} (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (sq : IsPullback fst (F.map snd) f g) : P snd :=
  hf.property g fst snd sq

/-- The selected pullback projection satisfies the relative property. -/
theorem relativeMorphismProperty_property_snd {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y : D} {f : X ⟶ Y} (hf : RelativeMorphismProperty F P f)
    {a : C} (g : F.obj a ⟶ Y) : P (hf.rep.snd g) :=
  hf.property_snd g

/-- Relative morphism properties compose when the underlying property is
stable under composition. -/
theorem relativeMorphismProperty_comp {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.IsStableUnderComposition]
    {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : RelativeMorphismProperty F P f)
    (hg : RelativeMorphismProperty F P g) :
    RelativeMorphismProperty F P (f ≫ g) := by
  exact MorphismProperty.comp_mem (RelativeMorphismProperty F P) f g hf hg

/-- Relative morphism properties are stable under base change. -/
theorem relativeMorphismProperty_baseChange {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    {X Y Y' S : D} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    (hg : RelativeMorphismProperty F P g) :
    RelativeMorphismProperty F P g' := by
  exact (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback sq hg

/-! ### Comparison criteria -/

/-- A Yoneda morphism has a relative morphism property exactly when the
original morphism has it, provided the property is base-change stable. -/
theorem morphismScheme_property_iff {C : Type u} [Category.{v} C]
    [HasPullbacks C] (P : MorphismProperty C)
    [P.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) :
    PresheafMorphismProperty P (morphismScheme f) ↔ P f := by
  exact MorphismProperty.relative_map_iff

/-- Relative morphism properties are monotone in the underlying property. -/
theorem relativeMorphismProperty_mono {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D}
    {P P' : MorphismProperty C} (h : P ≤ P') :
    RelativeMorphismProperty F P ≤ RelativeMorphismProperty F P' :=
  MorphismProperty.relative_monotone h

/-- The diagonal criterion for relative representability.  The explicit
preservation assumptions record the products and pullbacks used by the
categorical theorem. -/
theorem relativeRepresentable_diag_iff {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {X : D}
    [HasBinaryProducts C] [HasPullbacks C]
    [HasPullbacks D] [HasBinaryProducts D] [HasTerminal D]
    [F.Full] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingCospan F] :
    RelativeRepresentable F (Limits.diag X) ↔
      ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), RelativeRepresentable F g :=
  Functor.relativelyRepresentable.diag_iff

/-! A pairwise fibre-product form of the diagonal criterion. -/

/-- Relative representability of a diagonal is equivalent to represented
pullbacks for every pair of maps from test objects. -/
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

/-- An isomorphism has a relative morphism property whenever the underlying
property is multiplicative and respects isomorphisms. -/
theorem relativeMorphismProperty_of_isIso {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {P : MorphismProperty C}
    [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso]
    {X Y : D} (f : X ⟶ Y) [IsIso f] :
    RelativeMorphismProperty F P f := by
  letI : (P.relative F).IsMultiplicative :=
    MorphismProperty.relative_isMultiplicative P
  exact MorphismProperty.of_isIso _ f

end StacksPart08
