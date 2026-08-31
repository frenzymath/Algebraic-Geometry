/-
Copyright (c) 2026 The StacksPart07Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart07Lib Contributors
-/

import StacksPart07Lib.ProductRepresentability
import StacksPart07Lib.RepresentabilityAdvanced

/-!
# Products of relative morphism properties

This file supplies the product closure for the relative-property interface.
It is the categorical form of the algebraic-stacks blueprint's product
representable-transformations-property lemma (Stacks tag `045E`).
-/

namespace StacksPart07Lib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

/-- Relative morphism properties are closed under products.

The product test functor and product morphism property are formed
componentwise.  The proof chooses the represented pullback supplied by each
factor and combines the two pullback squares with `isPullback_prod_category`.
-/
theorem relativeMorphismProperty_prod
    {C₁ : Type u₁} [Category.{v₁} C₁]
    {D₁ : Type u₂} [Category.{v₂} D₁]
    {C₂ : Type u₃} [Category.{v₃} C₂]
    {D₂ : Type u₄} [Category.{v₄} D₂]
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
    {P₁ : MorphismProperty C₁} {P₂ : MorphismProperty C₂}
    [F₁.Faithful] [F₁.Full] [F₂.Faithful] [F₂.Full]
    [P₁.RespectsIso] [P₂.RespectsIso]
    {X₁ Y₁ : D₁} {X₂ Y₂ : D₂}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (h₁ : RelativeMorphismProperty F₁ P₁ f₁)
    (h₂ : RelativeMorphismProperty F₂ P₂ f₂) :
    RelativeMorphismProperty (F₁.prod F₂) (MorphismProperty.prod P₁ P₂)
      (Prod.mkHom f₁ f₂) := by
  letI : (F₁.prod F₂).Faithful :=
    { map_injective := by
        intro X Y f g h
        apply Prod.hom_ext
        · apply F₁.map_injective
          exact congrArg Prod.fst h
        · apply F₂.map_injective
          exact congrArg Prod.snd h }
  letI : (F₁.prod F₂).Full :=
    { map_surjective := by
        intro X Y f
        refine ⟨Prod.mkHom (F₁.preimage f.1) (F₂.preimage f.2), ?_⟩
        apply Prod.hom_ext <;> simp }
  letI : (MorphismProperty.prod P₁ P₂).RespectsIso :=
    RespectsIso.mk _
      (fun e f hf => by
        letI : IsIso e.hom.1 :=
          ((isIso_prod_iff (f := e.hom)).mp (inferInstance : IsIso e.hom)).1
        letI : IsIso e.hom.2 :=
          ((isIso_prod_iff (f := e.hom)).mp (inferInstance : IsIso e.hom)).2
        exact ⟨RespectsIso.precomp P₁ e.hom.1 f.1 hf.1,
          RespectsIso.precomp P₂ e.hom.2 f.2 hf.2⟩)
      (fun e f hf => by
        letI : IsIso e.hom.1 :=
          ((isIso_prod_iff (f := e.hom)).mp (inferInstance : IsIso e.hom)).1
        letI : IsIso e.hom.2 :=
          ((isIso_prod_iff (f := e.hom)).mp (inferInstance : IsIso e.hom)).2
        exact ⟨RespectsIso.postcomp P₁ e.hom.1 f.1 hf.1,
          RespectsIso.postcomp P₂ e.hom.2 f.2 hf.2⟩)
  apply MorphismProperty.relative.of_exists
  intro a g
  refine ⟨(h₁.rep.pullback g.1, h₂.rep.pullback g.2),
    Prod.mkHom (h₁.rep.fst g.1) (h₂.rep.fst g.2),
    Prod.mkHom (h₁.rep.snd g.1) (h₂.rep.snd g.2),
    isPullback_prod_category (h₁.rep.isPullback g.1) (h₂.rep.isPullback g.2), ?_⟩
  exact ⟨h₁.property_snd g.1, h₂.property_snd g.2⟩

end StacksPart07Lib
