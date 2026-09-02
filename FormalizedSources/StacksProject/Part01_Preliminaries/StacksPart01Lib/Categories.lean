import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Yoneda

universe u v w

/-!
# StacksPart01Lib.Categories

Basic categorical facts corresponding to Stacks tags 0017, 0018, and 003B.
-/

namespace StacksPart01Lib

open CategoryTheory

/-- The Yoneda correspondence identifies natural transformations from a
representable functor with the value of the target functor (Stacks, Tag 001P).
-/
noncomputable def yoneda_equiv {C : Type u} [Category.{v} C] {X : C}
    {F : Cᵒᵖ ⥤ Type v} :
    (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X) := by
  exact CategoryTheory.yonedaEquiv

/-!
An isomorphism is exactly a morphism admitting a two-sided inverse.  This is
the explicit form of the definition used in Stacks tag 0017.
-/
theorem isIso_iff_exists_inverse {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) :
    IsIso f ↔ ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · intro hf
    letI : IsIso f := hf
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
  · rintro ⟨g, hfg, hgf⟩
    exact IsIso.mk ⟨g, hfg, hgf⟩

/-!
The inverse in tag 0017 is unique.
-/
theorem inverse_unique {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y}
    {g h : Y ⟶ X}
    (hg : f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y)
    (hh : f ≫ h = 𝟙 X ∧ h ≫ f = 𝟙 Y) :
    g = h := by
  calc
    g = 𝟙 Y ≫ g := by simp
    _ = (h ≫ f) ≫ g := by rw [hh.2]
    _ = h ≫ (f ≫ g) := by simp only [Category.assoc]
    _ = h ≫ 𝟙 X := by rw [hg.1]
    _ = h := by simp

/-!
A category is a groupoid precisely when all of its morphisms are invertible,
the formulation of Stacks tag 0018.
-/
theorem isGroupoid_iff_all_isIso {C : Type*} [Category C] :
    IsGroupoid C ↔ ∀ {X Y : C} (f : X ⟶ Y), IsIso f := by
  constructor
  · intro h X Y f
    letI : IsGroupoid C := h
    exact IsGroupoid.all_isIso f
  · intro h
    exact IsGroupoid.mk h

/-!
Invertible morphisms are both monomorphisms and epimorphisms, as in the basic
mono/epi discussion of Stacks tag 003B.
-/
theorem isIso_mono_of {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : Mono f := by infer_instance

theorem isIso_epi_of {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : Epi f := by infer_instance

/-!
Cancellation gives the concrete form of the mono and epi conditions used
throughout the categorical preliminaries.
-/
theorem mono_cancel_iff {C : Type*} [Category C] {X Y Z : C}
    (f : Y ⟶ X) [Mono f] {g h : Z ⟶ Y} :
    g ≫ f = h ≫ f ↔ g = h := by
  exact CategoryTheory.cancel_mono f

theorem epi_cancel_iff {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} :
    f ≫ g = f ≫ h ↔ g = h := by
  exact CategoryTheory.cancel_epi f

theorem mono_comp {C : Type*} [Category C] {X Y Z : C}
    (g : Z ⟶ Y) (f : Y ⟶ X) [Mono g] [Mono f] : Mono (g ≫ f) := by
  exact CategoryTheory.mono_comp g f

theorem epi_comp {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [Epi g] : Epi (f ≫ g) := by
  exact CategoryTheory.epi_comp f g

/- A section (respectively retraction) exhibits a split mono (respectively
split epi), hence gives the corresponding cancellation property. -/
theorem mono_of_has_retraction {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (r : Y ⟶ X) (h : f ≫ r = 𝟙 X) : Mono f := by
  letI : IsSplitMono f := IsSplitMono.mk ⟨⟨r, h⟩⟩
  exact IsSplitMono.mono f

theorem epi_of_has_section {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (s : Y ⟶ X) (h : s ≫ f = 𝟙 Y) : Epi f := by
  letI : IsSplitEpi f := IsSplitEpi.mk ⟨⟨s, h⟩⟩
  exact IsSplitEpi.epi f

theorem mono_of_mono_comp {C : Type*} [Category C] {X Y Z : C}
    (g : Z ⟶ Y) (f : Y ⟶ X) [Mono (g ≫ f)] : Mono g := by
  exact CategoryTheory.mono_of_mono_fac (f := f) (g := g) (h := g ≫ f) rfl

theorem epi_of_epi_comp {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g := by
  exact CategoryTheory.epi_of_epi_fac (f := f) (g := g) (h := f ≫ g) rfl

theorem functor_map_mono_of_retraction {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X) : Mono (F.map f) := by
  apply mono_of_has_retraction (F.map f) (F.map r)
  rw [← F.map_comp, h, F.map_id]

theorem functor_map_epi_of_section {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (s : Y ⟶ X)
    (h : s ≫ f = 𝟙 Y) : Epi (F.map f) := by
  apply epi_of_has_section (F.map f) (F.map s)
  rw [← F.map_comp, h, F.map_id]

theorem isIso_comp {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso g] : IsIso (f ≫ g) := by
  exact CategoryTheory.IsIso.comp_isIso

theorem functor_map_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (X : C) : F.map (𝟙 X) = 𝟙 (F.obj X) := by
  exact F.map_id X

theorem functor_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  exact F.map_comp f g

/- Finite products and equalizers (respectively coproducts and coequalizers)
are enough to construct all finite limits (respectively colimits). -/
theorem hasFiniteLimitsOfFiniteProductsAndEqualizers
    (C : Type u) [Category.{v} C] [Limits.HasFiniteProducts C]
    [Limits.HasEqualizers C] : Limits.HasFiniteLimits C :=
  Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products

theorem hasFiniteColimitsOfFiniteCoproductsAndCoequalizers
    (C : Type u) [Category.{v} C] [Limits.HasFiniteCoproducts C]
    [Limits.HasCoequalizers C] : Limits.HasFiniteColimits C :=
  Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/- Products and equalizers suffice to construct all limits (Stacks, Tag 002N). -/
theorem hasLimitsOfProductsAndEqualizers
    (C : Type u) [Category.{v} C] [Limits.HasProducts.{w} C]
    [Limits.HasEqualizers C] : Limits.HasLimitsOfSize.{w, w} C :=
  Limits.has_limits_of_hasEqualizers_and_products

/- Coproducts and coequalizers suffice to construct all colimits
(Stacks, Tag 002P). -/
theorem hasColimitsOfCoproductsAndCoequalizers
    (C : Type u) [Category.{v} C] [Limits.HasCoproducts.{w} C]
    [Limits.HasCoequalizers C] : Limits.HasColimitsOfSize.{w, w} C :=
  Limits.has_colimits_of_hasCoequalizers_and_coproducts

end StacksPart01Lib
