/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.SectionsBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Section rings of a test object: pullback algebra maps and the affine identification

The Layer-2 étale Picard functor (`AlgebraicJacobian.Picard.PicEt`) evaluates the
affine-level plus construction `PicEtAff C ·` at the section rings `Γ(T.left, U)` of a
test object `T : Over (Spec k)`, with their `k`-algebra structure
`Over.sectionsAlgebra` (`AlgebraicJacobian.Cohomology.SectionsBaseChange`; a local
instance, per the house rule).  This file extends the section-ring toolkit:

* `AlgebraicGeometry.Over.resAlgHom_comp`, `Over.resAlgHom_rfl`: strict functoriality of
  restriction of sections.
* `AlgebraicGeometry.Over.appLEAlgHom f V U e`: pullback of sections along a morphism
  `f : T' ⟶ T` of test objects, from `V ⊆ T.left` to `U ⊆ f⁻¹ V ⊆ T'.left`, as a
  `k`-algebra map; composition laws against itself (`appLEAlgHom_comp`) and against
  restrictions (`resAlgHom_comp_appLEAlgHom`, `appLEAlgHom_comp_resAlgHom`), and the
  identity law (`appLEAlgHom_id`).
* `AlgebraicGeometry.Over.overSpecΓTopAlgEquiv k A`: the identification
  `Γ((overSpec k A).left, ⊤) ≃ₐ[k] A` through `Scheme.ΓSpecIso` — the bridge between the
  section-ring world and the test-algebra world on affine tests.
* `AlgebraicGeometry.Over.isScalarTower_sections_basicOpen`: mathlib's restriction
  algebra `Γ(T.left, U) → Γ(T.left, basicOpen r)` is a `k`-algebra tower, making the
  localization theory of basic opens (`IsAffineOpen.isLocalization_basicOpen`)
  available over the base field.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-- `appLE` respects equality of morphisms (with proof-irrelevant inclusion data). -/
lemma Hom.appLE_congr_hom {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f') (V : Y.Opens)
    (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) (e' : U ≤ f' ⁻¹ᵁ V) :
    f.appLE V U e = f'.appLE V U e' := by
  subst hf
  rfl

end Scheme

namespace Over

variable {k : Type u} [Field k]

attribute [local instance] Over.sectionsAlgebra

/-- Restriction of sections is strictly functorial. -/
lemma resAlgHom_comp (T : Over (Spec (.of k))) {U V W : T.left.Opens} (h : U ≤ V)
    (h' : V ≤ W) :
    (resAlgHom T h).comp (resAlgHom T h') = resAlgHom T (h.trans h') := by
  have key : T.left.presheaf.map (homOfLE h').op ≫ T.left.presheaf.map (homOfLE h).op
      = T.left.presheaf.map (homOfLE (h.trans h')).op := by
    rw [← Functor.map_comp, ← op_comp, homOfLE_comp]
  ext s
  exact congr($(key).hom s)

/-- Restriction along the trivial inclusion is the identity. -/
lemma resAlgHom_rfl (T : Over (Spec (.of k))) {U : T.left.Opens} (h : U ≤ U) :
    resAlgHom T h = AlgHom.id k Γ(T.left, U) := by
  have key : T.left.presheaf.map (homOfLE h).op = 𝟙 Γ(T.left, U) := by
    rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from rfl, CategoryTheory.Functor.map_id]
  ext s
  exact congr($(key).hom s)

/-- The algebra structure maps of `Over.sectionsAlgebra` intertwine pullback of sections
along a morphism of test objects. -/
lemma algebraMap_sections_comp_appLE {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (V : T.left.Opens) (U : T'.left.Opens) (e : U ≤ f.left ⁻¹ᵁ V) :
    CommRingCat.ofHom (algebraMap k Γ(T.left, V)) ≫ f.left.appLE V U e
      = CommRingCat.ofHom (algebraMap k Γ(T'.left, U)) := by
  rw [Over.ofHom_algebraMap_sections, Over.ofHom_algebraMap_sections, Category.assoc,
    Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_congr_hom (Over.w f) ⊤ U _
      (le_top.trans (Scheme.Hom.preimage_top T'.hom).ge)]

/-- Pullback of sections along a morphism `f : T' ⟶ T` of test objects, from an open
`V ⊆ T.left` to an open `U ⊆ f⁻¹ V` of `T'.left`, as a `k`-algebra map (with the
`Over.sectionsAlgebra` structures). -/
noncomputable def appLEAlgHom {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (V : T.left.Opens)
    (U : T'.left.Opens) (e : U ≤ f.left ⁻¹ᵁ V) : Γ(T.left, V) →ₐ[k] Γ(T'.left, U) where
  __ := (f.left.appLE V U e).hom
  commutes' r := congr($(algebraMap_sections_comp_appLE f V U e).hom r)

@[simp]
lemma appLEAlgHom_apply {T T' : Over (Spec (.of k))} (f : T' ⟶ T) (V : T.left.Opens)
    (U : T'.left.Opens) (e : U ≤ f.left ⁻¹ᵁ V) (s : Γ(T.left, V)) :
    appLEAlgHom f V U e s = f.left.appLE V U e s :=
  rfl

/-- Pullback of sections along a composite of test morphisms is the composite of the
pullbacks. -/
lemma appLEAlgHom_comp {T T' T'' : Over (Spec (.of k))} (f : T' ⟶ T) (g : T'' ⟶ T')
    (V : T.left.Opens) (U : T'.left.Opens) (W : T''.left.Opens) (e₁ : U ≤ f.left ⁻¹ᵁ V)
    (e₂ : W ≤ g.left ⁻¹ᵁ U) (e₃ : W ≤ (g ≫ f).left ⁻¹ᵁ V) :
    (appLEAlgHom g U W e₂).comp (appLEAlgHom f V U e₁) = appLEAlgHom (g ≫ f) V W e₃ := by
  have key : f.left.appLE V U e₁ ≫ g.left.appLE U W e₂ = (g ≫ f).left.appLE V W e₃ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_congr_hom (Over.comp_left _ _ _ g f).symm V W _ e₃
  ext s
  exact congr($(key).hom s)

/-- Pullback of sections along the identity is restriction. -/
lemma appLEAlgHom_id (T : Over (Spec (.of k))) (V U : T.left.Opens)
    (e : U ≤ Over.Hom.left (𝟙 T) ⁻¹ᵁ V) (e' : U ≤ V) :
    appLEAlgHom (𝟙 T) V U e = resAlgHom T e' := by
  have key : (Over.Hom.left (𝟙 T)).appLE V U e
      = T.left.presheaf.map (homOfLE e').op := by
    rw [Scheme.Hom.appLE_congr_hom (Over.id_left T) V U e e', Scheme.Hom.appLE,
      Scheme.Hom.id_app]
    exact Category.id_comp _
  ext s
  exact congr($(key).hom s)

/-- Restriction after pullback collapses to a single pullback. -/
lemma resAlgHom_comp_appLEAlgHom {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    (V : T.left.Opens) {U U' : T'.left.Opens} (e : U ≤ f.left ⁻¹ᵁ V) (h : U' ≤ U) :
    (resAlgHom T' h).comp (appLEAlgHom f V U e) = appLEAlgHom f V U' (h.trans e) := by
  have key : f.left.appLE V U e ≫ T'.left.presheaf.map (homOfLE h).op
      = f.left.appLE V U' (h.trans e) := by rw [Scheme.Hom.appLE_map]
  ext s
  exact congr($(key).hom s)

/-- Pullback after restriction collapses to a single pullback. -/
lemma appLEAlgHom_comp_resAlgHom {T T' : Over (Spec (.of k))} (f : T' ⟶ T)
    {V V' : T.left.Opens} (U : T'.left.Opens) (h : V ≤ V') (e : U ≤ f.left ⁻¹ᵁ V)
    (e' : U ≤ f.left ⁻¹ᵁ V') :
    (appLEAlgHom f V U e).comp (resAlgHom T h) = appLEAlgHom f V' U e' := by
  have key : T.left.presheaf.map (homOfLE h).op ≫ f.left.appLE V U e
      = f.left.appLE V' U e' := by rw [Scheme.Hom.map_appLE]
  ext s
  exact congr($(key).hom s)

/-- Scalars from the base field restrict through any section ring: the restriction
algebra of a basic open (mathlib's `Scheme.algebra_section_section_basicOpen`) is a
`k`-algebra tower over `Over.sectionsAlgebra`. -/
instance isScalarTower_sections_basicOpen (T : Over (Spec (.of k))) (U : T.left.Opens)
    (r : Γ(T.left, U)) :
    IsScalarTower k Γ(T.left, U) Γ(T.left, T.left.basicOpen r) :=
  IsScalarTower.of_algebraMap_eq' (by
    have h := Over.algebraMap_sections_comp_res T (T.left.basicOpen_le r)
    exact congrArg CommRingCat.Hom.hom h.symm)

section OverSpec

variable (k) (A : Type u) [CommRing A] [Algebra k A]

/-- The `ΓSpecIso` identification intertwines the `Over.sectionsAlgebra` structure map of
the affine test `overSpec k A` with the structure map of `A`. -/
lemma algebraMap_sections_comp_ΓSpecIso_hom :
    CommRingCat.ofHom (algebraMap k Γ((overSpec k A).left, ⊤))
        ≫ (Scheme.ΓSpecIso (.of A)).hom
      = CommRingCat.ofHom (algebraMap k A) := by
  have h₁ : (overSpec k A).hom.appLE ⊤ ⊤ (le_top.trans
        (Scheme.Hom.preimage_top (overSpec k A).hom).ge)
      = (overSpec k A).hom.appTop :=
    Scheme.Hom.appLE_eq_app _
  have h₂ : (overSpec k A).hom.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom
      = (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k A) :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k A))
  rw [Over.ofHom_algebraMap_sections, h₁, Category.assoc, h₂, Iso.inv_hom_id_assoc]

/-- The global sections of an affine test object `overSpec k A`, identified with the
test algebra `A` as a `k`-algebra through `Scheme.ΓSpecIso`. -/
noncomputable def overSpecΓTopAlgEquiv : Γ((overSpec k A).left, ⊤) ≃ₐ[k] A :=
  AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv)
    (fun r => congr($(algebraMap_sections_comp_ΓSpecIso_hom k A).hom r))

@[simp]
lemma overSpecΓTopAlgEquiv_apply (s : Γ((overSpec k A).left, ⊤)) :
    overSpecΓTopAlgEquiv k A s = (Scheme.ΓSpecIso (.of A)).hom s :=
  rfl

@[simp]
lemma overSpecΓTopAlgEquiv_symm_apply (a : A) :
    (overSpecΓTopAlgEquiv k A).symm a = (Scheme.ΓSpecIso (.of A)).inv a :=
  rfl

end OverSpec

end Over

end AlgebraicGeometry
