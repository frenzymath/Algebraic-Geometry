/-
Copyright (c) 2026 StacksPart04Lib authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The StacksPart04Lib Contributors
-/

import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Logic.Relation

/-!
# StacksPart04Lib.QuotientFoundations

Generic set-theoretic and categorical quotient foundations for Chapter 14.
The definitions are independent of geometric hypotheses: an invariant map is
constant on the chosen equivalence relation, while a categorical quotient is
characterized by its equalizing and universal factorization properties.
-/

namespace StacksPart04Lib

open CategoryTheory

universe u v

/-- A map is invariant for a setoid when it is constant on related points. -/
def Invariant {U X : Type _} (r : Setoid U) (φ : U → X) : Prop :=
  ∀ ⦃a b : U⦄, r.r a b → φ a = φ b

/-! ## Categorical quotients -/

/-- A categorical quotient equalizes a parallel pair and has the expected
universal factorization property.  This is the abstract categorical core of
the quotient definition in the source. -/
def CategoricalQuotient {C : Type u} [Category.{v} C]
    {R U X : C} (s t : R ⟶ U) (φ : U ⟶ X) : Prop :=
  s ≫ φ = t ≫ φ ∧
    ∀ {Y : C} (ψ : U ⟶ Y), s ≫ ψ = t ≫ ψ →
      ∃ χ : X ⟶ Y, φ ≫ χ = ψ ∧
        ∀ χ' : X ⟶ Y, φ ≫ χ' = ψ → χ' = χ

/-- Two categorical quotients of the same parallel pair are uniquely
isomorphic over the quotient map. -/
theorem categorical_quotient_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C] {R U X Y : C}
    {s t : R ⟶ U} {φ : U ⟶ X} {ψ : U ⟶ Y}
    (hφ : CategoricalQuotient s t φ)
    (hψ : CategoricalQuotient s t ψ) :
    ∃ e : X ≅ Y, φ ≫ e.hom = ψ ∧
      ∀ e' : X ≅ Y, φ ≫ e'.hom = ψ → e' = e := by
  obtain ⟨e, he, he_unique⟩ := hφ.2 ψ hψ.1
  obtain ⟨d, hd, hd_unique⟩ := hψ.2 φ hφ.1
  obtain ⟨a, ha, ha_unique⟩ := hφ.2 φ hφ.1
  obtain ⟨b, hb, hb_unique⟩ := hψ.2 ψ hψ.1
  have hed : e ≫ d = 𝟙 X := by
    have hcomp : φ ≫ (e ≫ d) = φ := by rw [← Category.assoc, he, hd]
    have hident : φ ≫ 𝟙 X = φ := Category.comp_id φ
    exact (ha_unique (e ≫ d) hcomp).trans (ha_unique (𝟙 X) hident).symm
  have hde : d ≫ e = 𝟙 Y := by
    have hcomp : ψ ≫ (d ≫ e) = ψ := by rw [← Category.assoc, hd, he]
    have hident : ψ ≫ 𝟙 Y = ψ := Category.comp_id ψ
    exact (hb_unique (d ≫ e) hcomp).trans (hb_unique (𝟙 Y) hident).symm
  let i : X ≅ Y := { hom := e, inv := d, hom_inv_id := hed, inv_hom_id := hde }
  refine ⟨i, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact he_unique e'.hom he'

/-- A categorical quotient map is an epimorphism: its universal property
forces any two maps out of the quotient that agree after precomposition to
coincide. -/
theorem categorical_quotient_epi
    {C : Type u} [Category.{v} C] {R U X : C}
    {s t : R ⟶ U} {φ : U ⟶ X}
    (hφ : CategoricalQuotient s t φ) : Epi φ := by
  constructor
  intro Y f g hfg
  have hinvf : s ≫ (φ ≫ f) = t ≫ (φ ≫ f) := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f) hφ.1
  obtain ⟨χ, hχ, hχ_unique⟩ := hφ.2 (φ ≫ f) hinvf
  exact (hχ_unique f rfl).trans (hχ_unique g hfg.symm).symm

/-! ## Setoid quotients in `Type` -/

section TypeQuotient

universe w

/-! The relation-pair type packages the parallel pair whose coequalizer is a
setoid quotient.  Keeping the proof of relatedness in the subtype makes the
construction work for an arbitrary (not necessarily decidable) setoid. -/
def RelationPair {U : Type w} (r : Setoid U) :=
  {p : U × U // r.r p.1 p.2}

def relationFst {U : Type w} {r : Setoid U} : RelationPair r → U :=
  fun p => p.1.1

def relationSnd {U : Type w} {r : Setoid U} : RelationPair r → U :=
  fun p => p.1.2

private def typeHom {A B : Type w} (f : A → B) : (A ⟶ B) :=
  ConcreteCategory.ofHom (TypeCat.Fun.mk f)

/-- The quotient of a setoid is the categorical coequalizer of its relation
pair.  This is the elementary quotient universal property used by the
coequalizer diagrams in the algebraic-space chapters. -/
theorem setoidQuotient_categoricalQuotient {U : Type w} (r : Setoid U) :
    CategoricalQuotient (typeHom (relationFst (r := r)))
      (typeHom (relationSnd (r := r)))
      (typeHom (Quotient.mk r : U → Quotient r)) := by
  constructor
  · apply ConcreteCategory.hom_ext _ _
    intro p
    change Quotient.mk r p.1.1 = Quotient.mk r p.1.2
    exact Quotient.sound p.2
  · intro Y ψ hψ
    have hinv : Invariant r (ConcreteCategory.hom ψ).toFun := by
      intro a b hab
      let p : RelationPair r := ⟨(a, b), hab⟩
      have hp := congrArg (fun k => (ConcreteCategory.hom k).toFun p) hψ
      exact hp
    let χ : Quotient r → Y :=
      Quotient.lift (ConcreteCategory.hom ψ).toFun
        (fun _ _ hab => hinv hab)
    have hχ : χ ∘ Quotient.mk r = (ConcreteCategory.hom ψ).toFun := by
      funext a
      rfl
    let χ' : (Quotient r ⟶ Y) := typeHom χ
    refine ⟨χ', ?_, ?_⟩
    · apply ConcreteCategory.hom_ext _ _
      intro a
      change χ (Quotient.mk r a) = (ConcreteCategory.hom ψ).toFun a
      exact congrFun hχ a
    · intro χ₂ hχ₂
      apply ConcreteCategory.hom_ext _ _
      intro q
      refine Quotient.inductionOn q ?_
      intro a
      change (ConcreteCategory.hom χ₂).toFun (Quotient.mk r a) =
        χ (Quotient.mk r a)
      have h₁ := congrArg (fun k => (ConcreteCategory.hom k).toFun a) hχ₂
      have h₂ := congrFun hχ a
      exact h₁.trans h₂.symm

end TypeQuotient

/-- An invariant map factors through the quotient by the relation. -/
theorem invariant_iff_factors_through_quotient {U X : Type _} (r : Setoid U)
    (φ : U → X) :
    Invariant r φ ↔ ∃ ψ : Quotient r → X, ψ ∘ Quotient.mk r = φ := by
  constructor
  · intro h
    refine ⟨Quotient.lift φ (fun a b hab => h hab), ?_⟩
    funext a
    rfl
  · rintro ⟨ψ, hψ⟩ a b hab
    rw [← hψ]
    exact congrArg ψ (Quotient.sound hab)

/-- A factorization through a quotient is unique. -/
theorem quotient_factorization_unique {U X : Type _} (r : Setoid U) (φ : U → X)
    {ψ χ : Quotient r → X}
    (hψ : ψ ∘ Quotient.mk r = φ)
    (hχ : χ ∘ Quotient.mk r = φ) :
    ψ = χ := by
  funext q
  refine Quotient.inductionOn q ?_
  intro u
  simpa only [Function.comp_apply] using
    (congrFun hψ u).trans (congrFun hχ u).symm

/-- Invariance is equivalent to existence of a unique quotient factorization. -/
theorem invariant_iff_existsUnique_factorization {U X : Type _} (r : Setoid U)
    (φ : U → X) :
    Invariant r φ ↔
      ∃ ψ : Quotient r → X, ψ ∘ Quotient.mk r = φ ∧
        ∀ χ : Quotient r → X, χ ∘ Quotient.mk r = φ → χ = ψ := by
  constructor
  · intro h
    obtain ⟨ψ, hψ⟩ := (invariant_iff_factors_through_quotient r φ).1 h
    refine ⟨ψ, hψ, ?_⟩
    intro χ hχ
    exact (quotient_factorization_unique r φ hψ hχ).symm
  · rintro ⟨ψ, hψ, _⟩
    exact (invariant_iff_factors_through_quotient r φ).2 ⟨ψ, hψ⟩

/-- The orbit generated by a (possibly non-symmetric) relation. -/
def orbit {U : Type _} (ρ : U → U → Prop) (u : U) : Set U :=
  {v | Relation.EqvGen ρ u v}

@[simp]
theorem mem_orbit_self {U : Type _} {ρ : U → U → Prop} (u : U) :
    u ∈ orbit ρ u :=
  Relation.EqvGen.refl u

/-- Generated-orbit membership is symmetric. -/
theorem mem_orbit_comm {U : Type _} {ρ : U → U → Prop} {u v : U} :
    v ∈ orbit ρ u ↔ u ∈ orbit ρ v := by
  constructor
  · intro h
    exact Relation.EqvGen.symm u v h
  · intro h
    exact Relation.EqvGen.symm v u h

/-- Points in the same generated orbit have equal generated-orbit sets. -/
theorem orbit_eq_of_mem {U : Type _} {ρ : U → U → Prop} {u v : U}
    (hv : v ∈ orbit ρ u) : orbit ρ v = orbit ρ u := by
  ext w
  constructor
  · intro hw
    exact Relation.EqvGen.trans u v w hv hw
  · intro hw
    exact Relation.EqvGen.trans v u w (Relation.EqvGen.symm u v hv) hw

/-- A map constant on the generating relation is constant on every orbit. -/
theorem invariant_map_constant_on_orbit {U X : Type _} {ρ : U → U → Prop}
    (φ : U → X) (hφ : ∀ ⦃a b : U⦄, ρ a b → φ a = φ b)
    {u v : U} (hv : v ∈ orbit ρ u) : φ u = φ v := by
  induction hv with
  | rel a b hab => exact hφ hab
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

/-- For an equivalence relation, the generated orbit is the original relation. -/
theorem mem_orbit_iff {U : Type _} {ρ : U → U → Prop} (hρ : Equivalence ρ)
    {u v : U} : v ∈ orbit ρ u ↔ ρ u v := by
  exact hρ.eqvGen_iff

/-- Quotient factorization for a map invariant under an arbitrary relation. -/
theorem relation_invariant_iff_factors_through_quotient {U X : Type _}
    (ρ : U → U → Prop) (φ : U → X) :
    (∀ ⦃a b : U⦄, ρ a b → φ a = φ b) ↔
      ∃ ψ : Quotient (Relation.EqvGen.setoid ρ) → X,
        ψ ∘ Quotient.mk (Relation.EqvGen.setoid ρ) = φ := by
  constructor
  · intro h
    apply (invariant_iff_factors_through_quotient
      (Relation.EqvGen.setoid ρ) φ).1
    intro a b hab
    exact invariant_map_constant_on_orbit φ h hab
  · rintro ⟨ψ, hψ⟩ a b hab
    rw [← hψ]
    exact congrArg ψ (Quotient.sound (Relation.EqvGen.rel a b hab))

/-! ## Orbit classes and quotient representatives -/

/-- Two points lie in the same generated orbit exactly when they have the
same representative in the quotient by the generated equivalence relation. -/
theorem mem_orbit_iff_quotient_mk_eq {U : Type _} {ρ : U → U → Prop}
    {u v : U} :
    v ∈ orbit ρ u ↔
      Quotient.mk (Relation.EqvGen.setoid ρ) u =
        Quotient.mk (Relation.EqvGen.setoid ρ) v := by
  change Relation.EqvGen ρ u v ↔ _
  rw [Quotient.eq]
  rfl

/-- Generated orbit sets are the equivalence classes of the generated
relation: two orbit sets agree precisely when their base points are related. -/
theorem orbit_eq_iff_mem {U : Type _} {ρ : U → U → Prop} {u v : U} :
    orbit ρ u = orbit ρ v ↔ v ∈ orbit ρ u := by
  constructor
  · intro h
    rw [h]
    exact mem_orbit_self v
  · intro h
    exact (orbit_eq_of_mem h).symm

/-- Constancy on generated orbits is equivalent to invariance under the
generating relation. -/
theorem invariant_iff_constant_on_orbits {U X : Type _}
    {ρ : U → U → Prop} (φ : U → X) :
    (∀ ⦃a b : U⦄, ρ a b → φ a = φ b) ↔
      ∀ ⦃a b : U⦄, b ∈ orbit ρ a → φ a = φ b := by
  constructor
  · intro h a b hab
    exact invariant_map_constant_on_orbit φ h hab
  · intro h a b hab
    exact h (Relation.EqvGen.rel a b hab)

end StacksPart04Lib
