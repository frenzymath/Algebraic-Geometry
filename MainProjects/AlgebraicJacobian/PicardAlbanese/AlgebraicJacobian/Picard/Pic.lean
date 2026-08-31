/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.UnitsCocycle

/-!
# The definitional Picard group: Čech `H¹` of the units presheaf

For a scheme `X`, this file defines the Picard group of record of this development:
the Čech cohomology `Ȟ¹(X, 𝒪_X^*)` on the small Zariski site, computed on **pointed
covers** (one open per point of `X`, `AlgebraicJacobian.Picard.UnitsCocycle`) and
stabilized along the refinement preorder.

## Main declarations

* `AlgebraicGeometry.Scheme.CechPic`: the Picard group `Ȟ¹(X, 𝒪_X^*)` as the quotient
  of `Σ 𝒰, X.unitsH1 𝒰` by agreement on a common refinement, with its `CommGroup`
  structure and the constructor/eliminator API `CechPic.mk`, `CechPic.ind`,
  `CechPic.mk_eq_mk_iff`, `CechPic.mk_unitsRes`, `CechPic.mk_mul_mk_inf`.
* `AlgebraicGeometry.Scheme.CechPic.map`: contravariant functoriality — for
  `f : X ⟶ Y` the pullback `Y.CechPic →* X.CechPic` — with the strict functor laws
  `CechPic.map_id` and `CechPic.map_comp` (the lane keystone).
* `AlgebraicGeometry.Scheme.CechPic.subsingleton_of_subsingleton`: on a scheme with a
  subsingleton underlying space (e.g. `Spec` of a field) the Picard group is trivial.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

namespace Scheme

variable {X Y Z : Scheme.{u}}

/-! ## The Picard group  -/

instance cechPicSetoid (X : Scheme.{u}) : Setoid (Σ 𝒰 : X.PointedCover, X.unitsH1 𝒰) where
  r p q := ∃ (𝒲 : X.PointedCover) (h₁ : 𝒲 ≤ p.1) (h₂ : 𝒲 ≤ q.1),
    unitsRes h₁ p.2 = unitsRes h₂ q.2
  iseqv := by
    constructor
    · exact fun p ↦ ⟨p.1, le_rfl, le_rfl, rfl⟩
    · rintro p q ⟨𝒲, h₁, h₂, e⟩
      exact ⟨𝒲, h₂, h₁, e.symm⟩
    · rintro p q r ⟨𝒲₁, h₁, h₂, e₁⟩ ⟨𝒲₂, h₃, h₄, e₂⟩
      refine ⟨𝒲₁ ⊓ 𝒲₂, inf_le_left.trans h₁, inf_le_right.trans h₄, ?_⟩
      have e₁' := congrArg (unitsRes (inf_le_left : 𝒲₁ ⊓ 𝒲₂ ≤ 𝒲₁)) e₁
      have e₂' := congrArg (unitsRes (inf_le_right : 𝒲₁ ⊓ 𝒲₂ ≤ 𝒲₂)) e₂
      simp only [unitsRes_unitsRes] at e₁' e₂'
      exact e₁'.trans e₂'

/-- The definitional Picard group of a scheme: Čech `H¹` of the units presheaf,
stabilized along refinement of pointed covers. -/
def CechPic (X : Scheme.{u}) : Type u :=
  Quotient (cechPicSetoid X)

namespace CechPic

/-- The Picard class of a unit Čech `H¹` class on a pointed cover. -/
def mk (𝒰 : X.PointedCover) (a : X.unitsH1 𝒰) : X.CechPic :=
  ⟦⟨𝒰, a⟩⟧

@[elab_as_elim]
theorem ind {motive : X.CechPic → Prop}
    (mk : ∀ (𝒰 : X.PointedCover) (a : X.unitsH1 𝒰), motive (mk 𝒰 a)) (x : X.CechPic) :
    motive x :=
  Quotient.ind (fun p ↦ by obtain ⟨𝒰, a⟩ := p; exact mk 𝒰 a) x

theorem mk_eq_mk_iff {𝒰 𝒱 : X.PointedCover} {a : X.unitsH1 𝒰} {b : X.unitsH1 𝒱} :
    mk 𝒰 a = mk 𝒱 b ↔
      ∃ (𝒲 : X.PointedCover) (h₁ : 𝒲 ≤ 𝒰) (h₂ : 𝒲 ≤ 𝒱),
        unitsRes h₁ a = unitsRes h₂ b :=
  Quotient.eq

/-- Two classes agreeing after restriction to a common refinement are equal; in
particular `mk` is invariant under restriction. -/
@[simp]
theorem mk_unitsRes {𝒰 𝒱 : X.PointedCover} (h : 𝒱 ≤ 𝒰) (a : X.unitsH1 𝒰) :
    mk 𝒱 (unitsRes h a) = mk 𝒰 a :=
  Quotient.sound ⟨𝒱, le_rfl, h, unitsRes_rfl _⟩

private def mulSig (p q : Σ 𝒰 : X.PointedCover, X.unitsH1 𝒰) :
    Σ 𝒰 : X.PointedCover, X.unitsH1 𝒰 :=
  ⟨p.1 ⊓ q.1, unitsRes inf_le_left p.2 * unitsRes inf_le_right q.2⟩

private lemma mulSig_assoc {𝒰 𝒱 𝒳 : X.PointedCover} (a : X.unitsH1 𝒰) (b : X.unitsH1 𝒱)
    (c : X.unitsH1 𝒳) :
    mk (𝒰 ⊓ 𝒱 ⊓ 𝒳)
        (unitsRes inf_le_left (unitsRes inf_le_left a * unitsRes inf_le_right b) *
          unitsRes inf_le_right c)
      = mk (𝒰 ⊓ (𝒱 ⊓ 𝒳))
        (unitsRes inf_le_left a *
          unitsRes inf_le_right (unitsRes inf_le_left b * unitsRes inf_le_right c)) := by
  refine mk_eq_mk_iff.mpr ⟨𝒰 ⊓ 𝒱 ⊓ 𝒳, le_rfl, (inf_assoc 𝒰 𝒱 𝒳).le, ?_⟩
  simp only [map_mul, unitsRes_unitsRes, unitsRes_rfl]
  exact mul_assoc _ _ _

private lemma mulSig_compat {p p' q q' : Σ 𝒰 : X.PointedCover, X.unitsH1 𝒰}
    (hp : p ≈ p') (hq : q ≈ q') : mulSig p q ≈ mulSig p' q' := by
  obtain ⟨𝒲₁, h₁, h₂, e₁⟩ := hp
  obtain ⟨𝒲₂, h₃, h₄, e₂⟩ := hq
  have e₁' := congrArg (unitsRes (inf_le_left : 𝒲₁ ⊓ 𝒲₂ ≤ 𝒲₁)) e₁
  have e₂' := congrArg (unitsRes (inf_le_right : 𝒲₁ ⊓ 𝒲₂ ≤ 𝒲₂)) e₂
  simp only [unitsRes_unitsRes] at e₁' e₂'
  refine ⟨𝒲₁ ⊓ 𝒲₂, inf_le_inf h₁ h₃, inf_le_inf h₂ h₄, ?_⟩
  show unitsRes (inf_le_inf h₁ h₃) (unitsRes inf_le_left p.2 * unitsRes inf_le_right q.2)
      = unitsRes (inf_le_inf h₂ h₄) (unitsRes inf_le_left p'.2 * unitsRes inf_le_right q'.2)
  simp only [map_mul, unitsRes_unitsRes]
  rw [e₁', e₂']

instance : CommGroup X.CechPic where
  mul := Quotient.map₂ mulSig (fun _ _ hp _ _ hq ↦ mulSig_compat hp hq)
  one := mk ⊤ 1
  inv := Quotient.map (fun p ↦ ⟨p.1, p.2⁻¹⟩) (by
    rintro p p' ⟨𝒲, h₁, h₂, e⟩
    exact ⟨𝒲, h₁, h₂, by simp only [map_inv, e]⟩)
  mul_assoc a b c := by
    induction a using CechPic.ind with | _ 𝒰 a =>
    induction b using CechPic.ind with | _ 𝒱 b =>
    induction c using CechPic.ind with | _ 𝒳 c =>
    exact mulSig_assoc a b c
  one_mul a := by
    induction a using CechPic.ind with | _ 𝒰 a =>
    show mk (⊤ ⊓ 𝒰) (unitsRes inf_le_left (1 : X.unitsH1 ⊤) * unitsRes inf_le_right a)
      = mk 𝒰 a
    rw [map_one, one_mul, mk_unitsRes]
  mul_one a := by
    induction a using CechPic.ind with | _ 𝒰 a =>
    show mk (𝒰 ⊓ ⊤) (unitsRes inf_le_left a * unitsRes inf_le_right (1 : X.unitsH1 ⊤))
      = mk 𝒰 a
    rw [map_one, mul_one, mk_unitsRes]
  inv_mul_cancel a := by
    induction a using CechPic.ind with | _ 𝒰 a =>
    show mk (𝒰 ⊓ 𝒰) (unitsRes inf_le_left a⁻¹ * unitsRes inf_le_right a) = mk ⊤ 1
    have h : unitsRes (inf_le_left : 𝒰 ⊓ 𝒰 ≤ 𝒰) a⁻¹
        * unitsRes (inf_le_right : 𝒰 ⊓ 𝒰 ≤ 𝒰) a = 1 := by
      rw [map_inv]
      exact inv_mul_cancel _
    rw [h]
    exact Quotient.sound ⟨𝒰 ⊓ 𝒰, le_rfl, le_top, by rw [map_one, map_one]⟩
  mul_comm a b := by
    induction a using CechPic.ind with | _ 𝒰 a =>
    induction b using CechPic.ind with | _ 𝒱 b =>
    show mk (𝒰 ⊓ 𝒱) (unitsRes inf_le_left a * unitsRes inf_le_right b)
      = mk (𝒱 ⊓ 𝒰) (unitsRes inf_le_left b * unitsRes inf_le_right a)
    refine mk_eq_mk_iff.mpr ⟨𝒰 ⊓ 𝒱, le_rfl, le_inf inf_le_right inf_le_left, ?_⟩
    simp only [map_mul, unitsRes_unitsRes, unitsRes_rfl]
    exact mul_comm _ _

lemma one_def : (1 : X.CechPic) = mk ⊤ 1 :=
  rfl

/-- Multiplication of Picard classes on representatives: restrict both to the common
refinement `𝒰 ⊓ 𝒱` and multiply there. Holds by definition. -/
lemma mk_mul_mk_inf {𝒰 𝒱 : X.PointedCover} (a : X.unitsH1 𝒰) (b : X.unitsH1 𝒱) :
    mk 𝒰 a * mk 𝒱 b
      = mk (𝒰 ⊓ 𝒱) (unitsRes inf_le_left a * unitsRes inf_le_right b) :=
  rfl

@[simp]
lemma mk_one (𝒰 : X.PointedCover) : mk 𝒰 (1 : X.unitsH1 𝒰) = 1 :=
  Quotient.sound ⟨𝒰, le_rfl, le_top, by rw [map_one, map_one]⟩

@[simp]
lemma mk_mul_mk (𝒰 : X.PointedCover) (a b : X.unitsH1 𝒰) :
    mk 𝒰 a * mk 𝒰 b = mk 𝒰 (a * b) := by
  rw [mk_mul_mk_inf]
  refine mk_eq_mk_iff.mpr ⟨𝒰 ⊓ 𝒰, le_rfl, inf_le_left, ?_⟩
  simp only [map_mul, unitsRes_rfl]

@[simp]
lemma mk_inv (𝒰 : X.PointedCover) (a : X.unitsH1 𝒰) : (mk 𝒰 a)⁻¹ = mk 𝒰 a⁻¹ :=
  rfl

/-! ## Functoriality: pullback of Picard classes -/

private def mapSig (f : X ⟶ Y) (p : Σ 𝒰 : Y.PointedCover, Y.unitsH1 𝒰) :
    Σ 𝒰 : X.PointedCover, X.unitsH1 𝒰 :=
  ⟨p.1.pullback f, f.pullbackUnitsH1 p.1 p.2⟩

private lemma mapSig_compat (f : X ⟶ Y) :
    ∀ {p q : Σ 𝒰 : Y.PointedCover, Y.unitsH1 𝒰}, p ≈ q → mapSig f p ≈ mapSig f q := by
  rintro ⟨𝒰, a⟩ ⟨𝒱, b⟩ ⟨𝒲, h₁, h₂, e⟩
  refine ⟨𝒲.pullback f, PointedCover.pullback_mono f h₁,
    PointedCover.pullback_mono f h₂, ?_⟩
  show unitsRes (PointedCover.pullback_mono f h₁) (f.pullbackUnitsH1 𝒰 a)
      = unitsRes (PointedCover.pullback_mono f h₂) (f.pullbackUnitsH1 𝒱 b)
  rw [Hom.unitsRes_pullbackUnitsH1 f h₁ a, Hom.unitsRes_pullbackUnitsH1 f h₂ b, e]

/-- Contravariant functoriality of the Čech Picard group: pull the cover back pointwise,
pull the unit cocycles back through `f`, restrict. -/
def map (f : X ⟶ Y) : Y.CechPic →* X.CechPic where
  toFun := Quotient.map (mapSig f) fun _ _ h ↦ mapSig_compat f h
  map_one' := by
    show mk ((⊤ : Y.PointedCover).pullback f) (f.pullbackUnitsH1 ⊤ 1) = 1
    rw [map_one, mk_one]
  map_mul' a b := by
    induction a using CechPic.ind with | _ 𝒰 a =>
    induction b using CechPic.ind with | _ 𝒱 b =>
    show mk ((𝒰 ⊓ 𝒱).pullback f)
        (f.pullbackUnitsH1 (𝒰 ⊓ 𝒱) (unitsRes inf_le_left a * unitsRes inf_le_right b))
      = mk (𝒰.pullback f) (f.pullbackUnitsH1 𝒰 a) *
          mk (𝒱.pullback f) (f.pullbackUnitsH1 𝒱 b)
    rw [mk_mul_mk_inf]
    refine mk_eq_mk_iff.mpr ⟨(𝒰 ⊓ 𝒱).pullback f, le_rfl,
      le_inf (PointedCover.pullback_mono f inf_le_left)
        (PointedCover.pullback_mono f inf_le_right), ?_⟩
    simp only [map_mul, ← Hom.unitsRes_pullbackUnitsH1, unitsRes_unitsRes, unitsRes_rfl]

@[simp]
lemma map_mk (f : X ⟶ Y) (𝒰 : Y.PointedCover) (a : Y.unitsH1 𝒰) :
    map f (mk 𝒰 a) = mk (𝒰.pullback f) (f.pullbackUnitsH1 𝒰 a) :=
  rfl

/-- Pullback of Picard classes along the identity is the identity. -/
@[simp]
theorem map_id (X : Scheme.{u}) : map (𝟙 X) = MonoidHom.id X.CechPic := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using CechPic.ind with | _ 𝒰 a =>
  show mk (𝒰.pullback (𝟙 X)) ((𝟙 X : X ⟶ X).pullbackUnitsH1 𝒰 a) = mk 𝒰 a
  have hle : 𝒰.pullback (𝟙 X) ≤ 𝒰 := fun x ↦ le_of_eq (by simp)
  refine mk_eq_mk_iff.mpr ⟨𝒰.pullback (𝟙 X), le_rfl, hle, ?_⟩
  induction a using Quot.ind with | _ γ =>
  refine congrArg (Quot.mk _) ?_
  ext x y T a b
  rw [OneCocycle.res_ev, OneCocycle.res_ev, Hom.pullbackUnitsCocycle_ev,
    γ.toOneCochain.ev_eq_evInf]
  exact id_unitsAppLE _ _

/-- Pullback of Picard classes along a composite (the lane keystone). -/
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = (map f).comp (map g) := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using CechPic.ind with | _ 𝒰 a =>
  show mk (𝒰.pullback (f ≫ g)) ((f ≫ g).pullbackUnitsH1 𝒰 a)
    = mk ((𝒰.pullback g).pullback f)
        (f.pullbackUnitsH1 (𝒰.pullback g) (g.pullbackUnitsH1 𝒰 a))
  have hle : 𝒰.pullback (f ≫ g) ≤ (𝒰.pullback g).pullback f := fun x ↦ le_of_eq (by simp)
  refine mk_eq_mk_iff.mpr ⟨𝒰.pullback (f ≫ g), le_rfl, hle, ?_⟩
  induction a using Quot.ind with | _ γ =>
  refine congrArg (Quot.mk _) ?_
  ext x y T a b
  rw [OneCocycle.res_ev, OneCocycle.res_ev, Hom.pullbackUnitsCocycle_ev,
    Hom.pullbackUnitsCocycle_ev, Hom.pullbackUnitsCocycle_unitsEvInf, unitsAppLE_unitsAppLE]
  rfl

/-! ## Sanity gate: triviality over a field -/

/-- On a scheme with a subsingleton underlying space — e.g. `Spec` of a field — the
Čech Picard group is trivial: every pointed cover is a cover by a single open, on which
every unit cocycle is a coboundary. -/
instance subsingleton_of_subsingleton (X : Scheme.{u}) [Subsingleton X] :
    Subsingleton X.CechPic := by
  refine ⟨fun p q ↦ ?_⟩
  induction p using CechPic.ind with | _ 𝒰 a =>
  induction q using CechPic.ind with | _ 𝒱 b =>
  refine mk_eq_mk_iff.mpr ⟨𝒰 ⊓ 𝒱, inf_le_left, inf_le_right, ?_⟩
  have := H1.subsingleton_of_forall_le (X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
    (𝒰 ⊓ 𝒱).opens (fun i j ↦ le_of_eq (congrArg _ (Subsingleton.elim i j)))
  exact Subsingleton.elim _ _

/-- The Čech Picard group of the spectrum of a field is trivial. -/
theorem eq_one_of_subsingleton (X : Scheme.{u}) [Subsingleton X] (x : X.CechPic) :
    x = 1 :=
  Subsingleton.elim x 1

example {K : Type u} [Field K] (x : (Spec (CommRingCat.of K)).CechPic) : x = 1 :=
  eq_one_of_subsingleton _ x

end CechPic

end Scheme

end AlgebraicGeometry
