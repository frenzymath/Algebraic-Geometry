/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Explicit pullback data for finite-stage constructions

The finite-stage gluing files frequently use `pullback` with independently inferred
`HasPullback` witnesses.  This makes two propositionally equal presentations carry
different dependent objects.  `PullbackData` keeps one cone and one proof of its
universal property together.  The API below is deliberately cone based: using it does
not create or infer a `HasPullback` instance.

`PullbackMapData` packages the three maps in a commuting square.  Its induced map is
defined by the target cone's universal property, so its projection and composition
laws are stable under changes to the surrounding instance environment.
-/

set_option autoImplicit false

universe v u

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicJacobian

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- A chosen pullback cone, including its universal-property witness.

The object and both projections are fields of `cone`; no `HasPullback` typeclass is
used in this record.  In particular, two records retain the exact cones selected by
their producers rather than silently selecting the ambient `pullback` object.
-/
structure PullbackData {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) where
  cone : PullbackCone f g
  isLimit : IsLimit cone

/-- Package the pullback selected by the ambient `HasPullback` instance.

This is an explicit migration boundary for legacy declarations whose statements still use
`pullback`, `pullback.fst`, and `pullback.snd`.  The instance is consulted exactly once, when
the package is built; consumers subsequently use the stored cone and limit proof. -/
noncomputable def PullbackData.ofHasPullback
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : PullbackData f g :=
  { cone := pullback.cone f g
    isLimit := pullback.isLimit f g }

namespace PullbackData

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The chosen pullback object. -/
abbrev pt (P : PullbackData f g) : C := P.cone.pt

/-- The first projection of the chosen pullback cone. -/
abbrev fst (P : PullbackData f g) : P.pt ⟶ X := P.cone.fst

/-- The second projection of the chosen pullback cone. -/
abbrev snd (P : PullbackData f g) : P.pt ⟶ Y := P.cone.snd

/-- The commutativity equation carried by a pullback cone. -/
abbrev condition (P : PullbackData f g) : P.fst ≫ f = P.snd ≫ g := P.cone.condition

/-- The universal map into the chosen pullback object. -/
def lift (P : PullbackData f g) {W : C} (a : W ⟶ X) (b : W ⟶ Y)
    (h : a ≫ f = b ≫ g) : W ⟶ P.pt :=
  P.isLimit.lift (PullbackCone.mk a b h)

@[simp]
theorem lift_fst (P : PullbackData f g) {W : C} (a : W ⟶ X) (b : W ⟶ Y)
    (h : a ≫ f = b ≫ g) : P.lift a b h ≫ P.fst = a := by
  exact PullbackCone.IsLimit.lift_fst P.isLimit a b h

@[simp]
theorem lift_snd (P : PullbackData f g) {W : C} (a : W ⟶ X) (b : W ⟶ Y)
    (h : a ≫ f = b ≫ g) : P.lift a b h ≫ P.snd = b := by
  exact PullbackCone.IsLimit.lift_snd P.isLimit a b h

/-- Maps into a chosen pullback are equal when their two projections agree. -/
theorem hom_ext (P : PullbackData f g) {W : C} {a b : W ⟶ P.pt}
    (h₁ : a ≫ P.fst = b ≫ P.fst) (h₂ : a ≫ P.snd = b ≫ P.snd) : a = b := by
  exact PullbackCone.IsLimit.hom_ext P.isLimit h₁ h₂

/-- The canonical comparison between two chosen presentations of the same pullback. -/
noncomputable def comparison (P Q : PullbackData f g) : P.pt ≅ Q.pt :=
  P.isLimit.conePointUniqueUpToIso Q.isLimit

@[simp]
theorem comparison_hom_fst (P Q : PullbackData f g) :
    (P.comparison Q).hom ≫ Q.fst = P.fst := by
  change (P.isLimit.conePointUniqueUpToIso Q.isLimit).hom ≫
      Q.cone.π.app WalkingCospan.left = P.cone.π.app WalkingCospan.left
  exact P.isLimit.conePointUniqueUpToIso_hom_comp Q.isLimit WalkingCospan.left

@[simp]
theorem comparison_hom_snd (P Q : PullbackData f g) :
    (P.comparison Q).hom ≫ Q.snd = P.snd := by
  change (P.isLimit.conePointUniqueUpToIso Q.isLimit).hom ≫
      Q.cone.π.app WalkingCospan.right = P.cone.π.app WalkingCospan.right
  exact P.isLimit.conePointUniqueUpToIso_hom_comp Q.isLimit WalkingCospan.right

@[simp]
theorem comparison_inv_fst (P Q : PullbackData f g) :
    (P.comparison Q).inv ≫ P.fst = Q.fst := by
  change (P.isLimit.conePointUniqueUpToIso Q.isLimit).inv ≫
      P.cone.π.app WalkingCospan.left = Q.cone.π.app WalkingCospan.left
  exact P.isLimit.conePointUniqueUpToIso_inv_comp Q.isLimit WalkingCospan.left

@[simp]
theorem comparison_inv_snd (P Q : PullbackData f g) :
    (P.comparison Q).inv ≫ P.snd = Q.snd := by
  change (P.isLimit.conePointUniqueUpToIso Q.isLimit).inv ≫
      P.cone.π.app WalkingCospan.right = Q.cone.π.app WalkingCospan.right
  exact P.isLimit.conePointUniqueUpToIso_inv_comp Q.isLimit WalkingCospan.right

end PullbackData

/-- The data in a commuting square of cospans.

For `P : PullbackData f₁ g₁` and `Q : PullbackData f₂ g₂`, `left`, `right`, and
`base` point from the source cospan to the target cospan.  The two equations are
stored explicitly, avoiding any reconstruction of the square by typeclass search.
-/
structure PullbackMapData
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    {f₁ : X₁ ⟶ Z₁} {g₁ : Y₁ ⟶ Z₁}
    {f₂ : X₂ ⟶ Z₂} {g₂ : Y₂ ⟶ Z₂}
    (P : PullbackData f₁ g₁) (Q : PullbackData f₂ g₂) where
  left : X₁ ⟶ X₂
  right : Y₁ ⟶ Y₂
  base : Z₁ ⟶ Z₂
  left_naturality : left ≫ f₂ = f₁ ≫ base
  right_naturality : right ≫ g₂ = g₁ ≫ base

namespace PullbackMapData

variable {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
variable {f₁ : X₁ ⟶ Z₁} {g₁ : Y₁ ⟶ Z₁}
variable {f₂ : X₂ ⟶ Z₂} {g₂ : Y₂ ⟶ Z₂}
variable {P : PullbackData f₁ g₁} {Q : PullbackData f₂ g₂}

/-- The map induced by a commuting square of cospans. -/
def map (m : PullbackMapData P Q) : P.pt ⟶ Q.pt :=
  Q.lift (P.fst ≫ m.left) (P.snd ≫ m.right) (by
    calc
      (P.fst ≫ m.left) ≫ f₂ = P.fst ≫ (m.left ≫ f₂) := by simp only [Category.assoc]
      _ = P.fst ≫ (f₁ ≫ m.base) := by rw [m.left_naturality]
      _ = (P.fst ≫ f₁) ≫ m.base := by simp only [Category.assoc]
      _ = (P.snd ≫ g₁) ≫ m.base := by rw [P.condition]
      _ = P.snd ≫ (g₁ ≫ m.base) := by simp only [Category.assoc]
      _ = P.snd ≫ (m.right ≫ g₂) := by rw [m.right_naturality]
      _ = (P.snd ≫ m.right) ≫ g₂ := by simp only [Category.assoc])

@[simp]
theorem map_fst (m : PullbackMapData P Q) :
    m.map ≫ Q.fst = P.fst ≫ m.left := by
  apply Q.lift_fst

@[simp]
theorem map_snd (m : PullbackMapData P Q) :
    m.map ≫ Q.snd = P.snd ≫ m.right := by
  apply Q.lift_snd

@[simp]
theorem map_base (m : PullbackMapData P Q) :
    m.map ≫ Q.fst ≫ f₂ = P.fst ≫ f₁ ≫ m.base := by
  calc
    m.map ≫ Q.fst ≫ f₂ = (m.map ≫ Q.fst) ≫ f₂ := (Category.assoc _ _ _).symm
    _ = (P.fst ≫ m.left) ≫ f₂ := congrArg (fun q => q ≫ f₂) (map_fst m)
    _ = P.fst ≫ (m.left ≫ f₂) := Category.assoc _ _ _
    _ = P.fst ≫ (f₁ ≫ m.base) := congrArg (fun q => P.fst ≫ q) m.left_naturality
    _ = P.fst ≫ f₁ ≫ m.base := rfl

/-- Composition of square data. -/
def comp
    {X₃ Y₃ Z₃ : C} {f₃ : X₃ ⟶ Z₃} {g₃ : Y₃ ⟶ Z₃}
    {R : PullbackData f₃ g₃}
    (m : PullbackMapData P Q) (n : PullbackMapData Q R) :
    PullbackMapData P R where
  left := m.left ≫ n.left
  right := m.right ≫ n.right
  base := m.base ≫ n.base
  left_naturality := by
    calc
      (m.left ≫ n.left) ≫ f₃ = m.left ≫ (n.left ≫ f₃) := Category.assoc _ _ _
      _ = m.left ≫ (f₂ ≫ n.base) :=
        congrArg (fun q => m.left ≫ q) n.left_naturality
      _ = (m.left ≫ f₂) ≫ n.base := (Category.assoc _ _ _).symm
      _ = (f₁ ≫ m.base) ≫ n.base :=
        congrArg (fun q => q ≫ n.base) m.left_naturality
      _ = f₁ ≫ (m.base ≫ n.base) := Category.assoc _ _ _
  right_naturality := by
    calc
      (m.right ≫ n.right) ≫ g₃ = m.right ≫ (n.right ≫ g₃) := Category.assoc _ _ _
      _ = m.right ≫ (g₂ ≫ n.base) :=
        congrArg (fun q => m.right ≫ q) n.right_naturality
      _ = (m.right ≫ g₂) ≫ n.base := (Category.assoc _ _ _).symm
      _ = (g₁ ≫ m.base) ≫ n.base :=
        congrArg (fun q => q ≫ n.base) m.right_naturality
      _ = g₁ ≫ (m.base ≫ n.base) := Category.assoc _ _ _

@[simp]
theorem map_comp
    {X₃ Y₃ Z₃ : C} {f₃ : X₃ ⟶ Z₃} {g₃ : Y₃ ⟶ Z₃}
    {R : PullbackData f₃ g₃}
    (m : PullbackMapData P Q) (n : PullbackMapData Q R) :
    (m.comp n).map = m.map ≫ n.map := by
  apply R.hom_ext
  · calc
      (m.comp n).map ≫ R.fst = P.fst ≫ (m.comp n).left := map_fst (m.comp n)
      _ = P.fst ≫ (m.left ≫ n.left) := rfl
      _ = (P.fst ≫ m.left) ≫ n.left := (Category.assoc _ _ _).symm
      _ = (m.map ≫ Q.fst) ≫ n.left := congrArg (fun q => q ≫ n.left) (map_fst m).symm
      _ = m.map ≫ (Q.fst ≫ n.left) := Category.assoc _ _ _
      _ = m.map ≫ (n.map ≫ R.fst) := congrArg (fun q => m.map ≫ q) (map_fst n).symm
      _ = (m.map ≫ n.map) ≫ R.fst := (Category.assoc _ _ _).symm
  · calc
      (m.comp n).map ≫ R.snd = P.snd ≫ (m.comp n).right := map_snd (m.comp n)
      _ = P.snd ≫ (m.right ≫ n.right) := rfl
      _ = (P.snd ≫ m.right) ≫ n.right := (Category.assoc _ _ _).symm
      _ = (m.map ≫ Q.snd) ≫ n.right := congrArg (fun q => q ≫ n.right) (map_snd m).symm
      _ = m.map ≫ (Q.snd ≫ n.right) := Category.assoc _ _ _
      _ = m.map ≫ (n.map ≫ R.snd) := congrArg (fun q => m.map ≫ q) (map_snd n).symm
      _ = (m.map ≫ n.map) ≫ R.snd := (Category.assoc _ _ _).symm

/-- Identity square data for a chosen pullback. -/
def id : PullbackMapData P P where
  left := 𝟙 _
  right := 𝟙 _
  base := 𝟙 _
  left_naturality := by simp
  right_naturality := by simp

@[simp]
theorem map_id : (PullbackMapData.id (P := P)).map = 𝟙 P.pt := by
  apply P.hom_ext <;> simp [PullbackMapData.id]

/-- Comparison isomorphisms are natural for square data with the same two legs.

The source and target pullback cones may be chosen independently.  If two induced maps
use equal left and right legs, this equation transports the map across both canonical
comparison isomorphisms. -/
theorem comparison_naturality
    {P P' : PullbackData f₁ g₁} {Q Q' : PullbackData f₂ g₂}
    (m : PullbackMapData P Q) (m' : PullbackMapData P' Q')
    (hleft : m.left = m'.left) (hright : m.right = m'.right) :
    (P.comparison P').hom ≫ m'.map = m.map ≫ (Q.comparison Q').hom := by
  apply Q'.hom_ext
  · calc
      ((P.comparison P').hom ≫ m'.map) ≫ Q'.fst =
          (P.comparison P').hom ≫ (m'.map ≫ Q'.fst) := Category.assoc _ _ _
      _ = (P.comparison P').hom ≫ (P'.fst ≫ m'.left) := by
        rw [PullbackMapData.map_fst]
      _ = ((P.comparison P').hom ≫ P'.fst) ≫ m'.left :=
        (Category.assoc _ _ _).symm
      _ = P.fst ≫ m'.left := by rw [PullbackData.comparison_hom_fst]
      _ = P.fst ≫ m.left := by rw [hleft]
      _ = m.map ≫ Q.fst := by rw [PullbackMapData.map_fst]
      _ = m.map ≫ ((Q.comparison Q').hom ≫ Q'.fst) := by
        rw [PullbackData.comparison_hom_fst]
      _ = (m.map ≫ (Q.comparison Q').hom) ≫ Q'.fst :=
        (Category.assoc _ _ _).symm
  · calc
      ((P.comparison P').hom ≫ m'.map) ≫ Q'.snd =
          (P.comparison P').hom ≫ (m'.map ≫ Q'.snd) := Category.assoc _ _ _
      _ = (P.comparison P').hom ≫ (P'.snd ≫ m'.right) := by
        rw [PullbackMapData.map_snd]
      _ = ((P.comparison P').hom ≫ P'.snd) ≫ m'.right :=
        (Category.assoc _ _ _).symm
      _ = P.snd ≫ m'.right := by rw [PullbackData.comparison_hom_snd]
      _ = P.snd ≫ m.right := by rw [hright]
      _ = m.map ≫ Q.snd := by rw [PullbackMapData.map_snd]
      _ = m.map ≫ ((Q.comparison Q').hom ≫ Q'.snd) := by
        rw [PullbackData.comparison_hom_snd]
      _ = (m.map ≫ (Q.comparison Q').hom) ≫ Q'.snd :=
        (Category.assoc _ _ _).symm

end PullbackMapData

open AlgebraicGeometry

/-! ### The canonical pullback underlying a scheme gluing -/

variable {X Y Z : Scheme.{u}} (𝒰 : Scheme.OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (𝒰.f i ≫ f) g]

/-- The pullback presentation supplied by Mathlib's scheme-gluing construction.

`Scheme.Pullback.gluedIsLimit` is the canonical universal-property proof for the glued
scheme.  Capturing it here prevents downstream code from selecting a fresh `HasPullback`
witness every time it mentions the same gluing. -/
noncomputable def schemeGluingPullbackData : PullbackData f g :=
  { cone := PullbackCone.mk
      (Scheme.Pullback.p1 𝒰 f g)
      (Scheme.Pullback.p2 𝒰 f g)
      (Scheme.Pullback.p_comm 𝒰 f g)
    isLimit := Scheme.Pullback.gluedIsLimit 𝒰 f g }

@[simp]
theorem schemeGluingPullbackData_pt :
    (schemeGluingPullbackData 𝒰 f g).pt = (Scheme.Pullback.gluing 𝒰 f g).glued :=
  rfl

@[simp]
theorem schemeGluingPullbackData_fst :
    (schemeGluingPullbackData 𝒰 f g).fst = Scheme.Pullback.p1 𝒰 f g :=
  rfl

@[simp]
theorem schemeGluingPullbackData_snd :
    (schemeGluingPullbackData 𝒰 f g).snd = Scheme.Pullback.p2 𝒰 f g :=
  rfl

end

end AlgebraicJacobian
