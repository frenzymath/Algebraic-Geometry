/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.CategoryTheory.Yoneda

/-!
# Explicit representer data

Many construction files return a dependent sigma type
`Σ X, F.RepresentableBy X`.  Projecting that sigma repeatedly makes the chosen
object and the proof of representability disappear into elaboration.  This file
provides a named package and the small transport API needed by consumers.  The
package is intentionally proof-agnostic: it does not select a new object and it
does not install any instances.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicJacobian

noncomputable section

/-- A chosen representing object together with its representation. -/
structure RepresenterData (C : Type u) [Category.{v} C]
    (F : Cᵒᵖ ⥤ Type w) where
  object : C
  representation : F.RepresentableBy object

namespace RepresenterData

variable {C : Type u} [Category.{v} C]
variable {F : Cᵒᵖ ⥤ Type w}

/-- Package a dependent-sigma representation without losing its two components. -/
def ofSigma (s : Σ X : C, F.RepresentableBy X) : RepresenterData C F :=
  ⟨s.1, s.2⟩

/-! A producer usually proves representability as a nonempty dependent sigma, or in
the logically equivalent form `∃ X, Nonempty (F.RepresentableBy X)`.  Keeping the choice
at this boundary means downstream declarations carry one
`RepresenterData` value instead of repeating `Classical.choose` and silently selecting
different objects at different call sites. -/

/-- Select one representing datum from a nonempty sigma certificate.

This is the one intentional use of choice in the representer API.  The selected object and
its representation are thereafter carried together by `RepresenterData`; consumers should
pass this value rather than unpacking the certificate again. -/
noncomputable def ofNonempty
    (h : Nonempty (Σ X : C, F.RepresentableBy X)) : RepresenterData C F :=
  ofSigma (Classical.choice h)

/-- Select one representing datum from the usual existential certificate. -/
noncomputable def ofExists
    (h : ∃ X : C, Nonempty (F.RepresentableBy X)) : RepresenterData C F :=
  ofNonempty
    (⟨⟨Classical.choose h, Classical.choice (Classical.choose_spec h)⟩⟩)

/-- Recover the dependent-sigma form when an API still expects it. -/
def toSigma (P : RepresenterData C F) : Σ X : C, F.RepresentableBy X :=
  ⟨P.object, P.representation⟩

@[simp]
theorem ofNonempty_toSigma
    (h : Nonempty (Σ X : C, F.RepresentableBy X)) :
    (ofNonempty (C := C) h).toSigma = Classical.choice h := by
  rfl

@[simp]
theorem ofSigma_toSigma (s : Σ X : C, F.RepresentableBy X) :
    (ofSigma (C := C) s).toSigma = s := by
  cases s
  rfl

@[simp]
theorem toSigma_ofSigma (P : RepresenterData C F) :
    ofSigma (C := C) P.toSigma = P := by
  cases P
  rfl

/-- The universal property in consumer form, without exposing the packaged
`RepresentableBy` proof. -/
def homEquiv (P : RepresenterData C F) {X : C} :
    (X ⟶ P.object) ≃ F.obj (Opposite.op X) :=
  P.representation.homEquiv

/-- The universal element associated to the pinned representing object. -/
def universalElement (P : RepresenterData C F) : F.obj (Opposite.op P.object) :=
  P.homEquiv (𝟙 P.object)

/-- Naturality of the packaged universal property. -/
theorem homEquiv_comp (P : RepresenterData C F) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ P.object) :
    P.homEquiv (f ≫ g) = F.map f.op (P.homEquiv g) :=
  P.representation.homEquiv_comp f g

/-- Every represented element is obtained by pulling back the universal element. -/
theorem homEquiv_eq (P : RepresenterData C F) {X : C} (f : X ⟶ P.object) :
    P.homEquiv f = F.map f.op P.universalElement :=
  P.representation.homEquiv_eq f

@[simp]
theorem homEquiv_id (P : RepresenterData C F) :
    P.homEquiv (𝟙 P.object) = P.universalElement :=
  rfl

/-- The canonical comparison between two chosen representing objects. -/
noncomputable def uniqueIso (P Q : RepresenterData C F) : P.object ≅ Q.object :=
  P.representation.uniqueUpToIso Q.representation

/-- The canonical comparison intertwines the two packaged universal properties. -/
theorem homEquiv_uniqueIso_hom (P Q : RepresenterData C F)
    {X : C} (f : X ⟶ P.object) :
    Q.homEquiv (f ≫ (P.uniqueIso Q).hom) = P.homEquiv f := by
  change Q.representation.homEquiv (f ≫ (P.uniqueIso Q).hom) =
    P.representation.homEquiv f
  have h : (P.uniqueIso Q).hom =
      Q.representation.homEquiv.symm
        (P.representation.homEquiv (𝟙 P.object)) := rfl
  rw [h, Functor.RepresentableBy.comp_homEquiv_symm, Equiv.apply_symm_apply]
  rw [← P.representation.homEquiv_comp f (𝟙 P.object), Category.comp_id]

/-- The inverse canonical comparison intertwines the universal properties in
the opposite direction. -/
theorem homEquiv_uniqueIso_inv (P Q : RepresenterData C F)
    {X : C} (f : X ⟶ Q.object) :
    P.homEquiv (f ≫ (P.uniqueIso Q).inv) = Q.homEquiv f := by
  rw [← P.homEquiv_uniqueIso_hom Q (f ≫ (P.uniqueIso Q).inv)]
  simp

/-- Canonical comparisons between three pinned representers satisfy the
cocycle law. -/
theorem uniqueIso_trans (P Q R : RepresenterData C F) :
    P.uniqueIso R = P.uniqueIso Q ≪≫ Q.uniqueIso R := by
  apply Iso.ext
  apply R.homEquiv.injective
  calc
    R.homEquiv (P.uniqueIso R).hom = P.homEquiv (𝟙 P.object) := by
      simpa using P.homEquiv_uniqueIso_hom R (𝟙 P.object)
    _ = Q.homEquiv (P.uniqueIso Q).hom := by
      symm
      simpa using P.homEquiv_uniqueIso_hom Q (𝟙 P.object)
    _ = R.homEquiv ((P.uniqueIso Q).hom ≫ (Q.uniqueIso R).hom) := by
      symm
      exact Q.homEquiv_uniqueIso_hom R (P.uniqueIso Q).hom

/-- Transport a representation along a specified object isomorphism. -/
def transport (P : RepresenterData C F) {Y : C} (e : Y ≅ P.object) :
    F.RepresentableBy Y :=
  P.representation.ofIsoObj e

/-- A package-level transport operation, retaining the supplied object name. -/
def transportData (P : RepresenterData C F) {Y : C} (e : Y ≅ P.object) :
    RepresenterData C F :=
  ⟨Y, P.transport e⟩

@[simp]
theorem transportData_object (P : RepresenterData C F) {Y : C} (e : Y ≅ P.object) :
    (P.transportData e).object = Y :=
  rfl

@[simp]
theorem transportData_homEquiv (P : RepresenterData C F)
    {Y X : C} (e : Y ≅ P.object) (f : X ⟶ Y) :
    (P.transportData e).homEquiv f = P.homEquiv (f ≫ e.hom) :=
  rfl

@[simp]
theorem transportData_homEquiv_symm (P : RepresenterData C F)
    {Y X : C} (e : Y ≅ P.object) (x : F.obj (Opposite.op X)) :
    (P.transportData e).homEquiv.symm x = P.homEquiv.symm x ≫ e.inv :=
  rfl

/-- Repackage `P` on the object selected by `Q`, using the canonical comparison
rather than a fresh choice. -/
noncomputable def transportTo (P Q : RepresenterData C F) : RepresenterData C F :=
  P.transportData (P.uniqueIso Q).symm

@[simp]
theorem transportTo_object (P Q : RepresenterData C F) :
    (P.transportTo Q).object = Q.object :=
  rfl

/-- Canonical transport to `Q.object` has the same universal property as `Q`. -/
@[simp]
theorem transportTo_homEquiv (P Q : RepresenterData C F)
    {X : C} (f : X ⟶ Q.object) :
    (P.transportTo Q).homEquiv f = Q.homEquiv f :=
  P.homEquiv_uniqueIso_inv Q f

@[simp]
theorem transportTo_homEquiv_symm (P Q : RepresenterData C F)
    {X : C} (x : F.obj (Opposite.op X)) :
    (P.transportTo Q).homEquiv.symm x = Q.homEquiv.symm x := by
  apply (P.transportTo Q).homEquiv.injective
  rw [Equiv.apply_symm_apply, P.transportTo_homEquiv Q,
    Equiv.apply_symm_apply]

end RepresenterData

end

end AlgebraicJacobian
