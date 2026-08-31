/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.FiberDivisor
import AlgebraicJacobian.RiemannRoch.Ledger.SectionsFieldBaseChange

/-!
# Source-side coordinate data for a fiber divisor

The fiber-twist argument only uses the source of a finite dominant map to `P1`: two affine
opens covering the source, inverse coordinates on their overlap, the identification of that
overlap with a basic open, and its nonemptiness.  `FiberCoordinateData` packages exactly those
facts.  Unlike a morphism to a chosen projective-line model, this package base-changes directly
along `Scheme.baseChangeFieldFst`.

`FiberCoordinateData.ofMap` records the data already proved by `FiberChart` and
`FiberDivisor`.  `FiberCoordinateData.baseChangeField` pulls the package to every field
extension.  The latter uses only affine-preimage stability, `Scheme.preimage_basicOpen`, and
naturality of restriction; it does not compare Ledger's `P1 k` with any other projective-line
model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme

/-- The source-side two-chart coordinate package used by a fiber divisor. -/
structure FiberCoordinateData (Y : Scheme.{u}) : Type u where
  /-- The chart on which the fiber coordinate is regular. -/
  V₀ : Y.Opens
  /-- The chart on which its inverse is regular. -/
  V₁ : Y.Opens
  /-- The first chart is affine. -/
  isAffineOpen_V₀ : IsAffineOpen V₀
  /-- The second chart is affine. -/
  isAffineOpen_V₁ : IsAffineOpen V₁
  /-- The two charts cover the source. -/
  cover : V₀ ⊔ V₁ = ⊤
  /-- The coordinate regular on `V₀`. -/
  x : Γ(Y, V₀)
  /-- Its inverse, regular on `V₁`. -/
  y : Γ(Y, V₁)
  /-- The overlap is the nonvanishing locus of `x`. -/
  inf_eq_basicOpen_x : V₀ ⊓ V₁ = Y.basicOpen x
  /-- The two coordinate restrictions multiply to one on the overlap. -/
  res_x_mul_res_y :
    (Y.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op).hom x *
      (Y.presheaf.map (homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op).hom y = 1
  /-- The overlap is nonempty. -/
  inf_nonempty : ((V₀ ⊓ V₁ : Y.Opens) : Set Y).Nonempty

namespace FiberCoordinateData

variable {Y : Scheme.{u}}

/-- The affine Mayer--Vietoris square underlying source-side fiber coordinates. -/
noncomputable def toAffineCoverMVSquare (D : FiberCoordinateData Y) :
    Y.AffineCoverMVSquare where
  U₁ := D.V₀
  U₂ := D.V₁
  isAffineOpen_U₁ := D.isAffineOpen_V₀
  isAffineOpen_U₂ := D.isAffineOpen_V₁
  isAffineOpen_inf := by
    rw [D.inf_eq_basicOpen_x]
    exact D.isAffineOpen_V₀.basicOpen D.x
  cover := D.cover

variable [IsIntegral Y]

/-- The generic point belongs to the coordinate overlap. -/
lemma genericPoint_mem_inf (D : FiberCoordinateData Y) : genericPoint Y ∈ D.V₀ ⊓ D.V₁ :=
  genericPoint_mem_of_nonempty D.inf_nonempty

section OfMap

variable {K : Type u} [Field K]
variable (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]

/-- A finite dominant map to Ledger's `P1` supplies source-side fiber coordinates. -/
noncomputable def ofMap : FiberCoordinateData Y where
  V₀ := fiberChart₀ π
  V₁ := fiberChart₁ π
  isAffineOpen_V₀ := isAffineOpen_preimage_chartOpen π 0
  isAffineOpen_V₁ := isAffineOpen_preimage_chartOpen π 1
  cover := preimage_chartOpen_sup π
  x := fiberCoord π
  y := fiberCoord₁ π
  inf_eq_basicOpen_x := preimage_inf_eq_basicOpen_fiberCoord π
  res_x_mul_res_y := fiberCoord_mul_fiberCoord₁_res π
  inf_nonempty := ⟨genericPoint Y, genericPoint_mem_preimage_inf π⟩

@[simp] lemma ofMap_V₀ : (ofMap π).V₀ = fiberChart₀ π := rfl

@[simp] lemma ofMap_V₁ : (ofMap π).V₁ = fiberChart₁ π := rfl

@[simp] lemma ofMap_x : (ofMap π).x = fiberCoord π := rfl

@[simp] lemma ofMap_y : (ofMap π).y = fiberCoord₁ π := rfl

end OfMap

section BaseChange

variable {k : Type u} [Field k]
variable (C : Over (Spec (CommRingCat.of k)))
variable (κ : Type u) [Field κ] [Algebra k κ]

/-- The first projection `C_κ -> C` is surjective for every extension of fields. -/
theorem surjective_baseChangeFieldFst : Surjective (baseChangeFieldFst C κ) := by
  letI : Surjective (baseChangeFieldMap k κ) := by
    constructor
    intro z
    obtain ⟨w⟩ : Nonempty (Spec (CommRingCat.of κ)) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩
  infer_instance

variable {C}

/-- Pull source-side fiber coordinates through an arbitrary field extension. -/
noncomputable def baseChangeField (D : FiberCoordinateData C.left) :
    FiberCoordinateData (Scheme.baseChangeField C κ).left where
  V₀ := baseChangeFieldFst C κ ⁻¹ᵁ D.V₀
  V₁ := baseChangeFieldFst C κ ⁻¹ᵁ D.V₁
  isAffineOpen_V₀ := D.isAffineOpen_V₀.preimage (baseChangeFieldFst C κ)
  isAffineOpen_V₁ := D.isAffineOpen_V₁.preimage (baseChangeFieldFst C κ)
  cover := by
    change baseChangeFieldFst C κ ⁻¹ᵁ (D.V₀ ⊔ D.V₁) = ⊤
    rw [D.cover]
    rfl
  x := ((baseChangeFieldFst C κ).app D.V₀).hom D.x
  y := ((baseChangeFieldFst C κ).app D.V₁).hom D.y
  inf_eq_basicOpen_x := by
    rw [← Scheme.Hom.preimage_inf, D.inf_eq_basicOpen_x, Scheme.preimage_basicOpen]
  res_x_mul_res_y := by
    let f := baseChangeFieldFst C κ
    have h₀ :
        ((Scheme.baseChangeField C κ).left.presheaf.map
          (homOfLE (inf_le_left :
            (f ⁻¹ᵁ D.V₀) ⊓ (f ⁻¹ᵁ D.V₁) ≤ f ⁻¹ᵁ D.V₀)).op).hom
            ((f.app D.V₀).hom D.x) =
          (f.app (D.V₀ ⊓ D.V₁)).hom
            ((C.left.presheaf.map
              (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op).hom D.x) := by
      have h := congrArg
        (fun g : Γ(C.left, D.V₀) ⟶
            Γ((Scheme.baseChangeField C κ).left, f ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom D.x)
        (f.naturality (homOfLE (inf_le_left : D.V₀ ⊓ D.V₁ ≤ D.V₀)).op)
      exact h.symm
    have h₁ :
        ((Scheme.baseChangeField C κ).left.presheaf.map
          (homOfLE (inf_le_right :
            (f ⁻¹ᵁ D.V₀) ⊓ (f ⁻¹ᵁ D.V₁) ≤ f ⁻¹ᵁ D.V₁)).op).hom
            ((f.app D.V₁).hom D.y) =
          (f.app (D.V₀ ⊓ D.V₁)).hom
            ((C.left.presheaf.map
              (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op).hom D.y) := by
      have h := congrArg
        (fun g : Γ(C.left, D.V₁) ⟶
            Γ((Scheme.baseChangeField C κ).left, f ⁻¹ᵁ (D.V₀ ⊓ D.V₁)) => g.hom D.y)
        (f.naturality (homOfLE (inf_le_right : D.V₀ ⊓ D.V₁ ≤ D.V₁)).op)
      exact h.symm
    rw [h₀, h₁]
    have hkey := congrArg
      (CommRingCat.Hom.hom (f.app (D.V₀ ⊓ D.V₁))) D.res_x_mul_res_y
    rw [map_mul, map_one] at hkey
    exact hkey
  inf_nonempty := by
    letI : Surjective (baseChangeFieldFst C κ) := surjective_baseChangeFieldFst C κ
    obtain ⟨x, hx⟩ := D.inf_nonempty
    obtain ⟨y, hy⟩ := (baseChangeFieldFst C κ).surjective x
    refine ⟨y, ?_⟩
    change (baseChangeFieldFst C κ).base y ∈ D.V₀ ⊓ D.V₁
    simpa [hy] using hx

@[simp] lemma baseChangeField_V₀ (D : FiberCoordinateData C.left) :
    (D.baseChangeField κ).V₀ = baseChangeFieldFst C κ ⁻¹ᵁ D.V₀ := rfl

@[simp] lemma baseChangeField_V₁ (D : FiberCoordinateData C.left) :
    (D.baseChangeField κ).V₁ = baseChangeFieldFst C κ ⁻¹ᵁ D.V₁ := rfl

@[simp] lemma baseChangeField_x (D : FiberCoordinateData C.left) :
    (D.baseChangeField κ).x = ((baseChangeFieldFst C κ).app D.V₀).hom D.x := rfl

@[simp] lemma baseChangeField_y (D : FiberCoordinateData C.left) :
    (D.baseChangeField κ).y = ((baseChangeFieldFst C κ).app D.V₁).hom D.y := rfl

end BaseChange

end FiberCoordinateData

end AlgebraicGeometry
