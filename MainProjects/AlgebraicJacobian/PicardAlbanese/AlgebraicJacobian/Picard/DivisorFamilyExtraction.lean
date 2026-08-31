/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Cohomology.GluedSheafExtraction

/-!
# Finite-adaptation extraction: every local-equation system has a chart adaptation
(`informal/spec-dd-1.md` §3 stage (d))

Every `LocalEquations` system `d` on the relative curve `C_R = relCurve C R` refines to a
finite chart adaptation `DivisorAdaptation C R π d` (`informal/spec-dd-1.md` §1a): the two
pinned charts `V₀ᴿ`, `V₁ᴿ` are affine, so the DAT-1 (1f) affine-refinement engine
(`IsAffineOpen.exists_finite_basicOpen_refinement` in
`AlgebraicJacobian.Cohomology.GluedSheafExtraction`)
produces, for each chart, a finite basic-open family subordinated to `d.cover` at anchor
points, with a partition of unity. Reindexing each chart family through `Fintype.equivFin`
gives the `Fin`-indexed `FinCoverData`; the equations are the restrictions of `d`'s
equations at the anchors (comparison unit `1`), regular by `d.regular` through the
refinement subordination.

The **certificate** (`DivisorAdaptation.IsCertified`) is deliberately NOT part of the
extraction: an adaptation always exists, whereas the colength certificate is an extra
finiteness/flatness hypothesis on `d` (the object of DD-1c's field dictionary and DAT-B's
coverage step, which supply it separately).

* `AlgebraicGeometry.exists_divisorAdaptation` — the extraction: `Nonempty
  (DivisorAdaptation C R π d)` for every `d : (relCurve C R).LocalEquations`.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (π : C.left ⟶ P1 k) [IsAffineHom π]

/-- **Finite-adaptation extraction** (`informal/spec-dd-1.md` §3 stage (d), the DAT-1 (1f)
pattern): every local-equation system on the relative curve refines to a finite chart
adaptation. The two pinned charts are affine, so on each the affine-refinement engine
produces a finite basic-open family subordinated to `d.cover` at anchor points with a
partition of unity; the equations are the anchor equations of `d` restricted to the pieces
(comparison unit `1`), regular through the subordination. The colength certificate is a
separate hypothesis and is not produced here. -/
theorem exists_divisorAdaptation (d : (relCurve C R).LocalEquations) :
    Nonempty (DivisorAdaptation C R π d) := by
  classical
  obtain ⟨ι₀, _, f₀, an₀, b₀, hsub₀, hpart₀⟩ :=
    (relCover_isAffineOpen₀ C R (fiberTwoCover π)).exists_finite_basicOpen_refinement d.cover
  obtain ⟨ι₁, _, f₁, an₁, b₁, hsub₁, hpart₁⟩ :=
    (relCover_isAffineOpen₁ C R (fiberTwoCover π)).exists_finite_basicOpen_refinement d.cover
  set e₀ : Fin (Fintype.card ι₀) ≃ ι₀ := (Fintype.equivFin ι₀).symm with he₀
  set e₁ : Fin (Fintype.card ι₁) ≃ ι₁ := (Fintype.equivFin ι₁).symm with he₁
  -- the `Fin`-indexed cover data
  set D : FinCoverData C R π :=
    { m₀ := Fintype.card ι₀
      m₁ := Fintype.card ι₁
      h₀ := fun j => f₀ (e₀ j)
      h₁ := fun j => f₁ (e₁ j)
      a₀ := fun j => b₀ (e₀ j)
      a₁ := fun j => b₁ (e₁ j)
      partition₀ := (Equiv.sum_comp e₀ (fun i => b₀ i * f₀ i)).trans hpart₀
      partition₁ := (Equiv.sum_comp e₁ (fun i => b₁ i * f₁ i)).trans hpart₁ } with hD
  -- the anchor of each piece and its subordination to a member of `d.cover`
  set pt : D.index → relCurve C R :=
    Sum.elim (fun j => an₀ (e₀ j)) (fun j => an₁ (e₁ j)) with hpt
  have hle : ∀ j : D.index, D.pieces j ≤ d.cover.opens (pt j) := by
    rintro (j | j)
    · exact hsub₀ (e₀ j)
    · exact hsub₁ (e₁ j)
  exact ⟨DivisorAdaptation.ofAnchors D
    (fun j => ((relCurve C R).presheaf.map (homOfLE (hle j)).op).hom (d.eqn (pt j)))
    pt hle (fun _ => 1) (fun _ => by rw [Units.val_one, one_mul])⟩

end AlgebraicGeometry
