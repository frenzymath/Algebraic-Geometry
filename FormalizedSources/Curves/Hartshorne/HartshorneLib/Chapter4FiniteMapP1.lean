/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4P1Overlap
import HartshorneLib.Chapter4P1Geometry

/-!
# A finite-map Laurent cover on the projective line

The standard two-chart cover of `P1 k` is already identified with Laurent coordinates in
`Chapter4P1Overlap`.  This file only specializes the generic
`FiniteMapLaurentCover` package to a supplied finite map into that projective line.  The
Laurent module, scalar tower, module-finiteness, and the four Laurent-window conditions are
left as hypotheses: they are the geometric input of the finite-map argument and are not
asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

namespace Hartshorne

attribute [local instance] Scheme.overModule

variable (k : Type u) [Field k] (X : Scheme.{u})

namespace FiniteMapLaurentCover

/-! The two target opens are fixed to the standard `P1` charts. -/

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The overlap of the pulled-back standard charts is the pullback of the canonical
`D₊(X₀ X₁)` overlap from the Laurent chart package. -/
theorem preimage_standard_overlap (π : X ⟶ AlgebraicGeometry.P1 k) :
    π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0 ⊓
      AlgebraicGeometry.P1.chartOpen k 1) =
      π ⁻¹ᵁ (Proj.basicOpen 𝒜
        (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  rw [AlgebraicGeometry.P1.chartOpen_inf]

section OverBase

variable [X.Over (Spec (CommRingCat.of k))]

/-- Package explicit Laurent-window data for a finite map to `P1` as a
`FiniteMapLaurentCover` using the standard affine charts.

No map to `P1` is constructed by this definition.  In particular, the finiteness instance and
all four window conditions are supplied by the caller. -/
noncomputable def ofP1
    (π : X ⟶ AlgebraicGeometry.P1 k) [IsFinite π]
    [Module (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))]
    [IsScalarTower k (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))]
    [Module.Finite (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))]
    (stable₀ : ∀ x ∈ LinearMap.range
      (CechTwoCover.leftRestriction k X
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))),
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈ LinearMap.range
        (CechTwoCover.leftRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))))
    (stable₁ : ∀ x ∈ LinearMap.range
      (CechTwoCover.rightRestriction k X
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))),
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈ LinearMap.range
        (CechTwoCover.rightRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))))
    (localize₀ : ∀ n : Γ(X,
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
          π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1)), ∃ m : ℕ,
      ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range
        (CechTwoCover.leftRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))))
    (localize₁ : ∀ n : Γ(X,
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
          π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1)), ∃ m : ℕ,
      ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range
        (CechTwoCover.rightRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1)))) :
    FiniteMapLaurentCover k X := by
  refine
    { Y := AlgebraicGeometry.P1 k
      π := π
      V₀ := AlgebraicGeometry.P1.chartOpen k 0
      V₁ := AlgebraicGeometry.P1.chartOpen k 1
      cover := AlgebraicGeometry.P1.chartOpen_sup k
      affine₀ := AlgebraicGeometry.P1.isAffineOpen_chartOpen k 0
      affine₁ := AlgebraicGeometry.P1.isAffineOpen_chartOpen k 1
      stable₀ := stable₀
      stable₁ := stable₁
      localize₀ := localize₀
      localize₁ := localize₁ }

/-- Finiteness of degree-one structure-sheaf cohomology from the standard `P1` cover.

This is a specialization of `FiniteMapLaurentCover.moduleFinite_hModule_one`; it remains
conditional on the supplied Laurent module and window data in `ofP1`. -/
theorem moduleFinite_hModule_one_of_p1
    (π : X ⟶ AlgebraicGeometry.P1 k) [IsFinite π]
    [Module (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))]
    [IsScalarTower k (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))]
    [Module.Finite (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))]
    (stable₀ : ∀ x ∈ LinearMap.range
      (CechTwoCover.leftRestriction k X
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))),
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈ LinearMap.range
        (CechTwoCover.leftRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))))
    (stable₁ : ∀ x ∈ LinearMap.range
      (CechTwoCover.rightRestriction k X
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
        (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))),
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈ LinearMap.range
        (CechTwoCover.rightRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))))
    (localize₀ : ∀ n : Γ(X,
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
          π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1)), ∃ m : ℕ,
      ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range
        (CechTwoCover.leftRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1))))
    (localize₁ : ∀ n : Γ(X,
        π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0) ⊓
          π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1)), ∃ m : ℕ,
      ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range
        (CechTwoCover.rightRestriction k X
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 0))
          (π ⁻¹ᵁ (AlgebraicGeometry.P1.chartOpen k 1)))) :
    Module.Finite k
      (Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) k
        (X.moduleKSheaf k) 1) := by
  exact moduleFinite_hModule_one k X
    (ofP1 k X π stable₀ stable₁ localize₀ localize₁)

end OverBase

end FiniteMapLaurentCover
end Hartshorne
