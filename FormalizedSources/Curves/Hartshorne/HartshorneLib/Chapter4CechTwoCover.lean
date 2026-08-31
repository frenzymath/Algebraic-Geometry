/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4TwoLattice
import Mathlib.RingTheory.Finiteness.Basic
import HartshorneLib.Chapter2Cohomology

/-!
# The algebraic two-cover Cech quotient

For a two-open cover, the degree-one Cech group is the overlap module modulo the
image of the restriction-difference map.  This file records that algebraic
quotient independently of the geometric comparison theorem.  The latter can
therefore supply a linear equivalence to `HModule` when the affine-cover
hypotheses have been established.

The range calculation uses `LinearMap.coprod`: the sign on the second leg is
irrelevant to its range, while making the Cech difference `(s₀, s₁) ↦
σ₀ s₀ - σ₁ s₁` explicit.
-/

set_option autoImplicit false

universe u v w z

namespace Hartshorne
namespace CechTwoCover

variable {k : Type u} [CommRing k]
variable {M₀ : Type v} [AddCommGroup M₀] [Module k M₀]
variable {M₁ : Type w} [AddCommGroup M₁] [Module k M₁]
variable {N : Type z} [AddCommGroup N] [Module k N]

/-- The restriction-difference map for a pair of opens. -/
noncomputable def diff (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N) :
    (M₀ × M₁) →ₗ[k] N :=
  σ₀.coprod (-σ₁)

@[simp]
lemma diff_apply (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N) (s : M₀ × M₁) :
    diff σ₀ σ₁ s = σ₀ s.1 - σ₁ s.2 := by
  simp [diff, sub_eq_add_neg]

/-- The two restriction lattices in the overlap module. -/
def imageLattice (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N) : Submodule k N :=
  LinearMap.range σ₀ ⊔ LinearMap.range σ₁

/-- The degree-one Cech quotient of the two-open diagram. -/
abbrev H1Cok (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N) :=
  N ⧸ LinearMap.range (diff σ₀ σ₁)

/-- The range of the Cech difference is the join of the two restriction ranges. -/
theorem range_diff_eq (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N) :
    LinearMap.range (diff σ₀ σ₁) = imageLattice σ₀ σ₁ := by
  rw [diff, LinearMap.range_coprod, LinearMap.range_neg]
  rfl

/-- Identify the quotient by the two lattice join with the Cech quotient. -/
noncomputable def h1CokEquiv (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N) :
    (N ⧸ imageLattice σ₀ σ₁) ≃ₗ[k] H1Cok σ₀ σ₁ :=
  Submodule.quotEquivOfEq _ _ (range_diff_eq σ₀ σ₁).symm

/-- Laurent two-lattice finiteness for the algebraic two-cover Cech quotient.

The four hypotheses are precisely stability under the two Laurent coordinates
and localization into the corresponding restriction ranges.  Geometric input
such as a finite map to `ProjectiveSpace 1` is intentionally left outside this
lemma.
-/
theorem moduleFinite_H1Cok
    (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N)
    [Module (LaurentPolynomial k) N]
    [IsScalarTower k (LaurentPolynomial k) N]
    [Module.Finite (LaurentPolynomial k) N]
    (hσ₀ : ∀ x ∈ LinearMap.range σ₀,
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈ LinearMap.range σ₀)
    (hσ₁ : ∀ x ∈ LinearMap.range σ₁,
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈ LinearMap.range σ₁)
    (hσ₀loc : ∀ n : N, ∃ m : ℕ,
      ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range σ₀)
    (hσ₁loc : ∀ n : N, ∃ m : ℕ,
      ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range σ₁) :
    Module.Finite k (H1Cok σ₀ σ₁) := by
  letI : Module.Finite k (N ⧸ imageLattice σ₀ σ₁) :=
    LaurentPolynomial.moduleFinite_quotient_sup_of_exists_pow_smul_mem
      hσ₀ hσ₁ hσ₀loc hσ₁loc
  exact Module.Finite.equiv (h1CokEquiv σ₀ σ₁)

/-! The finiteness result is independent of the presentation of the target: any
linear equivalence to the Cech quotient transports it to the compared module. -/

theorem moduleFinite_of_equiv_H1Cok
    {H : Type v} [AddCommGroup H] [Module k H]
    (σ₀ : M₀ →ₗ[k] N) (σ₁ : M₁ →ₗ[k] N)
    [Module (LaurentPolynomial k) N]
    [IsScalarTower k (LaurentPolynomial k) N]
    [Module.Finite (LaurentPolynomial k) N]
    (hσ₀ : ∀ x ∈ LinearMap.range σ₀,
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈ LinearMap.range σ₀)
    (hσ₁ : ∀ x ∈ LinearMap.range σ₁,
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈ LinearMap.range σ₁)
    (hσ₀loc : ∀ n : N, ∃ m : ℕ,
      ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range σ₀)
    (hσ₁loc : ∀ n : N, ∃ m : ℕ,
      ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈ LinearMap.range σ₁)
    (e : H ≃ₗ[k] H1Cok σ₀ σ₁) :
    Module.Finite k H := by
  letI : Module.Finite k (H1Cok σ₀ σ₁) :=
    moduleFinite_H1Cok σ₀ σ₁ hσ₀ hσ₁ hσ₀loc hσ₁loc
  exact Module.Finite.equiv e.symm

/-! ## Scheme-section specialization -/

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable (k : Type u) [CommRing k]
variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
variable (U₀ U₁ : X.Opens)

/-- Restriction of structure-sheaf sections from `U₀` to `U₀ ⊓ U₁`. -/
noncomputable def leftRestriction : Γ(X, U₀) →ₗ[k] Γ(X, U₀ ⊓ U₁) :=
  ((X.moduleKSheaf k).obj.map
    (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom

/-- Restriction of structure-sheaf sections from `U₁` to `U₀ ⊓ U₁`. -/
noncomputable def rightRestriction : Γ(X, U₁) →ₗ[k] Γ(X, U₀ ⊓ U₁) :=
  ((X.moduleKSheaf k).obj.map
    (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom

/-- The section-level Cech quotient for two opens of a `Spec k`-scheme. -/
abbrev schemeH1Cok :=
  H1Cok (leftRestriction k X U₀ U₁) (rightRestriction k X U₀ U₁)

@[simp]
lemma scheme_diff_apply (s : Γ(X, U₀) × Γ(X, U₁)) :
    diff (leftRestriction k X U₀ U₁) (rightRestriction k X U₀ U₁) s =
      (X.presheaf.map (homOfLE inf_le_left).op).hom s.1 -
        (X.presheaf.map (homOfLE inf_le_right).op).hom s.2 := by
  rw [CechTwoCover.diff_apply]
  change ((X.moduleKSheaf k).obj.map
      (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom s.1 -
      ((X.moduleKSheaf k).obj.map
        (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom s.2 = _
  rw [Scheme.moduleKSheaf_map_apply, Scheme.moduleKSheaf_map_apply]
  rfl

/-- Finiteness of the section quotient transports to degree-one sheaf cohomology
through an explicitly supplied comparison equivalence.  The equivalence is the
affine-cover/Cech comparison input; no such geometric comparison is inferred
here.
-/
theorem moduleFinite_hModule_one_of_h1CokEquiv
    [Module (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    [IsScalarTower k (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    [Module.Finite (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    (e : CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X : TopCat)) k (X.moduleKSheaf k) 1 ≃ₗ[k]
        schemeH1Cok k X U₀ U₁)
    (hσ₀ : ∀ x ∈ LinearMap.range (leftRestriction k X U₀ U₁),
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈
        LinearMap.range (leftRestriction k X U₀ U₁))
    (hσ₁ : ∀ x ∈ LinearMap.range (rightRestriction k X U₀ U₁),
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈
        LinearMap.range (rightRestriction k X U₀ U₁))
    (hσ₀loc : ∀ n : Γ(X, U₀ ⊓ U₁), ∃ m : ℕ,
      ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (leftRestriction k X U₀ U₁))
    (hσ₁loc : ∀ n : Γ(X, U₀ ⊓ U₁), ∃ m : ℕ,
      ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (rightRestriction k X U₀ U₁)) :
    Module.Finite k
      (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X : TopCat)) k (X.moduleKSheaf k) 1) := by
  letI : Module.Finite k (schemeH1Cok k X U₀ U₁) :=
    moduleFinite_H1Cok
      (leftRestriction k X U₀ U₁) (rightRestriction k X U₀ U₁)
      hσ₀ hσ₁ hσ₀loc hσ₁loc
  exact Module.Finite.equiv e.symm

end CechTwoCover
end Hartshorne
