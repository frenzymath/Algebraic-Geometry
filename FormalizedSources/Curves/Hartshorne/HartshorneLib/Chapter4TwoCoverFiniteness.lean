/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2TwoCover
import HartshorneLib.Chapter2AffineVanishingQcoh
import HartshorneLib.Chapter4CechTwoCover

/-!
# Finiteness transport across a two-open Cech comparison

This file records the algebraic consumer needed by the curve finiteness argument.  The
Mayer--Vietoris construction presents `H¹` as a quotient by its restriction-difference map,
while the Laurent-window lemma is phrased for the explicit Cech quotient.  For the canonical
two-open square these maps agree, so the quotient comparison is constructed here rather than
being carried as an additional geometric hypothesis.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne
namespace CechTwoCover

attribute [local instance] Scheme.overModule

variable (k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))]
variable (U₀ U₁ : X.Opens)

/-! ### Canonical Cech/Mayer--Vietoris identification -/

/-- The section-level Cech difference is the restriction-difference map of the canonical
Mayer--Vietoris square. -/
lemma scheme_diff_eq_moduleDiff (hcov : U₀ ⊔ U₁ = ⊤) :
    diff (leftRestriction k X U₀ U₁) (rightRestriction k X U₀ U₁) =
      (X.twoCoverSquare U₀ U₁ hcov).moduleDiff (X.moduleKSheaf k) := by
  apply LinearMap.ext
  intro s
  rw [diff_apply]
  rfl

/-- The quotient by the canonical Mayer--Vietoris difference map is linearly equivalent to the
section-level Cech quotient. -/
noncomputable def moduleDiffQuotientEquiv (hcov : U₀ ⊔ U₁ = ⊤) :
    ((X.moduleKSheaf k).obj.obj (op (U₀ ⊓ U₁)) ⧸
      LinearMap.range ((X.twoCoverSquare U₀ U₁ hcov).moduleDiff (X.moduleKSheaf k))) ≃ₗ[k]
        schemeH1Cok k X U₀ U₁ :=
  Submodule.quotEquivOfEq _ _
    (congrArg LinearMap.range (scheme_diff_eq_moduleDiff k X U₀ U₁ hcov).symm)

/-! ### The finiteness consumer -/

/-- If the two pieces are affine (so their degree-one cohomology vanishes through the supplied
cokernel-section maps), and the overlap satisfies the Laurent-window hypotheses, then the
degree-one cohomology of the structure sheaf is a finite `k`-module. -/
theorem moduleFinite_hModule_one_of_twoCover
    (hcov : U₀ ⊔ U₁ = ⊤)
    (hsurj₀ : Function.Surjective
      ((cokernel.π (Injective.ι (X.moduleKSheaf k))).hom.app (op U₀)).hom)
    (hsurj₁ : Function.Surjective
      ((cokernel.π (Injective.ι (X.moduleKSheaf k))).hom.app (op U₁)).hom)
    [Module (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    [IsScalarTower k (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    [Module.Finite (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
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
      (Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) k
        (X.moduleKSheaf k) 1) := by
  letI : Subsingleton (Sheaf.HModule' (X.moduleKSheaf k) U₀ 1) :=
    Sheaf.HModule'.subsingleton_one_of_cokernel_app_surjective
      (X.moduleKSheaf k) U₀ hsurj₀
  letI : Subsingleton (Sheaf.HModule' (X.moduleKSheaf k) U₁ 1) :=
    Sheaf.HModule'.subsingleton_one_of_cokernel_app_surjective
      (X.moduleKSheaf k) U₁ hsurj₁
  let eMV := Scheme.twoCoverH1LinearEquiv k X U₀ U₁
    (X.moduleKSheaf k) hcov
  have ecomp : Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) k
      (X.moduleKSheaf k) 1 ≃ₗ[k] schemeH1Cok k X U₀ U₁ :=
    eMV.trans (moduleDiffQuotientEquiv k X U₀ U₁ hcov)
  letI : Module.Finite k (schemeH1Cok k X U₀ U₁) :=
    moduleFinite_H1Cok
      (leftRestriction k X U₀ U₁) (rightRestriction k X U₀ U₁)
      hσ₀ hσ₁ hσ₀loc hσ₁loc
  exact Module.Finite.equiv ecomp.symm

/-- Affine-open specialization of the two-cover finiteness consumer.  The
surjectivity assumptions for the injective cokernel are discharged by the
quasi-coherent affine vanishing API; the Laurent-window conditions remain explicit
geometric/algebraic inputs. -/
theorem moduleFinite_hModule_one_of_twoCover_of_affine
    (hcov : U₀ ⊔ U₁ = ⊤)
    (hU₀ : IsAffineOpen U₀) (hU₁ : IsAffineOpen U₁)
    [Module (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    [IsScalarTower k (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
    [Module.Finite (LaurentPolynomial k) Γ(X, U₀ ⊓ U₁)]
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
      (Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) k
        (X.moduleKSheaf k) 1) := by
  have hsurj₀ : Function.Surjective
      ((cokernel.π (Injective.ι (X.moduleKSheaf k))).hom.app (op U₀)).hom := by
    intro q
    exact hU₀.cokernel_app_surjective_of_qcoh
      (Injective.ι (X.moduleKSheaf k)) q
  have hsurj₁ : Function.Surjective
      ((cokernel.π (Injective.ι (X.moduleKSheaf k))).hom.app (op U₁)).hom := by
    intro q
    exact hU₁.cokernel_app_surjective_of_qcoh
      (Injective.ι (X.moduleKSheaf k)) q
  exact moduleFinite_hModule_one_of_twoCover k X U₀ U₁ hcov hsurj₀ hsurj₁
    hσ₀ hσ₁ hσ₀loc hσ₁loc

/-! ### Finite-map consumer

The projective-line argument supplies a finite morphism together with two affine target
charts and Laurent-window data on their pulled-back overlap.  The following theorem isolates
the map-theoretic part of that argument: it pulls the affine cover back along a supplied finite
morphism, while leaving the Laurent module and four window conditions explicit.
-/

/-- Pulling back a cover preserves the top-open equality.  This named geometric fact is reused
by concrete finite-map constructions, including the eventual projective-line charts. -/
lemma preimage_sup_eq_top_of_sup_eq_top
    {Y : Scheme.{u}} (π : X ⟶ Y) {V₀ V₁ : Y.Opens}
    (hcov : V₀ ⊔ V₁ = ⊤) :
    π ⁻¹ᵁ V₀ ⊔ π ⁻¹ᵁ V₁ = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, hcov, Scheme.Hom.preimage_top]

theorem moduleFinite_hModule_one_of_isFinite_affineCover
    {Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]
    (V₀ V₁ : Y.Opens) (hcov : V₀ ⊔ V₁ = ⊤)
    (hV₀ : IsAffineOpen V₀) (hV₁ : IsAffineOpen V₁)
    [Module (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ V₀ ⊓ π ⁻¹ᵁ V₁)]
    [IsScalarTower k (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ V₀ ⊓ π ⁻¹ᵁ V₁)]
    [Module.Finite (LaurentPolynomial k)
      Γ(X, π ⁻¹ᵁ V₀ ⊓ π ⁻¹ᵁ V₁)]
    (hσ₀ : ∀ x ∈ LinearMap.range
      (leftRestriction k X (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁)),
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈
        LinearMap.range (leftRestriction k X (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁)))
    (hσ₁ : ∀ x ∈ LinearMap.range
      (rightRestriction k X (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁)),
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈
        LinearMap.range (rightRestriction k X (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁)))
    (hσ₀loc : ∀ n : Γ(X, π ⁻¹ᵁ V₀ ⊓ π ⁻¹ᵁ V₁), ∃ m : ℕ,
      ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (leftRestriction k X (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁)))
    (hσ₁loc : ∀ n : Γ(X, π ⁻¹ᵁ V₀ ⊓ π ⁻¹ᵁ V₁), ∃ m : ℕ,
      ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (rightRestriction k X (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁))) :
    Module.Finite k
      (Sheaf.HModule (Opens.grothendieckTopology (X : TopCat)) k
        (X.moduleKSheaf k) 1) := by
  have hpre : π ⁻¹ᵁ V₀ ⊔ π ⁻¹ᵁ V₁ = ⊤ :=
    preimage_sup_eq_top_of_sup_eq_top X π hcov
  exact moduleFinite_hModule_one_of_twoCover_of_affine k X
    (π ⁻¹ᵁ V₀) (π ⁻¹ᵁ V₁) hpre (hV₀.preimage π) (hV₁.preimage π)
    hσ₀ hσ₁ hσ₀loc hσ₁loc

end CechTwoCover
end Hartshorne
