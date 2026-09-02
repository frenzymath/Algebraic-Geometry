/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter1CurveStalks
import HartshorneLib.Chapter4P1Points

/-!
# Point topology of the projective line

The standard affine charts of `P1` are polynomial Dedekind domains.  This file records the
resulting height-one specialization order, closed-point criterion, and the existence of a
non-generic point used by finite-fiber arguments.
-/

set_option autoImplicit false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k]

local notation "𝒜" => homogeneousSubmodule (Fin 2) k

/-- The section ring of either standard chart is a principal ideal ring. -/
theorem isPrincipalIdealRing_chartSections (i : Fin 2) :
    IsPrincipalIdealRing Γ(P1 k, chartOpen k i) := by
  fin_cases i
  · exact IsPrincipalIdealRing.of_surjective (chartSectionsEquiv₀ k).symm.toRingHom
      (chartSectionsEquiv₀ k).symm.surjective
  · exact IsPrincipalIdealRing.of_surjective (chartSectionsEquiv₁ k).symm.toRingHom
      (chartSectionsEquiv₁ k).symm.surjective

/-- The section ring of either standard chart is a domain. -/
theorem isDomain_chartSections (i : Fin 2) : IsDomain Γ(P1 k, chartOpen k i) := by
  fin_cases i
  · exact MulEquiv.isDomain (Polynomial k) (chartSectionsEquiv₀ k).toMulEquiv
  · exact MulEquiv.isDomain (Polynomial k) (chartSectionsEquiv₁ k).toMulEquiv

/-- The section ring of either standard chart is a Dedekind domain. -/
theorem isDedekindDomain_chartSections (i : Fin 2) :
    IsDedekindDomain Γ(P1 k, chartOpen k i) :=
  letI := isDomain_chartSections k i
  letI := isPrincipalIdealRing_chartSections k i
  inferInstance

/-- `P1` has a point besides its generic point. -/
theorem exists_ne_genericPoint : ∃ z : P1 k, z ≠ genericPoint (P1 k) := by
  have hnf : ¬IsField (Away 𝒜 (X (0 : Fin 2))) := fun h =>
    Polynomial.not_isField k
      ((awayAlgEquiv k fin_zero_ne_one).symm.toRingEquiv.toMulEquiv.isField h)
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  refine ⟨(chartι k 0).base ⟨p, hp⟩, fun h => hp0 ?_⟩
  rw [← chartι_base_genericPoint, genericPoint_eq_bot_of_affine] at h
  have h' := (chartι k 0).isOpenEmbedding.injective h
  exact congrArg PrimeSpectrum.asIdeal h'

/-- Generalizations in `P1` are either the generic point or the point itself. -/
theorem specializes_eq_genericPoint_or_eq {x y : P1 k} (h : y ⤳ x) :
    y = genericPoint (P1 k) ∨ y = x := by
  have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  rw [TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h0 | h1
  · exact Hartshorne.affineOpen_specializes_eq_genericPoint_or_eq
      (isAffineOpen_chartOpen k 0) (isDedekindDomain_chartSections k 0) h0 h
  · exact Hartshorne.affineOpen_specializes_eq_genericPoint_or_eq
      (isAffineOpen_chartOpen k 1) (isDedekindDomain_chartSections k 1) h1 h

/-- Every non-generic point of `P1` is closed. -/
theorem isClosed_singleton_of_ne_genericPoint {x : P1 k}
    (hx : x ≠ genericPoint (P1 k)) : IsClosed ({x} : Set (P1 k)) := by
  have hcurve : ∀ a b : P1 k, b ⤳ a → b = genericPoint (P1 k) ∨ b = a :=
    fun _ _ h => specializes_eq_genericPoint_or_eq k h
  exact Hartshorne.closed_singleton_of_curve_specializations hcurve hx

/-- The projective line is separated as a scheme. -/
instance : Scheme.IsSeparated (P1 k) := by
  unfold P1
  infer_instance

end P1

end AlgebraicGeometry
