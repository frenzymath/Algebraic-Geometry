/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4RiemannRochEuler

/-!
# The curve Serre-duality interface

The construction of the canonical sheaf and its duality pairing is a substantial
geometric input.  This module keeps that input explicit while exposing the
dimension-level statement consumed by Riemann--Roch: degree-one cohomology of
`𝒪(D)` is linearly equivalent to the dual of degree-zero cohomology of
`𝒪(K-D)`.  The resulting theorem is therefore a genuine consumer of an
explicit, load-bearing duality certificate, rather than an unconditional axiom
or hidden instance.  The certificate does not construct `K`, a canonical
sheaf, or a trace pairing.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-- A source-level Serre-duality certificate for a smooth proper integral curve.

The field `h1_dual` records the duality pairing after passing to the induced
linear equivalence of cohomology spaces.  Existence of the canonical divisor
and this equivalence is deliberately an explicit producer obligation.
-/
structure CurveSerreDualityData where
  canonicalDivisor : CurveDivisor k X
  h1_dual : ∀ D : CurveDivisor k X,
    (CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k
      (divisorSheaf D) 1) ≃ₗ[k]
      Module.Dual k (CategoryTheory.Sheaf.HModule
        (Opens.grothendieckTopology (X.left : TopCat)) k
        (divisorSheaf (canonicalDivisor - D)) 0)

/-- Serre duality gives equality of the corresponding `Module.finrank` values.

The statement deliberately keeps finiteness as a separate producer concern:
`Subspace.dual_finrank_eq` is total even before finite-dimensional instances are
installed, while the smooth-proper finiteness APIs remain available to a
source-level producer.
-/
theorem h1_divisorSheaf_eq_h0_complementary
    (sd : CurveSerreDualityData (k := k) (X := X))
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.h1 (divisorSheaf D) =
      CategoryTheory.Sheaf.h0 (divisorSheaf (sd.canonicalDivisor - D)) := by
  have hfin := (sd.h1_dual D).finrank_eq
  rw [Subspace.dual_finrank_eq] at hfin
  exact hfin

/-!
## Riemann--Roch consumer

The theorem below is the exact integer-valued `h0 - h1` ledger form that
corresponds to Hartshorne IV.1.3 once the canonical-divisor and genus bridges
are supplied.  The project-level `Sheaf.chi` is this truncated degree-zero/one
ledger, not a separately proved higher-cohomology Euler characteristic.  Its
Euler increment is provided by `chi_divisorSheaf_eq_one_sub_h1_add_degree`; the
only additional input here is the explicit duality certificate above.
-/

theorem riemannRoch_of_curveSerreDuality
    (sd : CurveSerreDualityData (k := k) (X := X))
    (D : CurveDivisor k X) :
    (CategoryTheory.Sheaf.h0 (divisorSheaf D) : ℤ) -
        (CategoryTheory.Sheaf.h0
          (divisorSheaf (sd.canonicalDivisor - D)) : ℤ) =
      CurveDivisor.degree D + 1 -
        (CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) : ℤ) := by
  have hχ := chi_divisorSheaf_eq_one_sub_h1_add_degree (X := X) D
  have hdual := h1_divisorSheaf_eq_h0_complementary sd D
  simp only [CategoryTheory.Sheaf.chi] at hχ
  rw [hdual] at hχ
  omega

end
end Hartshorne
