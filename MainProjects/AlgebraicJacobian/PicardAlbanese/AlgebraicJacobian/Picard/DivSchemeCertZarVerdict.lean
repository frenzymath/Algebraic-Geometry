/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeCertZarC1
import AlgebraicJacobian.Picard.DivSchemeCertZarTransport

/-!
# The chart-confinement obstruction in witness form

`DivSchemeCertZarC1.lean` establishes the verdict positively: a certified adaptation of a
connected divisor confines its support to one pinned chart
(`supportLocus_subset_chart_of_isCertified`).  Its contrapositive is recorded there only for
the *leak-free* hypothesis and only in "not contained in either chart" form.

This file states the obstruction in the form a would-be user of the interface meets it: with
two **witness points** of the support, one off `V₀` and one off `V₁`.  That is the shape in
which a concrete divisor — e.g. one whose fibre over a base point is `{0, ∞}` — refutes
certifiability, and it needs no leak hypothesis.

Combined with the pullback transport (`DivSchemeCertZarTransport.lean`), which shows support
loci pull back along the base-shrinking maps, the obstruction is visibly Zariski-local on the
base: shrinking cannot separate the two witnesses.

## Main declarations

* `AlgebraicGeometry.DivisorAdaptation.not_isCertified_of_isPreconnected_of_witnesses` — a
  connected divisor with a support point off each pinned chart admits no certified adaptation,
  in any degree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); pin in-file. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace DivisorAdaptation

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]
variable {d : (relCurve C R).LocalEquations}
variable (A : DivisorAdaptation C R pi d)

/-- **The obstruction in witness form.** If the support is connected and contains a point
outside `V₀` and a point outside `V₁` — i.e. the divisor genuinely meets both `pi⁻¹(∞)` and
`pi⁻¹(0)` — then `A` carries no certificate, in any degree.

No leak hypothesis: clause (c1) of `IsCertified` supplies it
(`supportLeak_eq_empty_of_finite_colength`).  So the interface does not merely make such
divisors hard to certify, it excludes them. -/
theorem not_isCertified_of_isPreconnected_of_witnesses {n : ℕ}
    (hconn : _root_.IsPreconnected d.supportLocus)
    {x y : relCurve C R} (hx : x ∈ d.supportLocus) (hy : y ∈ d.supportLocus)
    (hx₀ : x ∉ ((relCover C R (fiberTwoCover pi)).V₀ : Set (relCurve C R)))
    (hy₁ : y ∉ ((relCover C R (fiberTwoCover pi)).V₁ : Set (relCurve C R))) :
    ¬ A.IsCertified n := by
  intro hc
  rcases A.supportLocus_subset_chart_of_isCertified hconn hc with h₀ | h₁
  · exact hx₀ (h₀ hx)
  · exact hy₁ (h₁ hy)

end DivisorAdaptation

end AlgebraicGeometry
