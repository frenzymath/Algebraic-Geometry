/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import AlgebraicJacobian.Picard.DivSchemeRedesignKappaZ

/-!
# DD-4 redesign: the exact single-point `κ(z)` support interface

`DivSchemeRedesignKappaZ.lean` provides the forward RD-N consumer from a vanishing
residue fibre.  This file exposes the underlying finite-module equivalence in the exact
shape needed by callers: at the chart prime of a point `z`, support avoidance is equivalent
to the residue-field tensor being subsingleton.  The prime is the prime of `Γ(V)` itself;
there is no comap to the test ring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}

namespace ThetaGeneratorSeed

set_option maxHeartbeats 2400000 in
-- The chart section-ring/support instance chain re-elaborates the finite-module witness.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- **Exact single-point XS equivalence.**  For a point `z` in the pinned affine chart
`V = relPinnedChart C R π b`, put `pz = primeIdealOf z` and
`κ(z) = pz.asIdeal.ResidueField`.  Since `chartColengthModule K b s` is finite over
`Γ(V)`, its support avoids `pz` exactly when its `κ(z)`-tensor is subsingleton. -/
theorem notMem_support_chartColengthModule_iff_subsingleton_tmul_residueField_kappaZ
    (K : Submodule R (relThetaSections C R π a)) (b : Bool)
    (s : relThetaSections C R π a) [Module.Finite R ↥K]
    {z : relCurve C R} (hz : z ∈ relPinnedChart C R π b) :
    (isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩ ∉
        Module.support Γ(relCurve C R, relPinnedChart C R π b)
          ↥(chartColengthModule K b s) ↔
      Subsingleton (↥(chartColengthModule K b s) ⊗[
        Γ(relCurve C R, relPinnedChart C R π b)]
        ((isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField) := by
  haveI := chartColengthModule_finite K b s
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    not_nontrivial_iff_subsingleton]
  exact (TensorProduct.comm Γ(relCurve C R, relPinnedChart C R π b)
    ((isAffineOpen_relPinnedChart C R π b).primeIdealOf ⟨z, hz⟩).asIdeal.ResidueField
    (↥(chartColengthModule K b s))).toEquiv.subsingleton_congr

end ThetaGeneratorSeed

end AlgebraicGeometry
