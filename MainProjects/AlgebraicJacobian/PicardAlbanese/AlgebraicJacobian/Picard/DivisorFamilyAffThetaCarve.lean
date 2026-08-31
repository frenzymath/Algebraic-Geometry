/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFraming
import AlgebraicJacobian.Picard.DivSchemeEpsCarve

/-!
# The carve condition for widened certified divisor families

The carve condition used by the divisor classifier depends only on the two divisor windows and
the local equations cutting out the divisor.  It is therefore independent of whether those
equations are packaged by the old chart-typed carrier or by `CertifiedDivisorFamilyAff`.

`CertifiedDivisorFamilyAff.eps_carve` records the carrier-free form needed by the widened
classifier.  Its proof is the same membership argument as `divFamEps_carve`: multiplication by a
section of the shift window preserves vanishing along arbitrary local equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]
variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
variable [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k ((Scheme.moduleKSheaf k C.left).HModule 0)]
  [Module.Finite k ((Scheme.moduleKSheaf k C.left).HModule 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k)) (g : ℕ)

namespace CertifiedDivisorFamilyAff

set_option maxHeartbeats 800000 in
-- Unfolding both widened windows traverses the relative-section algebra tower.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- The epsilon pair of every widened certified divisor family satisfies the divisor-carve
condition.  No cover or chart typing enters: the assertion follows directly from the local
equations defining the two windows. -/
theorem eps_carve (F : CertifiedDivisorFamilyAff C R g)
    (a : ↥(divisorSections k (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)) :
    carvePairArrow (windowShiftMul hpi g a) (F.eps hpi g).1 (F.eps hpi g).2 = 0 := by
  rw [carvePairArrow_eq_zero_iff]
  intro x hx
  rw [eps_fst] at hx
  rw [eps_snd]
  exact windowShiftMul_mem_divisorWindow C pi hpi g R F.eqns a hx

end CertifiedDivisorFamilyAff

end AlgebraicGeometry
