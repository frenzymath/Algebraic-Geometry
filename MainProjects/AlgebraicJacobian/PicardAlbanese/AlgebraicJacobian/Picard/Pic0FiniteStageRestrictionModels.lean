/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageOverlapRings
import AlgebraicJacobian.Picard.FinitePresentationAlgebraMapModels

/-!
# Finite-stage models of the Picard atlas restriction maps

The finite family of chart and overlap rings admits simultaneous presentation models over a
finite subextension.  After passing to a further finite subextension, the canonical restriction
maps descend between those chosen models.  This is only ring-and-map data; no gluing or cocycle
claim is made here.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

set_option synthInstance.maxHeartbeats 200000 in
-- The conclusion contains one dependent quotient-algebra instance for every restriction leg.
set_option maxHeartbeats 1200000 in
-- Elaborating the explicit transported commuting squares requires a larger unification budget.
/-- The chart and overlap presentations can be chosen at one finite stage `L`; at a further
finite stage `M/L`, every left and right atlas restriction has a descended algebra map.  The
displayed equality records that its ambient map is the original restriction transported through
the chosen source and target equivalences. -/
theorem exists_finSubext_pic0FiniteStageRestriction_models
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k] :
    ∃ (L : DatG0.FinSubext F k)
      (n m : Pic0FiniteStageRingIndex C → ℕ)
      (relation : ∀ j, Fin (m j) → MvPolynomial (Fin (n j)) L.1)
      (e : ∀ j,
        k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
          Pic0FiniteStageRing C j),
      ∃ M : DatG0.FinSubext L.1 k,
        ∀ i : Pic0FiniteStageRestrictionIndex C,
          ∃ phiM :
              M.1 ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
                    (n (Pic0FiniteStageRestrictionSource C i))
                    (m (Pic0FiniteStageRestrictionSource C i))
                    (relation (Pic0FiniteStageRestrictionSource C i)) →ₐ[M.1]
                M.1 ⊗[L.1] DatG0.FiniteRelationAlgebra L.1
                    (n (Pic0FiniteStageRestrictionTarget C i))
                    (m (Pic0FiniteStageRestrictionTarget C i))
                    (relation (Pic0FiniteStageRestrictionTarget C i)),
            (Algebra.TensorProduct.map M.1.val
                (AlgHom.id L.1
                  (DatG0.FiniteRelationAlgebra L.1
                    (n (Pic0FiniteStageRestrictionTarget C i))
                    (m (Pic0FiniteStageRestrictionTarget C i))
                    (relation (Pic0FiniteStageRestrictionTarget C i))))).comp
                (phiM.restrictScalars L.1) =
              (((e (Pic0FiniteStageRestrictionTarget C i)).symm.toAlgHom.comp
                  ((pic0FiniteStageRestriction C i).comp
                    (e (Pic0FiniteStageRestrictionSource C i)).toAlgHom)).restrictScalars
                    L.1).comp
                (Algebra.TensorProduct.map M.1.val
                  (AlgHom.id L.1
                    (DatG0.FiniteRelationAlgebra L.1
                      (n (Pic0FiniteStageRestrictionSource C i))
                      (m (Pic0FiniteStageRestrictionSource C i))
                      (relation (Pic0FiniteStageRestrictionSource C i))))) := by
  classical
  obtain ⟨L, hL⟩ :=
    exists_finSubext_pic0FiniteStageAtlas_ring_models (C := C) (F := F)
  choose n m relation hmodel using hL
  let e : ∀ j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j :=
    fun j => Classical.choice (hmodel j)
  refine ⟨L, n, m, relation, e, ?_⟩
  exact DatG0.exists_finSubext_tensorProduct_algHom_finite_of_models
    (F := L.1) (K := k)
    (fun i : Pic0FiniteStageRestrictionIndex C =>
      DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageRestrictionSource C i))
        (m (Pic0FiniteStageRestrictionSource C i))
        (relation (Pic0FiniteStageRestrictionSource C i)))
    (fun i : Pic0FiniteStageRestrictionIndex C =>
      DatG0.FiniteRelationAlgebra L.1
        (n (Pic0FiniteStageRestrictionTarget C i))
        (m (Pic0FiniteStageRestrictionTarget C i))
        (relation (Pic0FiniteStageRestrictionTarget C i)))
    (fun i : Pic0FiniteStageRestrictionIndex C =>
      Pic0FiniteStageRing C (Pic0FiniteStageRestrictionSource C i))
    (fun i : Pic0FiniteStageRestrictionIndex C =>
      Pic0FiniteStageRing C (Pic0FiniteStageRestrictionTarget C i))
    (fun i => e (Pic0FiniteStageRestrictionSource C i))
    (fun i => e (Pic0FiniteStageRestrictionTarget C i))
    (pic0FiniteStageRestriction C)

end

end AlgebraicGeometry
