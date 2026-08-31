/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.IsomorphismFieldTowerDescent
import AlgebraicJacobian.Picard.Pic0FiniteStageTransitionModels

/-!
# Diagonal restrictions in the finite-stage Picard atlas

On a diagonal chart pair `(U, U)`, the exact overlap is the same open as `U`.  Hence the
left restriction map induces an isomorphism on spectra.  The field-tower comparison square
then descends this fact to any common finite-stage transition model.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- The exact left restriction to the diagonal overlap `U \cap U` induces an isomorphism
on affine spectra. -/
theorem isIso_specMap_pic0FiniteStageRestriction_diagonal_left
    (U : Pic0FiniteStageChartIndex C) :
    IsIso (Spec.map (CommRingCat.ofHom
      (pic0FiniteStageRestriction C (Sum.inl (U, U))).toRingHom)) := by
  change IsIso
    (Spec.map (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
      (homOfLE (pic0FiniteStageAffineOverlap_le_left C U U)).op))
  have hback :
      U.1.1 <= (pic0FiniteStageAffineOverlap C U U).1 := by
    simp [pic0FiniteStageAffineOverlap]
  haveI : IsIso
      (homOfLE (pic0FiniteStageAffineOverlap_le_left C U U)) := by
    constructor
    refine ⟨homOfLE hback, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  haveI : IsIso
      (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
        (homOfLE (pic0FiniteStageAffineOverlap_le_left C U U)).op) :=
    Functor.map_isIso _
      (homOfLE (pic0FiniteStageAffineOverlap_le_left C U U)).op
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
-- Dependent source and target tensor products must elaborate at the selected diagonal index.
set_option maxHeartbeats 1600000 in
-- The field-tower comparison and conjugated exact restriction are unified simultaneously.
/-- A descended diagonal left restriction in a common finite-stage transition model induces
an isomorphism on spectra.  The only compatibility assumption is the comparison square already
produced by `exists_finSubext_pic0FiniteStageTransition_models`. -/
theorem isIso_specMap_pic0FiniteStageModelRestriction_diagonal_left
    {F : Type u} [Field F] [Algebra F k]
    (L : DatG0.FinSubext F k)
    (n m : Pic0FiniteStageRingIndex C -> Nat)
    (relation : forall j, Fin (m j) -> MvPolynomial (Fin (n j)) L.1)
    (e : forall j,
      k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 (n j) (m j) (relation j) ≃ₐ[k]
        Pic0FiniteStageRing C j)
    (M : DatG0.FinSubext L.1 k)
    (mapM : forall q : Pic0FiniteStageMapIndex C,
      Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapSource C q) →ₐ[M.1]
        Pic0FiniteStageModelRing C L n m relation M
          (Pic0FiniteStageMapTarget C q))
    (hmapM : forall q,
      (Algebra.TensorProduct.map M.1.val
          (AlgHom.id L.1
            (DatG0.FiniteRelationAlgebra L.1
              (n (Pic0FiniteStageMapTarget C q))
              (m (Pic0FiniteStageMapTarget C q))
              (relation (Pic0FiniteStageMapTarget C q))))).comp
          ((mapM q).restrictScalars L.1) =
        ((pic0FiniteStageTransportedMap C L n m relation e q).restrictScalars
          L.1).comp
          (Algebra.TensorProduct.map M.1.val
            (AlgHom.id L.1
              (DatG0.FiniteRelationAlgebra L.1
                (n (Pic0FiniteStageMapSource C q))
                (m (Pic0FiniteStageMapSource C q))
                (relation (Pic0FiniteStageMapSource C q))))))
    (U : Pic0FiniteStageChartIndex C) :
    IsIso (Spec.map (CommRingCat.ofHom
      (mapM (Sum.inl (Sum.inl (U, U)))).toRingHom)) := by
  let q : Pic0FiniteStageMapIndex C := Sum.inl (Sum.inl (U, U))
  let psi := pic0FiniteStageTransportedMap C L n m relation e q
  change IsIso (Spec.map (CommRingCat.ofHom (mapM q).toRingHom))
  apply isIso_specMap_of_fieldTower_tensorProducts
    (F := L.1) (L := M.1) (K := k) (mapM q) psi
  · have hval : M.1.val = IsScalarTower.toAlgHom L.1 M.1 k := by
      ext x
      rfl
    rw [← hval]
    exact hmapM q
  · apply isIso_specMap_conjugate
      (e (Pic0FiniteStageRestrictionSource C (Sum.inl (U, U)))).toRingEquiv
      (e (Pic0FiniteStageRestrictionTarget C (Sum.inl (U, U)))).toRingEquiv
      (pic0FiniteStageRestriction C (Sum.inl (U, U))).toRingHom
    exact isIso_specMap_pic0FiniteStageRestriction_diagonal_left C U

end

end AlgebraicGeometry
