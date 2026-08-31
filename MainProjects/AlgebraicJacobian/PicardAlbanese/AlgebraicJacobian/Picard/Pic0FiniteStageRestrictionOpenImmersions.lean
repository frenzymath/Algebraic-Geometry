/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.OpenImmersionFieldTowerDescent
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionModels

/-!
# Open immersions in the finite-stage Picard atlas

The canonical restriction from a chart ring to an affine intersection ring induces an
open immersion on spectra.  This property descends to every finite-stage restriction map
produced by `exists_finSubext_pic0FiniteStageRestriction_models`.

Only the objects, restriction maps, and their open-immersion certificates are packaged
here.  No transition, cocycle, or gluing assertion is made.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- Restriction between affine opens induces an open immersion on affine spectra. -/
theorem isOpenImmersion_specMap_affineRestriction
    {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hVU).op)) := by
  let f := Spec.map (X.presheaf.map (homOfLE hVU).op)
  haveI : IsOpenImmersion hU.fromSpec := inferInstance
  have hcomp : IsOpenImmersion (f ≫ hU.fromSpec) := by
    change IsOpenImmersion
      (Spec.map (X.presheaf.map (homOfLE hVU).op) ≫ hU.fromSpec)
    rw [IsAffineOpen.map_fromSpec hU hV (homOfLE hVU).op]
    infer_instance
  letI : IsOpenImmersion (f ≫ hU.fromSpec) := hcomp
  exact IsOpenImmersion.of_comp f hU.fromSpec

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- Every canonical restriction in the exact finite affine atlas induces an open immersion
on spectra. -/
theorem isOpenImmersion_pic0FiniteStageRestriction
    (i : Pic0FiniteStageRestrictionIndex C) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (pic0FiniteStageRestriction C i).toRingHom)) := by
  rcases i with ⟨U, V⟩ | ⟨U, V⟩
  · change IsOpenImmersion
      (Spec.map (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
        (homOfLE (pic0FiniteStageAffineOverlap_le_left C U V)).op))
    exact isOpenImmersion_specMap_affineRestriction U.1.2
      (pic0FiniteStageAffineOverlap C U V).2
      (pic0FiniteStageAffineOverlap_le_left C U V)
  · change IsOpenImmersion
      (Spec.map (((pic0_sepClosed_representableBy (C := C)).1.left).presheaf.map
        (homOfLE (pic0FiniteStageAffineOverlap_le_right C U V)).op))
    exact isOpenImmersion_specMap_affineRestriction V.1.2
      (pic0FiniteStageAffineOverlap C U V).2
      (pic0FiniteStageAffineOverlap_le_right C U V)

set_option synthInstance.maxHeartbeats 200000 in
-- The conclusion contains one dependent quotient-algebra instance for every restriction leg.
set_option maxHeartbeats 1200000 in
-- The transported commuting squares and their open-immersion certificates elaborate together.
/-- The simultaneous finite-stage restriction models may be chosen so that every descended
restriction map induces an open immersion on spectra. -/
theorem exists_finSubext_pic0FiniteStageRestriction_openImmersion_models
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
            ((Algebra.TensorProduct.map M.1.val
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
                      (relation (Pic0FiniteStageRestrictionSource C i)))))) ∧
              IsOpenImmersion (Spec.map (CommRingCat.ofHom phiM.toRingHom)) := by
  obtain ⟨L, n, m, relation, e, M, hM⟩ :=
    exists_finSubext_pic0FiniteStageRestriction_models (C := C) (F := F)
  refine ⟨L, n, m, relation, e, M, ?_⟩
  intro i
  obtain ⟨phiM, hphiM⟩ := hM i
  refine ⟨phiM, hphiM, ?_⟩
  let psi :=
    (e (Pic0FiniteStageRestrictionTarget C i)).symm.toAlgHom.comp
      ((pic0FiniteStageRestriction C i).comp
        (e (Pic0FiniteStageRestrictionSource C i)).toAlgHom)
  apply isOpenImmersion_of_fieldTower_tensorProducts
    (F := L.1) (L := M.1) (K := k) phiM psi
  · have hval : M.1.val = IsScalarTower.toAlgHom L.1 M.1 k := by
      ext x
      rfl
    rw [← hval]
    exact hphiM
  · apply isOpenImmersion_specMap_conjugate
      (e (Pic0FiniteStageRestrictionSource C i)).toRingEquiv
      (e (Pic0FiniteStageRestrictionTarget C i)).toRingEquiv
      (pic0FiniteStageRestriction C i).toRingHom
    exact isOpenImmersion_pic0FiniteStageRestriction C i

end

end AlgebraicGeometry
