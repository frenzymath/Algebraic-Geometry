/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.OpenImmersionFieldDescent
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Open immersions and iterated field extension

This file packages the tensor reassociation needed to descend an affine open immersion
through a tower of fields.  The input square is stated on the convenient tensor products
`L ⊗[ F ] A` and `K ⊗[ F ] A`; the proof converts it to the single scalar extension
used by `isOpenImmersion_of_tensorProduct`.
-/

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-- The canonical ring equivalence which cancels an intermediate scalar extension. -/
def tensorProductFieldTowerEquiv {F L K A : Type u}
    [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [CommRing A] [Algebra F A] :
    ((L ⊗[F] A) ⊗[L] K) ≃+* (K ⊗[F] A) :=
  (Algebra.TensorProduct.comm L (L ⊗[F] A) K).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange F L K K A).toRingEquiv

/-- Evaluation of `tensorProductFieldTowerEquiv` on a pure tensor. -/
theorem tensorProductFieldTowerEquiv_tmul {F L K A : Type u}
    [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [CommRing A] [Algebra F A]
    (x : L ⊗[F] A) (c : K) :
    tensorProductFieldTowerEquiv (F := F) (L := L) (K := K) (A := A)
        (x ⊗ₜ[L] c) =
      c • Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom F L K) (AlgHom.id F A) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      simp [tensorProductFieldTowerEquiv,
        Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy =>
      rw [TensorProduct.add_tmul, map_add, hx, hy, map_add, smul_add]

/-- Conjugating a ring map by ring equivalences preserves openness of its affine spectrum. -/
theorem isOpenImmersion_specMap_conjugate {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (eA : A ≃+* A') (eB : B ≃+* B') (phi : A' →+* B')
    (hphi : IsOpenImmersion (Spec.map (CommRingCat.ofHom phi))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (eB.symm.toRingHom.comp (phi.comp eA.toRingHom)))) := by
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom phi)) := hphi
  haveI : IsIso (CommRingCat.ofHom eA.toRingHom) := by
    change IsIso eA.toCommRingCatIso.hom
    infer_instance
  haveI : IsIso (CommRingCat.ofHom eB.symm.toRingHom) := by
    change IsIso eB.symm.toCommRingCatIso.hom
    infer_instance
  infer_instance

/-- If the scalar extension of an algebra map is conjugate to an open immersion, then the
original affine spectrum map is an open immersion. -/
theorem isOpenImmersion_of_tensorProduct_conjugate {L K A B A' B' : Type u}
    [Field L] [Field K] [Algebra L K]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    [CommRing A'] [CommRing B']
    (phi : A →ₐ[L] B)
    (eA : (A ⊗[L] K) ≃+* A') (eB : (B ⊗[L] K) ≃+* B')
    (psi : A' →+* B')
    (hconj : eB.toRingHom.comp
        (Algebra.TensorProduct.map phi (AlgHom.id L K)).toRingHom =
      psi.comp eA.toRingHom)
    (hpsi : IsOpenImmersion (Spec.map (CommRingCat.ofHom psi))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom phi.toRingHom)) := by
  apply isOpenImmersion_of_tensorProduct (K := K) phi
  let basePhi : (A ⊗[L] K) →+* (B ⊗[L] K) :=
    (Algebra.TensorProduct.map phi (AlgHom.id L K)).toRingHom
  have hbase :
      basePhi = eB.symm.toRingHom.comp (psi.comp eA.toRingHom) := by
    apply DFunLike.ext _ _
    intro x
    apply eB.injective
    change eB (basePhi x) = eB (eB.symm (psi (eA x)))
    rw [eB.apply_symm_apply]
    exact DFunLike.congr_fun hconj x
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom basePhi))
  rw [hbase, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp]
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom psi)) := hpsi
  haveI : IsIso (CommRingCat.ofHom eA.toRingHom) := by
    change IsIso eA.toCommRingCatIso.hom
    infer_instance
  haveI : IsIso (CommRingCat.ofHom eB.symm.toRingHom) := by
    change IsIso eB.symm.toCommRingCatIso.hom
    infer_instance
  infer_instance

/-- Open immersions descend through a tower of fields when the iterated tensor-product
square commutes.  This is the reassociated form needed by finite-stage spreading out. -/
theorem isOpenImmersion_of_fieldTower_tensorProducts {F L K A B : Type u}
    [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    (phi : (L ⊗[F] A) →ₐ[L] (L ⊗[F] B))
    (psi : (K ⊗[F] A) →ₐ[K] (K ⊗[F] B))
    (hcomm :
      (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom F L K) (AlgHom.id F B)).comp
          (phi.restrictScalars F) =
        (psi.restrictScalars F).comp
          (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom F L K) (AlgHom.id F A)))
    (hpsi : IsOpenImmersion (Spec.map (CommRingCat.ofHom psi.toRingHom))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom phi.toRingHom)) := by
  apply isOpenImmersion_of_tensorProduct_conjugate (K := K) phi
    (tensorProductFieldTowerEquiv (F := F) (L := L) (K := K) (A := A))
    (tensorProductFieldTowerEquiv (F := F) (L := L) (K := K) (A := B))
    psi.toRingHom
  · apply DFunLike.ext _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        change
          tensorProductFieldTowerEquiv
              ((Algebra.TensorProduct.map phi (AlgHom.id L K)) (x ⊗ₜ[L] c)) =
            psi (tensorProductFieldTowerEquiv (x ⊗ₜ[L] c))
        rw [Algebra.TensorProduct.map_tmul, tensorProductFieldTowerEquiv_tmul,
          tensorProductFieldTowerEquiv_tmul, map_smul]
        exact congrArg (c • ·) (DFunLike.congr_fun hcomm x)
    | add x y hx hy =>
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · exact hpsi

end

end AlgebraicGeometry
