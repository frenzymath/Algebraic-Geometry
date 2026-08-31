/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineBaseChange

/-!
# Transitivity of affine base-change comparisons

A natural square of scalar-extended affine rings remains natural after the
pullback-Spec comparison and two chosen ring identifications.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

namespace Pic0FiniteStageGluePackage

variable (R K A B A' B' : Type u)
variable [CommRing R] [CommRing K] [CommRing A] [CommRing B]
  [CommRing A'] [CommRing B']
variable [Algebra R K] [Algebra R A] [Algebra R B]
  [Algebra K A'] [Algebra K B']

set_option maxHeartbeats 12800000 in
-- The proof expands tensor-product Spec maps and both comparison equivalences.
/-- A natural square of scalar-extended affine rings remains natural after the
pullback-Spec comparison and the two final ring identifications. -/
theorem affineBaseChangeIso_trans_naturality
    (phi : A →ₐ[R] B)
    (eA : K ⊗[R] A ≃ₐ[K] A')
    (eB : K ⊗[R] B ≃ₐ[K] B')
    (psi : A' →ₐ[K] B')
    (hnat :
      eB.toAlgHom.comp
          (AlgebraicJacobian.scalarExtensionMapOfAlgHom
            (R := R) (K := K) phi) =
        psi.comp eA.toAlgHom) :
    affineBaseChangeMap R K A B phi ≫
        (affineBaseChangeIso R K A ≪≫
          Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op).hom =
      (affineBaseChangeIso R K B ≪≫
          Scheme.Spec.mapIso eB.symm.toRingEquiv.toCommRingCatIso.op).hom ≫
        Spec.map (CommRingCat.ofHom psi.toRingHom) := by
  let f := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) phi
  have hinv : f.comp eA.symm.toAlgHom = eB.symm.toAlgHom.comp psi := by
    ext x
    apply eB.injective
    have hx := DFunLike.congr_fun hnat (eA.symm x)
    simpa [f] using hx
  have hspec :
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          (Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op).hom =
        (Scheme.Spec.mapIso eB.symm.toRingEquiv.toCommRingCatIso.op).hom ≫
          Spec.map (CommRingCat.ofHom psi.toRingHom) := by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map eA.symm.toRingEquiv.toCommRingCatIso.hom =
      Spec.map eB.symm.toRingEquiv.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom psi.toRingHom)
    have hcat :
        eA.symm.toRingEquiv.toCommRingCatIso.hom ≫
            CommRingCat.ofHom f.toRingHom =
          CommRingCat.ofHom psi.toRingHom ≫
            eB.symm.toRingEquiv.toCommRingCatIso.hom := by
      ext x
      exact DFunLike.congr_fun hinv x
    calc
      _ = Spec.map (eA.symm.toRingEquiv.toCommRingCatIso.hom ≫
            CommRingCat.ofHom f.toRingHom) := (Spec.map_comp _ _).symm
      _ = Spec.map (CommRingCat.ofHom psi.toRingHom ≫
            eB.symm.toRingEquiv.toCommRingCatIso.hom) := congrArg Spec.map hcat
      _ = _ := Spec.map_comp _ _
  simp only [Iso.trans_hom]
  have haff := affineBaseChangeIso_naturality R K A B phi
  calc
    _ = (affineBaseChangeMap R K A B phi ≫
          (affineBaseChangeIso R K A).hom) ≫
        (Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op).hom :=
      (Category.assoc _ _ _).symm
    _ = ((affineBaseChangeIso R K B).hom ≫
          Spec.map (CommRingCat.ofHom f.toRingHom)) ≫
        (Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op).hom :=
      congrArg
        (fun h => h ≫
          (Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op).hom)
        haff
    _ = (affineBaseChangeIso R K B).hom ≫
        (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          (Scheme.Spec.mapIso eA.symm.toRingEquiv.toCommRingCatIso.op).hom) :=
      Category.assoc _ _ _
    _ = (affineBaseChangeIso R K B).hom ≫
        ((Scheme.Spec.mapIso eB.symm.toRingEquiv.toCommRingCatIso.op).hom ≫
          Spec.map (CommRingCat.ofHom psi.toRingHom)) :=
      congrArg (fun h => (affineBaseChangeIso R K B).hom ≫ h) hspec
    _ = _ := (Category.assoc _ _ _).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
