/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageTensorPushoutUniversal
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelScalarExtensionFaces

/-!
# Comparing scalar extensions of named finite-stage tensor pushouts

Three component equivalences and two naturality squares transport an exact pushout
square to the scalar extensions of a pair of algebra maps.  The named tensor-pushout
universal property then identifies the scalar extension of the original pushout with
the exact target.  Keeping both scalar-extension maps in this abstract context avoids
reconstructing hierarchy instances at dependent specialization sites.

The final two theorems identify the forward faces of the comparison as algebra-map
equalities.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

section Comparison

variable {R K A B1 B2 A0 B10 B20 T : Type u}
variable [CommRing R] [CommRing K] [CommRing A] [CommRing B1] [CommRing B2]
variable [CommRing A0] [CommRing B10] [CommRing B20] [CommRing T]
variable [Algebra R K] [Algebra R A] [Algebra R B1] [Algebra R B2]
variable [Algebra K A0] [Algebra K B10] [Algebra K B20] [Algebra K T]

variable (f1 : A →ₐ[R] B1) (f2 : A →ₐ[R] B2)
variable (eA : (K ⊗[R] A) ≃ₐ[K] A0)
variable (eB1 : (K ⊗[R] B1) ≃ₐ[K] B10)
variable (eB2 : (K ⊗[R] B2) ≃ₐ[K] B20)
variable (g1 : A0 →ₐ[K] B10) (g2 : A0 →ₐ[K] B20)
variable (j1 : B10 →ₐ[K] T) (j2 : B20 →ₐ[K] T)
variable (h1 : eB1.toAlgHom.comp
  (AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f1) = g1.comp eA.toAlgHom)
variable (h2 : eB2.toAlgHom.comp
  (AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f2) = g2.comp eA.toAlgHom)
variable (hPush : IsPushout
  (CommRingCat.ofHom g1.toRingHom)
  (CommRingCat.ofHom g2.toRingHom)
  (CommRingCat.ofHom j1.toRingHom)
  (CommRingCat.ofHom j2.toRingHom))

include eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush

/-- Transporting the exact pushout square through the component equivalences makes the
scalar-extended source maps a pushout with the transported target legs. -/
theorem finiteStageTensorPushoutComparisonSquare :
    let kf1 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f1
    let kf2 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f2
    IsPushout
      (CommRingCat.ofHom kf1.toRingHom)
      (CommRingCat.ofHom kf2.toRingHom)
      (CommRingCat.ofHom (j1.comp eB1.toAlgHom).toRingHom)
      (CommRingCat.ofHom (j2.comp eB2.toAlgHom).toRingHom) := by
  dsimp only
  let kf1 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f1
  let kf2 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f2
  apply hPush.of_iso'
    eA.toRingEquiv.toCommRingCatIso
    eB1.toRingEquiv.toCommRingCatIso
    eB2.toRingEquiv.toCommRingCatIso
    (Iso.refl (CommRingCat.of T))
  · change CommRingCat.ofHom ((g1.comp eA.toAlgHom).toRingHom) =
      CommRingCat.ofHom ((eB1.toAlgHom.comp kf1).toRingHom)
    exact congrArg (fun q => CommRingCat.ofHom q.toRingHom) h1.symm
  · change CommRingCat.ofHom ((g2.comp eA.toAlgHom).toRingHom) =
      CommRingCat.ofHom ((eB2.toAlgHom.comp kf2).toRingHom)
    exact congrArg (fun q => CommRingCat.ofHom q.toRingHom) h2.symm
  · rfl
  · rfl

/-- The named scalar-extended pushout is canonically equivalent to the exact target. -/
noncomputable def finiteStageTensorPushoutMiddleComparison :
    let kf1 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f1
    let kf2 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f2
    Pic0FiniteStageTensorPushoutRing kf1 kf2 ≃ₐ[K] T := by
  dsimp only
  let kf1 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f1
  let kf2 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f2
  exact finiteStageTensorPushoutAlgEquivOfIsPushout
    kf1 kf2 (j1.comp eB1.toAlgHom) (j2.comp eB2.toAlgHom)
    (finiteStageTensorPushoutComparisonSquare
      f1 f2 eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush)

/-- Scalar extension of the original named pushout, followed by the transported
universal comparison, is an equivalence with the exact target. -/
noncomputable def finiteStageTensorPushoutComparison :
    (K ⊗[R] Pic0FiniteStageTensorPushoutRing f1 f2) ≃ₐ[K] T :=
  (finiteStageTensorPushoutScalarExtension_named (K := K) f1 f2).trans
    (finiteStageTensorPushoutMiddleComparison
      f1 f2 eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush)

/-- The comparison carries the scalar extension of the left face to the transported
exact left target leg. -/
theorem finiteStageTensorPushoutComparison_faceLeft :
    (finiteStageTensorPushoutComparison
        f1 f2 eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush).toAlgHom.comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := R) (K := K) (finiteStageTensorPushoutFaceLeft f1 f2)) =
      j1.comp eB1.toAlgHom := by
  let kf1 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f1
  let kf2 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f2
  let q1 := j1.comp eB1.toAlgHom
  let q2 := j2.comp eB2.toAlgHom
  let square := finiteStageTensorPushoutComparisonSquare
    f1 f2 eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush
  let middle := finiteStageTensorPushoutAlgEquivOfIsPushout
    kf1 kf2 q1 q2 square
  let beta := finiteStageTensorPushoutScalarExtension_named
    (K := K) f1 f2
  let scalarFace := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) (finiteStageTensorPushoutFaceLeft f1 f2)
  apply DFunLike.ext _ _
  intro x
  change middle (beta (scalarFace x)) = q1 x
  have hbeta : beta (scalarFace x) =
      finiteStageTensorPushoutFaceLeft kf1 kf2 x :=
    DFunLike.congr_fun
      (finiteStageTensorPushoutScalarExtension_faceLeft_map
        (K := K) f1 f2) x
  rw [hbeta]
  exact finiteStageTensorPushoutAlgEquivOfIsPushout_faceLeft
    kf1 kf2 q1 q2 square x

/-- The comparison carries the scalar extension of the right face to the transported
exact right target leg. -/
theorem finiteStageTensorPushoutComparison_faceRight :
    (finiteStageTensorPushoutComparison
        f1 f2 eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush).toAlgHom.comp
      (AlgebraicJacobian.scalarExtensionMapOfAlgHom
        (R := R) (K := K) (finiteStageTensorPushoutFaceRight f1 f2)) =
      j2.comp eB2.toAlgHom := by
  let kf1 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f1
  let kf2 := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) f2
  let q1 := j1.comp eB1.toAlgHom
  let q2 := j2.comp eB2.toAlgHom
  let square := finiteStageTensorPushoutComparisonSquare
    f1 f2 eA eB1 eB2 g1 g2 j1 j2 h1 h2 hPush
  let middle := finiteStageTensorPushoutAlgEquivOfIsPushout
    kf1 kf2 q1 q2 square
  let beta := finiteStageTensorPushoutScalarExtension_named
    (K := K) f1 f2
  let scalarFace := AlgebraicJacobian.scalarExtensionMapOfAlgHom
    (R := R) (K := K) (finiteStageTensorPushoutFaceRight f1 f2)
  apply DFunLike.ext _ _
  intro x
  change middle (beta (scalarFace x)) = q2 x
  have hbeta : beta (scalarFace x) =
      finiteStageTensorPushoutFaceRight kf1 kf2 x :=
    DFunLike.congr_fun
      (finiteStageTensorPushoutScalarExtension_faceRight_map
        (K := K) f1 f2) x
  rw [hbeta]
  exact finiteStageTensorPushoutAlgEquivOfIsPushout_faceRight
    kf1 kf2 q1 q2 square x

end Comparison

end

end AlgebraicGeometry
