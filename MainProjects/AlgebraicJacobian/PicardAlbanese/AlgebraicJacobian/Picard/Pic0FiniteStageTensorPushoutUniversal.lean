/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.TensorProductFieldTowerMap
import AlgebraicJacobian.Picard.Pic0FiniteStageTripleModelScalarExtension

/-!
# Universal property of named finite-stage tensor pushouts

This file exposes the categorical universal property of
`Pic0FiniteStageTensorPushoutRing` without requiring consumers to unfold that named ring.
It also gives the canonical comparison with any other pushout and records its two face
formulas.  The final declaration presents scalar extension entirely through the named
finite-stage interface.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace TensorProduct
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

set_option maxHeartbeats 800000 in
-- Unfolding the map-selected algebra instances can make synthesis expensive.
/-- The named finite-stage tensor-pushout ring, together with its named faces, is a
pushout in commutative rings. -/
theorem finiteStageTensorPushout_isPushout
    {R A B₁ B₂ : Type u}
    [CommRing R] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    IsPushout
      (CommRingCat.ofHom f₁.toRingHom)
      (CommRingCat.ofHom f₂.toRingHom)
      (CommRingCat.ofHom
        (finiteStageTensorPushoutFaceLeft f₁ f₂).toRingHom)
      (CommRingCat.ofHom
        (finiteStageTensorPushoutFaceRight f₁ f₂).toRingHom) := by
  letI : Algebra A B₁ := pic0FiniteStageAlgebraOfMap f₁
  letI : Algebra A B₂ := pic0FiniteStageAlgebraOfMap f₂
  change IsPushout
    (CommRingCat.ofHom (algebraMap A B₁))
    (CommRingCat.ofHom (algebraMap A B₂))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom
        (R := A) (A := B₁) (B := B₂)))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight
        (R := A) (A := B₁) (B := B₂)).toRingHom)
  exact CommRingCat.isPushout_tensorProduct A B₁ B₂

set_option maxHeartbeats 1600000 in
-- The categorical comparison elaborates through the dependent named pushout type.
/-- The canonical algebra equivalence from the named finite-stage tensor pushout to any
other pushout of the same two algebra maps. -/
noncomputable def finiteStageTensorPushoutAlgEquivOfIsPushout
    {R A B₁ B₂ T : Type u}
    [CommRing R] [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing T]
    [Algebra R A] [Algebra R B₁] [Algebra R B₂] [Algebra R T]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂)
    (g₁ : B₁ →ₐ[R] T) (g₂ : B₂ →ₐ[R] T)
    (h : IsPushout
      (CommRingCat.ofHom f₁.toRingHom)
      (CommRingCat.ofHom f₂.toRingHom)
      (CommRingCat.ofHom g₁.toRingHom)
      (CommRingCat.ofHom g₂.toRingHom)) :
    Pic0FiniteStageTensorPushoutRing f₁ f₂ ≃ₐ[R] T := by
  let hs := finiteStageTensorPushout_isPushout f₁ f₂
  let ie : CommRingCat.of (Pic0FiniteStageTensorPushoutRing f₁ f₂) ≅
      CommRingCat.of T :=
    hs.isoIsPushout (CommRingCat.of B₁) (CommRingCat.of B₂) h
  let re := ie.commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := re) fun x => ?_
  have hleft := hs.inl_isoIsPushout_hom
    (CommRingCat.of B₁) (CommRingCat.of B₂) h
  have hx := congrArg
    (fun q : CommRingCat.of B₁ ⟶ CommRingCat.of T =>
      q.hom ((algebraMap R B₁) x)) hleft
  change ie.hom.hom
      (finiteStageTensorPushoutFaceLeft f₁ f₂ ((algebraMap R B₁) x)) =
    g₁ ((algebraMap R B₁) x) at hx
  change ie.hom.hom
      (finiteStageTensorPushoutFaceLeft f₁ f₂ ((algebraMap R B₁) x)) =
    algebraMap R T x
  exact hx.trans (g₁.commutes x)

set_option maxHeartbeats 800000 in
-- Reducing the categorical comparison to its left face needs the same named instances.
/-- The canonical equivalence to another pushout carries the named left face to the
given left face. -/
theorem finiteStageTensorPushoutAlgEquivOfIsPushout_faceLeft
    {R A B₁ B₂ T : Type u}
    [CommRing R] [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing T]
    [Algebra R A] [Algebra R B₁] [Algebra R B₂] [Algebra R T]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂)
    (g₁ : B₁ →ₐ[R] T) (g₂ : B₂ →ₐ[R] T)
    (h : IsPushout
      (CommRingCat.ofHom f₁.toRingHom)
      (CommRingCat.ofHom f₂.toRingHom)
      (CommRingCat.ofHom g₁.toRingHom)
      (CommRingCat.ofHom g₂.toRingHom))
    (b₁ : B₁) :
    finiteStageTensorPushoutAlgEquivOfIsPushout f₁ f₂ g₁ g₂ h
        (finiteStageTensorPushoutFaceLeft f₁ f₂ b₁) =
      g₁ b₁ := by
  let hs := finiteStageTensorPushout_isPushout f₁ f₂
  let ie : CommRingCat.of (Pic0FiniteStageTensorPushoutRing f₁ f₂) ≅
      CommRingCat.of T :=
    hs.isoIsPushout (CommRingCat.of B₁) (CommRingCat.of B₂) h
  change ie.hom.hom (finiteStageTensorPushoutFaceLeft f₁ f₂ b₁) = g₁ b₁
  have hleft := hs.inl_isoIsPushout_hom
    (CommRingCat.of B₁) (CommRingCat.of B₂) h
  have hx := congrArg
    (fun q : CommRingCat.of B₁ ⟶ CommRingCat.of T => q.hom b₁) hleft
  exact hx

set_option maxHeartbeats 800000 in
-- Reducing the categorical comparison to its right face needs the same named instances.
/-- The canonical equivalence to another pushout carries the named right face to the
given right face. -/
theorem finiteStageTensorPushoutAlgEquivOfIsPushout_faceRight
    {R A B₁ B₂ T : Type u}
    [CommRing R] [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing T]
    [Algebra R A] [Algebra R B₁] [Algebra R B₂] [Algebra R T]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂)
    (g₁ : B₁ →ₐ[R] T) (g₂ : B₂ →ₐ[R] T)
    (h : IsPushout
      (CommRingCat.ofHom f₁.toRingHom)
      (CommRingCat.ofHom f₂.toRingHom)
      (CommRingCat.ofHom g₁.toRingHom)
      (CommRingCat.ofHom g₂.toRingHom))
    (b₂ : B₂) :
    finiteStageTensorPushoutAlgEquivOfIsPushout f₁ f₂ g₁ g₂ h
        (finiteStageTensorPushoutFaceRight f₁ f₂ b₂) =
      g₂ b₂ := by
  let hs := finiteStageTensorPushout_isPushout f₁ f₂
  let ie : CommRingCat.of (Pic0FiniteStageTensorPushoutRing f₁ f₂) ≅
      CommRingCat.of T :=
    hs.isoIsPushout (CommRingCat.of B₁) (CommRingCat.of B₂) h
  change ie.hom.hom (finiteStageTensorPushoutFaceRight f₁ f₂ b₂) = g₂ b₂
  have hright := hs.inr_isoIsPushout_hom
    (CommRingCat.of B₁) (CommRingCat.of B₂) h
  have hx := congrArg
    (fun q : CommRingCat.of B₂ ⟶ CommRingCat.of T => q.hom b₂) hright
  exact hx

set_option maxHeartbeats 1600000 in
-- Both scalar-extended map-selected algebra structures elaborate in this signature.
/-- Scalar extension of a named finite-stage tensor pushout, expressed with the named
source and target rings and the scalar extensions of the original algebra maps. -/
noncomputable def finiteStageTensorPushoutScalarExtension_named
    {R K A B₁ B₂ : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂]
    [Algebra R K] [Algebra R A] [Algebra R B₁] [Algebra R B₂]
    (f₁ : A →ₐ[R] B₁) (f₂ : A →ₐ[R] B₂) :
    let kf₁ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f₁
    let kf₂ := AlgebraicJacobian.scalarExtensionMapOfAlgHom
      (R := R) (K := K) f₂
    (K ⊗[R] Pic0FiniteStageTensorPushoutRing f₁ f₂) ≃ₐ[K]
      Pic0FiniteStageTensorPushoutRing kf₁ kf₂ :=
  finiteStageTensorPushoutScalarExtension (K := K) f₁ f₂

end

end AlgebraicGeometry
