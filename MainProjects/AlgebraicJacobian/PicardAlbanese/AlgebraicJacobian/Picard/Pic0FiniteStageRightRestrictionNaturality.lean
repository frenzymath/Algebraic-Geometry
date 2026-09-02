/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionNaturality
import AlgebraicJacobian.Picard.Pic0FiniteStageRightRestrictionAlgHom

/-!
# Naturality of the right finite-stage Picard restriction

The scalar-extended right restriction descends to the exact right restriction
under the final chart and overlap comparisons.  Applying the affine base-change
comparison gives the corresponding scheme-level naturality square.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

/-- The exact right restriction with its indexed source and target rings. -/
noncomputable def exactRightRestrictionAlgHom
    (U V : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageRing C (Sum.inl V) →ₐ[k]
      Pic0FiniteStageRing C (Sum.inr (U, V)) :=
  pic0FiniteStageMap C (Sum.inl (Sum.inr (U, V)))

/-- The spectrum of the exact right restriction, followed by the right chart's
affine identification, is the affine-overlap identification. -/
theorem exactRightRestrictionAlgHom_fromSpec
    (U V : Pic0FiniteStageChartIndex C) :
    Spec.map (CommRingCat.ofHom
        (exactRightRestrictionAlgHom C U V).toRingHom) ≫
        V.1.2.fromSpec =
      (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  change Spec.map (CommRingCat.ofHom
      (pic0FiniteStageRestrictionRight C U V).toRingHom) ≫
      V.1.2.fromSpec = _
  change Spec.map
      ((pic0_sepClosed_representableBy (C := C)).1.left.presheaf.map
        (homOfLE (pic0FiniteStageAffineOverlap_le_right C U V)).op) ≫
      V.1.2.fromSpec = _
  exact V.1.2.map_fromSpec (pic0FiniteStageAffineOverlap C U V).2
    (homOfLE (pic0FiniteStageAffineOverlap_le_right C U V)).op

/-!
The final comparison maps and the scalar extension map below are written with
the carrier and structure witnesses selected by the pinned final-stage API.
Keeping these witnesses in the declarations prevents importing modules from
reconstructing dependent tensor-product instances while elaborating a theorem
statement.
-/
/-- Pinned forward map from the scalar-extended right chart to the exact chart ring. -/
noncomputable def rightChartFinalBaseChangeHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (V : Pic0FiniteStageChartIndex C) :
    @AlgHom k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageRing C (Sum.inl V))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (instCommRingPic0FiniteStageRing C (Sum.inl V)).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (instAlgebraPic0FiniteStageRing C (Sum.inl V)) :=
  pic0FiniteStageFinalBaseChangeForwardPinned
    C P.L P.n P.m P.relation P.e P.M P.N (Sum.inl V)

/-- Pinned forward map from the scalar-extended overlap to the exact overlap ring. -/
noncomputable def rightOverlapFinalBaseChangeHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (Pic0FiniteStageRing C (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instCommRingPic0FiniteStageRing C (Sum.inr (U, V))).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instAlgebraPic0FiniteStageRing C (Sum.inr (U, V))) :=
  pic0FiniteStageFinalBaseChangeForwardPinned
    C P.L P.n P.m P.relation P.e P.M P.N (Sum.inr (U, V))

/-- The direct scalar extension of the exact right restriction, with all tensor
structure witnesses fixed by the final-stage API. -/
noncomputable def rightScalarExtensionHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
  pic0FiniteStageFinalScalarExtensionMapPinned
    C P.L P.n P.m P.relation P.M P.mapM P.N
      (Sum.inl (Sum.inr (U, V)))

/-- The scalar extension obtained from the package right restriction map.  This
is the compatibility-side name used by the affine square theorem. -/
noncomputable def rightRestrictionScalarExtensionHom
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V))) :=
  @AlgebraicJacobian.scalarExtensionMapOfAlgHom
    P.N.1 k
    (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)
    (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
    (inferInstance : CommRing P.N.1)
    (inferInstance : CommRing k)
    (pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N V).toSemiring
    (pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V).toSemiring
    (inferInstance : Algebra P.N.1 k)
    (pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N V)
    (pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V)
    (rightRestrictionBaseChangeAlgHomPinned C P U V)

/-- The package scalar-extension map agrees with the direct pinned map. -/
theorem rightRestrictionScalarExtensionHom_eq_direct
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    rightRestrictionScalarExtensionHom C P U V =
      rightScalarExtensionHom C P U V := by
  rw [rightRestrictionScalarExtensionHom, rightScalarExtensionHom,
    rightRestrictionBaseChangeAlgHomPinned,
    rightRestrictionBaseChangeAlgHom_eq_direct C P U V]
  rfl

set_option synthInstance.maxHeartbeats 3200000 in
-- Pointwise comparison uses the pinned carrier and structure witnesses.
set_option maxHeartbeats 12800000 in
/-- Naturality on the fully pinned carrier: the final chart and overlap
comparisons identify the direct scalar-extended right restriction with the exact
right restriction before it is adapted to the affine API. -/
theorem rightRestrictionFinalBaseChangeEquivPinned_naturality
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom.comp k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (Pic0FiniteStageRing C (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instCommRingPic0FiniteStageRing C (Sum.inr (U, V))).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instAlgebraPic0FiniteStageRing C (Sum.inr (U, V)))
      (rightOverlapFinalBaseChangeHom C P U V)
      (rightScalarExtensionHom C P U V) =
    @AlgHom.comp k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageRing C (Sum.inl V))
      (Pic0FiniteStageRing C (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (instCommRingPic0FiniteStageRing C (Sum.inl V)).toSemiring
      (instCommRingPic0FiniteStageRing C (Sum.inr (U, V))).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (instAlgebraPic0FiniteStageRing C (Sum.inl V))
      (instAlgebraPic0FiniteStageRing C (Sum.inr (U, V)))
      (exactRightRestrictionAlgHom C U V)
      (rightChartFinalBaseChangeHom C P V) := by
  apply DFunLike.ext _ _
  intro x
  change
    (pic0FiniteStageFinalBaseChangeForwardPinned
        C P.L P.n P.m P.relation P.e P.M P.N (Sum.inr (U, V)))
        (pic0FiniteStageFinalScalarExtensionMapPinned
          C P.L P.n P.m P.relation P.M P.mapM P.N
            (Sum.inl (Sum.inr (U, V))) x) =
      (exactRightRestrictionAlgHom C U V)
        (pic0FiniteStageFinalBaseChangeForwardPinned
          C P.L P.n P.m P.relation P.e P.M P.N (Sum.inl V) x)
  exact pic0FiniteStageFinalBaseChangeEquivPinned_naturality
    C P.L P.n P.m P.relation P.e P.M P.mapM P.hmapM P.N
      (Sum.inl (Sum.inr (U, V))) x

set_option synthInstance.maxHeartbeats 3200000 in
-- The explicit scalar-extension wrapper preserves the legacy theorem boundary.
set_option maxHeartbeats 12800000 in
/-- Compatibility form consumed by the affine scheme-square theorem. -/
theorem rightRestrictionFinalBaseChangeEquiv_naturality
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    @AlgHom.comp k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (Pic0FiniteStageRing C (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instCommRingPic0FiniteStageRing C (Sum.inr (U, V))).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inr (U, V)))
      (instAlgebraPic0FiniteStageRing C (Sum.inr (U, V)))
      (rightOverlapFinalBaseChangeHom C P U V)
      (rightRestrictionScalarExtensionHom C P U V) =
    @AlgHom.comp k
      (Pic0FiniteStageFinalScalarExtensionCarrier C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (Pic0FiniteStageRing C (Sum.inl V))
      (Pic0FiniteStageRing C (Sum.inr (U, V)))
      (inferInstance : CommSemiring k)
      (pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (instCommRingPic0FiniteStageRing C (Sum.inl V)).toSemiring
      (instCommRingPic0FiniteStageRing C (Sum.inr (U, V))).toSemiring
      (pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
        (Sum.inl V))
      (instAlgebraPic0FiniteStageRing C (Sum.inl V))
      (instAlgebraPic0FiniteStageRing C (Sum.inr (U, V)))
      (exactRightRestrictionAlgHom C U V)
      (rightChartFinalBaseChangeHom C P V) := by
  rw [rightRestrictionScalarExtensionHom_eq_direct C P U V]
  exact rightRestrictionFinalBaseChangeEquivPinned_naturality C P U V

set_option synthInstance.maxHeartbeats 3200000 in
-- The explicit pullback type fixes the package's dependent chart and overlap rings.
set_option maxHeartbeats 12800000 in
/-- Pullback of the scalar-extended right restriction from the forward overlap
to the right chart. -/
noncomputable def rightRestrictionBaseChangeMap
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    pullback (overlapBaseChangeMap C P U V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) ⟶
      pullback (chartBaseChangeMap C P V)
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k))) :=
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N V
  letI : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N V
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V
  letI : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing
        C P.L P.n P.m P.relation P.M P.N U V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V
  affineBaseChangeMap P.N.1 k
    (Pic0FiniteStageChartBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N V)
    (Pic0FiniteStageOverlapBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U V)
    (rightRestrictionBaseChangeAlgHomPinned C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Specializing the generic affine square unfolds both final ring comparisons.
set_option maxHeartbeats 12800000 in
/-- Under the final chart and overlap comparisons, the pulled-back right
restriction is the exact right restriction of the separably closed atlas. -/
theorem rightRestrictionBaseChangeMap_naturality
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    rightRestrictionBaseChangeMap C P U V ≫
        (chartRingBaseChangeIso C P V).hom =
      (overlapRingBaseChangeIso C P U V).hom ≫
        Spec.map (CommRingCat.ofHom
          (exactRightRestrictionAlgHom C U V).toRingHom) := by
  letI : Algebra.IsAlgebraic P.L.1 k := by infer_instance
  letI : Algebra.IsAlgebraic P.M.1 k := by infer_instance
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N V
  letI : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N V
  letI : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U V
  letI : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommRing
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageOverlapBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U V
  letI : CommRing
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    @Algebra.TensorProduct.instCommRing P.N.1 k
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)
      (inferInstance : CommSemiring P.N.1) (inferInstance : CommRing k)
      (inferInstance : Algebra P.N.1 k)
      (inferInstance : CommSemiring
        (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V))
      (inferInstance : Algebra P.N.1
        (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V))
  letI : CommSemiring
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    (inferInstance : CommRing
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V)).toCommSemiring
  letI : Semiring
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
      (Sum.inl V)
  letI : Algebra k
      (k ⊗[P.N.1]
        Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N V) :=
    pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inl V)
  letI : CommRing
      (k ⊗[P.N.1]
        Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    @Algebra.TensorProduct.instCommRing P.N.1 k
      (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)
      (inferInstance : CommSemiring P.N.1) (inferInstance : CommRing k)
      (inferInstance : Algebra P.N.1 k)
      (inferInstance : CommSemiring
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V))
      (inferInstance : Algebra P.N.1
        (Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V))
  letI : CommSemiring
      (k ⊗[P.N.1]
        Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    (inferInstance : CommRing
      (k ⊗[P.N.1]
        Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V)).toCommSemiring
  letI : Semiring
      (k ⊗[P.N.1]
        Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageFinalScalarExtensionSemiring C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))
  letI : Algebra k
      (k ⊗[P.N.1]
        Pic0FiniteStageOverlapBaseChangeRing C P.L P.n P.m P.relation P.M P.N U V) :=
    pic0FiniteStageFinalScalarExtensionAlgebra C P.L P.n P.m P.relation P.M P.N
      (Sum.inr (U, V))
  exact affineBaseChangeIso_trans_naturality
    P.N.1 k
    (Pic0FiniteStageChartBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N V)
    (Pic0FiniteStageOverlapBaseChangeRing
      C P.L P.n P.m P.relation P.M P.N U V)
    (Pic0FiniteStageRing C (Sum.inl V))
    (Pic0FiniteStageRing C (Sum.inr (U, V)))
    (rightRestrictionBaseChangeAlgHomPinned C P U V)
    (chartFinalBaseChangeEquiv C P V)
    (overlapFinalBaseChangeEquiv C P U V)
    (exactRightRestrictionAlgHom C U V)
    (rightRestrictionFinalBaseChangeEquiv_naturality C P U V)

set_option synthInstance.maxHeartbeats 3200000 in
-- Normalize the stable-index naturality square before entering glued diagrams.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back right restriction carries the right chart's affine
identification to the affine-overlap identification. -/
theorem rightRestrictionBaseChangeMap_fromSpec
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    rightRestrictionBaseChangeMap C P U V ≫
          (chartRingBaseChangeIso C P V).hom ≫ V.1.2.fromSpec =
      (overlapRingBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  rw [← Category.assoc, rightRestrictionBaseChangeMap_naturality C P U V,
    Category.assoc, exactRightRestrictionAlgHom_fromSpec C U V]

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
