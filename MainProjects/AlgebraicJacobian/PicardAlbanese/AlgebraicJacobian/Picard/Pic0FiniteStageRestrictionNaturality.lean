/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineBaseChangeTrans
import AlgebraicJacobian.Picard.Pic0FiniteStageRestrictionBaseChange

/-!
# Naturality of finite-stage Picard restrictions after base change

The affine base-change comparison and the final finite-stage ring comparison
identify the pulled-back left restriction with the exact left restriction in
the separably closed Picard atlas.
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

set_option synthInstance.maxHeartbeats 3200000 in
-- Specialization unfolds the package's dependent finite-subextension towers.
set_option maxHeartbeats 12800000 in
/-- Under the final chart and overlap comparisons, the pulled-back left
restriction is the exact left restriction of the separably closed atlas. -/
theorem restrictionBaseChangeMap_naturality
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    restrictionBaseChangeMap C P U V ≫
        (chartRingBaseChangeIso C P U).hom =
      (overlapRingBaseChangeIso C P U V).hom ≫
        Spec.map (CommRingCat.ofHom
          (exactRestrictionAlgHom C U V).toRingHom) := by
  letI : Algebra.IsAlgebraic P.L.1 k := by infer_instance
  letI : Algebra.IsAlgebraic P.M.1 k := by infer_instance
  /- Pin the chart and overlap carrier witnesses before specializing the generic
     affine-base-change square.  These carriers are reducible tensors, but the
     generic theorem compares their instance arguments definitionally. -/
  letI : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageChartBaseChangeRingCommRing
      C P.L P.n P.m P.relation P.M P.N U
  letI : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    (inferInstance : CommRing
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)).toCommSemiring
  letI : Semiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    (inferInstance : CommSemiring
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U)).toSemiring
  letI : Algebra P.N.1
      (Pic0FiniteStageChartBaseChangeRing C P.L P.n P.m P.relation P.M P.N U) :=
    pic0FiniteStageChartBaseChangeRingAlgebra
      C P.L P.n P.m P.relation P.M P.N U
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
  apply affineBaseChangeIso_trans_naturality
    P.N.1 k
    (P.N.1 ⊗[P.M.1]
      Pic0FiniteStageChartModelRing C P.L P.n P.m P.relation P.M U)
    (P.N.1 ⊗[P.M.1]
      Pic0FiniteStageOverlapModelRing C P.L P.n P.m P.relation P.M U V)
    (Pic0FiniteStageRing C (Sum.inl U))
    (Pic0FiniteStageRing C (Sum.inr (U, V)))
    (restrictionBaseChangeAlgHomPinned C P U V)
    (chartFinalBaseChangeEquiv C P U)
    (overlapFinalBaseChangeEquiv C P U V)
    (exactRestrictionAlgHom C U V)
  apply DFunLike.ext _ _
  intro x
  exact pic0FiniteStageFinalBaseChangeEquivPinned_naturality
    C P.L P.n P.m P.relation P.e P.M P.mapM P.hmapM P.N
      (Sum.inl (Sum.inl (U, V))) x

/-- The spectrum of the exact left restriction, followed by the chart's affine
identification, is the affine-overlap identification. -/
theorem exactRestrictionAlgHom_fromSpec
    (U V : Pic0FiniteStageChartIndex C) :
    Spec.map (CommRingCat.ofHom
        (exactRestrictionAlgHom C U V).toRingHom) ≫
        U.1.2.fromSpec =
      (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  change Spec.map (CommRingCat.ofHom
      (pic0FiniteStageRestrictionLeft C U V).toRingHom) ≫
      U.1.2.fromSpec = _
  change Spec.map
      ((pic0_sepClosed_representableBy (C := C)).1.left.presheaf.map
        (homOfLE (pic0FiniteStageAffineOverlap_le_left C U V)).op) ≫
      U.1.2.fromSpec = _
  exact U.1.2.map_fromSpec (pic0FiniteStageAffineOverlap C U V).2
    (homOfLE (pic0FiniteStageAffineOverlap_le_left C U V)).op

set_option synthInstance.maxHeartbeats 3200000 in
-- Normalize the stable-index naturality square before entering glued diagrams.
set_option maxHeartbeats 12800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back left restriction carries the chart's affine identification
to the affine-overlap identification. -/
theorem restrictionBaseChangeMap_fromSpec
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]
    (P : Pic0FiniteStageGluePackage C F)
    (U V : Pic0FiniteStageChartIndex C) :
    restrictionBaseChangeMap C P U V ≫
          (chartRingBaseChangeIso C P U).hom ≫ U.1.2.fromSpec =
      (overlapRingBaseChangeIso C P U V).hom ≫
        (pic0FiniteStageAffineOverlap C U V).2.fromSpec := by
  rw [← Category.assoc, restrictionBaseChangeMap_naturality C P U V,
    Category.assoc, exactRestrictionAlgHom_fromSpec C U V]

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
