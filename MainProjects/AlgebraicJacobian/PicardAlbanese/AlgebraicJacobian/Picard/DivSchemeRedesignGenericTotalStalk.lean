/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeRedesignGenericFibre
import AlgebraicJacobian.Picard.DivSchemeFibrePointRead

/-!
# Reflecting the generic-fibre unit to the total stalk

At a point whose residue-field lift is the generic point of its fibre, the generic-fibre
module gives a unit germ.  `DivSchemeFibrePointRead` identifies the corresponding fibre germ
with the image of the total germ under the scheme stalk map.  Since scheme stalk maps are
local, `isUnit_map_iff` reflects that unit back to the total stalk.

This is deliberately a unit statement for one section.  It does not infer flatness, ideal
purity, or generation of the total chart ideal; those remain the separate closed-branch
problem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

/-! ## Small point-transport helpers -/

/-- Unitness of a fixed chart germ is invariant under replacing its point by an equal point.
The explicit lemma avoids dependent-rewrite failures caused by the membership proof in the
germ argument. -/
theorem isUnit_germ_at_eq_of_isUnit {X : Scheme.{u}} {U : X.Opens}
    {y z : X} (hy : y ∈ U) (hz : z ∈ U) (h : y = z) {s : Γ(X, U)}
    (hu : IsUnit ((X.presheaf.germ U y hy).hom s)) :
    IsUnit ((X.presheaf.germ U z hz).hom s) := by
  subst z
  exact hu

section StalkReflection

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftGenericTotal : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

/-- A fibre point in a pinned chart maps to a point in the corresponding total pinned chart.
This is the membership leg needed to state the total germ at the image point. -/
theorem relCurveMap_mem_relPinnedChart
    (b : Bool) {zK : relCurve C K} (hzK : zK ∈ relPinnedChart C K π b) :
    (relCurveMap C R K).base zK ∈ relPinnedChart C R π b := by
  change zK ∈ (relCurveMap C R K) ⁻¹ᵁ relPinnedChart C R π b
  rw [relCurveMap_preimage_relPinnedChart C R (π := π) b K]
  exact hzK

/-- **Total-stalk unit reflection.** If the fibre germ of the transported section is a unit,
then the total germ at the image point is a unit.  The proof is exactly the stalk comparison
`relPinnedSectionsMap_germ_eq_stalkMap` followed by localness of the stalk map. -/
theorem isUnit_total_germ_of_fibre_germ
    (b : Bool) {zK : relCurve C K}
    (hzK : zK ∈ relPinnedChart C K π b)
    (hzR : (relCurveMap C R K).base zK ∈ relPinnedChart C R π b)
    (s : Γ(relCurve C R, relPinnedChart C R π b))
    (hu : IsUnit (((relCurve C K).presheaf.germ (relPinnedChart C K π b) zK hzK).hom
      (relPinnedSectionsMap C R K π b s))) :
    IsUnit (((relCurve C R).presheaf.germ (relPinnedChart C R π b)
      ((relCurveMap C R K).base zK) hzR).hom s) := by
  rw [relPinnedSectionsMap_germ_eq_stalkMap C R K (π := π) b hzK] at hu
  exact (isUnit_map_iff ((relCurveMap C R K).stalkMap zK).hom _).mp hu

end StalkReflection

/-! ## The generic-window specialization -/

section GenericWindow

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable (R : Type u) [CommRing R] [Algebra k R]
variable (K : Type u) [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftGenericWindow : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

-- These base-change instances are needed when the generic theorem is instantiated at a
-- residue field.  They are local so this file does not alter global instance search.
noncomputable local instance instIsIntegralRelCurveGenericWindow (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
noncomputable local instance instSmoothRelCurveGenericWindow (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L
noncomputable local instance instQCRelCurveGenericWindow (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1200000 in
-- The generic fibre unit and stalk comparison cross the mixed total/fibre curve spellings.
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- A nonzero compared vector gives a unit **total** germ at the image of the fibre generic
point.  `hηR` is the corresponding total-chart membership proof. -/
theorem isUnit_total_germ_image_genericPoint_of_windowCompare_ne_zero
    (b : Bool)
    (hη : genericPoint (relCurve C K) ∈ relPinnedChart C K π b)
    (hηR : (relCurveMap C R K).base (genericPoint (relCurve C K)) ∈
      relPinnedChart C R π b)
    {x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)}
    (hx : windowCompare R K x ≠ 0) :
    IsUnit (((relCurve C R).presheaf.germ (relPinnedChart C R π b)
      ((relCurveMap C R K).base (genericPoint (relCurve C K))) hηR).hom
      (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x))) := by
  exact isUnit_total_germ_of_fibre_germ C R K π b hη hηR _
    (isUnit_germ_genericPoint_of_windowCompare_ne_zero C R K π a hH1 b hη hx)

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- Point-equality form of the generic-fibre unit lift.  This is convenient for a total point
`z` once a proof `hmap : (relCurveMap C R K).base η = z` is available; the helper
`isUnit_germ_at_eq_of_isUnit` handles the dependent germ membership proof. -/
theorem isUnit_total_germ_of_fibre_genericPoint_eq
    (b : Bool)
    (hη : genericPoint (relCurve C K) ∈ relPinnedChart C K π b)
    {z : relCurve C R} (hz : z ∈ relPinnedChart C R π b)
    (hmap : (relCurveMap C R K).base (genericPoint (relCurve C K)) = z)
    {x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)}
    (hx : windowCompare R K x ≠ 0) :
    IsUnit (((relCurve C R).presheaf.germ (relPinnedChart C R π b) z hz).hom
      (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x))) := by
  have hηR := relCurveMap_mem_relPinnedChart C R K π b hη
  exact isUnit_germ_at_eq_of_isUnit hηR hz hmap
    (isUnit_total_germ_image_genericPoint_of_windowCompare_ne_zero
      C R K π a hH1 b hη hηR hx)

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 600000 in
set_option maxRecDepth 8000 in
/-- Residue-point specialization: if `relCurveResiduePoint C R z` is the fibre generic point,
the corresponding total germ at `z` is a unit.  This is the generic branch of the pointwise
seed, and still makes no ideal-purity assertion. -/
theorem isUnit_total_germ_of_residuePoint_generic
    (z : relCurve C R) (b : Bool) (hz : z ∈ relPinnedChart C R π b)
    {x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)}
    (hx : windowCompare R (relCurveBasePoint C R z).asIdeal.ResidueField x ≠ 0)
    (hzg : relCurveResiduePoint C R z =
      genericPoint (relCurve C (relCurveBasePoint C R z).asIdeal.ResidueField)) :
    IsUnit (((relCurve C R).presheaf.germ (relPinnedChart C R π b) z hz).hom
      (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x))) := by
  let K := (relCurveBasePoint C R z).asIdeal.ResidueField
  have hzK : relCurveResiduePoint C R z ∈ relPinnedChart C K π b :=
    relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz
  have hη : genericPoint (relCurve C K) ∈ relPinnedChart C K π b := by
    rw [← hzg]
    exact hzK
  have hmap : (relCurveMap C R K).base (genericPoint (relCurve C K)) = z := by
    rw [← hzg]
    exact relCurveMap_relCurveResiduePoint C R z
  exact isUnit_total_germ_of_fibre_genericPoint_eq C R K π a hH1 b hη hz hmap hx

end GenericWindow

end AlgebraicGeometry
