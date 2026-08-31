/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFibrePoint
import AlgebraicJacobian.Picard.DivSchemeSeedUnivRead

/-!
# Reading compatibility at a residue-field point

The chart comparison map is defined by the scheme `appLE`.  This file records its
stalk form, and then combines it with the universal-window comparison.  The latter
is the pointwise bridge used by the single-point RD-N argument: a total-space reading
transported to `κ(p)` and germed at the canonical lift of `z` is the germ of the
`windowCompare` fibre reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace MonoidalCategory CartesianMonoidalCategory
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (R' : Type u) [CommRing R'] [Algebra k R'] [Algebra R R']
  [IsScalarTower k R R']
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-! ## Stalk form of the chart comparison -/

/-- The germ of a section after the relative-curve comparison is the image of the
germ at the image point under the induced stalk map. -/
theorem relPinnedSectionsMap_germ_eq_stalkMap
    (b : Bool) {s : Γ(relCurve C R, relPinnedChart C R π b)}
    {z : relCurve C R'} (hz : z ∈ relPinnedChart C R' π b) :
    ((relCurve C R').presheaf.germ (relPinnedChart C R' π b) z hz).hom
        (relPinnedSectionsMap C R R' π b s)
      = ((relCurveMap C R R').stalkMap z).hom
          (((relCurve C R).presheaf.germ (relPinnedChart C R π b)
            ((relCurveMap C R R').base z)
            (by
              change z ∈ relCurveMap C R R' ⁻¹ᵁ relPinnedChart C R π b
              rw [relCurveMap_preimage_relPinnedChart C R (π := π) b R']
              exact hz)).hom s) := by
  cases b with
  | false =>
      let f := relCurveMap C R R'
      let U := relPinnedChart C R π false
      let W := relPinnedChart C R' π false
      let e : W ≤ f ⁻¹ᵁ U :=
        le_of_eq (relCurveMap_preimage_relPinnedChart C R (π := π) false R').symm
      have happ : relPinnedSectionsMap C R R' π false s =
          (f.appLE U W e).hom s := by
        rfl
      rw [happ]
      rw [show (f.appLE U W e).hom s =
          ((relCurve C R').presheaf.map (homOfLE e).op).hom
            ((f.app U).hom s) by rfl]
      rw [TopCat.Presheaf.germ_res_apply]
      exact (f.germ_stalkMap_apply U z (e hz) s).symm
  | true =>
      let f := relCurveMap C R R'
      let U := relPinnedChart C R π true
      let W := relPinnedChart C R' π true
      let e : W ≤ f ⁻¹ᵁ U :=
        le_of_eq (relCurveMap_preimage_relPinnedChart C R (π := π) true R').symm
      have happ : relPinnedSectionsMap C R R' π true s =
          (f.appLE U W e).hom s := by
        rfl
      rw [happ]
      rw [show (f.appLE U W e).hom s =
          ((relCurve C R').presheaf.map (homOfLE e).op).hom
            ((f.app U).hom s) by rfl]
      rw [TopCat.Presheaf.germ_res_apply]
      exact (f.germ_stalkMap_apply U z (e hz) s).symm

/-- Membership in the point prime is preserved and reflected by the pinned-chart
base-change map.  This is the affine-ring form of locality of the induced stalk map. -/
theorem relPinnedSectionsMap_mem_primeIdealOf_iff
    (b : Bool) {z : relCurve C R'} (hz : z ∈ relPinnedChart C R' π b)
    (s : Γ(relCurve C R, relPinnedChart C R π b)) :
    relPinnedSectionsMap C R R' π b s ∈
        ((isAffineOpen_relPinnedChart C R' π b).primeIdealOf ⟨z, hz⟩).asIdeal ↔
      s ∈ ((isAffineOpen_relPinnedChart C R π b).primeIdealOf
        ⟨(relCurveMap C R R').base z, by
          change z ∈ relCurveMap C R R' ⁻¹ᵁ relPinnedChart C R π b
          rw [relCurveMap_preimage_relPinnedChart C R (π := π) b R']
          exact hz⟩).asIdeal := by
  let hzbase : (relCurveMap C R R').base z ∈ relPinnedChart C R π b := by
    change z ∈ relCurveMap C R R' ⁻¹ᵁ relPinnedChart C R π b
    rw [relCurveMap_preimage_relPinnedChart C R (π := π) b R']
    exact hz
  have hcomp := relPinnedSectionsMap_germ_eq_stalkMap C R R' (π := π) b hz (s := s)
  rw [(isAffineOpen_relPinnedChart C R' π b).primeIdealOf_eq_map_closedPoint,
    (isAffineOpen_relPinnedChart C R π b).primeIdealOf_eq_map_closedPoint]
  change ((relCurve C R').presheaf.germ (relPinnedChart C R' π b) z hz).hom
      (relPinnedSectionsMap C R R' π b s) ∈
        IsLocalRing.maximalIdeal ((relCurve C R').presheaf.stalk z) ↔
    ((relCurve C R).presheaf.germ (relPinnedChart C R π b)
      ((relCurveMap C R R').base z) hzbase).hom s ∈
        IsLocalRing.maximalIdeal
          ((relCurve C R).presheaf.stalk ((relCurveMap C R R').base z))
  rw [hcomp, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]

/-! ## The residue-point/window comparison -/

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option linter.unusedSectionVars false in
/-- At the canonical residue-field lift of a point `z`, the germ of the transported
total universal-window reading is the germ of the fibre reading obtained by
`windowCompare`. -/
theorem germ_relPinnedSectionsMap_relThetaResSide_windowEquiv_at_relCurveResiduePoint
    (b : Bool) {z : relCurve C R}
    (hz : z ∈ relPinnedChart C R π b)
    (x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    let K := (relCurveBasePoint C R z).asIdeal.ResidueField
    let zK := relCurveResiduePoint C R z
    ((relCurve C K).presheaf.germ (relPinnedChart C K π b) zK
      (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom
      (relPinnedSectionsMap C R K π b
        (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x)))
      = ((relCurve C K).presheaf.germ (relPinnedChart C K π b) zK
          (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom
        (relThetaResSide a b le_rfl
          (relThetaWindowEquiv C K π a hH1 (windowCompare R K x))) := by
  dsimp
  exact congrArg
    (((relCurve C (relCurveBasePoint C R z).asIdeal.ResidueField).presheaf.germ
      (relPinnedChart C (relCurveBasePoint C R z).asIdeal.ResidueField π b)
      (relCurveResiduePoint C R z)
      (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom)
    (relPinnedSectionsMap_relThetaResSide_windowEquiv C R
      (relCurveBasePoint C R z).asIdeal.ResidueField π a hH1 b x)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option linter.unusedSectionVars false in
/-- Stalk-map form of the residue-point reading comparison: the image of the total
reading germ is exactly the germ of the `windowCompare` fibre reading. -/
theorem stalkMap_germ_relThetaResSide_windowEquiv_at_relCurveResiduePoint
    (b : Bool) {z : relCurve C R}
    (hz : z ∈ relPinnedChart C R π b)
    (x : R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) :
    let K := (relCurveBasePoint C R z).asIdeal.ResidueField
    let zK := relCurveResiduePoint C R z
    ((relCurveMap C R K).stalkMap zK).hom
        (((relCurve C R).presheaf.germ (relPinnedChart C R π b)
          ((relCurveMap C R K).base zK)
          (by
            change zK ∈ relCurveMap C R K ⁻¹ᵁ relPinnedChart C R π b
            rw [relCurveMap_preimage_relPinnedChart C R (π := π) b K]
            exact relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom
          (relThetaResSide a b le_rfl (relThetaWindowEquiv C R π a hH1 x)))
      = ((relCurve C K).presheaf.germ (relPinnedChart C K π b) zK
          (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)).hom
        (relThetaResSide a b le_rfl
          (relThetaWindowEquiv C K π a hH1 (windowCompare R K x))) := by
  dsimp
  rw [← relPinnedSectionsMap_germ_eq_stalkMap C R
    (relCurveBasePoint C R z).asIdeal.ResidueField (π := π) b
    (relCurveResiduePoint_mem_relPinnedChart C R (π := π) b hz)]
  exact germ_relPinnedSectionsMap_relThetaResSide_windowEquiv_at_relCurveResiduePoint
    C R (π := π) a hH1 b hz x

end AlgebraicGeometry
