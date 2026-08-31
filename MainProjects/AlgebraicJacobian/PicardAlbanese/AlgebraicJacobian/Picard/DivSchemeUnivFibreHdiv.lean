/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeUnivFibreWindow
import AlgebraicJacobian.Picard.DivisorFamilyFieldDictionary
import AlgebraicJacobian.Picard.DivisorStalkIdeal
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeRelWindow

/-!
# G-4 — the germ bridge: piece reading ↔ function-field reading

The two seed-close cores read a `K`-side component of a window section on a base-changed
piece `D(h')` at a residue field `κ(p)`.  This file identifies, over the *fibre* curve
`relCurve C K` (`K` a field), the **germ** of the piece side component
`relThetaResSide a b hV s` with the function-field reading `thetaFieldRead C K π a s`, up to
the trivializing element of the theta presentation and a chart-transition unit.  Both the
transition unit (from the theta cocycle on the chart overlap) and the trivializing element
cancel in a *divisibility* comparison, so the bridge takes the crisp form:

* `AlgebraicGeometry.germ_relThetaResSide_dvd_iff_ord_le` — at a closed point `z` of a piece
  `V ≤ relPinnedChart C K π b`, the germ of one piece side component divides that of another
  exactly when the orders of the corresponding function-field readings compare — the DVR
  divisibility of the stalk read through the theta trivialization.

The proof factors through two structural steps:

* `AlgebraicGeometry.algebraMap_germ_thetaFieldGluedEquiv_eq` — the glued-component germ, in
  the function field, is `elem z · thetaFieldRead s` (the trivialization identity);
* `AlgebraicGeometry.exists_unit_germ_relThetaResSide_eq` — the piece side component germ is a
  fixed stalk unit times the glued-component germ (the chart-transition, cased over the
  side and the chart the point sits in).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

section GermBridge

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- **The glued-component germ is the trivialized reading**: in the function field, the
image of the germ (at any point `z`) of the deterministic glued component of a global theta
section is the trivializing element `elem z` times its function-field reading
`thetaFieldRead s`.  Unwinds `thetaFieldRead = gluedVal = elem⁻¹ · germ_η(glued)` through the
generic-germ/stalk seam. -/
lemma algebraMap_germ_thetaFieldGluedEquiv_eq (s : relThetaSections C K π a)
    (z : relCurve C K) :
    algebraMap ((relCurve C K).presheaf.stalk z) (relCurve C K).functionField
        (((relCurve C K).presheaf.germ (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
            ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
          ((thetaFieldGluedEquiv C K π a s).val z))
      = (((thetaFieldPresentation C K π a).elem z : (relCurve C K).functionFieldˣ) :
          (relCurve C K).functionField)
        * thetaFieldRead C K π a s := by
  have hh : (((thetaFieldPresentation C K π a).elem z : (relCurve C K).functionFieldˣ) :
        (relCurve C K).functionField) * thetaFieldRead C K π a s
      = algebraMap ((relCurve C K).presheaf.stalk z) (relCurve C K).functionField
          (((relCurve C K).presheaf.germ
              (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
              ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
            ((thetaFieldGluedEquiv C K π a s).val z)) := by
    rw [thetaFieldRead_apply, Scheme.MeromorphicPresentation.gluedVal_eq_elem_inv_mul K
      (thetaFieldPresentation C K π a) z (W := ⊤) trivial (thetaFieldGluedEquiv C K π a s)]
    simp only [thetaFieldPresentation_cover]
    rw [Scheme.germ_generic_eq_algebraMap_germ
        (⟨trivial, (thetaFieldPointedCover C K π).genericPoint_mem_opens z⟩ :
          genericPoint (relCurve C K) ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens z)
        (⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ :
          z ∈ ⊤ ⊓ (thetaFieldPointedCover C K π).opens z)
        ((thetaFieldGluedEquiv C K π a s).val z),
      ← mul_assoc, Units.mul_inv, one_mul]
  exact hh.symm

omit [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))] in
/-- **The piece side component germ is a unit times the glued-component germ**: at a point
`z` of a piece `V ≤ relPinnedChart C K π b`, the germ of the side component
`relThetaResSide a b hV s` is a fixed stalk unit (independent of `s`) times the germ of the
deterministic glued component.  On the chart the deterministic selector picks the unit is
`1`; on the other chart it is the germ of the theta cocycle (a unit on the overlap). -/
lemma exists_unit_germ_relThetaResSide_eq (b : Bool)
    {V : (relCurve C K).Opens} (hV : V ≤ relPinnedChart C K π b)
    {z : relCurve C K} (hzV : z ∈ V) :
    ∃ w : ((relCurve C K).presheaf.stalk z)ˣ, ∀ (s : relThetaSections C K π a),
      ((relCurve C K).presheaf.germ V z hzV).hom (relThetaResSide a b hV s)
        = (w : (relCurve C K).presheaf.stalk z) *
          ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
              ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
            ((thetaFieldGluedEquiv C K π a s).val z) := by
  by_cases hz0 : z ∈ (relCover C K (fiberTwoCover π)).V₀
  · cases b with
    | false =>
      rw [relPinnedChart_false] at hV
      refine ⟨1, fun s => ?_⟩
      rw [Units.val_one, one_mul, relThetaResSide_false, germ_resHom]
      exact (germ_thetaFieldGluedEquiv_fst C K π a s hz0
        ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz0⟩).symm
    | true =>
      -- `z ∈ V₀ ⊓ V₁`: the two components differ by the theta cocycle germ (a unit)
      have hz01 : z ∈ (relCover C K (fiberTwoCover π)).V₀
          ⊓ (relCover C K (fiberTwoCover π)).V₁ := ⟨hz0, hV hzV⟩
      set cocU : ((relCurve C K).presheaf.stalk z)ˣ :=
        Units.map ((relCurve C K).presheaf.germ ((relCover C K (fiberTwoCover π)).V₀
            ⊓ (relCover C K (fiberTwoCover π)).V₁) z hz01).hom.toMonoidHom
          (relThetaCocycle C K π a) with hcocU
      have hcoc : (cocU : (relCurve C K).presheaf.stalk z)
          = ((relCurve C K).presheaf.germ ((relCover C K (fiberTwoCover π)).V₀
              ⊓ (relCover C K (fiberTwoCover π)).V₁) z hz01).hom
            ((relThetaCocycle C K π a : Γ(relCurve C K,
              (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁))) :=
        rfl
      refine ⟨cocU⁻¹, fun s => ?_⟩
      have hm := congrArg
        ((relCurve C K).presheaf.germ ((relCover C K (fiberTwoCover π)).V₀
          ⊓ (relCover C K (fiberTwoCover π)).V₁) z hz01).hom
        (relThetaSections_matching a s
          (le_rfl : (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁
            ≤ (relCover C K (fiberTwoCover π)).V₀ ⊓ (relCover C K (fiberTwoCover π)).V₁))
      rw [map_mul, germ_resHom, germ_resHom, germ_resHom, ← hcoc] at hm
      rw [relThetaResSide_true, germ_resHom]
      have hfinal : ((relCurve C K).presheaf.germ
            (⊤ ⊓ (relCover C K (fiberTwoCover π)).V₁) z ⟨trivial, hV hzV⟩).hom s.val.2
          = ((cocU⁻¹ : ((relCurve C K).presheaf.stalk z)ˣ) :
              (relCurve C K).presheaf.stalk z) *
            ((relCurve C K).presheaf.germ (⊤ ⊓ (thetaFieldPointedCover C K π).opens z) z
                ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩).hom
              ((thetaFieldGluedEquiv C K π a s).val z) := by
        rw [germ_thetaFieldGluedEquiv_fst C K π a s hz0
            ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz0⟩,
          hm, ← mul_assoc, Units.inv_mul, one_mul]
      exact hfinal
  · -- `z ∉ V₀`, so `z ∈ V₁` and the deterministic selector picks chart 1
    have hz1 : z ∈ (relCover C K (fiberTwoCover π)).V₁ := mem_V₁_of_notMem_V₀ C K π hz0
    cases b with
    | false => exact absurd (hV hzV) hz0
    | true =>
      rw [relPinnedChart_true] at hV
      refine ⟨1, fun s => ?_⟩
      rw [Units.val_one, one_mul, relThetaResSide_true, germ_resHom]
      exact (germ_thetaFieldGluedEquiv_snd C K π a s hz0
        ⟨trivial, (thetaFieldPointedCover C K π).mem_opens z⟩ ⟨trivial, hz1⟩).symm

set_option maxHeartbeats 800000 in
-- the chained order/valuation/stalk-DVR rewrites over the fibre curve exceed the default
/-- **The germ bridge, divisibility form**: at a closed point `z` of a piece
`V ≤ relPinnedChart C K π b` on the fibre curve `relCurve C K`, the germ of the side
component `relThetaResSide a b hV t` divides that of `relThetaResSide a b hV s` exactly when
the order of the reading `thetaFieldRead s` dominates that of `thetaFieldRead t`.  The
chart-transition unit and the trivializing element `elem z` cancel in the divisibility. -/
theorem germ_relThetaResSide_dvd_iff_ord_le (s t : relThetaSections C K π a) (b : Bool)
    {V : (relCurve C K).Opens} (hV : V ≤ relPinnedChart C K π b)
    {z : relCurve C K} (hzV : z ∈ V) (hzg : z ≠ genericPoint (relCurve C K)) :
    ((relCurve C K).presheaf.germ V z hzV).hom (relThetaResSide a b hV t)
        ∣ ((relCurve C K).presheaf.germ V z hzV).hom (relThetaResSide a b hV s)
      ↔ Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hzg (thetaFieldRead C K π a s)
          ≤ Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hzg
              (thetaFieldRead C K π a t) := by
  letI := isDiscreteValuationRing_stalk (relCurve C K ↘ Spec (CommRingCat.of K)) hzg
  obtain ⟨w, hw⟩ := exists_unit_germ_relThetaResSide_eq C K π a b hV hzV
  have hpos : (0 : WithZero (Multiplicative ℤ))
      < Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hzg
          (((thetaFieldPresentation C K π a).elem z : (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
  rw [hw s, hw t, mul_dvd_mul_iff_left (Units.ne_zero w), Scheme.dvd_iff_ord_le K hzg,
    algebraMap_germ_thetaFieldGluedEquiv_eq C K π a s z,
    algebraMap_germ_thetaFieldGluedEquiv_eq C K π a t z, map_mul, map_mul,
    mul_le_mul_iff_right₀ hpos]

/-! ## The fibre divisibility reduction: from pointwise order to piece divisibility -/

set_option maxHeartbeats 800000 in
-- the section-ring gluing of the pointwise germ divisibilities over the fibre curve
/-- **Piece divisibility from pointwise order domination**: on the fibre curve
`relCurve C K` (`K` a field), the piece side component `relThetaResSide a b … s` of a
theta section `s` lies in the principal ideal generated by that of `t`, provided the
reading `t` is a nonzerodivisor on the piece `D(h)` and, at every closed point of `D(h)`,
the order of `thetaFieldRead s` dominates that of `thetaFieldRead t`.  Glues the pointwise
germ divisibilities (the germ bridge `germ_relThetaResSide_dvd_iff_ord_le` at closed
points; a unit at the generic point) through the section-ring locality
`Scheme.mem_span_singleton_of_forall_germ`.  The remaining honest content of `hdiv` is the
`hle` order comparison at the universal seed (the base-point-free / achiever argument). -/
theorem relThetaResSide_mem_span_of_forall_ord_le (s t : relThetaSections C K π a) (b : Bool)
    (h : Γ(relCurve C K, relPinnedChart C K π b))
    (hE : relThetaResSide a b ((relCurve C K).basicOpen_le h) t
        ∈ nonZeroDivisors Γ(relCurve C K, (relCurve C K).basicOpen h))
    (hle : ∀ (w : relCurve C K) (hwg : w ≠ genericPoint (relCurve C K)),
        w ∈ (relCurve C K).basicOpen h →
        Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hwg (thetaFieldRead C K π a s)
          ≤ Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hwg
              (thetaFieldRead C K π a t)) :
    relThetaResSide a b ((relCurve C K).basicOpen_le h) s
      ∈ Ideal.span {relThetaResSide a b ((relCurve C K).basicOpen_le h) t} := by
  refine Scheme.mem_span_singleton_of_forall_germ
    (fun z hz => ((isAffineOpen_relPinnedChart C K π b).basicOpen h).germ_mem_nonZeroDivisors
      hE _ hz)
    (fun z hz => ?_)
  rw [Ideal.mem_span_singleton]
  by_cases hzg : z = genericPoint (relCurve C K)
  · subst hzg
    exact (isUnit_of_mem_nonZeroDivisors
      (((isAffineOpen_relPinnedChart C K π b).basicOpen h).germ_mem_nonZeroDivisors
        hE _ hz)).dvd
  · rw [germ_relThetaResSide_dvd_iff_ord_le C K π a s t b
      ((relCurve C K).basicOpen_le h) hz hzg]
    exact hle z hzg hz

end GermBridge

end AlgebraicGeometry
