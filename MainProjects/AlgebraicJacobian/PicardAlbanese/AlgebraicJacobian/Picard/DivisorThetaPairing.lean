/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyThetaSections
import AlgebraicJacobian.Algebra.MonicReverseInverse
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# DD-4 (Task 4, (c2)-transport) — discharge of the pairing input `IsThetaPaired`

The affine-colength-scheme trivialization (inbox I-0199 route 1, realized without any
sheaf-theoretic localization brick): the colength scheme is *finite* over the base, so
the chart-1 coordinate `t₁` is **integral over `R`** in every chart-1 colength algebra
(certificate clause (c1)).  A single monic annihilator `p` of all the `t₁`-images
(`exists_monic_forall_aeval_eq_zero`) turns, through the reciprocal-witness identity
(`Polynomial.Monic.mul_aeval_neg_divX_reverse`) and the overlap relation `t₀ · t₁ = 1`,
into a *global chart-0 section* `H = q(t₀)` with `t₀ · H ≡ 1` on every cross-overlap
colength — the algebraic partition of unity subordinate to the two coordinate loci.
The manufactured inverse-twisted glued families

* `u' = (Hᵃ on the chart-0 pieces; 1 on the chart-1 pieces)` and
* `v' = (1 − (t₀·H)ᵃ on the chart-0 pieces; 0 on the chart-1 pieces)`

satisfy the `Θ⁻ᵃ`-twisted matching, and pair against the manufactured theta sections
`σ = (t₀ᵃ; 1)`, `τ = (1; t₁ᵃ)` to `σ·u' + τ·v' = 1` — exactly the witness shape of
`isThetaPaired_of_sectionWitness`.

* `DivisorAdaptation.thetaInvSectionFst`/`thetaInvSectionSnd` — the manufactured
  inverse-twisted sections attached to a chart-0 gauge `H`.
* `DivisorAdaptation.isThetaPaired_of_coordInverse` — any global chart-0 section `H`
  with `t₀ · H ≡ 1` on all cross-overlap colengths discharges the pairing input.
* `DivisorAdaptation.isThetaPaired_of_finite_colength` — **the discharge**: finiteness
  of the chart-1 colengths over `R` suffices.
* `DivisorAdaptation.IsCertified.isThetaPaired` — the certificate form; with it the
  (c2)-transport keystones fire unconditionally:
  `IsCertified.finite_thetaGlued` / `projective_thetaGlued` / `rankAtStalk_thetaGlued`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); see
`AlgebraicJacobian.Picard.DivisorFamilyThetaRank`. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite Polynomial

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

section CoordPow

variable (C R π)

/-- The relative chart-0 coordinate powers collapse: `t₀ᵃ` is the `a`-th power of
`t₀ = relFiberCoordPow C R π 1`. -/
lemma relFiberCoordPow_one_pow (a : ℕ) :
    relFiberCoordPow C R π 1 ^ a = relFiberCoordPow C R π a :=
  calc relFiberCoordPow C R π 1 ^ a
      = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π)
          ((relCover C R (fiberTwoCover π)).V₀) le_rfl).hom ((fiberCoord π ^ 1) ^ a) :=
        (map_pow _ _ _).symm
    _ = relFiberCoordPow C R π a := by
        rw [← pow_mul, one_mul]
        rfl

end CoordPow

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d) (a : ℕ)

/-- The value of a restricted unit is the restriction of the value. -/
private lemma val_unitsRestrict' {W U : (relCurve C R).Opens} (h : W ≤ U)
    (w : Γ(relCurve C R, U)ˣ) :
    (((relCurve C R).unitsRestrict h w : Γ(relCurve C R, W)ˣ) : Γ(relCurve C R, W))
      = (relCurve C R).resHom h (w : Γ(relCurve C R, U)) := rfl

/-- The value of the inverse of a restricted unit is the restriction of the inverse's
value. -/
private lemma val_unitsRestrict_inv {W U : (relCurve C R).Opens} (h : W ≤ U)
    (w : Γ(relCurve C R, U)ˣ) :
    ((((relCurve C R).unitsRestrict h w)⁻¹ : Γ(relCurve C R, W)ˣ) : Γ(relCurve C R, W))
      = (relCurve C R).resHom h ((w⁻¹ : Γ(relCurve C R, U)ˣ) : Γ(relCurve C R, U)) := by
  rw [← map_inv]
  rfl

/-! ## The coordinate reciprocal on the cross-overlap colengths -/

/-- **The cross-overlap coordinate reciprocal**: on an overlap colength lying below both
pinned charts, a monic annihilator `p` of the chart-1 coordinate image turns into the
reciprocal identity `t₀ · q(t₀) = 1` for the universal witness polynomial
`q = -(p.reverse.divX)` — the overlap relation `t₀ · t₁ = 1` reads the annihilator of
`t₁ = t₀⁻¹` backwards. -/
theorem mk_ovlIdeal_coord_mul_aeval_eq_one {p : R[X]} (hp : p.Monic) (i j : A.index)
    (hW0 : A.pieces i ⊓ A.pieces j ≤ (relCover C R (fiberTwoCover π)).V₀)
    (hW1 : A.pieces i ⊓ A.pieces j ≤ (relCover C R (fiberTwoCover π)).V₁)
    (hw : Polynomial.aeval (Ideal.Quotient.mk (A.ovlIdeal i j)
      ((relCurve C R).resHom hW1 (relFiberCoordOnePow C R π 1))) p = 0) :
    Ideal.Quotient.mk (A.ovlIdeal i j) ((relCurve C R).resHom hW0
      (relFiberCoordPow C R π 1
        * Polynomial.aeval (relFiberCoordPow C R π 1) (-p.reverse.divX))) = 1 := by
  -- the two coordinate images are mutually inverse in the overlap colength
  have hsw : Ideal.Quotient.mk (A.ovlIdeal i j)
      ((relCurve C R).resHom hW0 (relFiberCoordPow C R π 1))
      * Ideal.Quotient.mk (A.ovlIdeal i j)
        ((relCurve C R).resHom hW1 (relFiberCoordOnePow C R π 1)) = 1 := by
    rw [← map_mul,
      ← Scheme.resHom_resHom inf_le_left (le_inf hW0 hW1) (relFiberCoordPow C R π 1),
      ← Scheme.resHom_resHom inf_le_right (le_inf hW0 hW1) (relFiberCoordOnePow C R π 1),
      resHom_relFiberCoordPow C R π 1, resHom_relFiberCoordOnePow C R π 1,
      ← map_mul, Units.mul_inv, map_one, map_one]
  -- naturality of `aeval` along the quotient-restriction algebra map
  have hnat : Ideal.Quotient.mk (A.ovlIdeal i j) ((relCurve C R).resHom hW0
        (Polynomial.aeval (relFiberCoordPow C R π 1) (-p.reverse.divX)))
      = Polynomial.aeval (Ideal.Quotient.mk (A.ovlIdeal i j)
          ((relCurve C R).resHom hW0 (relFiberCoordPow C R π 1))) (-p.reverse.divX) :=
    (Polynomial.aeval_algHom_apply ((Ideal.Quotient.mkₐ R (A.ovlIdeal i j)).comp
      (relResAlgHom C R hW0)) (relFiberCoordPow C R π 1) (-p.reverse.divX)).symm
  rw [map_mul, map_mul, hnat]
  exact hp.mul_aeval_neg_divX_reverse hsw hw

/-! ## The manufactured inverse-twisted sections -/

variable (H : Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀))

/-- **The first manufactured inverse-twisted section** `u' = (Hᵃ; 1)` attached to a
chart-0 gauge `H`: the gauge power on the chart-0 pieces, `1` on the chart-1 pieces. -/
noncomputable def thetaInvSectionFst : A.chartProd := fun j =>
  match j with
  | Sum.inl j₀ => Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
      ((relCurve C R).resHom (A.pieces_inl_le j₀) (H ^ a))
  | Sum.inr _ => 1

/-- **The second manufactured inverse-twisted section** `v' = (1 − (t₀·H)ᵃ; 0)`. -/
noncomputable def thetaInvSectionSnd : A.chartProd := fun j =>
  match j with
  | Sum.inl j₀ => 1 - Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
      ((relCurve C R).resHom (A.pieces_inl_le j₀)
        ((relFiberCoordPow C R π 1 * H) ^ a))
  | Sum.inr _ => 0

@[simp]
lemma thetaInvSectionFst_inl (j₀ : Fin A.m₀) :
    A.thetaInvSectionFst a H (Sum.inl j₀)
      = Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
          ((relCurve C R).resHom (A.pieces_inl_le j₀) (H ^ a)) := rfl

@[simp]
lemma thetaInvSectionFst_inr (j₁ : Fin A.m₁) :
    A.thetaInvSectionFst a H (Sum.inr j₁) = 1 := rfl

@[simp]
lemma thetaInvSectionSnd_inl (j₀ : Fin A.m₀) :
    A.thetaInvSectionSnd a H (Sum.inl j₀)
      = 1 - Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
          ((relCurve C R).resHom (A.pieces_inl_le j₀)
            ((relFiberCoordPow C R π 1 * H) ^ a)) := rfl

@[simp]
lemma thetaInvSectionSnd_inr (j₁ : Fin A.m₁) :
    A.thetaInvSectionSnd a H (Sum.inr j₁) = 0 := rfl

variable {H}

/-- **`u'` is a `Θ⁻ᵃ`-twisted glued section** when the gauge inverts `t₀` on all
cross-overlap colengths. -/
theorem thetaInvSectionFst_mem
    (hovl : ∀ (i₀ : Fin A.m₀) (j₁ : Fin A.m₁),
      Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
        ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π 1 * H)) = 1)
    (hovl' : ∀ (j₁ : Fin A.m₁) (i₀ : Fin A.m₀),
      Ideal.Quotient.mk (A.ovlIdeal (Sum.inr j₁) (Sum.inl i₀))
        ((relCurve C R).resHom (inf_le_right.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π 1 * H)) = 1) :
    A.thetaInvSectionFst a H ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹ := by
  rw [mem_unitGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rcases i with i₀ | i₁ <;> rcases j with j₀ | j₁
  · -- chart 0 / chart 0: both components restrict from `Hᵃ`
    rw [thetaInvSectionFst_inl, thetaInvSectionFst_inl, toOvlLeft_mk, toOvlRight_mk]
    simp only [Pi.inv_apply]
    rw [FinCoverData.thetaOvlUnit_inl_inl, inv_one, Units.val_one, map_one, one_mul,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- chart 0 / chart 1: the reciprocal case `Hᵃ ≡ θₐ⁻¹`
    rw [thetaInvSectionFst_inl, thetaInvSectionFst_inr, toOvlLeft_mk, map_one, mul_one]
    simp only [Pi.inv_apply]
    rw [FinCoverData.thetaOvlUnit_inl_inr, val_unitsRestrict_inv, Scheme.resHom_resHom]
    -- both sides invert the same element, hence agree
    have hx : Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
        ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inl_le i₀)) (H ^ a))
        * Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
          ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inl_le i₀))
            (relFiberCoordPow C R π a)) = 1 := by
      rw [← map_mul, ← map_mul, ← relFiberCoordPow_one_pow C R π a, ← mul_pow,
        mul_comm H (relFiberCoordPow C R π 1), map_pow, map_pow, hovl i₀ j₁, one_pow]
    have hy : Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
        ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π a))
        * Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
          ((relCurve C R).resHom
            (inf_le_inf (A.pieces_inl_le i₀) (A.pieces_inr_le j₁))
            (((relThetaCocycle C R π a)⁻¹ :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁)ˣ) :
              Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
                (relCover C R (fiberTwoCover π)).V₁))) = 1 := by
      rw [← map_mul,
        ← Scheme.resHom_resHom inf_le_left
          (inf_le_inf (A.pieces_inl_le i₀) (A.pieces_inr_le j₁))
          (relFiberCoordPow C R π a),
        resHom_relFiberCoordPow C R π a, ← map_mul, Units.mul_inv, map_one, map_one]
    exact left_inv_eq_right_inv hx hy
  · -- chart 1 / chart 0: the twisting unit against the gauge power is the reciprocal
    rw [thetaInvSectionFst_inr, thetaInvSectionFst_inl, map_one, toOvlRight_mk]
    simp only [Pi.inv_apply]
    rw [FinCoverData.thetaOvlUnit_inr_inl, inv_inv, val_unitsRestrict',
      Scheme.resHom_resHom, ← resHom_relFiberCoordPow C R π a, Scheme.resHom_resHom,
      ← map_mul, ← map_mul, ← relFiberCoordPow_one_pow C R π a, ← mul_pow,
      map_pow, map_pow, hovl' i₁ j₀, one_pow]
  · -- chart 1 / chart 1: both components are `1`
    rw [thetaInvSectionFst_inr, thetaInvSectionFst_inr, map_one, map_one]
    simp only [Pi.inv_apply]
    rw [FinCoverData.thetaOvlUnit_inr_inr, inv_one, Units.val_one, map_one, mul_one]

/-- **`v'` is a `Θ⁻ᵃ`-twisted glued section** when the gauge inverts `t₀` on all
cross-overlap colengths. -/
theorem thetaInvSectionSnd_mem
    (hovl : ∀ (i₀ : Fin A.m₀) (j₁ : Fin A.m₁),
      Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
        ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π 1 * H)) = 1)
    (hovl' : ∀ (j₁ : Fin A.m₁) (i₀ : Fin A.m₀),
      Ideal.Quotient.mk (A.ovlIdeal (Sum.inr j₁) (Sum.inl i₀))
        ((relCurve C R).resHom (inf_le_right.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π 1 * H)) = 1) :
    A.thetaInvSectionSnd a H ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹ := by
  rw [mem_unitGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rcases i with i₀ | i₁ <;> rcases j with j₀ | j₁
  · -- chart 0 / chart 0: both components restrict from `1 − (t₀·H)ᵃ`
    rw [thetaInvSectionSnd_inl, thetaInvSectionSnd_inl, map_sub, map_sub, map_one,
      map_one, toOvlLeft_mk, toOvlRight_mk]
    simp only [Pi.inv_apply]
    rw [FinCoverData.thetaOvlUnit_inl_inl, inv_one, Units.val_one, map_one, one_mul,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- chart 0 / chart 1: `1 − (t₀·H)ᵃ` vanishes on the cross overlap
    rw [thetaInvSectionSnd_inl, thetaInvSectionSnd_inr, map_zero, mul_zero, map_sub,
      map_one, toOvlLeft_mk, Scheme.resHom_resHom, map_pow, map_pow, hovl i₀ j₁,
      one_pow, sub_self]
  · -- chart 1 / chart 0: the mirrored vanishing
    rw [thetaInvSectionSnd_inr, thetaInvSectionSnd_inl, map_zero, map_sub, map_one,
      toOvlRight_mk, Scheme.resHom_resHom, map_pow, map_pow, hovl' i₁ j₀, one_pow,
      sub_self, mul_zero]
  · -- chart 1 / chart 1: both components are `0`
    rw [thetaInvSectionSnd_inr, thetaInvSectionSnd_inr, map_zero, map_zero, mul_zero]

variable (H)

/-- **The pairing identity** `σ·u' + τ·v' = 1`: the manufactured theta sections pair
against the manufactured inverse-twisted sections onto `1`, componentwise by the very
construction of the gauge splitting. -/
theorem thetaSection_pairing :
    A.thetaSectionFst a * A.thetaInvSectionFst a H
      + A.thetaSectionSnd a * A.thetaInvSectionSnd a H = 1 := by
  funext j
  rcases j with j₀ | j₁
  · simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, thetaSectionFst_inl,
      thetaSectionSnd_inl, thetaInvSectionFst_inl, thetaInvSectionSnd_inl, one_mul]
    rw [← map_mul, ← map_mul, ← relFiberCoordPow_one_pow C R π a, ← mul_pow]
    ring
  · simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, thetaSectionFst_inr,
      thetaSectionSnd_inr, thetaInvSectionFst_inr, thetaInvSectionSnd_inr, one_mul,
      mul_zero, add_zero]

variable {H}

/-! ## The discharge of the pairing input -/

/-- **The gauge form of the pairing discharge**: any global chart-0 section `H` with
`t₀ · H ≡ 1` on all cross-overlap colengths discharges `IsThetaPaired`. -/
theorem isThetaPaired_of_coordInverse
    (hovl : ∀ (i₀ : Fin A.m₀) (j₁ : Fin A.m₁),
      Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
        ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π 1 * H)) = 1)
    (hovl' : ∀ (j₁ : Fin A.m₁) (i₀ : Fin A.m₀),
      Ideal.Quotient.mk (A.ovlIdeal (Sum.inr j₁) (Sum.inl i₀))
        ((relCurve C R).resHom (inf_le_right.trans (A.pieces_inl_le i₀))
          (relFiberCoordPow C R π 1 * H)) = 1) :
    A.IsThetaPaired a :=
  A.isThetaPaired_of_sectionWitness a (A.thetaInvSectionFst_mem a hovl hovl')
    (A.thetaInvSectionSnd_mem a hovl hovl') (A.thetaSection_pairing a H)

/-- **The pairing input holds** (DD-4 Task 4, the (c2)-transport residual of I-0199):
finiteness of the chart-1 colength modules over `R` — certificate clause (c1) on the
chart-1 pieces — discharges `IsThetaPaired` for every twist exponent.  The chart-1
coordinate is integral over `R` in every chart-1 colength, one monic annihilator serves
all pieces, and its reciprocal witness is the global chart-0 gauge. -/
theorem isThetaPaired_of_finite_colength
    (hfin : ∀ j₁ : Fin A.m₁, Module.Finite R (A.colength (Sum.inr j₁))) :
    A.IsThetaPaired a := by
  have hint : ∀ j₁ : Fin A.m₁, _root_.IsIntegral R
      (Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j₁)})
        ((relCurve C R).resHom (A.pieces_inr_le j₁) (relFiberCoordOnePow C R π 1))) :=
    fun j₁ => by
      haveI := hfin j₁
      exact _root_.IsIntegral.of_finite R _
  obtain ⟨p, hp, hz⟩ := exists_monic_forall_aeval_eq_zero hint
  refine A.isThetaPaired_of_coordInverse a
    (H := Polynomial.aeval (relFiberCoordPow C R π 1) (-p.reverse.divX))
    (fun i₀ j₁ => ?_) (fun j₁ i₀ => ?_)
  · -- transport the annihilator into the overlap colength through `toOvlRight`
    have hw : Polynomial.aeval (Ideal.Quotient.mk (A.ovlIdeal (Sum.inl i₀) (Sum.inr j₁))
        ((relCurve C R).resHom (inf_le_right.trans (A.pieces_inr_le j₁))
          (relFiberCoordOnePow C R π 1))) p = 0 := by
      have h : Polynomial.aeval (A.toOvlRight (Sum.inl i₀) (Sum.inr j₁)
          (Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j₁)})
            ((relCurve C R).resHom (A.pieces_inr_le j₁)
              (relFiberCoordOnePow C R π 1)))) p = 0 := by
        rw [Polynomial.aeval_algHom_apply, hz j₁, map_zero]
      rwa [toOvlRight_mk, Scheme.resHom_resHom] at h
    exact A.mk_ovlIdeal_coord_mul_aeval_eq_one hp (Sum.inl i₀) (Sum.inr j₁)
      (inf_le_left.trans (A.pieces_inl_le i₀))
      (inf_le_right.trans (A.pieces_inr_le j₁)) hw
  · -- the mirrored transport through `toOvlLeft`
    have hw : Polynomial.aeval (Ideal.Quotient.mk (A.ovlIdeal (Sum.inr j₁) (Sum.inl i₀))
        ((relCurve C R).resHom (inf_le_left.trans (A.pieces_inr_le j₁))
          (relFiberCoordOnePow C R π 1))) p = 0 := by
      have h : Polynomial.aeval (A.toOvlLeft (Sum.inr j₁) (Sum.inl i₀)
          (Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j₁)})
            ((relCurve C R).resHom (A.pieces_inr_le j₁)
              (relFiberCoordOnePow C R π 1)))) p = 0 := by
        rw [Polynomial.aeval_algHom_apply, hz j₁, map_zero]
      rwa [toOvlLeft_mk, Scheme.resHom_resHom] at h
    exact A.mk_ovlIdeal_coord_mul_aeval_eq_one hp (Sum.inr j₁) (Sum.inl i₀)
      (inf_le_right.trans (A.pieces_inl_le i₀))
      (inf_le_left.trans (A.pieces_inr_le j₁)) hw

variable {A}

/-- **The certificate discharges the pairing input**: clause (c1) on the chart-1 pieces
is exactly the finiteness the coordinate-integrality route needs. -/
theorem IsCertified.isThetaPaired {n : ℕ} (hc : A.IsCertified n) (a : ℕ) :
    A.IsThetaPaired a :=
  A.isThetaPaired_of_finite_colength a fun j₁ => hc.finite_colength (Sum.inr j₁)

/-- **(c2)-transport, finiteness, unconditional form**: under the certificate the
Θ-twisted glued module is a finite `R`-module. -/
theorem IsCertified.finite_thetaGlued {n : ℕ} (hc : A.IsCertified n) (a : ℕ) :
    Module.Finite R (A.ThetaGlued a) :=
  A.finite_thetaGlued a (hc.isThetaPaired a) hc.finite_glued

/-- **(c2)-transport, projectivity, unconditional form**: under the certificate the
Θ-twisted glued module is projective over `R`. -/
theorem IsCertified.projective_thetaGlued {n : ℕ} (hc : A.IsCertified n) (a : ℕ) :
    Module.Projective R (A.ThetaGlued a) :=
  A.projective_thetaGlued a (hc.isThetaPaired a) hc.projective_glued

/-- **(c2)-transport, constant rank, unconditional form**: under the certificate the
Θ-twisted glued module has the same constant fibre rank `n` as the untwisted one —
exactly the `divisorWindowGr` input shape. -/
theorem IsCertified.rankAtStalk_thetaGlued {n : ℕ} (hc : A.IsCertified n) (a : ℕ)
    (p : PrimeSpectrum R) : Module.rankAtStalk (A.ThetaGlued a) p = n :=
  A.rankAtStalk_thetaGlued a (hc.isThetaPaired a) hc p

end DivisorAdaptation

end AlgebraicGeometry
