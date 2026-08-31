/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyThetaRank

/-!
# DD-4 (Task 4, (c2)-transport) — the manufactured theta sections `σ = (t₀ᵃ, 1)`,
`τ = (1, t₁ᵃ)`

The two canonical global sections of the Θ-twisted glued colength module `W(d)^{Θᵃ}`
(`AlgebraicJacobian.Picard.DivisorFamilyThetaRank`), manufactured from the pinned
chart coordinates: the relative theta cocycle is the restriction of the pulled-back
chart-0 coordinate power `t₀ᵃ` (with inverse the chart-1 coordinate power `t₁ᵃ`), so

* `σ = (t₀ᵃ on the chart-0 pieces; 1 on the chart-1 pieces)` and
* `τ = (1 on the chart-0 pieces; t₁ᵃ on the chart-1 pieces)`

satisfy the Θ-twisted matching (`thetaSectionFst_mem`/`thetaSectionSnd_mem`).  They are
**jointly unit-componented** — on every piece one of the two components is `1` — so they
generate the twist pointwise on the colength scheme; a pairing witness against them
(`isThetaPaired_of_sectionWitness`) discharges the pairing input `IsThetaPaired` of the
(c2)-transport keystones.  Producing that witness (a partition of unity subordinate to
the two coordinate loci by inverse-twisted sections) is the affine-colength-scheme
trivialization — the open cohomological residue of the transport.

* `AlgebraicGeometry.relFiberCoordPow`/`relFiberCoordOnePow` — the pulled-back chart
  coordinate powers `t₀ᵃ ∈ Γ(V₀ᴿ)`, `t₁ᵃ ∈ Γ(V₁ᴿ)`.
* `AlgebraicGeometry.resHom_relFiberCoordPow`/`resHom_relFiberCoordOnePow` — restricted
  to the chart overlap they are the value of the relative theta cocycle (resp. its
  inverse).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161); see
`AlgebraicJacobian.Picard.DivisorFamilyThetaRank`. -/
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 80000

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

section ThetaSections

variable (C R π)

/-- Elementwise form of `Scheme.Hom.appLE_map` for the first projection: restricting an
`appLE`-pullback is the `appLE`-pullback into the smaller open. -/
private lemma resHom_appLE_apply {U : C.left.Opens} {V W : (relCurve C R).Opens}
    (e : V ≤ (fst C (overSpec k R)).left ⁻¹ᵁ U) (h : W ≤ V) (x : Γ(C.left, U)) :
    (relCurve C R).resHom h
        (((fst C (overSpec k R)).left.appLE U V e).hom x)
      = ((fst C (overSpec k R)).left.appLE U W (h.trans e)).hom x := by
  have hcomp := (fst C (overSpec k R)).left.appLE_map e (homOfLE h).op
  calc (relCurve C R).resHom h (((fst C (overSpec k R)).left.appLE U V e).hom x)
      = (((fst C (overSpec k R)).left.appLE U V e) ≫
          (C ⊗ overSpec k R).left.presheaf.map (homOfLE h).op).hom x := rfl
    _ = ((fst C (overSpec k R)).left.appLE U W (h.trans e)).hom x := by rw [hcomp]

/-- Elementwise form of `Scheme.Hom.map_appLE` for the first projection: the
`appLE`-pullback of a restricted section is the `appLE`-pullback of the section. -/
private lemma appLE_map_apply {U U' : C.left.Opens} {W : (relCurve C R).Opens}
    (hU : U ≤ U') (e : W ≤ (fst C (overSpec k R)).left ⁻¹ᵁ U)
    (e' : W ≤ (fst C (overSpec k R)).left ⁻¹ᵁ U') (x : Γ(C.left, U')) :
    ((fst C (overSpec k R)).left.appLE U W e).hom
        ((C.left.presheaf.map (homOfLE hU).op).hom x)
      = ((fst C (overSpec k R)).left.appLE U' W e').hom x := by
  have hcomp := (fst C (overSpec k R)).left.map_appLE e (homOfLE hU).op
  calc ((fst C (overSpec k R)).left.appLE U W e).hom
        ((C.left.presheaf.map (homOfLE hU).op).hom x)
      = ((C.left.presheaf.map (homOfLE hU).op ≫
          (fst C (overSpec k R)).left.appLE U W e).hom) x := rfl
    _ = ((fst C (overSpec k R)).left.appLE U' W e').hom x := by rw [hcomp]

variable (a : ℕ)

/-- The relative chart-0 coordinate power `t₀ᵃ` on the pinned chart `V₀ᴿ`: the pullback
of `fiberCoord π ^ a` along the first projection. -/
noncomputable def relFiberCoordPow :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀) :=
  ((fst C (overSpec k R)).left.appLE (fiberChart₀ π)
    ((relCover C R (fiberTwoCover π)).V₀) le_rfl).hom (fiberCoord π ^ a)

/-- The relative chart-1 coordinate power `t₁ᵃ` on the pinned chart `V₁ᴿ`. -/
noncomputable def relFiberCoordOnePow :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁) :=
  ((fst C (overSpec k R)).left.appLE (fiberChart₁ π)
    ((relCover C R (fiberTwoCover π)).V₁) le_rfl).hom (fiberCoord₁ π ^ a)

/-- Restricted to the chart overlap, `t₀ᵃ` is the value of the relative theta
cocycle. -/
lemma resHom_relFiberCoordPow :
    (relCurve C R).resHom
        (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)
        (relFiberCoordPow C R π a)
      = ((relThetaCocycle C R π a :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)ˣ) :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)) := by
  rw [relFiberCoordPow, resHom_appLE_apply]
  have hpow : ((thetaUnit π ^ a : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
      Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π))
      = (C.left.presheaf.map (homOfLE
          (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom
        (fiberCoord π ^ a) := by
    rw [Units.val_pow_eq_pow_val, thetaUnit_val, map_pow]
  -- the cocycle value, unfolded to an `appLE`-pullback of the chart coordinate
  have key : ((relThetaCocycle C R π a :
      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁))
      = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π)
          ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
          inf_le_left).hom (fiberCoord π ^ a) := by
    calc ((relThetaCocycle C R π a : Γ(relCurve C R, _)ˣ) : Γ(relCurve C R, _))
        = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
            ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
            (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom
          ((thetaUnit π ^ a : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
            Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)) := rfl
      _ = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
            ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
            (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom
          ((C.left.presheaf.map (homOfLE
              (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)).op).hom
            (fiberCoord π ^ a)) := congrArg _ hpow
      _ = _ := appLE_map_apply C R
            (inf_le_left : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₀ π)
            (le_of_eq (relCover_inf C R (fiberTwoCover π))) inf_le_left
            (fiberCoord π ^ a)
  rw [key]

/-- Restricted to the chart overlap, `t₁ᵃ` is the value of the inverse relative theta
cocycle. -/
lemma resHom_relFiberCoordOnePow :
    (relCurve C R).resHom
        (inf_le_right : (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₁)
        (relFiberCoordOnePow C R π a)
      = (((relThetaCocycle C R π a)⁻¹ :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)ˣ) :
          Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁)) := by
  rw [relFiberCoordOnePow, resHom_appLE_apply]
  have hinv : (relThetaCocycle C R π a)⁻¹
      = Units.map ((fst C (overSpec k R)).left.appLE
          ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁)
          ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
          (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom.toMonoidHom
        ((thetaUnit π ^ a)⁻¹) :=
    (map_inv _ _).symm
  have hpow : (((thetaUnit π ^ a)⁻¹ : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
      Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π))
      = (C.left.presheaf.map (homOfLE
          (inf_le_right : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)).op).hom
        (fiberCoord₁ π ^ a) := by
    rw [← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    rfl
  have key : (((relThetaCocycle C R π a)⁻¹ :
      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁)ˣ) :
      Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀ ⊓
        (relCover C R (fiberTwoCover π)).V₁))
      = ((fst C (overSpec k R)).left.appLE (fiberChart₁ π)
          ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
          inf_le_right).hom (fiberCoord₁ π ^ a) := by
    calc (((relThetaCocycle C R π a)⁻¹ : Γ(relCurve C R, _)ˣ) : Γ(relCurve C R, _))
        = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
            ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
            (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom
          (((thetaUnit π ^ a)⁻¹ : Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)ˣ) :
            Γ(C.left, fiberChart₀ π ⊓ fiberChart₁ π)) := by rw [hinv]; rfl
      _ = ((fst C (overSpec k R)).left.appLE (fiberChart₀ π ⊓ fiberChart₁ π)
            ((relCover C R (fiberTwoCover π)).V₀ ⊓ (relCover C R (fiberTwoCover π)).V₁)
            (le_of_eq (relCover_inf C R (fiberTwoCover π)))).hom
          ((C.left.presheaf.map (homOfLE
              (inf_le_right : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)).op).hom
            (fiberCoord₁ π ^ a)) := congrArg _ hpow
      _ = _ := appLE_map_apply C R
            (inf_le_right : fiberChart₀ π ⊓ fiberChart₁ π ≤ fiberChart₁ π)
            (le_of_eq (relCover_inf C R (fiberTwoCover π))) inf_le_right
            (fiberCoord₁ π ^ a)
  rw [key]

/-! ## The canonical global theta sections -/

/-- The canonical global relative theta section `(t₀ᵃ, 1)`.  Its first component is
the chart-0 coordinate power and its second component is the constant section `1`. -/
noncomputable def relThetaSectionFst : relThetaSections C R π a := by
  refine ⟨((relCurve C R).resHom inf_le_right (relFiberCoordPow C R π a), 1), ?_⟩
  rw [mem_twistSubmodule_iff]
  have key := congrArg
    ((relCurve C R).resHom
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁ ≤
          (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁))
    (resHom_relFiberCoordPow C R π a)
  simpa only [Scheme.resHom_resHom, map_one, mul_one] using key

/-- The canonical global relative theta section `(1, t₁ᵃ)`.  Its first component is
the constant section `1` and its second component is the chart-1 coordinate power. -/
noncomputable def relThetaSectionSnd : relThetaSections C R π a := by
  refine ⟨(1, (relCurve C R).resHom inf_le_right (relFiberCoordOnePow C R π a)), ?_⟩
  rw [mem_twistSubmodule_iff]
  have key := congrArg
    ((relCurve C R).resHom
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        ⊤ ⊓ (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁ ≤
          (relCover C R (fiberTwoCover π)).V₀ ⊓
            (relCover C R (fiberTwoCover π)).V₁))
    (resHom_relFiberCoordOnePow C R π a)
  rw [map_one]
  simp only [Scheme.resHom_resHom] at key ⊢
  rw [key, ← map_mul, Units.mul_inv, map_one]

@[simp]
lemma relThetaSectionFst_val_fst :
    (relThetaSectionFst C R π a).val.1 =
      (relCurve C R).resHom inf_le_right (relFiberCoordPow C R π a) := rfl

@[simp]
lemma relThetaSectionFst_val_snd : (relThetaSectionFst C R π a).val.2 = 1 := rfl

@[simp]
lemma relThetaSectionSnd_val_fst : (relThetaSectionSnd C R π a).val.1 = 1 := rfl

@[simp]
lemma relThetaSectionSnd_val_snd :
    (relThetaSectionSnd C R π a).val.2 =
      (relCurve C R).resHom inf_le_right (relFiberCoordOnePow C R π a) := rfl

/-- The section `(1, t₁ᵃ)` reads as `1` on the first pinned chart. -/
@[simp]
lemma relThetaResFst_relThetaSectionSnd :
    relThetaResFst a (le_inf le_top le_rfl) (relThetaSectionSnd C R π a) = 1 := by
  rw [relThetaResFst_apply, relThetaSectionSnd_val_fst, map_one]

/-- The section `(t₀ᵃ, 1)` reads as `1` on the second pinned chart. -/
@[simp]
lemma relThetaResSnd_relThetaSectionFst :
    relThetaResSnd a (le_inf le_top le_rfl) (relThetaSectionFst C R π a) = 1 := by
  rw [relThetaResSnd_apply, relThetaSectionFst_val_snd, map_one]

end ThetaSections

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d) (a : ℕ)

/-- **The first manufactured theta section** `σ = (t₀ᵃ; 1)`: the chart-0 coordinate
power on the chart-0 pieces, `1` on the chart-1 pieces. -/
noncomputable def thetaSectionFst : A.chartProd := fun j =>
  match j with
  | Sum.inl j₀ => Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
      ((relCurve C R).resHom (A.pieces_inl_le j₀) (relFiberCoordPow C R π a))
  | Sum.inr _ => 1

/-- **The second manufactured theta section** `τ = (1; t₁ᵃ)`. -/
noncomputable def thetaSectionSnd : A.chartProd := fun j =>
  match j with
  | Sum.inl _ => 1
  | Sum.inr j₁ => Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j₁)})
      ((relCurve C R).resHom (A.pieces_inr_le j₁) (relFiberCoordOnePow C R π a))

@[simp]
lemma thetaSectionFst_inl (j₀ : Fin A.m₀) :
    A.thetaSectionFst a (Sum.inl j₀)
      = Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inl j₀)})
          ((relCurve C R).resHom (A.pieces_inl_le j₀) (relFiberCoordPow C R π a)) := rfl

@[simp]
lemma thetaSectionFst_inr (j₁ : Fin A.m₁) :
    A.thetaSectionFst a (Sum.inr j₁) = 1 := rfl

@[simp]
lemma thetaSectionSnd_inl (j₀ : Fin A.m₀) :
    A.thetaSectionSnd a (Sum.inl j₀) = 1 := rfl

@[simp]
lemma thetaSectionSnd_inr (j₁ : Fin A.m₁) :
    A.thetaSectionSnd a (Sum.inr j₁)
      = Ideal.Quotient.mk (Ideal.span {A.eqn (Sum.inr j₁)})
          ((relCurve C R).resHom (A.pieces_inr_le j₁) (relFiberCoordOnePow C R π a)) :=
  rfl

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

/-- **`σ` is a `Θᵃ`-twisted glued section.** -/
theorem thetaSectionFst_mem : A.thetaSectionFst a ∈ A.thetaGluedSubmodule a := by
  rw [mem_thetaGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rcases i with i₀ | i₁ <;> rcases j with j₀ | j₁
  · -- chart 0 / chart 0: both components restrict from `t₀ᵃ`
    rw [thetaSectionFst_inl, thetaSectionFst_inl, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inl_inl, Units.val_one, map_one, one_mul,
      Scheme.resHom_resHom, Scheme.resHom_resHom]
  · -- chart 0 / chart 1: the coordinate restricts to the cocycle value
    rw [thetaSectionFst_inl, thetaSectionFst_inr, toOvlLeft_mk, map_one, mul_one,
      FinCoverData.thetaOvlUnit_inl_inr, val_unitsRestrict',
      Scheme.resHom_resHom, ← resHom_relFiberCoordPow C R π a,
      Scheme.resHom_resHom]
  · -- chart 1 / chart 0: the inverse cocycle value cancels the coordinate
    rw [thetaSectionFst_inr, thetaSectionFst_inl, map_one, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inr_inl, val_unitsRestrict_inv, Scheme.resHom_resHom,
      ← Scheme.resHom_resHom
        (inf_le_left : (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₀)
        (le_inf (inf_le_right.trans (A.pieces_inl_le j₀))
          (inf_le_left.trans (A.pieces_inr_le i₁)))
        (relFiberCoordPow C R π a),
      resHom_relFiberCoordPow C R π a, ← map_mul, ← map_mul, Units.inv_mul,
      map_one, map_one]
  · -- chart 1 / chart 1: both components are `1`
    rw [thetaSectionFst_inr, thetaSectionFst_inr, FinCoverData.thetaOvlUnit_inr_inr,
      Units.val_one, map_one, map_one, map_one, one_mul]

/-- **`τ` is a `Θᵃ`-twisted glued section.** -/
theorem thetaSectionSnd_mem : A.thetaSectionSnd a ∈ A.thetaGluedSubmodule a := by
  rw [mem_thetaGluedSubmodule_iff]
  rintro ⟨i, j⟩
  rcases i with i₀ | i₁ <;> rcases j with j₀ | j₁
  · -- chart 0 / chart 0: both components are `1`
    rw [thetaSectionSnd_inl, thetaSectionSnd_inl, FinCoverData.thetaOvlUnit_inl_inl,
      Units.val_one, map_one, map_one, map_one, one_mul]
  · -- chart 0 / chart 1: the cocycle value cancels the coordinate
    rw [thetaSectionSnd_inl, thetaSectionSnd_inr, map_one, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inl_inr, val_unitsRestrict', Scheme.resHom_resHom,
      ← Scheme.resHom_resHom
        (inf_le_right : (relCover C R (fiberTwoCover π)).V₀ ⊓
          (relCover C R (fiberTwoCover π)).V₁ ≤ (relCover C R (fiberTwoCover π)).V₁)
        (inf_le_inf (A.pieces_inl_le i₀) (A.pieces_inr_le j₁))
        (relFiberCoordOnePow C R π a),
      resHom_relFiberCoordOnePow C R π a, ← map_mul, ← map_mul, Units.mul_inv,
      map_one, map_one]
  · -- chart 1 / chart 0: the coordinate restricts to the inverse cocycle value
    rw [thetaSectionSnd_inr, thetaSectionSnd_inl, toOvlLeft_mk, map_one, mul_one,
      FinCoverData.thetaOvlUnit_inr_inl, val_unitsRestrict_inv,
      Scheme.resHom_resHom, ← resHom_relFiberCoordOnePow C R π a,
      Scheme.resHom_resHom]
  · -- chart 1 / chart 1: both components restrict from `t₁ᵃ`
    rw [thetaSectionSnd_inr, thetaSectionSnd_inr, toOvlLeft_mk, toOvlRight_mk,
      FinCoverData.thetaOvlUnit_inr_inr, Units.val_one, map_one, one_mul,
      Scheme.resHom_resHom, Scheme.resHom_resHom]

/-- A pairing witness against the manufactured sections `σ, τ` suffices for the pairing
input: two inverse-twisted glued families `u, v` with `σ·u + τ·v = 1`. -/
theorem isThetaPaired_of_sectionWitness {u' v' : A.chartProd}
    (hu : u' ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹)
    (hv : v' ∈ A.unitGluedSubmodule (A.thetaOvlUnit a)⁻¹)
    (h : A.thetaSectionFst a * u' + A.thetaSectionSnd a * v' = 1) :
    A.IsThetaPaired a :=
  A.isThetaPaired_of_witness a (A.thetaSectionFst_mem a) (A.thetaSectionSnd_mem a)
    hu hv h

end DivisorAdaptation

end AlgebraicGeometry
