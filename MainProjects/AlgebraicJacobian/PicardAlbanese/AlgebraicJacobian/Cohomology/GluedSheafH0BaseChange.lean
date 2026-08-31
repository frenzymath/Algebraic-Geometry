/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafTermBaseChangeEquiv
import AlgebraicJacobian.Cohomology.GluedSheafEngine

/-!
# H⁰ of the glued datum sheaf, on the nose (DAT-1, stage 1d-ii, the tail)

The on-the-nose base-change export of the m-chart glued constructor's engine, mirroring the
2-chart `relTwistH0BaseChange` (`RigidEngine4BaseChange`). The abstract kernel clause
`datumH0BaseChangeEquiv` (`GluedSheafEngine`) is threaded through the stage-(1d-ii) chart-term
identifications `termBaseChange`/`termBaseChange_tmul` (`GluedSheafTermBaseChangeEquiv`) onto
`H⁰` of the base-changed datum sheaf.

* `termBaseChange₀`/`termBaseChange₁`/`termBaseChangeInf` — the chart-term base changes at the
  two pinned charts and their overlap.
* `datumDomBaseChange` — the base change of the two-cover degree-zero term
  `F(V₀ᴮ) × F(V₁ᴮ)`.
* `datumDiffBaseChange` — **the δ-naturality square** (the glued analogue of
  `relTwistDiffBaseChange`; no cocycle conjugation — the componentwise restrictions commute
  with `sectionsMap` through `gluedRes_sectionsMap`).
* `datumH0BaseChange` — **`H⁰` base change on the nose**:
  `B' ⊗[B] H⁰(C_B, F_D) ≃ₗ[B'] H⁰(C_{B'}, F_{D'})` on the vanishing locus, for every ring map
  `B → B'` (`D' = D.baseChange B'`) — the on-the-nose form RE-5's DAT-B route consumes.
* `datum_subsingleton_h1_baseChange` — **`H¹` vanishes after base change** on the vanishing
  locus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
variable {π : C.left ⟶ P1 k} [IsFinite π]

namespace BasicOpenCocycleDatum

variable (D : BasicOpenCocycleDatum C B π)

/-! ## The chart-term base changes at the datum's charts -/

/-- The chart-term base change at the pinned chart `V₀ᴮ`. -/
noncomputable def termBaseChange₀ :
    B' ⊗[B] (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) ≃ₗ[B']
      ((D.baseChange B').sheaf.obj.obj (op (relCover C B' (fiberTwoCover π)).V₀)) := by
  letI : Scheme.QcohOn D.sheaf
      ((fst C (overSpec k B)).left ⁻¹ᵁ (fiberTwoCover π).V₀) := D.instQcohOn₀
  letI : Scheme.QcohOn (D.baseChange B').sheaf
      ((fst C (overSpec k B')).left ⁻¹ᵁ (fiberTwoCover π).V₀) := (D.baseChange B').instQcohOn₀
  exact D.termBaseChange B' (fiberTwoCover π).V₀ Sum.inl D.h₀
    (fiberTwoCover π).isAffineOpen₀.isCompact (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
    (relCover_isAffineOpen₀ C B (fiberTwoCover π)) (relCover_isAffineOpen₀ C B' (fiberTwoCover π))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => le_rfl) D.span_range_h₀

/-- The chart-term base change at the pinned chart `V₁ᴮ`. -/
noncomputable def termBaseChange₁ :
    B' ⊗[B] (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁)) ≃ₗ[B']
      ((D.baseChange B').sheaf.obj.obj (op (relCover C B' (fiberTwoCover π)).V₁)) := by
  letI : Scheme.QcohOn D.sheaf
      ((fst C (overSpec k B)).left ⁻¹ᵁ (fiberTwoCover π).V₁) := D.instQcohOn₁
  letI : Scheme.QcohOn (D.baseChange B').sheaf
      ((fst C (overSpec k B')).left ⁻¹ᵁ (fiberTwoCover π).V₁) := (D.baseChange B').instQcohOn₁
  exact D.termBaseChange B' (fiberTwoCover π).V₁ Sum.inr D.h₁
    (fiberTwoCover π).isAffineOpen₁.isCompact (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
    (relCover_isAffineOpen₁ C B (fiberTwoCover π)) (relCover_isAffineOpen₁ C B' (fiberTwoCover π))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => le_rfl) D.span_range_h₁

/-- The chart-term base change at the overlap `V₀ᴮ ⊓ V₁ᴮ` (side-0's restricted family). -/
noncomputable def termBaseChangeInf :
    B' ⊗[B] (D.sheaf.obj.obj (op ((relCover C B (fiberTwoCover π)).V₀ ⊓
        (relCover C B (fiberTwoCover π)).V₁))) ≃ₗ[B']
      ((D.baseChange B').sheaf.obj.obj (op ((relCover C B' (fiberTwoCover π)).V₀ ⊓
        (relCover C B' (fiberTwoCover π)).V₁))) := by
  letI : Scheme.QcohOn D.sheaf
      ((fst C (overSpec k B)).left ⁻¹ᵁ ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁)) :=
    gluedQcohOn B D.pieces D.unit D.isGluingCocycle (σ := Sum.inl) (h := D.hInf)
      D.basicOpen_hInf_le D.coverInf
  letI : Scheme.QcohOn (D.baseChange B').sheaf
      ((fst C (overSpec k B')).left ⁻¹ᵁ ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁)) :=
    gluedQcohOn B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle (σ := Sum.inl) (h := (D.baseChange B').hInf)
      (D.baseChange B').basicOpen_hInf_le (D.baseChange B').coverInf
  exact D.termBaseChange B' ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁) Sum.inl D.hInf
    (fiberTwoCover π).isAffineOpen_inf.isCompact
    (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
    (relCover C B (fiberTwoCover π)).isAffineOpen_inf
    (relCover C B' (fiberTwoCover π)).isAffineOpen_inf
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) D.basicOpen_hInf_le D.span_range_hInf

/-- The chart-`V₀ᴮ` term base change on a pure tensor. -/
theorem termBaseChange₀_tmul (b' : B')
    (s : D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) :
    D.termBaseChange₀ B' (b' ⊗ₜ[B] s) =
      b' • D.sectionsMap B' (le_preimage_chart B' (fiberTwoCover π).V₀) s := by
  letI : Scheme.QcohOn D.sheaf
      ((fst C (overSpec k B)).left ⁻¹ᵁ (fiberTwoCover π).V₀) := D.instQcohOn₀
  letI : Scheme.QcohOn (D.baseChange B').sheaf
      ((fst C (overSpec k B')).left ⁻¹ᵁ (fiberTwoCover π).V₀) := (D.baseChange B').instQcohOn₀
  exact D.termBaseChange_tmul B' (fiberTwoCover π).V₀ Sum.inl D.h₀
    (fiberTwoCover π).isAffineOpen₀.isCompact (fiberTwoCover π).isAffineOpen₀.isQuasiSeparated
    (relCover_isAffineOpen₀ C B (fiberTwoCover π)) (relCover_isAffineOpen₀ C B' (fiberTwoCover π))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => le_rfl) D.span_range_h₀ b' s

/-- The chart-`V₁ᴮ` term base change on a pure tensor. -/
theorem termBaseChange₁_tmul (b' : B')
    (s : D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁)) :
    D.termBaseChange₁ B' (b' ⊗ₜ[B] s) =
      b' • D.sectionsMap B' (le_preimage_chart B' (fiberTwoCover π).V₁) s := by
  letI : Scheme.QcohOn D.sheaf
      ((fst C (overSpec k B)).left ⁻¹ᵁ (fiberTwoCover π).V₁) := D.instQcohOn₁
  letI : Scheme.QcohOn (D.baseChange B').sheaf
      ((fst C (overSpec k B')).left ⁻¹ᵁ (fiberTwoCover π).V₁) := (D.baseChange B').instQcohOn₁
  exact D.termBaseChange_tmul B' (fiberTwoCover π).V₁ Sum.inr D.h₁
    (fiberTwoCover π).isAffineOpen₁.isCompact (fiberTwoCover π).isAffineOpen₁.isQuasiSeparated
    (relCover_isAffineOpen₁ C B (fiberTwoCover π)) (relCover_isAffineOpen₁ C B' (fiberTwoCover π))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => le_rfl) D.span_range_h₁ b' s

/-- The overlap term base change on a pure tensor. -/
theorem termBaseChangeInf_tmul (b' : B')
    (s : D.sheaf.obj.obj (op ((relCover C B (fiberTwoCover π)).V₀ ⊓
      (relCover C B (fiberTwoCover π)).V₁))) :
    D.termBaseChangeInf B' (b' ⊗ₜ[B] s) =
      b' • D.sectionsMap B'
        (le_preimage_chart B' ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁)) s := by
  letI : Scheme.QcohOn D.sheaf
      ((fst C (overSpec k B)).left ⁻¹ᵁ ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁)) :=
    gluedQcohOn B D.pieces D.unit D.isGluingCocycle (σ := Sum.inl) (h := D.hInf)
      D.basicOpen_hInf_le D.coverInf
  letI : Scheme.QcohOn (D.baseChange B').sheaf
      ((fst C (overSpec k B')).left ⁻¹ᵁ ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁)) :=
    gluedQcohOn B' (D.baseChange B').pieces (D.baseChange B').unit
      (D.baseChange B').isGluingCocycle (σ := Sum.inl) (h := (D.baseChange B').hInf)
      (D.baseChange B').basicOpen_hInf_le (D.baseChange B').coverInf
  exact D.termBaseChange_tmul B' ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁) Sum.inl D.hInf
    (fiberTwoCover π).isAffineOpen_inf.isCompact
    (fiberTwoCover π).isAffineOpen_inf.isQuasiSeparated
    (relCover C B (fiberTwoCover π)).isAffineOpen_inf
    (relCover C B' (fiberTwoCover π)).isAffineOpen_inf
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) D.basicOpen_hInf_le D.span_range_hInf b' s

/-! ## The degree-zero term base change and the δ-naturality square -/

/-- The base change of the two-cover degree-zero term `F(V₀ᴮ) × F(V₁ᴮ)`. -/
noncomputable def datumDomBaseChange :
    B' ⊗[B] ((D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) ×
        (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁))) ≃ₗ[B']
      ((D.baseChange B').sheaf.obj.obj (op (relCover C B' (fiberTwoCover π)).V₀)) ×
        ((D.baseChange B').sheaf.obj.obj (op (relCover C B' (fiberTwoCover π)).V₁)) :=
  (TensorProduct.prodRight B B' B' _ _).trans
    ((D.termBaseChange₀ B').prodCongr (D.termBaseChange₁ B'))

/-- The degree-zero term base change on a pure tensor. -/
lemma datumDomBaseChange_tmul (b' : B')
    (p : (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) ×
      (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁))) :
    D.datumDomBaseChange B' (b' ⊗ₜ[B] p) =
      (D.termBaseChange₀ B' (b' ⊗ₜ[B] p.1), D.termBaseChange₁ B' (b' ⊗ₜ[B] p.2)) := by
  rw [datumDomBaseChange, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The δ-naturality square** (the glued analogue of `relTwistDiffBaseChange`): the base
change of the datum's Čech differential over `B` is carried to the datum's Čech differential
over `B'` under the term identifications. There is no cocycle conjugation — the componentwise
restrictions commute with `sectionsMap` through `gluedRes_sectionsMap`. -/
theorem datumDiffBaseChange
    (x : B' ⊗[B] ((D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₀)) ×
      (D.sheaf.obj.obj (op (relCover C B (fiberTwoCover π)).V₁)))) :
    D.termBaseChangeInf B' (((datumPair D).diff).baseChange B' x) =
      (datumPair (D.baseChange B')).diff (D.datumDomBaseChange B' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b' p =>
    have hbc : ((datumPair D).diff).baseChange B' (b' ⊗ₜ[B] p) =
        b' ⊗ₜ[B] (datumPair D).diff p := LinearMap.baseChange_tmul _ _ _
    rw [hbc]
    simp only [D.datumDomBaseChange_tmul B', TwoLatticePair.diff_apply,
      D.termBaseChange₀_tmul B', D.termBaseChange₁_tmul B']
    rw [TensorProduct.tmul_sub, map_sub, D.termBaseChangeInf_tmul B',
      D.termBaseChangeInf_tmul B', map_smul, map_smul]
    congr 1
    · congr 1
      exact (D.gluedRes_sectionsMap B'
        (inf_le_left : (relCover C B (fiberTwoCover π)).V₀ ⊓
          (relCover C B (fiberTwoCover π)).V₁ ≤ (relCover C B (fiberTwoCover π)).V₀)
        (le_preimage_chart B' (fiberTwoCover π).V₀)
        (le_preimage_chart B' ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁))
        (inf_le_left : (relCover C B' (fiberTwoCover π)).V₀ ⊓
          (relCover C B' (fiberTwoCover π)).V₁ ≤ (relCover C B' (fiberTwoCover π)).V₀)
        p.1).symm
    · congr 1
      exact (D.gluedRes_sectionsMap B'
        (inf_le_right : (relCover C B (fiberTwoCover π)).V₀ ⊓
          (relCover C B (fiberTwoCover π)).V₁ ≤ (relCover C B (fiberTwoCover π)).V₁)
        (le_preimage_chart B' (fiberTwoCover π).V₁)
        (le_preimage_chart B' ((fiberTwoCover π).V₀ ⊓ (fiberTwoCover π).V₁))
        (inf_le_right : (relCover C B' (fiberTwoCover π)).V₀ ⊓
          (relCover C B' (fiberTwoCover π)).V₁ ≤ (relCover C B' (fiberTwoCover π)).V₁)
        p.2).symm

/-! ## The on-the-nose H⁰ base change and H¹ vanishing -/

open AlgebraicJacobian

/-- **`H⁰` base change on the nose** (DAT-1 (1d-ii) tail; the RE-5/DAT-B transport interface):
on the vanishing locus, for every ring map `B → B'`,

`B' ⊗[B] H⁰(C_B, F_D) ≃ₗ[B'] H⁰(C_{B'}, F_{D'})`

with `D' = D.baseChange B'` — the abstract kernel clause `datumH0BaseChangeEquiv` threaded
through the term identifications by the δ-naturality square `datumDiffBaseChange`. -/
noncomputable def datumH0BaseChange (hH1 : Subsingleton (datumPair D).H1) :
    B' ⊗[B] (Sheaf.HModule D.sheaf 0) ≃ₗ[B']
      Sheaf.HModule (D.baseChange B').sheaf 0 :=
  (datumH0BaseChangeEquiv D hH1 B').trans
    ((RigidEngine.kerCongr ((datumPair D).diff.baseChange B')
        ((datumPair (D.baseChange B')).diff)
        (D.datumDomBaseChange B') (D.termBaseChangeInf B')
        (fun x => D.datumDiffBaseChange B' x)).trans
      ((D.baseChange B').pairData.h0Equiv
        (relCover_isAffineOpen₀ C B' (fiberTwoCover π))
        (relCover_isAffineOpen₁ C B' (fiberTwoCover π))
        (relCover_sup C B' (fiberTwoCover π))).symm)

/-- **`H¹` vanishes after base change** on the vanishing locus: the base-changed Čech
differential is surjective (right-exactness of `B' ⊗[B] -` plus the δ-square), so `H¹` of the
base-changed datum sheaf vanishes. -/
theorem datum_subsingleton_h1_baseChange (hH1 : Subsingleton (datumPair D).H1) :
    Subsingleton (Sheaf.HModule (D.baseChange B').sheaf 1) := by
  have hsurj : Function.Surjective (datumPair D).diff :=
    D.pairData.surjective_diff (relCover_isAffineOpen₀ C B (fiberTwoCover π))
      (relCover_isAffineOpen₁ C B (fiberTwoCover π)) hH1
  have hbc : Function.Surjective ((datumPair D).diff.baseChange B') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective B' hsurj
  have hsurj' : Function.Surjective (datumPair (D.baseChange B')).diff :=
    RigidEngine.surjective_congr _ _ (D.datumDomBaseChange B') (D.termBaseChangeInf B')
      (fun x => D.datumDiffBaseChange B' x) hbc
  haveI : Subsingleton (datumPair (D.baseChange B')).H1 := by
    have h : (datumPair (D.baseChange B')).imageLattice = ⊤ := by
      rw [← (datumPair (D.baseChange B')).range_diff_eq, LinearMap.range_eq_top]
      exact hsurj'
    rw [TwoLatticePair.H1, h]
    infer_instance
  exact ((D.baseChange B').pairData.h1Equiv
    (relCover_isAffineOpen₀ C B' (fiberTwoCover π))
    (relCover_isAffineOpen₁ C B' (fiberTwoCover π))
    (relCover_sup C B' (fiberTwoCover π))).toEquiv.subsingleton

end BasicOpenCocycleDatum

end AlgebraicGeometry
