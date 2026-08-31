/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorThetaDatum
import AlgebraicJacobian.Cohomology.RelCurveCollapse

/-!
# G-0a — the class law of the theta-ideal datum (`informal/w4-g4-worksheet.md` §2.3)

The named residual of `Picard/DivisorThetaFibre.lean` (its "class-degree law" half): the
Čech Picard class of the twisted ideal datum `𝒪(Θᵃ − d)` of a divisor adaptation is the
theta class divided by the class of the divisor,

* `DivisorAdaptation.cechPicClass_thetaIdealDatum` —
  `(A.thetaIdealDatum a).cechPicClass = (thetaChartDatum C R π a).cechPicClass ·
  d.picClass⁻¹`.

Route: compute all three classes on the common pointed refinement
`𝒲 = (pieces through each point) ⊓ d.cover`.  There the subordinated cocycle of the
ideal datum is `eqnRatio · thetaOvlUnit` restricted; the `eqn_rel` comparison units
`u_{j,y}` (`f_j = u_{j,y} · e_y` on `D(h_j) ⊓ d.cover.opens y`) form a `0`-cochain
conjugating it into (theta cocycle) · (ratio cocycle of `d`)⁻¹:

`u_{i,x} · (f_j/f_i) · (e_x/e_y) = u_{j,y}`  (the master ratio identity, proved by
multiplying through by the regular restriction of `e_y` and cancelling), while the
`thetaOvlUnit` block agrees with the whole-chart `thetaChartUnit` restrictionwise in all
four chart cases.  The class equality is then `IsCohomologous.class_eq` plus the
`CechPic` group laws on a fixed cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {R : Type u} [CommRing R]
  [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

/-- The underlying section of a restricted unit is the restricted underlying section. -/
private lemma val_unitsRestrict {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U)
    (u : Γ(X, U)ˣ) :
    ((X.unitsRestrict h u : Γ(X, W)ˣ) : Γ(X, W)) = X.resHom h (u : Γ(X, U)) := rfl

/-- Restriction of units along inclusions composes. -/
private lemma unitsRestrict_unitsRestrict {X : Scheme.{u}} {U V W : X.Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    X.unitsRestrict h₂ (X.unitsRestrict h₁ u) = X.unitsRestrict (h₂.trans h₁) u :=
  Units.ext (Scheme.resHom_resHom h₁ h₂ (u : Γ(X, U)))

/-- The pair value of an inverse unit cocycle is the inverse pair value. -/
private lemma inv_unitsEvInf {X : Scheme.{u}} {𝒰 : X.PointedCover}
    (γ : X.unitsCocycle 𝒰) (i j : X) :
    Scheme.unitsEvInf γ⁻¹ i j = (Scheme.unitsEvInf γ i j)⁻¹ := rfl

namespace DivisorAdaptation

variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-! ## The comparison units of the refinement clause -/

/-- **The comparison unit of the pointwise refinement clause** `eqn_rel`: on
`D(h_j) ⊓ d.cover.opens y` the piece equation is `f_j = relUnit j y · e_y`. -/
noncomputable def relUnit (j : A.index) (y : relCurve C R) :
    Γ(relCurve C R, A.pieces j ⊓ d.cover.opens y)ˣ :=
  (A.eqn_rel j y).choose

/-- The defining equation of the comparison unit. -/
lemma res_eqn_eq_relUnit_mul (j : A.index) (y : relCurve C R) :
    (relCurve C R).resHom (inf_le_left : A.pieces j ⊓ d.cover.opens y ≤ A.pieces j)
        (A.eqn j)
      = (A.relUnit j y : Γ(relCurve C R, A.pieces j ⊓ d.cover.opens y))
        * (relCurve C R).resHom inf_le_right (d.eqn y) :=
  (A.eqn_rel j y).choose_spec

/-- The ratio equation of `d`, in `resHom` spelling. -/
private lemma res_d_ratio_eq (x y : relCurve C R) :
    (relCurve C R).resHom
        (inf_le_left : d.cover.opens x ⊓ d.cover.opens y ≤ d.cover.opens x) (d.eqn x)
      = (d.ratioUnit x y : Γ(relCurve C R, d.cover.opens x ⊓ d.cover.opens y))
        * (relCurve C R).resHom inf_le_right (d.eqn y) :=
  d.eqn_restrict_eq x y

/-- Regularity of the restricted equations of `d`, in `resHom` spelling. -/
private lemma res_d_eqn_mem_nonZeroDivisors (y : relCurve C R) {W : (relCurve C R).Opens}
    (hW : W ≤ d.cover.opens y) :
    (relCurve C R).resHom hW (d.eqn y) ∈ nonZeroDivisors Γ(relCurve C R, W) :=
  d.eqn_restrict_mem_nonZeroDivisors y hW

/-! ## The master ratio identity -/

/-- **The master ratio identity**: on any open below both `D(h_i) ⊓ d.cover.opens x`
and `D(h_j) ⊓ d.cover.opens y`,

`u_{i,x} · (f_j/f_i) · (e_x/e_y) = u_{j,y}`

(value form).  Multiplying through by the regular restriction of `e_y` turns each factor
into one of the defining equations of `relUnit`, `eqnRatio`, `ratioUnit`. -/
private lemma relUnit_mul_eqnRatio_mul_ratioUnit (i j : A.index) (x y : relCurve C R)
    {O : (relCurve C R).Opens}
    (hOx : O ≤ A.pieces i ⊓ d.cover.opens x) (hOy : O ≤ A.pieces j ⊓ d.cover.opens y) :
    (relCurve C R).resHom hOx
        ((A.relUnit i x : Γ(relCurve C R, A.pieces i ⊓ d.cover.opens x)))
      * (relCurve C R).resHom (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
          ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)))
      * (relCurve C R).resHom (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right))
          ((d.ratioUnit x y : Γ(relCurve C R, d.cover.opens x ⊓ d.cover.opens y)))
      = (relCurve C R).resHom hOy
          ((A.relUnit j y : Γ(relCurve C R, A.pieces j ⊓ d.cover.opens y))) := by
  refine (mul_cancel_right_mem_nonZeroDivisors
    (res_d_eqn_mem_nonZeroDivisors (d := d) y (hOy.trans inf_le_right))).mp ?_
  -- the transported defining equations
  have h₁ : (relCurve C R).resHom
        (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right))
        ((d.ratioUnit x y : Γ(relCurve C R, d.cover.opens x ⊓ d.cover.opens y)))
      * (relCurve C R).resHom (hOy.trans inf_le_right) (d.eqn y)
      = (relCurve C R).resHom (hOx.trans inf_le_right) (d.eqn x) := by
    have h := congrArg ((relCurve C R).resHom
      (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right)))
      (res_d_ratio_eq (d := d) x y)
    rw [map_mul, Scheme.resHom_resHom, Scheme.resHom_resHom] at h
    exact h.symm
  have h₂ : (relCurve C R).resHom hOx
        ((A.relUnit i x : Γ(relCurve C R, A.pieces i ⊓ d.cover.opens x)))
      * (relCurve C R).resHom (hOx.trans inf_le_right) (d.eqn x)
      = (relCurve C R).resHom (hOx.trans inf_le_left) (A.eqn i) := by
    have h := congrArg ((relCurve C R).resHom hOx) (A.res_eqn_eq_relUnit_mul i x)
    rw [map_mul, Scheme.resHom_resHom, Scheme.resHom_resHom] at h
    exact h.symm
  have h₃ : (relCurve C R).resHom hOy
        ((A.relUnit j y : Γ(relCurve C R, A.pieces j ⊓ d.cover.opens y)))
      * (relCurve C R).resHom (hOy.trans inf_le_right) (d.eqn y)
      = (relCurve C R).resHom (hOy.trans inf_le_left) (A.eqn j) := by
    have h := congrArg ((relCurve C R).resHom hOy) (A.res_eqn_eq_relUnit_mul j y)
    rw [map_mul, Scheme.resHom_resHom, Scheme.resHom_resHom] at h
    exact h.symm
  have h₄ : (relCurve C R).resHom (hOx.trans inf_le_left) (A.eqn i)
      * (relCurve C R).resHom (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
          ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)))
      = (relCurve C R).resHom (hOy.trans inf_le_left) (A.eqn j) := by
    have h := congrArg ((relCurve C R).resHom
      (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))) (A.eqn_mul_eqnRatio i j)
    rw [map_mul, Scheme.resHom_resHom, Scheme.resHom_resHom] at h
    exact h
  calc (relCurve C R).resHom hOx
          ((A.relUnit i x : Γ(relCurve C R, A.pieces i ⊓ d.cover.opens x)))
        * (relCurve C R).resHom (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
            ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)))
        * (relCurve C R).resHom
            (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right))
            ((d.ratioUnit x y : Γ(relCurve C R, d.cover.opens x ⊓ d.cover.opens y)))
        * (relCurve C R).resHom (hOy.trans inf_le_right) (d.eqn y)
      = (relCurve C R).resHom (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
            ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)))
          * ((relCurve C R).resHom hOx
              ((A.relUnit i x : Γ(relCurve C R, A.pieces i ⊓ d.cover.opens x)))
            * ((relCurve C R).resHom
                (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right))
                ((d.ratioUnit x y :
                  Γ(relCurve C R, d.cover.opens x ⊓ d.cover.opens y)))
              * (relCurve C R).resHom (hOy.trans inf_le_right) (d.eqn y))) := by ring
    _ = (relCurve C R).resHom (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
            ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)))
          * ((relCurve C R).resHom hOx
              ((A.relUnit i x : Γ(relCurve C R, A.pieces i ⊓ d.cover.opens x)))
            * (relCurve C R).resHom (hOx.trans inf_le_right) (d.eqn x)) := by rw [h₁]
    _ = (relCurve C R).resHom (hOx.trans inf_le_left) (A.eqn i)
          * (relCurve C R).resHom (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
              ((A.eqnRatio i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j))) := by
        rw [h₂]; ring
    _ = (relCurve C R).resHom (hOy.trans inf_le_left) (A.eqn j) := h₄
    _ = (relCurve C R).resHom hOy
            ((A.relUnit j y : Γ(relCurve C R, A.pieces j ⊓ d.cover.opens y)))
          * (relCurve C R).resHom (hOy.trans inf_le_right) (d.eqn y) := h₃.symm

/-- The master identity at the ideal transition unit (units form): the comparison units
conjugate `thetaIdealUnit = eqnRatio · thetaOvlUnit` into
`thetaOvlUnit · ratioUnit⁻¹`. -/
private lemma relUnit_mul_thetaIdealUnit_mul_ratioUnit (a : ℕ) (i j : A.index)
    (x y : relCurve C R) {O : (relCurve C R).Opens}
    (hOx : O ≤ A.pieces i ⊓ d.cover.opens x) (hOy : O ≤ A.pieces j ⊓ d.cover.opens y) :
    (relCurve C R).unitsRestrict hOx (A.relUnit i x)
      * (relCurve C R).unitsRestrict
          (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
          (A.thetaIdealUnit a i j)
      * (relCurve C R).unitsRestrict
          (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right)) (d.ratioUnit x y)
      = (relCurve C R).unitsRestrict
          (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
          (A.thetaOvlUnit a i j)
        * (relCurve C R).unitsRestrict hOy (A.relUnit j y) := by
  have hmv := A.relUnit_mul_eqnRatio_mul_ratioUnit i j x y hOx hOy
  refine Units.ext ?_
  simp only [Units.val_mul, val_unitsRestrict, DivisorAdaptation.thetaIdealUnit,
    map_mul]
  linear_combination ((relCurve C R).resHom
    (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
    ((A.thetaOvlUnit a i j : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)))) * hmv

/-! ## The theta block against the whole-chart theta datum -/

/-- The chart side of a theta-ideal-datum index. -/
def thetaSide (a : ℕ) : (A.thetaIdealDatum a).index → (thetaChartCover C R π).index
  | Sum.inl _ => Sum.inl PUnit.unit
  | Sum.inr _ => Sum.inr PUnit.unit

@[simp]
lemma thetaSide_inl (a : ℕ) (i : ULift.{u} (Fin A.m₀)) :
    A.thetaSide a (Sum.inl i) = Sum.inl PUnit.unit := rfl

@[simp]
lemma thetaSide_inr (a : ℕ) (i : ULift.{u} (Fin A.m₁)) :
    A.thetaSide a (Sum.inr i) = Sum.inr PUnit.unit := rfl

/-- Each piece of the theta-ideal datum sits inside its whole pinned chart. -/
lemma thetaIdealDatum_pieces_le_chart (a : ℕ) (i : (A.thetaIdealDatum a).index) :
    (A.thetaIdealDatum a).pieces i
      ≤ (thetaChartCover C R π).pieces (A.thetaSide a i) := by
  rcases i with i | i
  · rw [A.thetaIdealDatum_pieces_inl, A.thetaSide_inl, thetaChartCover_pieces_inl]
    exact A.toFinCoverData.pieces_inl_le i.down
  · rw [A.thetaIdealDatum_pieces_inr, A.thetaSide_inr, thetaChartCover_pieces_inr]
    exact A.toFinCoverData.pieces_inr_le i.down

/-- The theta twisting unit of two chart-0 pieces agrees with the whole-chart theta
unit, restrictionwise. -/
private lemma theta_chart_inl_inl (a : ℕ) (i j : Fin A.m₀) {O : (relCurve C R).Opens}
    (hOc : O ≤ (thetaChartCover C R π).pieces (Sum.inl PUnit.unit)
      ⊓ (thetaChartCover C R π).pieces (Sum.inl PUnit.unit))
    (hOp : O ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inl j)) :
    (relCurve C R).unitsRestrict hOc
        (thetaChartUnit C R π a (Sum.inl PUnit.unit) (Sum.inl PUnit.unit))
      = (relCurve C R).unitsRestrict hOp (A.thetaOvlUnit a (Sum.inl i) (Sum.inl j)) := by
  rw [A.toFinCoverData.thetaOvlUnit_inl_inl,
    show thetaChartUnit C R π a (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) = 1 from rfl,
    map_one, map_one]

/-- The theta twisting unit of two chart-1 pieces agrees with the whole-chart theta
unit, restrictionwise. -/
private lemma theta_chart_inr_inr (a : ℕ) (i j : Fin A.m₁) {O : (relCurve C R).Opens}
    (hOc : O ≤ (thetaChartCover C R π).pieces (Sum.inr PUnit.unit)
      ⊓ (thetaChartCover C R π).pieces (Sum.inr PUnit.unit))
    (hOp : O ≤ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inr j)) :
    (relCurve C R).unitsRestrict hOc
        (thetaChartUnit C R π a (Sum.inr PUnit.unit) (Sum.inr PUnit.unit))
      = (relCurve C R).unitsRestrict hOp (A.thetaOvlUnit a (Sum.inr i) (Sum.inr j)) := by
  rw [A.toFinCoverData.thetaOvlUnit_inr_inr,
    show thetaChartUnit C R π a (Sum.inr PUnit.unit) (Sum.inr PUnit.unit) = 1 from rfl,
    map_one, map_one]

/-- The cross-chart theta twisting unit agrees with the whole-chart theta unit,
restrictionwise: both restrict the relative theta cocycle. -/
private lemma theta_chart_inl_inr (a : ℕ) (i : Fin A.m₀) (j : Fin A.m₁)
    {O : (relCurve C R).Opens}
    (hOc : O ≤ (thetaChartCover C R π).pieces (Sum.inl PUnit.unit)
      ⊓ (thetaChartCover C R π).pieces (Sum.inr PUnit.unit))
    (hOp : O ≤ A.pieces (Sum.inl i) ⊓ A.pieces (Sum.inr j)) :
    (relCurve C R).unitsRestrict hOc
        (thetaChartUnit C R π a (Sum.inl PUnit.unit) (Sum.inr PUnit.unit))
      = (relCurve C R).unitsRestrict hOp (A.thetaOvlUnit a (Sum.inl i) (Sum.inr j)) := by
  rw [A.toFinCoverData.thetaOvlUnit_inl_inr,
    show thetaChartUnit C R π a (Sum.inl PUnit.unit) (Sum.inr PUnit.unit)
        = (relCurve C R).unitsRestrict
            (inf_le_inf (thetaChartCover_pieces_le_inl C R π PUnit.unit)
              (thetaChartCover_pieces_le_inr C R π PUnit.unit))
            (relThetaCocycle C R π a) from rfl,
    unitsRestrict_unitsRestrict, unitsRestrict_unitsRestrict]

/-- The reverse cross-chart theta twisting unit agrees with the whole-chart theta unit,
restrictionwise: both restrict the inverse relative theta cocycle. -/
private lemma theta_chart_inr_inl (a : ℕ) (i : Fin A.m₁) (j : Fin A.m₀)
    {O : (relCurve C R).Opens}
    (hOc : O ≤ (thetaChartCover C R π).pieces (Sum.inr PUnit.unit)
      ⊓ (thetaChartCover C R π).pieces (Sum.inl PUnit.unit))
    (hOp : O ≤ A.pieces (Sum.inr i) ⊓ A.pieces (Sum.inl j)) :
    (relCurve C R).unitsRestrict hOc
        (thetaChartUnit C R π a (Sum.inr PUnit.unit) (Sum.inl PUnit.unit))
      = (relCurve C R).unitsRestrict hOp (A.thetaOvlUnit a (Sum.inr i) (Sum.inl j)) := by
  rw [A.toFinCoverData.thetaOvlUnit_inr_inl,
    show thetaChartUnit C R π a (Sum.inr PUnit.unit) (Sum.inl PUnit.unit)
        = (relCurve C R).unitsRestrict
            (le_inf
              (inf_le_right.trans (thetaChartCover_pieces_le_inl C R π PUnit.unit))
              (inf_le_left.trans (thetaChartCover_pieces_le_inr C R π PUnit.unit)))
            (relThetaCocycle C R π a)⁻¹ from rfl]
  simp only [map_inv, unitsRestrict_unitsRestrict]

/-! ## The master identity at the datum index -/

/-- **The master identity at the datum index**: the `eqn_rel` comparison units conjugate
the transition units of the theta-ideal datum into the whole-chart theta units divided
by the ratio units of `d`.  Value shape `L₁ · L₂ · ρ = θ · L₃`, quantified over an
arbitrary common open `O`. -/
private lemma datum_master (a : ℕ) (i j : (A.thetaIdealDatum a).index)
    (x y : relCurve C R) {O : (relCurve C R).Opens}
    (hOx : O ≤ (A.thetaIdealDatum a).pieces i ⊓ d.cover.opens x)
    (hOy : O ≤ (A.thetaIdealDatum a).pieces j ⊓ d.cover.opens y) :
    (relCurve C R).unitsRestrict
        (hOx.trans (inf_le_inf (le_of_eq (A.thetaIdealDatum_pieces a i)) le_rfl))
        (A.relUnit (A.lowerIndex a i) x)
      * (relCurve C R).unitsRestrict
          (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))
          ((A.thetaIdealDatum a).unit i j)
      * (relCurve C R).unitsRestrict
          (le_inf (hOx.trans inf_le_right) (hOy.trans inf_le_right)) (d.ratioUnit x y)
      = (relCurve C R).unitsRestrict
          (le_inf ((hOx.trans inf_le_left).trans (A.thetaIdealDatum_pieces_le_chart a i))
            ((hOy.trans inf_le_left).trans (A.thetaIdealDatum_pieces_le_chart a j)))
          (thetaChartUnit C R π a (A.thetaSide a i) (A.thetaSide a j))
        * (relCurve C R).unitsRestrict
            (hOy.trans (inf_le_inf (le_of_eq (A.thetaIdealDatum_pieces a j)) le_rfl))
            (A.relUnit (A.lowerIndex a j) y) := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [thetaSide_inl, thetaSide_inr]
  · rw [A.theta_chart_inl_inl a i.down j.down _
      (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))]
    exact A.relUnit_mul_thetaIdealUnit_mul_ratioUnit a (Sum.inl i.down) (Sum.inl j.down)
      x y hOx hOy
  · rw [A.theta_chart_inl_inr a i.down j.down _
      (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))]
    exact A.relUnit_mul_thetaIdealUnit_mul_ratioUnit a (Sum.inl i.down) (Sum.inr j.down)
      x y hOx hOy
  · rw [A.theta_chart_inr_inl a i.down j.down _
      (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))]
    exact A.relUnit_mul_thetaIdealUnit_mul_ratioUnit a (Sum.inr i.down) (Sum.inl j.down)
      x y hOx hOy
  · rw [A.theta_chart_inr_inr a i.down j.down _
      (le_inf (hOx.trans inf_le_left) (hOy.trans inf_le_left))]
    exact A.relUnit_mul_thetaIdealUnit_mul_ratioUnit a (Sum.inr i.down) (Sum.inr j.down)
      x y hOx hOy

/-! ## The class law -/

/-- **G-0a — the class law of the theta-ideal datum** (`informal/w4-g4-worksheet.md`
§2.3, the named residual of `Picard/DivisorThetaFibre.lean`): the Čech Picard class of
the twisted ideal datum `𝒪(Θᵃ − d)` of a divisor adaptation is the whole-chart theta
class divided by the Picard class of the divisor,

`[𝒪(Θᵃ − d)] = [Θᵃ] · [𝒪(d)]⁻¹`.

All three classes are computed on the common pointed refinement
`(piece through each point) ⊓ d.cover`, where the `eqn_rel` comparison units form the
conjugating `0`-cochain. -/
theorem cechPicClass_thetaIdealDatum (a : ℕ) :
    (A.thetaIdealDatum a).cechPicClass
      = (thetaChartDatum C R π a).cechPicClass * d.picClass⁻¹ := by
  classical
  -- the common pointed refinement
  set 𝒲 : (relCurve C R).PointedCover :=
    (A.thetaIdealDatum a).pointedCover ⊓ d.cover with h𝒲
  have hσ : ∀ x, 𝒲.opens x
      ≤ (A.thetaIdealDatum a).pieces ((A.thetaIdealDatum a).pieceIndex x) :=
    fun _ => inf_le_left
  have hσθ : ∀ x, 𝒲.opens x ≤ (thetaChartDatum C R π a).pieces
      (A.thetaSide a ((A.thetaIdealDatum a).pieceIndex x)) :=
    fun x => (hσ x).trans (A.thetaIdealDatum_pieces_le_chart a _)
  have h𝒲d : 𝒲 ≤ d.cover := fun _ => inf_le_right
  -- the three subordinated cocycles
  set γ := gluedSubordCocycle (A.thetaIdealDatum a).isGluingCocycle 𝒲
    (A.thetaIdealDatum a).pieceIndex hσ with hγ
  set γθ := gluedSubordCocycle (thetaChartDatum C R π a).isGluingCocycle 𝒲
    (fun x => A.thetaSide a ((A.thetaIdealDatum a).pieceIndex x)) hσθ with hγθ
  set γd := d.unitsCocycle.res (fun x => homOfLE (h𝒲d x)) with hγd
  -- the eqn_rel comparison units conjugate γ into γθ · γd⁻¹
  have hcoh : γ.IsCohomologous (γθ * γd⁻¹) := by
    refine Scheme.unitsCocycle_isCohomologous
      (fun x => (relCurve C R).unitsRestrict
        (inf_le_inf (le_of_eq (A.thetaIdealDatum_pieces a _)) le_rfl :
          𝒲.opens x ≤ A.pieces
            (A.lowerIndex a ((A.thetaIdealDatum a).pieceIndex x)) ⊓ d.cover.opens x)
        (A.relUnit (A.lowerIndex a ((A.thetaIdealDatum a).pieceIndex x)) x))
      (fun x y => ?_)
    have key := A.datum_master a ((A.thetaIdealDatum a).pieceIndex x)
      ((A.thetaIdealDatum a).pieceIndex y) x y
      (O := 𝒲.opens x ⊓ 𝒲.opens y) inf_le_left inf_le_right
    -- the collapsed conjugating factors
    have hUx := unitsRestrict_unitsRestrict
      (inf_le_inf (le_of_eq (A.thetaIdealDatum_pieces a
          ((A.thetaIdealDatum a).pieceIndex x))) le_rfl :
        𝒲.opens x ≤ A.pieces (A.lowerIndex a ((A.thetaIdealDatum a).pieceIndex x))
          ⊓ d.cover.opens x)
      (inf_le_left : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens x)
      (A.relUnit (A.lowerIndex a ((A.thetaIdealDatum a).pieceIndex x)) x)
    have hUy := unitsRestrict_unitsRestrict
      (inf_le_inf (le_of_eq (A.thetaIdealDatum_pieces a
          ((A.thetaIdealDatum a).pieceIndex y))) le_rfl :
        𝒲.opens y ≤ A.pieces (A.lowerIndex a ((A.thetaIdealDatum a).pieceIndex y))
          ⊓ d.cover.opens y)
      (inf_le_right : 𝒲.opens x ⊓ 𝒲.opens y ≤ 𝒲.opens y)
      (A.relUnit (A.lowerIndex a ((A.thetaIdealDatum a).pieceIndex y)) y)
    -- the three pair values
    have hevγ : Scheme.unitsEvInf γ x y
        = (relCurve C R).unitsRestrict
            (le_inf (inf_le_left.trans (hσ x)) (inf_le_right.trans (hσ y)))
            ((A.thetaIdealDatum a).unit ((A.thetaIdealDatum a).pieceIndex x)
              ((A.thetaIdealDatum a).pieceIndex y)) :=
      gluedSubordCocycle_evInf (A.thetaIdealDatum a).isGluingCocycle 𝒲
        (A.thetaIdealDatum a).pieceIndex hσ x y
    have hevθ : Scheme.unitsEvInf γθ x y
        = (relCurve C R).unitsRestrict
            (le_inf (inf_le_left.trans (hσθ x)) (inf_le_right.trans (hσθ y)))
            (thetaChartUnit C R π a
              (A.thetaSide a ((A.thetaIdealDatum a).pieceIndex x))
              (A.thetaSide a ((A.thetaIdealDatum a).pieceIndex y))) :=
      gluedSubordCocycle_evInf (thetaChartDatum C R π a).isGluingCocycle 𝒲
        (fun z => A.thetaSide a ((A.thetaIdealDatum a).pieceIndex z)) hσθ x y
    have hevd : Scheme.unitsEvInf γd x y
        = (relCurve C R).unitsRestrict (inf_le_inf (h𝒲d x) (h𝒲d y))
            (d.ratioUnit x y) :=
      (Scheme.res_unitsEvInf h𝒲d d.unitsCocycle x y).trans
        (congrArg ((relCurve C R).unitsRestrict (inf_le_inf (h𝒲d x) (h𝒲d y)))
          (d.unitsCocycle_evInf x y))
    exact (congrArg₂ (· * ·) hUx hevγ).trans
      (((mul_inv_cancel_right _ _).symm.trans
        ((congrArg (fun t => t * ((relCurve C R).unitsRestrict
            (inf_le_inf (h𝒲d x) (h𝒲d y)) (d.ratioUnit x y))⁻¹) key).trans
          (mul_right_comm _ _ _))).trans
        (congrArg₂ (· * ·)
          (congrArg₂ (fun s t => s * t⁻¹) hevθ.symm hevd.symm) hUy.symm))
  -- assemble the classes on the common cover
  have hmk : Scheme.CechPic.mk 𝒲 γ.class = Scheme.CechPic.mk 𝒲 (γθ * γd⁻¹).class :=
    congrArg (Scheme.CechPic.mk 𝒲) hcoh.class_eq
  have hdleg : Scheme.CechPic.mk 𝒲 γd.class = d.picClass := by
    have h1 : γd.class = Scheme.unitsRes h𝒲d d.unitsCocycle.class :=
      (H1.res_class (fun x => homOfLE (h𝒲d x)) d.unitsCocycle).symm
    rw [h1]
    exact Scheme.CechPic.mk_unitsRes h𝒲d d.unitsCocycle.class
  calc (A.thetaIdealDatum a).cechPicClass
      = Scheme.CechPic.mk 𝒲 γ.class :=
        ((A.thetaIdealDatum a).cechPicClass_eq_mk 𝒲
          (A.thetaIdealDatum a).pieceIndex hσ).symm
    _ = Scheme.CechPic.mk 𝒲 (γθ * γd⁻¹).class := hmk
    _ = Scheme.CechPic.mk 𝒲 γθ.class * (Scheme.CechPic.mk 𝒲 γd.class)⁻¹ := by
        rw [OneCocycle.class_mul, OneCocycle.class_inv, ← Scheme.CechPic.mk_mul_mk,
          ← Scheme.CechPic.mk_inv]
    _ = (thetaChartDatum C R π a).cechPicClass * d.picClass⁻¹ := by
        rw [(thetaChartDatum C R π a).cechPicClass_eq_mk 𝒲
          (fun x => A.thetaSide a ((A.thetaIdealDatum a).pieceIndex x)) hσθ, hdleg]

end DivisorAdaptation

end AlgebraicGeometry
