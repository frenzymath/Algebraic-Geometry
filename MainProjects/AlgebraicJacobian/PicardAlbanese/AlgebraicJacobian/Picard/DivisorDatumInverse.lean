/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFibreH1
import AlgebraicJacobian.Picard.SectionsToDivisorsClass

/-!
# DAT-C C0 — the datum inverse, the divisor datum, and the canonical section
(`informal/w4-datc-worksheet.md` GAP-1 + §2 (N2))

Every landed datum built from a divisor family is the *twisted ideal* datum
`𝒪(Θᵃ − d)` of class `θᵃ·[d]⁻¹` (G-0a). DAT-C's normalization layer needs a datum in
the class `[𝒪(d)]` itself, together with its canonical section. This file pins both:

* `AlgebraicGeometry.BasicOpenCocycleDatum.inv` — the **datum inverse**: same cover
  data, transition units `(g i j)⁻¹`; the cocycle law inverts termwise.
* `BasicOpenCocycleDatum.cechPicClass_inv` — the class law
  `D.inv.cechPicClass = D.cechPicClass⁻¹` (subordinated-cocycle level).
* `AlgebraicGeometry.relThetaCocycle_zero`, `FinCoverData.thetaOvlUnit_zero`,
  `thetaChartUnit_zero`, `cechPicClass_thetaChartDatum_zero` — at exponent `a = 0`
  the theta twisting cocycle is trivial, so the whole-chart theta datum has class `1`
  **over an arbitrary test ring** (the worksheet cites the base-`k` class law
  `cechPicClass_thetaChartDatum` + `fiberTwist_zero`; the direct `a = 0` computation
  is ring-generic, which the §2 consumers need — recorded deviation).
* `DivisorAdaptation.divisorDatum` — **the divisor datum**
  `(A.thetaIdealDatum 0).inv`, with class law
  `cechPicClass_divisorDatum : A.divisorDatum.cechPicClass = d.picClass`
  (G-0a at `a = 0` + the trivial theta block + `cechPicClass_inv`).
* `DivisorAdaptation.canonSection` — **the canonical section is the equation system
  itself** (N2): the components `(A.eqn j)` satisfy the inverse-datum matching
  condition (`eqn_mul_eqnRatio` read against the inverted units), giving a global
  section of the divisor datum's glued sheaf.
* `DivisorAdaptation.divEq_sectionLocalEquations_canonSection` — **(N2) cut-back by
  pure refinement**: the `LocalEquations` datum cut by `canonSection` (DAT-A
  `sectionLocalEquations`, on any subordinated pointed cover) is `DivEq` to `d` —
  the comparison units are the adaptation's own `eqn_rel` units; no fibre argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite
open CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} {B : Type u} [CommRing B]
  [Algebra k B]

/-! ## The datum inverse -/

namespace BasicOpenCocycleDatum

variable {π : C.left ⟶ P1 k} [IsAffineHom π]

/-- The pair value of an inverse unit cocycle is the inverse pair value. -/
private lemma inv_unitsEvInf {X : Scheme.{u}} {𝒰 : X.PointedCover}
    (γ : X.unitsCocycle 𝒰) (i j : X) :
    Scheme.unitsEvInf γ⁻¹ i j = (Scheme.unitsEvInf γ i j)⁻¹ := rfl

/-- The unit-level cocycle identity of a datum (the value-level law `mul_res`
re-packaged through `Units.ext`). -/
private lemma unitsRestrict_unit_mul (D : BasicOpenCocycleDatum C B π)
    (i j l : D.index) :
    (relCurve C B).unitsRestrict
        (inf_le_left : D.pieces i ⊓ D.pieces j ⊓ D.pieces l ≤ D.pieces i ⊓ D.pieces j)
        (D.unit i j)
      * (relCurve C B).unitsRestrict (gluedInclCoc D.pieces (D.pieces i) j l)
          (D.unit j l)
      = (relCurve C B).unitsRestrict (gluedInclSnd D.pieces (D.pieces i) j l)
          (D.unit i l) :=
  Units.ext (D.isGluingCocycle.mul_res i j l)

/-- **The datum inverse** (worksheet GAP-1): the same basic-open cover data with the
termwise-inverted transition units `(g i j)⁻¹`. The cocycle law inverts termwise —
the units are honest `Units`, and the section rings are commutative. -/
noncomputable def inv (D : BasicOpenCocycleDatum C B π) :
    BasicOpenCocycleDatum C B π where
  toBasicOpenCoverData := D.toBasicOpenCoverData
  unit i j := (D.unit i j)⁻¹
  isGluingCocycle := by
    constructor
    · intro i
      rw [show D.unit i i = 1 from Units.ext (D.isGluingCocycle.unit_self i), inv_one,
        Units.val_one]
    · intro i j l
      have key : ((relCurve C B).unitsRestrict
            (inf_le_left :
              D.pieces i ⊓ D.pieces j ⊓ D.pieces l ≤ D.pieces i ⊓ D.pieces j)
            (D.unit i j))⁻¹
          * ((relCurve C B).unitsRestrict (gluedInclCoc D.pieces (D.pieces i) j l)
              (D.unit j l))⁻¹
          = ((relCurve C B).unitsRestrict (gluedInclSnd D.pieces (D.pieces i) j l)
              (D.unit i l))⁻¹ := by
        rw [← mul_inv]
        exact congrArg (·⁻¹) (D.unitsRestrict_unit_mul i j l)
      have hval := congrArg Units.val key
      rw [Units.val_mul] at hval
      exact hval

@[simp]
lemma inv_pieces (D : BasicOpenCocycleDatum C B π) : D.inv.pieces = D.pieces := rfl

@[simp]
lemma inv_unit (D : BasicOpenCocycleDatum C B π) (i j : D.index) :
    D.inv.unit i j = (D.unit i j)⁻¹ := rfl

/-- **The class law of the datum inverse**: `[D⁻¹] = [D]⁻¹`. Both classes are computed
by subordinated cocycles on `D`'s canonical pointed cover by pieces, where the
subordinated cocycle of the inverse datum is the inverse cocycle. -/
theorem cechPicClass_inv (D : BasicOpenCocycleDatum C B π) :
    D.inv.cechPicClass = D.cechPicClass⁻¹ := by
  have hσ : ∀ x : relCurve C B,
      D.pointedCover.opens x ≤ D.inv.pieces (D.pieceIndex x) :=
    fun _ => le_rfl
  have hco : gluedSubordCocycle D.inv.isGluingCocycle D.pointedCover D.pieceIndex hσ
      = (gluedSubordCocycle D.isGluingCocycle D.pointedCover D.pieceIndex
          (fun _ => le_rfl))⁻¹ := by
    refine Scheme.unitsCocycle_ext fun x y => ?_
    rw [gluedSubordCocycle_evInf, inv_unitsEvInf, gluedSubordCocycle_evInf]
    exact Units.ext rfl
  calc D.inv.cechPicClass
      = Scheme.CechPic.mk D.pointedCover
          (gluedSubordCocycle D.inv.isGluingCocycle D.pointedCover D.pieceIndex
            hσ).class :=
        (D.inv.cechPicClass_eq_mk D.pointedCover D.pieceIndex hσ).symm
    _ = Scheme.CechPic.mk D.pointedCover
          ((gluedSubordCocycle D.isGluingCocycle D.pointedCover D.pieceIndex
            (fun _ => le_rfl)).class)⁻¹ := by
        rw [hco, OneCocycle.class_inv]
    _ = D.cechPicClass⁻¹ := rfl

end BasicOpenCocycleDatum

/-! ## The theta block is trivial at exponent zero -/

section ThetaZero

variable {π : C.left ⟶ P1 k} [IsFinite π]

/-- The relative theta cocycle at exponent `0` is the trivial unit: `t₀⁰ = 1`. -/
theorem relThetaCocycle_zero : relThetaCocycle C B π 0 = 1 := by
  change relUnitCocycle C B (fiberTwoCover π) (thetaUnit π ^ 0) = 1
  rw [pow_zero]
  exact map_one _

/-- The theta twisting units of a finite cover datum are trivial at exponent `0`. -/
theorem FinCoverData.thetaOvlUnit_zero (D : FinCoverData C B π) (i j : D.index) :
    D.thetaOvlUnit 0 i j = 1 := by
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rw [FinCoverData.thetaOvlUnit_inl_inr, relThetaCocycle_zero, map_one]
  · rw [FinCoverData.thetaOvlUnit_inr_inl, relThetaCocycle_zero, map_one, inv_one]
  · rfl

/-- The whole-chart theta transition units are trivial at exponent `0`. -/
theorem thetaChartUnit_zero (i j : (thetaChartCover C B π).index) :
    thetaChartUnit C B π 0 i j = 1 := by
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · change (relCurve C B).unitsRestrict _ (relThetaCocycle C B π 0) = 1
    rw [relThetaCocycle_zero, map_one]
  · change (relCurve C B).unitsRestrict _ (relThetaCocycle C B π 0)⁻¹ = 1
    rw [relThetaCocycle_zero, inv_one, map_one]
  · rfl

/-- **The whole-chart theta datum has trivial class at exponent `0`, over an arbitrary
test ring**: all its transition units are `1`, so the subordinated cocycle is the
trivial cocycle. (Ring-generic strengthening of the base-`k` route
`cechPicClass_thetaChartDatum` + `fiberTwist_zero`.) -/
theorem cechPicClass_thetaChartDatum_zero :
    (thetaChartDatum C B π 0).cechPicClass = 1 := by
  have hco : gluedSubordCocycle (thetaChartDatum C B π 0).isGluingCocycle
      (thetaChartDatum C B π 0).pointedCover (thetaChartDatum C B π 0).pieceIndex
      (fun _ => le_rfl) = 1 := by
    refine Scheme.unitsCocycle_ext fun x y => ?_
    rw [gluedSubordCocycle_evInf, Scheme.one_unitsEvInf]
    change (relCurve C B).unitsRestrict _
        (thetaChartUnit C B π 0 ((thetaChartDatum C B π 0).pieceIndex x)
          ((thetaChartDatum C B π 0).pieceIndex y)) = 1
    rw [thetaChartUnit_zero, map_one]
  change Scheme.CechPic.mk (thetaChartDatum C B π 0).pointedCover
      (gluedSubordCocycle (thetaChartDatum C B π 0).isGluingCocycle
        (thetaChartDatum C B π 0).pointedCover (thetaChartDatum C B π 0).pieceIndex
        (fun _ => le_rfl)).class = 1
  rw [hco, OneCocycle.class_one, Scheme.CechPic.mk_one]

end ThetaZero

/-! ## The divisor datum and its class law -/

namespace DivisorAdaptation

variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable {d : (relCurve C R).LocalEquations} (A : DivisorAdaptation C R π d)

/-- The ideal transition units at exponent `0` are the plain ratio units `f_j/f_i`:
the theta block is trivial. -/
theorem thetaIdealUnit_zero (i j : A.index) :
    A.thetaIdealUnit 0 i j = A.eqnRatio i j := by
  rw [thetaIdealUnit, A.toFinCoverData.thetaOvlUnit_zero, mul_one]

/-- **The divisor datum of an adaptation** (worksheet GAP-1): the inverse of the
twisted ideal datum at exponent `0` — a pinned cocycle datum in the class `[𝒪(d)]`
(`cechPicClass_divisorDatum`), whose transition units are the inverted ratio units
`(f_j/f_i)⁻¹`. -/
noncomputable def divisorDatum : BasicOpenCocycleDatum C R π :=
  (A.thetaIdealDatum 0).inv

/-- **The class law of the divisor datum**: `[divisorDatum] = [𝒪(d)]` — G-0a at
`a = 0`, the trivial theta block, and the class law of the datum inverse. -/
theorem cechPicClass_divisorDatum : A.divisorDatum.cechPicClass = d.picClass := by
  change (A.thetaIdealDatum 0).inv.cechPicClass = d.picClass
  rw [BasicOpenCocycleDatum.cechPicClass_inv, A.cechPicClass_thetaIdealDatum 0,
    cechPicClass_thetaChartDatum_zero, one_mul, inv_inv]

/-! ### The canonical section -/

/-- The value-level matching law of the equation components against the inverted ratio
units: `f_i = (f_j/f_i)⁻¹ · f_j` on any open below the piece overlap. -/
private lemma res_eqn_eq_inv_eqnRatio_mul (i j : A.index) {O : (relCurve C R).Opens}
    (hO : O ≤ A.pieces i ⊓ A.pieces j) :
    (relCurve C R).resHom (hO.trans inf_le_left) (A.eqn i)
      = (relCurve C R).resHom hO
          (((A.eqnRatio i j)⁻¹ : Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
            Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
        * (relCurve C R).resHom (hO.trans inf_le_right) (A.eqn j) := by
  have key := congrArg ((relCurve C R).resHom hO) (A.eqn_mul_eqnRatio i j)
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  -- key : `res f_i · res (f_j/f_i) = res f_j` on `O`; divide by the restricted unit
  refine (Units.eq_inv_mul_iff_mul_eq
    ((relCurve C R).unitsRestrict hO (A.eqnRatio i j))).mpr ?_
  rw [mul_comm]
  exact key

/-- The matching condition of the equation components for the divisor datum, in the
exact shape of the `gluedSubmodule` carrier at `W = ⊤` (adaptation-index form; each
datum-index case is definitionally this statement). -/
private lemma canon_matching (i j : A.index) :
    (relCurve C R).resHom
        (inf_le_left : ⊤ ⊓ A.pieces i ⊓ A.pieces j ≤ ⊤ ⊓ A.pieces i)
        ((relCurve C R).resHom (inf_le_right : ⊤ ⊓ A.pieces i ≤ A.pieces i) (A.eqn i))
      = (relCurve C R).resHom
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            ⊤ ⊓ A.pieces i ⊓ A.pieces j ≤ A.pieces i ⊓ A.pieces j)
          (((A.thetaIdealUnit 0 i j)⁻¹ :
              Γ(relCurve C R, A.pieces i ⊓ A.pieces j)ˣ) :
            Γ(relCurve C R, A.pieces i ⊓ A.pieces j))
        * (relCurve C R).resHom
            (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              ⊤ ⊓ A.pieces i ⊓ A.pieces j ≤ ⊤ ⊓ A.pieces j)
            ((relCurve C R).resHom (inf_le_right : ⊤ ⊓ A.pieces j ≤ A.pieces j)
              (A.eqn j)) := by
  rw [A.thetaIdealUnit_zero i j]
  have key := A.res_eqn_eq_inv_eqnRatio_mul i j
    (O := ⊤ ⊓ A.pieces i ⊓ A.pieces j)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  simp only [Scheme.resHom_resHom]
  exact key

/-- **The canonical section of the divisor datum is the equation system itself**
(worksheet §2 (N2)): the components `A.eqn j`, restricted to the pieces, form a
matching family for the inverted ratio units — a global section of the divisor
datum's glued sheaf. -/
noncomputable def canonSection :
    ↥(_root_.AlgebraicGeometry.gluedSubmodule R A.divisorDatum.pieces
        A.divisorDatum.unit ⊤) :=
  ⟨fun j => (relCurve C R).resHom
      (inf_le_right.trans (le_of_eq (A.thetaIdealDatum_pieces 0 j)))
      (A.eqn (A.lowerIndex 0 j)),
    by
      intro i j
      rcases i with i | i <;> rcases j with j | j
      · exact A.canon_matching (Sum.inl i.down) (Sum.inl j.down)
      · exact A.canon_matching (Sum.inl i.down) (Sum.inr j.down)
      · exact A.canon_matching (Sum.inr i.down) (Sum.inl j.down)
      · exact A.canon_matching (Sum.inr i.down) (Sum.inr j.down)⟩

/-- The components of the canonical section are the (piece-restricted) equations. -/
lemma component_canonSection (j : (A.thetaIdealDatum 0).index) :
    A.divisorDatum.component A.canonSection j
      = (relCurve C R).resHom (le_of_eq (A.thetaIdealDatum_pieces 0 j))
          (A.eqn (A.lowerIndex 0 j)) :=
  Scheme.resHom_resHom _ _ _

/-- The canonical section is germ-regular: its components are the adaptation's own
regular equations (`eqn_regular`) — the `hreg` input of `sectionLocalEquations`,
with no fibrewise hypothesis. -/
theorem germ_component_canonSection_mem_nonZeroDivisors
    (j : (A.thetaIdealDatum 0).index) (y : relCurve C R)
    (hy : y ∈ A.divisorDatum.pieces j) :
    ((relCurve C R).presheaf.germ (A.divisorDatum.pieces j) y hy).hom
        (A.divisorDatum.component A.canonSection j)
      ∈ nonZeroDivisors ((relCurve C R).presheaf.stalk y) := by
  have hy' : y ∈ A.pieces (A.lowerIndex 0 j) :=
    (le_of_eq (A.thetaIdealDatum_pieces 0 j)) hy
  have hswap : ((relCurve C R).presheaf.germ (A.divisorDatum.pieces j) y hy).hom
      (A.divisorDatum.component A.canonSection j)
      = ((relCurve C R).presheaf.germ (A.pieces (A.lowerIndex 0 j)) y hy').hom
          (A.eqn (A.lowerIndex 0 j)) := by
    rw [A.component_canonSection j]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [hswap]
  exact A.eqn_regular (A.lowerIndex 0 j) y hy'

/-- **(N2) — the canonical section cuts back `d` by pure refinement**: the
`LocalEquations` datum cut by the canonical section on any pointed cover subordinated
to the pieces is `DivEq` to `d`. The common refinement is `𝒲 ⊓ d.cover`, and the
comparison units are the adaptation's own `eqn_rel` units (`relUnit`) — no fibre
argument anywhere. -/
theorem divEq_sectionLocalEquations_canonSection
    (𝒲 : (relCurve C R).PointedCover) (σ : relCurve C R → (A.thetaIdealDatum 0).index)
    (hσ : ∀ y : relCurve C R, 𝒲.opens y ≤ A.divisorDatum.pieces (σ y)) :
    Scheme.LocalEquations.DivEq
      (A.divisorDatum.sectionLocalEquations A.canonSection 𝒲 σ hσ
        (fun j y hy => A.germ_component_canonSection_mem_nonZeroDivisors j y hy))
      d := by
  refine ⟨𝒲 ⊓ d.cover, fun x => inf_le_left, fun x => inf_le_right, fun x => ?_⟩
  -- the piece through `x` sits inside the adaptation piece of its lowered index
  have hpc : 𝒲.opens x ≤ A.pieces (A.lowerIndex 0 (σ x)) :=
    (hσ x).trans (le_of_eq (A.thetaIdealDatum_pieces 0 (σ x)))
  have hle : 𝒲.opens x ⊓ d.cover.opens x
      ≤ A.pieces (A.lowerIndex 0 (σ x)) ⊓ d.cover.opens x :=
    inf_le_inf_right _ hpc
  refine ⟨(relCurve C R).unitsRestrict hle (A.relUnit (A.lowerIndex 0 (σ x)) x), ?_⟩
  -- the defining equation of the comparison unit, restricted to the refinement
  have key := congrArg ((relCurve C R).resHom hle)
    (A.res_eqn_eq_relUnit_mul (A.lowerIndex 0 (σ x)) x)
  rw [map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  -- collapse the constructed datum's restricted equation onto the adaptation
  -- equation, term-mode (`rw` walks into the relCurve spelling seam — I-0237(a))
  have hlhs := (Scheme.resHom_resHom (hσ x)
      (inf_le_left : 𝒲.opens x ⊓ d.cover.opens x ≤ 𝒲.opens x)
      (A.divisorDatum.component A.canonSection (σ x))).trans
    ((congrArg ((relCurve C R).resHom
        ((inf_le_left : 𝒲.opens x ⊓ d.cover.opens x ≤ 𝒲.opens x).trans (hσ x)))
      (A.component_canonSection (σ x))).trans
      (Scheme.resHom_resHom (le_of_eq (A.thetaIdealDatum_pieces 0 (σ x)))
        ((inf_le_left : 𝒲.opens x ⊓ d.cover.opens x ≤ 𝒲.opens x).trans (hσ x))
        (A.eqn (A.lowerIndex 0 (σ x)))))
  exact hlhs.trans key

end DivisorAdaptation

end AlgebraicGeometry
