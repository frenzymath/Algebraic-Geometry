/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafDatumBaseChange
import AlgebraicJacobian.Cohomology.GluedSheafCongr
import AlgebraicJacobian.Picard.DivisorClass

/-!
# The Čech Picard class of a gluing cocycle (DAT-1, stage 1e — the class law)

The class law of `informal/spec-dat-1.md` stage (1e): a gluing cocycle on pieces
`U : J → X.Opens` determines a class in the definitional Picard group
`Scheme.CechPic` on every pointed cover subordinated to the pieces, independently of
the subordination; for the pinned basic-open cocycle datum the pieces cover the
relative curve, giving **the** class of the datum, natural in the test ring.

* `AlgebraicGeometry.gluedSubordCocycle` — the unit Čech 1-cocycle induced on a
  pointed cover `𝒲` subordinated to the pieces (`σ : X → J`,
  `hσ : 𝒲.opens x ≤ U (σ x)`): pair values the restricted transition units.
* `gluedSubordCocycle_class_eq` — **subordination independence**: any two subordinated
  pointed covers give the same `CechPic` class (restrict to the common refinement; the
  two restricted cocycles are cohomologous through the `0`-cochain
  `x ↦ g (σ' x) (σ x)`, by the cocycle law).
* `gluedSubordCocycle_isCohomologous_of_coboundary` — cohomologous gluing cocycles
  (`Scheme.IsGluingCoboundary`) induce cohomologous subordinated cocycles, hence equal
  classes (`gluedSubordCocycle_class_eq_of_coboundary`) — the class-level face of the
  landed sheaf-level transport `gluedSheafCongr`.
* `BasicOpenCocycleDatum.cechPicClass` — the class of the pinned datum (worksheet
  §3.2), on the canonical pointed cover by pieces; `cechPicClass_eq_mk` re-expresses it
  on **any** subordinated pointed cover (the interface the stage-(1f) extraction and
  DAT-3 consume).
* `BasicOpenCocycleDatum.cechPicClass_baseChange` — **naturality in the test ring**:
  the class of the base-changed datum is the `CechPic.map`-pullback of the class along
  `relCurveMap C B B'`.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C B, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k B).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry

/-! ## The subordinated unit cocycle of a gluing cocycle -/

section Subord

variable {X : Scheme.{u}} {J : Type u} {U : J → X.Opens}
variable {g g' : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ}

/-- The underlying section of a restricted unit is the restricted underlying section. -/
private lemma coe_unitsRestrict {W U₀ : X.Opens} (h : W ≤ U₀) (u : Γ(X, U₀)ˣ) :
    (X.unitsRestrict h u : Γ(X, W)) = X.resHom h (u : Γ(X, U₀)) :=
  rfl

/-- The pair value of the subordinated cocycle: the transition unit `g (σ x) (σ y)`
restricted to the overlap `𝒲.opens x ⊓ 𝒲.opens y` of the subordinated cover. -/
noncomputable def gluedSubordUnit (g : ∀ i j : J, Γ(X, U i ⊓ U j)ˣ) (𝒲 : X.PointedCover)
    (σ : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) (x y : X) :
    Γ(X, 𝒲.opens x ⊓ 𝒲.opens y)ˣ :=
  X.unitsRestrict
    (le_inf (inf_le_left.trans (hσ x)) (inf_le_right.trans (hσ y)) :
      𝒲.opens x ⊓ 𝒲.opens y ≤ U (σ x) ⊓ U (σ y))
    (g (σ x) (σ y))

/-- The cocycle identity for the subordinated pair values, in unit-section language
(the shape `PresheafOfGroups.OneCocycle.ofPairs` consumes). -/
lemma gluedSubordUnit_trans (hc : Scheme.IsGluingCocycle U g) (𝒲 : X.PointedCover)
    (σ : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) (x y z : X) :
    X.unitsRestrict (inf_le_left :
          𝒲.opens x ⊓ 𝒲.opens y ⊓ 𝒲.opens z ≤ 𝒲.opens x ⊓ 𝒲.opens y)
        (gluedSubordUnit g 𝒲 σ hσ x y)
      * X.unitsRestrict (inf_le_inf_right _ inf_le_right :
          𝒲.opens x ⊓ 𝒲.opens y ⊓ 𝒲.opens z ≤ 𝒲.opens y ⊓ 𝒲.opens z)
          (gluedSubordUnit g 𝒲 σ hσ y z)
      = X.unitsRestrict (inf_le_inf_right _ inf_le_left :
          𝒲.opens x ⊓ 𝒲.opens y ⊓ 𝒲.opens z ≤ 𝒲.opens x ⊓ 𝒲.opens z)
          (gluedSubordUnit g 𝒲 σ hσ x z) := by
  have hO : 𝒲.opens x ⊓ 𝒲.opens y ⊓ 𝒲.opens z ≤ U (σ x) ⊓ U (σ y) ⊓ U (σ z) :=
    le_inf (le_inf ((inf_le_left.trans inf_le_left).trans (hσ x))
      ((inf_le_left.trans inf_le_right).trans (hσ y))) (inf_le_right.trans (hσ z))
  refine Units.ext ?_
  rw [Units.val_mul, coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict,
    gluedSubordUnit, gluedSubordUnit, gluedSubordUnit,
    coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict]
  simp only [Scheme.resHom_resHom]
  exact hc.mul_res_of_le hO

/-- **The subordinated unit Čech cocycle** of a gluing cocycle: on a pointed cover
subordinated to the pieces, the restricted transition units form a unit 1-cocycle. -/
noncomputable def gluedSubordCocycle (hc : Scheme.IsGluingCocycle U g)
    (𝒲 : X.PointedCover) (σ : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) :
    X.unitsCocycle 𝒲 :=
  OneCocycle.ofPairs (G := X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
    (U := 𝒲.opens) (fun x y => gluedSubordUnit g 𝒲 σ hσ x y)
    (fun x y z => gluedSubordUnit_trans hc 𝒲 σ hσ x y z)

@[simp]
lemma gluedSubordCocycle_evInf (hc : Scheme.IsGluingCocycle U g) (𝒲 : X.PointedCover)
    (σ : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) (x y : X) :
    Scheme.unitsEvInf (gluedSubordCocycle hc 𝒲 σ hσ) x y =
      gluedSubordUnit g 𝒲 σ hσ x y :=
  OneCocycle.ofPairs_evInf (G := X.unitsPresheaf ⋙ forget₂ CommGrpCat GrpCat)
    (U := 𝒲.opens) (fun x y => gluedSubordUnit g 𝒲 σ hσ x y)
    (fun x y z => gluedSubordUnit_trans hc 𝒲 σ hσ x y z) x y

/-- Restricting the subordinated cocycle to a refinement gives the subordinated cocycle
of the refinement (with the induced subordination). -/
lemma gluedSubordCocycle_res (hc : Scheme.IsGluingCocycle U g) {𝒲' 𝒲 : X.PointedCover}
    (h : 𝒲' ≤ 𝒲) (σ : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) :
    (gluedSubordCocycle hc 𝒲 σ hσ).res (fun x => homOfLE (h x)) =
      gluedSubordCocycle hc 𝒲' σ (fun x => (h x).trans (hσ x)) := by
  refine Scheme.unitsCocycle_ext fun x y => ?_
  rw [Scheme.res_unitsEvInf h (gluedSubordCocycle hc 𝒲 σ hσ) x y,
    gluedSubordCocycle_evInf, gluedSubordCocycle_evInf]
  refine Units.ext ?_
  rw [coe_unitsRestrict, gluedSubordUnit, gluedSubordUnit,
    coe_unitsRestrict, coe_unitsRestrict]
  simp only [Scheme.resHom_resHom]

/-- **Two subordinations of the same cover give cohomologous cocycles**, through the
`0`-cochain `x ↦ g (σ' x) (σ x)` (the cocycle law makes the coboundary law hold). -/
lemma gluedSubordCocycle_isCohomologous (hc : Scheme.IsGluingCocycle U g)
    (𝒲 : X.PointedCover) (σ σ' : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x))
    (hσ' : ∀ x : X, 𝒲.opens x ≤ U (σ' x)) :
    (gluedSubordCocycle hc 𝒲 σ hσ).IsCohomologous (gluedSubordCocycle hc 𝒲 σ' hσ') := by
  refine Scheme.unitsCocycle_isCohomologous
    (fun x => X.unitsRestrict (le_inf (hσ' x) (hσ x) : 𝒲.opens x ≤ U (σ' x) ⊓ U (σ x))
      (g (σ' x) (σ x))) (fun x y => ?_)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, gluedSubordCocycle_evInf, gluedSubordCocycle_evInf,
    coe_unitsRestrict, coe_unitsRestrict, gluedSubordUnit, gluedSubordUnit,
    coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict]
  simp only [Scheme.resHom_resHom]
  have hL : X.resHom (le_inf ((inf_le_left.trans (hσ' x)))
        ((inf_le_left.trans (hσ x))) :
        𝒲.opens x ⊓ 𝒲.opens y ≤ U (σ' x) ⊓ U (σ x)) (g (σ' x) (σ x) : Γ(X, _)) *
      X.resHom (le_inf (inf_le_left.trans (hσ x)) (inf_le_right.trans (hσ y)))
        (g (σ x) (σ y) : Γ(X, _)) =
      X.resHom (le_inf (inf_le_left.trans (hσ' x)) (inf_le_right.trans (hσ y)))
        (g (σ' x) (σ y) : Γ(X, _)) :=
    hc.mul_res_of_le (le_inf (le_inf (inf_le_left.trans (hσ' x))
      (inf_le_left.trans (hσ x))) (inf_le_right.trans (hσ y)))
  have hR : X.resHom (le_inf ((inf_le_left.trans (hσ' x)))
        ((inf_le_right.trans (hσ' y))) :
        𝒲.opens x ⊓ 𝒲.opens y ≤ U (σ' x) ⊓ U (σ' y)) (g (σ' x) (σ' y) : Γ(X, _)) *
      X.resHom (le_inf (inf_le_right.trans (hσ' y)) (inf_le_right.trans (hσ y)))
        (g (σ' y) (σ y) : Γ(X, _)) =
      X.resHom (le_inf (inf_le_left.trans (hσ' x)) (inf_le_right.trans (hσ y)))
        (g (σ' x) (σ y) : Γ(X, _)) :=
    hc.mul_res_of_le (le_inf (le_inf (inf_le_left.trans (hσ' x))
      (inf_le_right.trans (hσ' y))) (inf_le_right.trans (hσ y)))
  exact hL.trans hR.symm

/-- **Subordination independence of the class**: any two pointed covers subordinated to
the pieces of a gluing cocycle carry the same `CechPic` class. -/
theorem gluedSubordCocycle_class_eq (hc : Scheme.IsGluingCocycle U g)
    (𝒲 𝒲' : X.PointedCover) (σ σ' : X → J) (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x))
    (hσ' : ∀ x : X, 𝒲'.opens x ≤ U (σ' x)) :
    Scheme.CechPic.mk 𝒲 (gluedSubordCocycle hc 𝒲 σ hσ).class =
      Scheme.CechPic.mk 𝒲' (gluedSubordCocycle hc 𝒲' σ' hσ').class := by
  refine Scheme.CechPic.mk_eq_mk_iff.mpr ⟨𝒲 ⊓ 𝒲', inf_le_left, inf_le_right, ?_⟩
  have h₁ : Scheme.unitsRes (inf_le_left : 𝒲 ⊓ 𝒲' ≤ 𝒲)
      (gluedSubordCocycle hc 𝒲 σ hσ).class =
      (gluedSubordCocycle hc (𝒲 ⊓ 𝒲') σ
        (fun x => ((inf_le_left : 𝒲 ⊓ 𝒲' ≤ 𝒲) x).trans (hσ x))).class :=
    congrArg OneCocycle.class
      (gluedSubordCocycle_res hc (inf_le_left : 𝒲 ⊓ 𝒲' ≤ 𝒲) σ hσ)
  have h₂ : Scheme.unitsRes (inf_le_right : 𝒲 ⊓ 𝒲' ≤ 𝒲')
      (gluedSubordCocycle hc 𝒲' σ' hσ').class =
      (gluedSubordCocycle hc (𝒲 ⊓ 𝒲') σ'
        (fun x => ((inf_le_right : 𝒲 ⊓ 𝒲' ≤ 𝒲') x).trans (hσ' x))).class :=
    congrArg OneCocycle.class
      (gluedSubordCocycle_res hc (inf_le_right : 𝒲 ⊓ 𝒲' ≤ 𝒲') σ' hσ')
  rw [h₁, h₂]
  exact (gluedSubordCocycle_isCohomologous hc (𝒲 ⊓ 𝒲') σ σ' _ _).class_eq

/-- **Cohomologous gluing cocycles induce cohomologous subordinated cocycles**: a
gluing coboundary `c` between multiplier families restricts to a Čech coboundary
between the subordinated cocycles — the class-level face of the sheaf-level transport
`gluedSheafCongr`. -/
lemma gluedSubordCocycle_isCohomologous_of_coboundary (hc : Scheme.IsGluingCocycle U g)
    (hc' : Scheme.IsGluingCocycle U g') {c : ∀ j : J, Γ(X, U j)ˣ}
    (hcob : Scheme.IsGluingCoboundary U g g' c) (𝒲 : X.PointedCover) (σ : X → J)
    (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) :
    (gluedSubordCocycle hc 𝒲 σ hσ).IsCohomologous (gluedSubordCocycle hc' 𝒲 σ hσ) := by
  refine Scheme.unitsCocycle_isCohomologous
    (fun x => X.unitsRestrict (hσ x) (c (σ x))) (fun x y => ?_)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, gluedSubordCocycle_evInf, gluedSubordCocycle_evInf,
    coe_unitsRestrict, coe_unitsRestrict, gluedSubordUnit, gluedSubordUnit,
    coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict, coe_unitsRestrict]
  simp only [Scheme.resHom_resHom]
  have key := congrArg
    (X.resHom (le_inf (inf_le_left.trans (hσ x)) (inf_le_right.trans (hσ y)) :
      𝒲.opens x ⊓ 𝒲.opens y ≤ U (σ x) ⊓ U (σ y))) (hcob (σ x) (σ y))
  rw [map_mul, map_mul] at key
  simp only [Scheme.resHom_resHom] at key
  exact key

/-- Cohomologous gluing cocycles give equal `CechPic` classes on every subordinated
pointed cover. -/
theorem gluedSubordCocycle_class_eq_of_coboundary (hc : Scheme.IsGluingCocycle U g)
    (hc' : Scheme.IsGluingCocycle U g') {c : ∀ j : J, Γ(X, U j)ˣ}
    (hcob : Scheme.IsGluingCoboundary U g g' c) (𝒲 : X.PointedCover) (σ : X → J)
    (hσ : ∀ x : X, 𝒲.opens x ≤ U (σ x)) :
    Scheme.CechPic.mk 𝒲 (gluedSubordCocycle hc 𝒲 σ hσ).class =
      Scheme.CechPic.mk 𝒲 (gluedSubordCocycle hc' 𝒲 σ hσ).class :=
  congrArg (Scheme.CechPic.mk 𝒲)
    (gluedSubordCocycle_isCohomologous_of_coboundary hc hc' hcob 𝒲 σ hσ).class_eq

end Subord

/-! ## The class of the pinned cocycle datum -/

section Datum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {π : C.left ⟶ P1 k} [IsAffineHom π]

namespace BasicOpenCocycleDatum

variable (D : BasicOpenCocycleDatum C B π)

/-- Every point of the relative curve lies in a piece of the datum: the two pinned
charts cover the curve and each chart is covered by its basic-open pieces. -/
lemma exists_mem_pieces (x : relCurve C B) : ∃ j : D.index, x ∈ D.pieces j := by
  have hx : x ∈ (relCover C B (fiberTwoCover π)).V₀ ⊔ (relCover C B (fiberTwoCover π)).V₁ := by
    rw [relCover_sup]
    trivial
  rcases (TopologicalSpace.Opens.mem_sup).mp hx with h0 | h1
  · have hcov := D.cover₀ h0
    rw [TopologicalSpace.Opens.mem_iSup] at hcov
    obtain ⟨j, hj⟩ := hcov
    exact ⟨Sum.inl j, hj⟩
  · have hcov := D.cover₁ h1
    rw [TopologicalSpace.Opens.mem_iSup] at hcov
    obtain ⟨j, hj⟩ := hcov
    exact ⟨Sum.inr j, hj⟩

/-- A choice of piece through every point of the relative curve. -/
noncomputable def pieceIndex (x : relCurve C B) : D.index :=
  (D.exists_mem_pieces x).choose

lemma mem_pieces_pieceIndex (x : relCurve C B) : x ∈ D.pieces (D.pieceIndex x) :=
  (D.exists_mem_pieces x).choose_spec

/-- **The canonical pointed cover by pieces** of the datum. -/
noncomputable def pointedCover : (relCurve C B).PointedCover where
  opens x := D.pieces (D.pieceIndex x)
  mem_opens x := D.mem_pieces_pieceIndex x

@[simp]
lemma pointedCover_opens (x : relCurve C B) :
    D.pointedCover.opens x = D.pieces (D.pieceIndex x) := rfl

/-- **The Čech Picard class of the pinned cocycle datum** (stage 1e): the class of the
subordinated unit cocycle on the canonical pointed cover by pieces. By
`cechPicClass_eq_mk` it is computed by **any** pointed cover subordinated to the
pieces. -/
noncomputable def cechPicClass : (relCurve C B).CechPic :=
  Scheme.CechPic.mk D.pointedCover
    (gluedSubordCocycle D.isGluingCocycle D.pointedCover D.pieceIndex
      (fun _ => le_rfl)).class

/-- **The class law on subordinated covers**: the class of the datum is computed by the
subordinated cocycle on any pointed cover subordinated to the pieces (the interface the
stage-(1f) extraction and DAT-3 consume). -/
theorem cechPicClass_eq_mk (𝒲 : (relCurve C B).PointedCover) (σ : relCurve C B → D.index)
    (hσ : ∀ x : relCurve C B, 𝒲.opens x ≤ D.pieces (σ x)) :
    Scheme.CechPic.mk 𝒲 (gluedSubordCocycle D.isGluingCocycle 𝒲 σ hσ).class =
      D.cechPicClass :=
  gluedSubordCocycle_class_eq D.isGluingCocycle 𝒲 D.pointedCover σ D.pieceIndex hσ
    (fun _ => le_rfl)

end BasicOpenCocycleDatum

/-! ## Naturality of the class in the test ring -/

namespace BasicOpenCocycleDatum

variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B'] [IsScalarTower k B B']
variable (D : BasicOpenCocycleDatum C B π)

/-- The pullback of the canonical pointed cover is subordinated to the pieces of the
base-changed datum (pieces base-change to pieces). -/
lemma pullback_pointedCover_le (x : relCurve C B') :
    (D.pointedCover.pullback (relCurveMap C B B')).opens x ≤
      (D.baseChange B').pieces (D.pieceIndex ((relCurveMap C B B').base x)) := by
  rw [Scheme.PointedCover.pullback_opens, pointedCover_opens]
  exact (D.toBasicOpenCoverData.pieces_baseChange B'
    (D.pieceIndex ((relCurveMap C B B').base x))).ge

/-- (Implementation) **The pulled-back subordinated cocycle is the subordinated cocycle
of the base-changed datum**: comparing pair values, both are one `appLE` of the
transition unit. -/
lemma pullbackUnitsCocycle_gluedSubordCocycle :
    (relCurveMap C B B').pullbackUnitsCocycle
      (gluedSubordCocycle D.isGluingCocycle D.pointedCover D.pieceIndex
        (fun _ => le_rfl)) =
    gluedSubordCocycle (D.baseChange B').isGluingCocycle
      (D.pointedCover.pullback (relCurveMap C B B'))
      (fun x => D.pieceIndex ((relCurveMap C B B').base x))
      (fun x => D.pullback_pointedCover_le B' x) := by
  refine Scheme.unitsCocycle_ext fun x y => ?_
  rw [Scheme.Hom.pullbackUnitsCocycle_unitsEvInf, gluedSubordCocycle_evInf,
    gluedSubordCocycle_evInf]
  refine Units.ext ?_
  rw [Scheme.Hom.coe_unitsAppLE, gluedSubordUnit, gluedSubordUnit,
    coe_unitsRestrict, coe_unitsRestrict]
  -- left side: `appLE` of the restricted unit collapses to one `appLE`
  have hL := congr((CommRingCat.Hom.hom
    $(Scheme.Hom.map_appLE (relCurveMap C B B')
      ((relCurveMap C B B').le_preimage_inf
        (inf_le_left : (D.pointedCover.pullback (relCurveMap C B B')).opens x ⊓
          (D.pointedCover.pullback (relCurveMap C B B')).opens y ≤
            (D.pointedCover.pullback (relCurveMap C B B')).opens x)
        (inf_le_right))
      (homOfLE (le_inf (inf_le_left.trans le_rfl) (inf_le_right.trans le_rfl) :
        D.pointedCover.opens ((relCurveMap C B B').base x) ⊓
          D.pointedCover.opens ((relCurveMap C B B').base y) ≤
            D.pieces (D.pieceIndex ((relCurveMap C B B').base x)) ⊓
              D.pieces (D.pieceIndex ((relCurveMap C B B').base y)))).op))
    ((D.unit (D.pieceIndex ((relCurveMap C B B').base x))
        (D.pieceIndex ((relCurveMap C B B').base y)) :
      Γ(relCurve C B, D.pieces (D.pieceIndex ((relCurveMap C B B').base x)) ⊓
        D.pieces (D.pieceIndex ((relCurveMap C B B').base y))))))
  -- right side: restriction of the base-changed unit collapses to one `appLE`
  have hR := congr((CommRingCat.Hom.hom
    $(Scheme.Hom.appLE_map (relCurveMap C B B')
      (D.toBasicOpenCoverData.baseChange_inf_le_preimage B'
        (D.pieceIndex ((relCurveMap C B B').base x))
        (D.pieceIndex ((relCurveMap C B B').base y)))
      (homOfLE (le_inf (inf_le_left.trans (D.pullback_pointedCover_le B' x))
        (inf_le_right.trans (D.pullback_pointedCover_le B' y)) :
        (D.pointedCover.pullback (relCurveMap C B B')).opens x ⊓
          (D.pointedCover.pullback (relCurveMap C B B')).opens y ≤
            (D.baseChange B').pieces (D.pieceIndex ((relCurveMap C B B').base x)) ⊓
              (D.baseChange B').pieces
                (D.pieceIndex ((relCurveMap C B B').base y)))).op))
    ((D.unit (D.pieceIndex ((relCurveMap C B B').base x))
        (D.pieceIndex ((relCurveMap C B B').base y)) :
      Γ(relCurve C B, D.pieces (D.pieceIndex ((relCurveMap C B B').base x)) ⊓
        D.pieces (D.pieceIndex ((relCurveMap C B B').base y))))))
  exact hL.trans hR.symm

/-- **Naturality of the class in the test ring** (stage 1e, last clause): the Čech
Picard class of the base-changed datum is the pullback of the class of the datum along
the relative-curve comparison morphism. -/
theorem cechPicClass_baseChange :
    (D.baseChange B').cechPicClass =
      Scheme.CechPic.map (relCurveMap C B B') D.cechPicClass := by
  calc (D.baseChange B').cechPicClass
      = Scheme.CechPic.mk (D.pointedCover.pullback (relCurveMap C B B'))
          (gluedSubordCocycle (D.baseChange B').isGluingCocycle
            (D.pointedCover.pullback (relCurveMap C B B'))
            (fun x => D.pieceIndex ((relCurveMap C B B').base x))
            (fun x => D.pullback_pointedCover_le B' x)).class :=
        ((D.baseChange B').cechPicClass_eq_mk
          (D.pointedCover.pullback (relCurveMap C B B'))
          (fun x => D.pieceIndex ((relCurveMap C B B').base x))
          (fun x => D.pullback_pointedCover_le B' x)).symm
    _ = Scheme.CechPic.map (relCurveMap C B B') D.cechPicClass := by
        rw [← D.pullbackUnitsCocycle_gluedSubordCocycle B']
        rfl

end BasicOpenCocycleDatum

end Datum

end AlgebraicGeometry
