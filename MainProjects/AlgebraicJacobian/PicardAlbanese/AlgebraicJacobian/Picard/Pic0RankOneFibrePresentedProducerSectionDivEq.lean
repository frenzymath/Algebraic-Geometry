/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsToDivisorsClass
import AlgebraicJacobian.Picard.DivisorFamily
import AlgebraicJacobian.Picard.DivisorFamilyAffSections
import AlgebraicJacobian.Picard.Pic0AdmissibleAbelEtaleSurjectiveH0

/-!
# Cover independence for section-cut evaluation divisors

The evaluation divisor used by the arbitrary-scheme `PicRankOneOpen.FibrePresented`
producer is cut from an actual glued section.  Pulling such a divisor through an affine
coefficient change retains the pulled-back pointed cover, whereas the direct construction
uses the canonical pointed cover of the base-changed cocycle datum.  This file supplies the
pure refinement step between those covers: local equations cut by the same section on any
two subordinated pointed covers are `DivEq`.

The comparison unit is the datum's transition unit restricted to the common refinement.
Thus this result records construction-level divisor equality, not merely equality of Picard
classes, and assumes neither `PicRankOneOpen.FibrePresented` nor a pullback square.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k}

namespace BasicOpenCocycleDatum

/-- Local equations cut by one glued section are independent, up to `DivEq`, of the
subordinated pointed cover used to write them.  The witness is the intersection cover and
the restricted transition unit between the two selected datum pieces. -/
theorem sectionLocalEquations_divEq_of_same_section
    [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↑(gluedSubmodule B D.pieces D.unit ⊤))
    (W W' : (relCurve C B).PointedCover)
    (σ σ' : relCurve C B → D.index)
    (hσ : ∀ x : relCurve C B, W.opens x ≤ D.pieces (σ x))
    (hσ' : ∀ x : relCurve C B, W'.opens x ≤ D.pieces (σ' x))
    (hreg : ∀ (j : D.index) (x : relCurve C B) (hx : x ∈ D.pieces j),
      ((relCurve C B).presheaf.germ (D.pieces j) x hx).hom (D.component s j)
        ∈ nonZeroDivisors ((relCurve C B).presheaf.stalk x)) :
    Scheme.LocalEquations.DivEq
      (D.sectionLocalEquations s W σ hσ hreg)
      (D.sectionLocalEquations s W' σ' hσ' hreg) := by
  refine ⟨W ⊓ W', (fun _ => inf_le_left), (fun _ => inf_le_right), fun x => ?_⟩
  have hleft : (W ⊓ W').opens x ≤ D.pieces (σ x) :=
    inf_le_left.trans (hσ x)
  have hright : (W ⊓ W').opens x ≤ D.pieces (σ' x) :=
    inf_le_right.trans (hσ' x)
  have hoverlap : (W ⊓ W').opens x ≤ D.pieces (σ x) ⊓ D.pieces (σ' x) :=
    le_inf hleft hright
  have htriple : (W ⊓ W').opens x ≤ ⊤ ⊓ D.pieces (σ x) ⊓ D.pieces (σ' x) :=
    le_inf (le_inf le_top hleft) hright
  refine ⟨(relCurve C B).unitsRestrict hoverlap (D.unit (σ x) (σ' x)), ?_⟩
  have key := congrArg ((relCurve C B).resHom htriple)
    (s.property (σ x) (σ' x))
  rw [map_mul] at key
  simp only [sectionLocalEquations_eqn]
  change (relCurve C B).resHom inf_le_left
      ((relCurve C B).resHom (hσ x) (D.component s (σ x))) =
    ((relCurve C B).unitsRestrict hoverlap (D.unit (σ x) (σ' x)) :
      Γ(relCurve C B, (W ⊓ W').opens x)) *
      (relCurve C B).resHom inf_le_right
        ((relCurve C B).resHom (hσ' x) (D.component s (σ' x)))
  rw [show (((relCurve C B).unitsRestrict hoverlap (D.unit (σ x) (σ' x)) :
      Γ(relCurve C B, (W ⊓ W').opens x)ˣ) : Γ(relCurve C B, (W ⊓ W').opens x)) =
        (relCurve C B).resHom hoverlap
          (D.unit (σ x) (σ' x) : Γ(relCurve C B, D.pieces (σ x) ⊓ D.pieces (σ' x)))
      from rfl, BasicOpenCocycleDatum.component, BasicOpenCocycleDatum.component]
  simp only [Scheme.resHom_resHom] at key ⊢
  exact key

/-! ## Coefficient-change naturality -/

/-- Restricting the datum-piece comparison to the actual preimage piece gives the
arbitrary-affine section comparison.  This is the pointwise equation bridge between the
base-changed glued section and `LocalEquations.pullbackEqn`. -/
theorem resHom_piecesMap_eq_relAffSectionsMap
    [IsAffineHom pi]
    (D : BasicOpenCocycleDatum C B pi)
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B'] (j : D.index)
    (t : Γ(relCurve C B, D.pieces j)) :
    (relCurve C B').resHom
        (D.toBasicOpenCoverData.pieces_baseChange B' j).ge
        (D.toBasicOpenCoverData.piecesMap B' j t) =
      relAffSectionsMap C B' (D.pieces j) t := by
  cases j with
  | inl j =>
      simpa only [BasicOpenCoverData.piecesMap, pieceSectionsMap,
        BasicOpenCoverData.pieces, BasicOpenCoverData.baseChange, Sum.elim_inl,
        relAffSectionsMap, Scheme.resHom_refl] using
        ((relCurveMap C B B').appLE_resHom
          (le_rfl : D.pieces (Sum.inl j) ≤ D.pieces (Sum.inl j))
          (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' (Sum.inl j))
          (le_rfl : relCurveMap C B B' ⁻¹ᵁ D.pieces (Sum.inl j) ≤
            relCurveMap C B B' ⁻¹ᵁ D.pieces (Sum.inl j))
          (D.toBasicOpenCoverData.pieces_baseChange B' (Sum.inl j)).ge t)
  | inr j =>
      simpa only [BasicOpenCoverData.piecesMap, pieceSectionsMap,
        BasicOpenCoverData.pieces, BasicOpenCoverData.baseChange, Sum.elim_inr,
        relAffSectionsMap, Scheme.resHom_refl] using
        ((relCurveMap C B B').appLE_resHom
          (le_rfl : D.pieces (Sum.inr j) ≤ D.pieces (Sum.inr j))
          (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' (Sum.inr j))
          (le_rfl : relCurveMap C B B' ⁻¹ᵁ D.pieces (Sum.inr j) ≤
            relCurveMap C B B' ⁻¹ᵁ D.pieces (Sum.inr j))
          (D.toBasicOpenCoverData.pieces_baseChange B' (Sum.inr j)).ge t)

/-- The equation obtained by pulling back the canonical section-cut local equations is the
arbitrary-affine comparison of the selected datum component. -/
theorem pullbackEqn_sectionLocalEquations_eq_relAffSectionsMap
    [IsFinite pi] [IsNoetherianRing B]
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↑(gluedSubmodule B D.pieces D.unit ⊤))
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B'] (z : relCurve C B') :
    Scheme.LocalEquations.pullbackEqn (relCurveMap C B B')
        (D.sectionLocalEquationsOfFibrewiseRegular s hfib) z =
      relAffSectionsMap C B'
        (D.pieces (D.pieceIndex ((relCurveMap C B B').base z)))
        (D.component s (D.pieceIndex ((relCurveMap C B B').base z))) := by
  simp [Scheme.LocalEquations.pullbackEqn,
    BasicOpenCocycleDatum.sectionLocalEquationsOfFibrewiseRegular,
    BasicOpenCocycleDatum.sectionLocalEquations,
    relAffSectionsMap, Scheme.resHom]

/-- Pulling back the divisor cut by a fibrewise-regular glued section is `DivEq` to the
divisor cut by the compared section on the canonical cover after an arbitrary affine
coefficient change.  The first comparison has unit `1` on the pulled cover; the second is
the transition-unit refinement supplied by `sectionLocalEquations_divEq_of_same_section`. -/
theorem pullback_sectionLocalEquationsOfFibrewiseRegular_divEq_sectionsMapTop
    [IsFinite pi] [IsNoetherianRing B]
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↑(gluedSubmodule B D.pieces D.unit ⊤))
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B'] [IsNoetherianRing B']
    (hfib' : ∀ (j : (D.baseChange B').index) (p : PrimeSpectrum B'),
      Function.Injective
        ((Scheme.mulSectionEnd B'
          ((D.baseChange B').component (D.sectionsMapTop B' s) j)).rTensor
            p.asIdeal.ResidueField))
    (hpull : ∀ (y z : relCurve C B')
      (hz : z ∈ ((D.sectionLocalEquationsOfFibrewiseRegular s hfib).cover.pullback
        (relCurveMap C B B')).opens y),
      ((relCurve C B').presheaf.germ
        (((D.sectionLocalEquationsOfFibrewiseRegular s hfib).cover.pullback
          (relCurveMap C B B')).opens y) z hz).hom
          (Scheme.LocalEquations.pullbackEqn (relCurveMap C B B')
            (D.sectionLocalEquationsOfFibrewiseRegular s hfib) y) ∈
        nonZeroDivisors ((relCurve C B').presheaf.stalk z)) :
    Scheme.LocalEquations.DivEq
      ((D.sectionLocalEquationsOfFibrewiseRegular s hfib).pullback
        (relCurveMap C B B') hpull)
      ((D.baseChange B').sectionLocalEquationsOfFibrewiseRegular
        (D.sectionsMapTop B' s) hfib') := by
  let f := relCurveMap C B B'
  let W := D.pointedCover.pullback f
  let sigma : relCurve C B' → D.index := fun z => D.pieceIndex (f.base z)
  let hsigma : ∀ z : relCurve C B', W.opens z ≤ (D.baseChange B').pieces (sigma z) :=
    fun z => D.pullback_pointedCover_le B' z
  let s' := D.sectionsMapTop B' s
  let hreg' : ∀ (j : (D.baseChange B').index) (z : relCurve C B')
      (hz : z ∈ (D.baseChange B').pieces j),
      ((relCurve C B').presheaf.germ ((D.baseChange B').pieces j) z hz).hom
          ((D.baseChange B').component s' j) ∈
        nonZeroDivisors ((relCurve C B').presheaf.stalk z) :=
    fun j z hz =>
      (D.baseChange B').germ_component_mem_nonZeroDivisors s' j (hfib' j) z hz
  refine Scheme.LocalEquations.DivEq.trans (d₂ :=
    (D.baseChange B').sectionLocalEquations s' W sigma hsigma hreg') ?_ ?_
  · refine ⟨W, (fun _ => le_rfl), (fun _ => le_rfl), fun z => ?_⟩
    refine ⟨1, ?_⟩
    rw [Units.val_one, one_mul]
    simp only [Scheme.LocalEquations.pullback_eqn, sectionLocalEquations_eqn]
    rw [D.pullbackEqn_sectionLocalEquations_eq_relAffSectionsMap s hfib B' z]
    rw [D.component_sectionsMapTop B' s (sigma z)]
    apply congrArg ((relCurve C B').resHom _)
    exact (D.resHom_piecesMap_eq_relAffSectionsMap B' (sigma z)
      (D.component s (sigma z))).symm
  · simpa only [BasicOpenCocycleDatum.sectionLocalEquationsOfFibrewiseRegular,
      s', hreg'] using
      (D.baseChange B').sectionLocalEquations_divEq_of_same_section s'
        W (D.baseChange B').pointedCover sigma (D.baseChange B').pieceIndex
        hsigma (fun _ => le_rfl) hreg'

end BasicOpenCocycleDatum

end AlgebraicGeometry
