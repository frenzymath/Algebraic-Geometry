/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.GluedSheafH0BaseChange
import AlgebraicJacobian.Picard.DivisorFamilyPullbackMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace BasicOpenCoverData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
  [IsScalarTower k B B']
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]
variable (D : BasicOpenCoverData C B pi)

/-- The comparison of sections on a datum piece with sections on its base change. -/
noncomputable def piecesMap : ∀ j : D.index,
    Γ(relCurve C B, D.pieces j) →+*
      Γ(relCurve C B', (D.baseChange B').pieces j)
  | .inl j => pieceSectionsMap B' (fiberChart₀ pi) (D.h₀ j)
  | .inr j => pieceSectionsMap B' (fiberChart₁ pi) (D.h₁ j)

/-- Base change commutes with the basic-open localization defining each datum piece. -/
noncomputable def pieceTermBaseChange : ∀ j : D.index,
    B' ⊗[B] Γ(relCurve C B, D.pieces j) ≃ₐ[B']
      Γ(relCurve C B', (D.baseChange B').pieces j)
  | .inl j =>
      pieceTermBaseChangeAlg B' (fiberChart₀ pi)
        (fiberTwoCover pi).isAffineOpen₀.isCompact
        (fiberTwoCover pi).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₀ C B' (fiberTwoCover pi)) (D.h₀ j)
  | .inr j =>
      pieceTermBaseChangeAlg B' (fiberChart₁ pi)
        (fiberTwoCover pi).isAffineOpen₁.isCompact
        (fiberTwoCover pi).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C B' (fiberTwoCover pi)) (D.h₁ j)

/-- The datum-piece base-change equivalence sends `1 ⊗ t` to the compared section. -/
theorem pieceTermBaseChange_one_tmul (j : D.index)
    (t : Γ(relCurve C B, D.pieces j)) :
    D.pieceTermBaseChange B' j ((1 : B') ⊗ₜ[B] t) = D.piecesMap B' j t := by
  cases j with
  | inl j =>
      exact pieceTermBaseChangeAlg_one_tmul B' (fiberChart₀ pi)
        (fiberTwoCover pi).isAffineOpen₀.isCompact
        (fiberTwoCover pi).isAffineOpen₀.isQuasiSeparated
        (relCover_isAffineOpen₀ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₀ C B' (fiberTwoCover pi)) (D.h₀ j) t
  | inr j =>
      exact pieceTermBaseChangeAlg_one_tmul B' (fiberChart₁ pi)
        (fiberTwoCover pi).isAffineOpen₁.isCompact
        (fiberTwoCover pi).isAffineOpen₁.isQuasiSeparated
        (relCover_isAffineOpen₁ C B (fiberTwoCover pi))
        (relCover_isAffineOpen₁ C B' (fiberTwoCover pi)) (D.h₁ j) t

end BasicOpenCoverData

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
  [IsScalarTower k B B']
variable {pi : C.left ⟶ P1 k} [IsAffineHom pi]

/-- Compare a global glued section along a change of coefficient ring. -/
noncomputable def sectionsMapTop (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) :
    ↥(gluedSubmodule B' (D.baseChange B').pieces (D.baseChange B').unit ⊤) :=
  D.sectionsMap B' (by rw [Scheme.Hom.preimage_top]) s

/-- Components of the compared global section are the compared original components. -/
theorem component_sectionsMapTop (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) (j : D.index) :
    (D.baseChange B').component (D.sectionsMapTop B' s) j =
      D.toBasicOpenCoverData.piecesMap B' j (D.component s j) := by
  let htop : (⊤ : (relCurve C B').Opens) ≤
      relCurveMap C B B' ⁻¹ᵁ (⊤ : (relCurve C B).Opens) := by
    rw [Scheme.Hom.preimage_top]
  cases j with
  | inl j =>
      simpa only [sectionsMapTop, component, sectionsMap_coe,
        BasicOpenCocycleDatum.baseChange, BasicOpenCoverData.piecesMap,
        BasicOpenCoverData.pieces, BasicOpenCoverData.baseChange,
        Sum.elim_inl, pieceSectionsMap] using
        (relCurveMap C B B').appLE_resHom
          (le_inf le_top le_rfl : D.pieces (Sum.inl j) ≤ ⊤ ⊓ D.pieces (Sum.inl j))
          (D.sectionsMap_component_le B' htop (Sum.inl j))
          (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' (Sum.inl j))
          (le_inf le_top le_rfl : (D.baseChange B').pieces (Sum.inl j) ≤
            ⊤ ⊓ (D.baseChange B').pieces (Sum.inl j)) (s.val (Sum.inl j))
  | inr j =>
      simpa only [sectionsMapTop, component, sectionsMap_coe,
        BasicOpenCocycleDatum.baseChange, BasicOpenCoverData.piecesMap,
        BasicOpenCoverData.pieces, BasicOpenCoverData.baseChange,
        Sum.elim_inr, pieceSectionsMap] using
        (relCurveMap C B B').appLE_resHom
          (le_inf le_top le_rfl : D.pieces (Sum.inr j) ≤ ⊤ ⊓ D.pieces (Sum.inr j))
          (D.sectionsMap_component_le B' htop (Sum.inr j))
          (D.toBasicOpenCoverData.baseChange_pieces_le_preimage B' (Sum.inr j))
          (le_inf le_top le_rfl : (D.baseChange B').pieces (Sum.inr j) ≤
            ⊤ ⊓ (D.baseChange B').pieces (Sum.inr j)) (s.val (Sum.inr j))

variable {K : Type u} [Field K] [Algebra k K]

set_option synthInstance.maxHeartbeats 800000 in
-- The glued trivialization carries a large dependent family of section rings.
-- A nonzero global section of a cocycle-glued line bundle on an integral scheme is
-- nonzero in every nonempty trivializing piece.
theorem component_ne_zero_of_global_ne_zero
    [IsIntegral (relCurve C K)] (D : BasicOpenCocycleDatum C K pi)
    (s : ↥(gluedSubmodule K D.pieces D.unit ⊤)) (hs : s ≠ 0)
    (j : D.index) (hj : D.pieces j ≠ ⊥) : D.component s j ≠ 0 := by
  intro hcomponent
  apply hs
  have hUj : ((D.pieces j : Set (relCurve C K))).Nonempty := by
    rcases Set.eq_empty_or_nonempty (D.pieces j : Set (relCurve C K)) with h | h
    · exact (hj (by ext x; rw [h]; simp)).elim
    · exact h
  have hres : gluedRes K D.pieces D.unit (le_top : D.pieces j ≤ ⊤) s = 0 := by
    apply (gluedTriv K D.isGluingCocycle j le_rfl).injective
    rw [map_zero, gluedTriv_apply, gluedRes_coe]
    simpa only [component, Scheme.resHom_resHom] using hcomponent
  apply Subtype.ext
  funext i
  by_cases hi : D.pieces i = ⊥
  · have hopen : ⊤ ⊓ D.pieces i = ⊥ := by rw [hi]; simp
    letI : Subsingleton Γ(relCurve C K, ⊤ ⊓ D.pieces i) := hopen ▸ inferInstance
    exact Subsingleton.elim _ _
  · have hUi : ((D.pieces i : Set (relCurve C K))).Nonempty := by
      rcases Set.eq_empty_or_nonempty (D.pieces i : Set (relCurve C K)) with h | h
      · exact (hi (by ext x; rw [h]; simp)).elim
      · exact h
    have hUji : (((D.pieces j ⊓ D.pieces i : (relCurve C K).Opens) :
        Set (relCurve C K))).Nonempty := by
      simpa only [Opens.coe_inf] using
        nonempty_preirreducible_inter (D.pieces j).isOpen (D.pieces i).isOpen hUj hUi
    letI : Nonempty ↥((D.pieces j ⊓ D.pieces i : (relCurve C K).Opens) :
        Set (relCurve C K)) := by
      obtain ⟨x, hx⟩ := hUji
      exact ⟨⟨x, hx⟩⟩
    have hinj : Function.Injective ((relCurve C K).resHom
        (show D.pieces j ⊓ D.pieces i ≤ ⊤ ⊓ D.pieces i by simp)) :=
      map_injective_of_isIntegral (H := this) (relCurve C K)
        (homOfLE (show D.pieces j ⊓ D.pieces i ≤ ⊤ ⊓ D.pieces i by simp))
    apply hinj
    have hval := congrArg (fun t => t.val i) hres
    simpa only [gluedRes_coe, Pi.zero_apply, Submodule.coe_zero, map_zero] using hval

/-- Every component of a nonzero global cocycle-glued section on an integral scheme is
a nonzerodivisor, including the vacuous empty-piece case. -/
theorem component_mem_nonZeroDivisors_of_global_ne_zero
    [IsIntegral (relCurve C K)] (D : BasicOpenCocycleDatum C K pi)
    (s : ↥(gluedSubmodule K D.pieces D.unit ⊤)) (hs : s ≠ 0) (j : D.index) :
    D.component s j ∈ nonZeroDivisors Γ(relCurve C K, D.pieces j) := by
  by_cases hj : D.pieces j = ⊥
  · letI : Subsingleton Γ(relCurve C K, D.pieces j) := hj ▸ inferInstance
    rw [mem_nonZeroDivisors_iff_right]
    intro z _
    exact Subsingleton.elim z 0
  · have hUj : ((D.pieces j : Set (relCurve C K))).Nonempty := by
      rcases Set.eq_empty_or_nonempty (D.pieces j : Set (relCurve C K)) with h | h
      · exact (hj (by ext x; rw [h]; simp)).elim
      · exact h
    let hnonempty : Nonempty {x : relCurve C K // x ∈ D.pieces j} := by
      obtain ⟨x, hx⟩ := hUj
      exact ⟨⟨x, hx⟩⟩
    haveI : IsDomain Γ(relCurve C K, D.pieces j) :=
      @IsIntegral.component_integral (relCurve C K) _ (D.pieces j) hnonempty
    exact mem_nonZeroDivisors_of_ne_zero
      (D.component_ne_zero_of_global_ne_zero s hs j hj)

variable {B : Type u} [CommRing B] [Algebra k B]

set_option maxHeartbeats 800000 in
-- Elaborating the tensor swap and piecewise base-change equivalence needs extra heartbeats.
theorem injective_rTensor_component_of_sectionsMapTop_ne_zero
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) (p : PrimeSpectrum B)
    [IsIntegral (relCurve C p.asIdeal.ResidueField)]
    (hs : D.sectionsMapTop p.asIdeal.ResidueField s ≠ 0) (j : D.index) :
    Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField) := by
  let e : Γ(relCurve C B, D.pieces j) ⊗[B] p.asIdeal.ResidueField ≃+*
      Γ(relCurve C p.asIdeal.ResidueField,
        (D.baseChange p.asIdeal.ResidueField).pieces j) :=
    (Algebra.TensorProduct.comm B Γ(relCurve C B, D.pieces j)
      p.asIdeal.ResidueField).toRingEquiv.trans
        (D.toBasicOpenCoverData.pieceTermBaseChange p.asIdeal.ResidueField j).toRingEquiv
  have hvalue : e (D.component s j ⊗ₜ[B] (1 : p.asIdeal.ResidueField)) =
      (D.baseChange p.asIdeal.ResidueField).component
        (D.sectionsMapTop p.asIdeal.ResidueField s) j := by
    change D.toBasicOpenCoverData.pieceTermBaseChange p.asIdeal.ResidueField j
      (Algebra.TensorProduct.comm B Γ(relCurve C B, D.pieces j)
        p.asIdeal.ResidueField
          (D.component s j ⊗ₜ[B] (1 : p.asIdeal.ResidueField))) = _
    rw [Algebra.TensorProduct.comm_tmul,
      D.toBasicOpenCoverData.pieceTermBaseChange_one_tmul
        p.asIdeal.ResidueField j (D.component s j),
      ← D.component_sectionsMapTop p.asIdeal.ResidueField s j]
  have hregular : (D.baseChange p.asIdeal.ResidueField).component
        (D.sectionsMapTop p.asIdeal.ResidueField s) j ∈
      nonZeroDivisors Γ(relCurve C p.asIdeal.ResidueField,
        (D.baseChange p.asIdeal.ResidueField).pieces j) :=
    (D.baseChange p.asIdeal.ResidueField).component_mem_nonZeroDivisors_of_global_ne_zero
      (D.sectionsMapTop p.asIdeal.ResidueField s) hs j
  have himage : e (D.component s j ⊗ₜ[B] (1 : p.asIdeal.ResidueField)) ∈
      nonZeroDivisors Γ(relCurve C p.asIdeal.ResidueField,
        (D.baseChange p.asIdeal.ResidueField).pieces j) := by
    rwa [hvalue]
  have hback : e.symm (e (D.component s j ⊗ₜ[B]
      (1 : p.asIdeal.ResidueField))) ∈
      nonZeroDivisors (Γ(relCurve C B, D.pieces j) ⊗[B] p.asIdeal.ResidueField) := by
    rw [← MulEquivClass.map_nonZeroDivisors e.symm]
    exact ⟨_, himage, rfl⟩
  apply injective_rTensor_mulSectionEnd_of_tmul_mem_nonZeroDivisors B
    (D.component s j) p
  simpa only [e.symm_apply_apply] using hback

end BasicOpenCocycleDatum

end AlgebraicGeometry
