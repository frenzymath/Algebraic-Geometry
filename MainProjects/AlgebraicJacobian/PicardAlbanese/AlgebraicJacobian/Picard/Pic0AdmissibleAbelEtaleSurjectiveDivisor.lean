/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.SectionsToDivisorsClass
import AlgebraicJacobian.Picard.LocalGenerators
import AlgebraicJacobian.Picard.DivisorFamilyAffAssemble
import AlgebraicJacobian.Picard.DivisorFamilyAffFibreTower

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

namespace BasicOpenCoverData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

/-- The pinned-chart side containing a basic-open piece. -/
def pinnedSide (D : BasicOpenCoverData C B pi) : D.index → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- The pinned-chart section cutting out a basic-open piece. -/
noncomputable def pinnedGenerator (D : BasicOpenCoverData C B pi) :
    (j : D.index) → Γ(relCurve C B, relPinnedChart C B pi (D.pinnedSide j))
  | Sum.inl j => D.h₀ j
  | Sum.inr j => D.h₁ j

theorem pieces_eq_basicOpen_pinnedGenerator
    (D : BasicOpenCoverData C B pi) (j : D.index) :
    D.pieces j = (relCurve C B).basicOpen (D.pinnedGenerator j) := by
  cases j <;> rfl

end BasicOpenCoverData

namespace BasicOpenCocycleDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {B : Type u} [CommRing B] [Algebra k B]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

/-- A datum component, with its open written using the uniform pinned generator. -/
noncomputable def pinnedComponent (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤)) :
    (j : D.index) → Γ(relCurve C B,
      (relCurve C B).basicOpen (D.toBasicOpenCoverData.pinnedGenerator j))
  | Sum.inl j => D.component s (Sum.inl j)
  | Sum.inr j => D.component s (Sum.inr j)

/-- Fibrewise injectivity of multiplication by a datum component gives the ring-theoretic
nonzerodivisor condition on its pure tensor. -/
theorem component_tmul_one_mem_nonZeroDivisors
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (j : D.index) (p : PrimeSpectrum B) :
    letI : Algebra B Γ(relCurve C B, D.pieces j) :=
      ((relCurve C B).overAlgebraMap B (D.pieces j)).toAlgebra
    (D.component s j ⊗ₜ[B] (1 : p.asIdeal.ResidueField) :
      Γ(relCurve C B, D.pieces j) ⊗[B] p.asIdeal.ResidueField) ∈
        nonZeroDivisors
          (Γ(relCurve C B, D.pieces j) ⊗[B] p.asIdeal.ResidueField) := by
  letI : Algebra B Γ(relCurve C B, D.pieces j) :=
    ((relCurve C B).overAlgebraMap B (D.pieces j)).toAlgebra
  have hend : Scheme.mulSectionEnd B (D.component s j) =
      LinearMap.mulLeft B (D.component s j) := by
    ext t
    simp [Scheme.mulSectionEnd_apply]
  have hinj := hfib j p
  rw [hend, rTensor_mulLeft_eq_mulLeft_tmul p.asIdeal.ResidueField
    (D.component s j)] at hinj
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro z hz
    apply hinj
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_zero]
    exact hz
  · intro z hz
    apply hinj
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_zero, mul_comm]
    exact hz

/-- Fibrewise-regular datum components remain nonzerodivisors on their pinned basic opens
after every coefficient-ring extension. -/
theorem pinnedComponent_baseChange_mem_nonZeroDivisors [IsNoetherianRing B]
    (D : BasicOpenCocycleDatum C B pi)
    (s : ↥(gluedSubmodule B D.pieces D.unit ⊤))
    (hfib : ∀ (j : D.index) (p : PrimeSpectrum B), Function.Injective
      ((Scheme.mulSectionEnd B (D.component s j)).rTensor p.asIdeal.ResidueField))
    (B' : Type u) [CommRing B'] [Algebra k B'] [Algebra B B']
    [IsScalarTower k B B'] (j : D.index) :
    relPinnedPieceSectionsMap (C := C) (R := B) (pi := pi) B'
        (D.toBasicOpenCoverData.pinnedSide j)
        (D.toBasicOpenCoverData.pinnedGenerator j) (D.pinnedComponent s j) ∈
      nonZeroDivisors
        Γ(relCurve C B', (relCurve C B').basicOpen
          (relPinnedSectionsMap C B B' pi
            (D.toBasicOpenCoverData.pinnedSide j)
            (D.toBasicOpenCoverData.pinnedGenerator j))) := by
  cases j with
  | inl j =>
      haveI : Module.Free B
          Γ(relCurve C B, (relCover C B (fiberTwoCover pi)).V₀) :=
        free_relSections C B (fiberChart₀ pi)
          (isAffineOpen_preimage_chartOpen pi 0).isCompact
          (isAffineOpen_preimage_chartOpen pi 0).isQuasiSeparated
      letI : Module.Flat B Γ(relCurve C B, D.pieces (Sum.inl j)) := by
        rw [D.toBasicOpenCoverData.pieces_inl]
        exact flat_sections_basicOpen B
          (relCover_isAffineOpen₀ C B (fiberTwoCover pi)) Module.Flat.of_free (D.h₀ j)
      have hbase :=
        Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_forall_tmul_residueField
          (fun p => D.component_tmul_one_mem_nonZeroDivisors s hfib (Sum.inl j) p) B'
      have hpulled := map_mem_nonZeroDivisors'
        (relPinnedPieceBaseChange (C := C) (R := B) (pi := pi)
          B' false (D.h₀ j)).toRingEquiv hbase
      change relPinnedPieceBaseChange (C := C) (R := B) (pi := pi)
          B' false (D.h₀ j) ((1 : B') ⊗ₜ[B] D.component s (Sum.inl j)) ∈
        nonZeroDivisors _ at hpulled
      rw [relPinnedPieceBaseChange_one_tmul] at hpulled
      change relPinnedPieceSectionsMap (C := C) (R := B) (pi := pi)
          B' false (D.h₀ j) (D.component s (Sum.inl j)) ∈ nonZeroDivisors _
      exact hpulled
  | inr j =>
      haveI : Module.Free B
          Γ(relCurve C B, (relCover C B (fiberTwoCover pi)).V₁) :=
        free_relSections C B (fiberChart₁ pi)
          (isAffineOpen_preimage_chartOpen pi 1).isCompact
          (isAffineOpen_preimage_chartOpen pi 1).isQuasiSeparated
      letI : Module.Flat B Γ(relCurve C B, D.pieces (Sum.inr j)) := by
        rw [D.toBasicOpenCoverData.pieces_inr]
        exact flat_sections_basicOpen B
          (relCover_isAffineOpen₁ C B (fiberTwoCover pi)) Module.Flat.of_free (D.h₁ j)
      have hbase :=
        Algebra.TensorProduct.includeRight_mem_nonZeroDivisors_of_forall_tmul_residueField
          (fun p => D.component_tmul_one_mem_nonZeroDivisors s hfib (Sum.inr j) p) B'
      have hpulled := map_mem_nonZeroDivisors'
        (relPinnedPieceBaseChange (C := C) (R := B) (pi := pi)
          B' true (D.h₁ j)).toRingEquiv hbase
      change relPinnedPieceBaseChange (C := C) (R := B) (pi := pi)
          B' true (D.h₁ j) ((1 : B') ⊗ₜ[B] D.component s (Sum.inr j)) ∈
        nonZeroDivisors _ at hpulled
      rw [relPinnedPieceBaseChange_one_tmul] at hpulled
      change relPinnedPieceSectionsMap (C := C) (R := B) (pi := pi)
          B' true (D.h₁ j) (D.component s (Sum.inr j)) ∈ nonZeroDivisors _
      exact hpulled

end BasicOpenCocycleDatum

end AlgebraicGeometry
