/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0SepClosedJacobianData
import AlgebraicJacobian.Picard.FinitePresentationAlgebraFiniteStage

/-!
# A finite affine atlas for the separably closed Picard representer

The exact separably closed `Pic^0` representer is quasi-compact, quasi-separated, and
locally of finite presentation over the ground field.  This file combines those facts
into a finite affine atlas whose overlap spaces are quasi-compact and whose chart rings
are finitely presented over the ground field.  This is the finite collection of algebraic
data needed to spread the representer out from a separable closure.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace TensorProduct

namespace AlgebraicGeometry

noncomputable section

/-! ## A project-local finite-cover supplement -/

/-- A quasi-compact, quasi-separated scheme has a finite affine open cover with
quasi-compact pairwise intersections. -/
theorem Scheme.exists_finite_affineCover_inter_isQuasiCompact (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ s : Set X.affineOpens, s.Finite ∧ (⨆ i ∈ s, (i : X.Opens)) = ⊤ ∧
      ∀ U ∈ s, ∀ V ∈ s, IsCompact ((U : Set X) ∩ (V : Set X)) := by
  obtain ⟨s, hs, he⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
      (by simpa using isCompact_univ (X := X))
  refine ⟨s, hs, he.symm, ?_⟩
  intro U _ V _
  exact quasiSeparatedSpace_iff_forall_affineOpens.mp ‹_› U V

/-- A finite affine presentation of the intersection of two affine opens.  Besides
covering the intersection exactly, it records finite presentation of both restriction
maps from the chart rings to every overlap-piece ring. -/
structure Scheme.FiniteAffineOverlapPresentation (X : Scheme.{u})
    (U V : X.affineOpens) where
  pieces : Set X.affineOpens
  finite_pieces : pieces.Finite
  iSup_opens : (⨆ W ∈ pieces, (W : X.Opens)) = U.1 ⊓ V.1
  piece_le_left : ∀ W ∈ pieces, W.1 ≤ U.1
  piece_le_right : ∀ W ∈ pieces, W.1 ≤ V.1
  leftRestriction_finitePresentation : ∀ W (hW : W ∈ pieces),
    (X.homOfLE (piece_le_left W hW)).appTop.hom.FinitePresentation
  rightRestriction_finitePresentation : ∀ W (hW : W ∈ pieces),
    (X.homOfLE (piece_le_right W hW)).appTop.hom.FinitePresentation

/-- A compact intersection of two affine opens admits a finite affine overlap
presentation.  The two restriction maps are finitely presented because the inclusions
of the affine overlap pieces into the affine charts are open immersions. -/
noncomputable def Scheme.finiteAffineOverlapPresentation (X : Scheme.{u})
    (U V : X.affineOpens) (h : IsCompact ((U : Set X) ∩ (V : Set X))) :
    X.FiniteAffineOverlapPresentation U V := by
  apply Classical.choice
  obtain ⟨s, hs, he⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := U.1 ⊓ V.1)).mp
      (by simpa using h)
  have hle (W : X.affineOpens) (hW : W ∈ s) : W.1 ≤ U.1 ⊓ V.1 := by
    rw [he]
    exact le_iSup_of_le W (le_iSup_of_le hW le_rfl)
  refine ⟨
    { pieces := s
      finite_pieces := hs
      iSup_opens := he.symm
      piece_le_left := fun W hW => (hle W hW).trans inf_le_left
      piece_le_right := fun W hW => (hle W hW).trans inf_le_right
      leftRestriction_finitePresentation := ?_
      rightRestriction_finitePresentation := ?_ }⟩
  · intro W hW
    exact (X.homOfLE ((hle W hW).trans inf_le_left)).finitePresentation_appTop
  · intro W hW
    exact (X.homOfLE ((hle W hW).trans inf_le_right)).finitePresentation_appTop

/-! ## The finite atlas on the exact `Pic^0` representer -/

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-- A finite affine atlas on the exact separably closed `Pic^0` representer, including
the two finiteness properties needed for chart-ring spreading: quasi-compact overlaps
and finite presentation of every selected chart ring over the ground field. -/
structure Pic0FiniteStageAtlas where
  charts : Set (pic0_sepClosed_representableBy (C := C)).1.left.affineOpens
  finite_charts : charts.Finite
  iSup_opens :
    (⨆ U ∈ charts,
      (U : (pic0_sepClosed_representableBy (C := C)).1.left.Opens)) = ⊤
  inter_isCompact : ∀ U ∈ charts, ∀ V ∈ charts,
    IsCompact
      ((U : Set (pic0_sepClosed_representableBy (C := C)).1.left) ∩
        (V : Set (pic0_sepClosed_representableBy (C := C)).1.left))
  chartRing_finitePresentation : ∀ U ∈ charts,
    ((pic0_sepClosed_representableBy (C := C)).1.hom.appLE
      (⊤ : (Spec (.of k)).Opens) U.1 le_top).hom.FinitePresentation
  overlapPresentation : ∀ U ∈ charts, ∀ V ∈ charts,
    (pic0_sepClosed_representableBy (C := C)).1.left.FiniteAffineOverlapPresentation U V

/-- The finite affine atlas obtained from quasi-compactness, quasi-separatedness, and
local finite presentation of the exact separably closed `Pic^0` representer. -/
noncomputable def pic0FiniteStageAtlas : Pic0FiniteStageAtlas C := by
  apply Classical.choice
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : QuasiCompact J.hom := quasiCompact_pic0SepClosedRepresenter C
  letI : CompactSpace J.left := QuasiCompact.compactSpace_of_compactSpace J.hom
  letI : QuasiSeparatedSpace J.left := quasiSeparatedSpace_pic0SepClosedRepresenter C
  letI : LocallyOfFinitePresentation J.hom :=
    locallyOfFinitePresentation_pic0_sepClosed_representableBy C
  obtain ⟨s, hs, hcover, hinter⟩ :=
    Scheme.exists_finite_affineCover_inter_isQuasiCompact J.left
  refine ⟨
    { charts := s
      finite_charts := hs
      iSup_opens := hcover
      inter_isCompact := hinter
      chartRing_finitePresentation := ?_
      overlapPresentation := fun U hU V hV =>
        J.left.finiteAffineOverlapPresentation U V (hinter U hU V hV) }⟩
  intro U _
  exact J.hom.finitePresentation_appLE (isAffineOpen_top _) U.2 le_top

/-! ## Simultaneous finite-stage chart-ring models -/

/-- The section ring of one chart in the chosen finite `Pic^0` atlas, equipped below with
the algebra structure induced by the structure morphism of the exact representer. -/
def Pic0FiniteStageChartRing
    (U : { U // U ∈ (pic0FiniteStageAtlas C).charts }) : Type u :=
  Γ((pic0_sepClosed_representableBy (C := C)).1.left, U.1.1)

instance (U : { U // U ∈ (pic0FiniteStageAtlas C).charts }) :
    CommRing (Pic0FiniteStageChartRing C U) := by
  dsimp [Pic0FiniteStageChartRing]
  infer_instance

noncomputable instance (U : { U // U ∈ (pic0FiniteStageAtlas C).charts }) :
    Algebra k (Pic0FiniteStageChartRing C U) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact (J.left.overAlgebraMap k U.1.1).toAlgebra

/-- Every ring in the chosen finite `Pic^0` atlas is finitely presented for its canonical
algebra structure over the separably closed ground field. -/
theorem finitePresentation_pic0FiniteStageChartRing
    (U : { U // U ∈ (pic0FiniteStageAtlas C).charts }) :
    Algebra.FinitePresentation k (Pic0FiniteStageChartRing C U) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  change (J.left.overAlgebraMap k U.1.1).FinitePresentation
  rw [Scheme.overAlgebraMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  apply RingHom.FinitePresentation.comp
  · exact (pic0FiniteStageAtlas C).chartRing_finitePresentation U.1 U.2
  · exact RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)

set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating the dependent quotient inside the tensor product requires a larger typeclass budget.
/-- All chart rings in the finite atlas of the exact separably closed `Pic^0` representer
are simultaneously defined over one finite subextension.  This is the object layer of
spreading out the atlas; restriction maps and their cocycle equations remain separate data. -/
theorem exists_finSubext_pic0FiniteStageAtlas_chartRing_models
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k] :
    ∃ L : DatG0.FinSubext F k,
      ∀ U : { U // U ∈ (pic0FiniteStageAtlas C).charts },
        ∃ n m : ℕ, ∃ relation : Fin m → MvPolynomial (Fin n) L.1,
          Nonempty
            (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 n m relation ≃ₐ[k]
              Pic0FiniteStageChartRing C U) := by
  letI : Finite { U // U ∈ (pic0FiniteStageAtlas C).charts } :=
    (pic0FiniteStageAtlas C).finite_charts.to_subtype
  letI (U : { U // U ∈ (pic0FiniteStageAtlas C).charts }) :
      Algebra.FinitePresentation k (Pic0FiniteStageChartRing C U) :=
    finitePresentation_pic0FiniteStageChartRing C U
  exact DatG0.exists_finSubext_finitePresentation_algebra_model_finite
    (fun U : { U // U ∈ (pic0FiniteStageAtlas C).charts } =>
      Pic0FiniteStageChartRing C U)

end

end AlgebraicGeometry
