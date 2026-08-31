/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageAffineIntersections
import AlgebraicJacobian.Picard.FinitePresentationAlgebraFiniteStage

/-!
# Simultaneous finite-stage models for Picard atlas and overlap rings

The pairwise intersections in the chosen finite affine atlas of the exact separably closed
`Pic^0` representer are affine.  This file packages their section rings with their canonical
ground-field algebra structures and spreads all chart and pair-overlap rings out over one
finite subextension.  Restriction maps and gluing identities are separate descent data.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

/-! ## Canonical affine overlap rings -/

/-- The section ring of the exact intersection of two chosen charts in the finite atlas. -/
def Pic0FiniteStageOverlapRing
    (U V : Pic0FiniteStageChartIndex C) : Type u :=
  Γ((pic0_sepClosed_representableBy (C := C)).1.left,
    (pic0FiniteStageAffineOverlap C U V).1)

instance (U V : Pic0FiniteStageChartIndex C) :
    CommRing (Pic0FiniteStageOverlapRing C U V) := by
  dsimp [Pic0FiniteStageOverlapRing]
  infer_instance

/-- The overlap ring's canonical algebra structure induced by the representer's structure
morphism to `Spec k`. -/
noncomputable instance (U V : Pic0FiniteStageChartIndex C) :
    Algebra k (Pic0FiniteStageOverlapRing C U V) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact (J.left.overAlgebraMap k (pic0FiniteStageAffineOverlap C U V).1).toAlgebra

/-- Every exact pair-overlap ring is finitely presented over the separably closed ground
field.  Affineness comes from separatedness of the group representer. -/
theorem finitePresentation_pic0FiniteStageOverlapRing
    (U V : Pic0FiniteStageChartIndex C) :
    Algebra.FinitePresentation k (Pic0FiniteStageOverlapRing C U V) := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  letI : LocallyOfFinitePresentation J.hom :=
    locallyOfFinitePresentation_pic0_sepClosed_representableBy C
  change (J.left.overAlgebraMap k (pic0FiniteStageAffineOverlap C U V).1).FinitePresentation
  rw [Scheme.overAlgebraMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  apply RingHom.FinitePresentation.comp
  · exact J.hom.finitePresentation_appLE (isAffineOpen_top _)
      (pic0FiniteStageAffineOverlap C U V).2 le_top
  · exact RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)

/-! ## One finite family containing charts and overlaps -/

/-- A finite tag for every chart ring and every ordered pair-overlap ring in the atlas. -/
abbrev Pic0FiniteStageRingIndex :=
  Pic0FiniteStageChartIndex C ⊕
    (Pic0FiniteStageChartIndex C × Pic0FiniteStageChartIndex C)

/-- The ring selected by a finite-stage ring tag. -/
def Pic0FiniteStageRing (i : Pic0FiniteStageRingIndex C) : Type u :=
  match i with
  | Sum.inl U => Pic0FiniteStageChartRing C U
  | Sum.inr UV => Pic0FiniteStageOverlapRing C UV.1 UV.2

instance (i : Pic0FiniteStageRingIndex C) :
    CommRing (Pic0FiniteStageRing C i) := by
  rcases i with U | ⟨U, V⟩
  · change CommRing (Pic0FiniteStageChartRing C U)
    infer_instance
  · change CommRing (Pic0FiniteStageOverlapRing C U V)
    infer_instance

noncomputable instance (i : Pic0FiniteStageRingIndex C) :
    Algebra k (Pic0FiniteStageRing C i) := by
  rcases i with U | ⟨U, V⟩
  · change Algebra k (Pic0FiniteStageChartRing C U)
    infer_instance
  · change Algebra k (Pic0FiniteStageOverlapRing C U V)
    infer_instance

/-- Every ring in the combined finite family is finitely presented over the ground field. -/
theorem finitePresentation_pic0FiniteStageRing
    (i : Pic0FiniteStageRingIndex C) :
    Algebra.FinitePresentation k (Pic0FiniteStageRing C i) := by
  rcases i with U | ⟨U, V⟩
  · exact finitePresentation_pic0FiniteStageChartRing C U
  · exact finitePresentation_pic0FiniteStageOverlapRing C U V

/-! ## The finite family of canonical restriction maps -/

/-- Restriction from the left chart to its exact pairwise overlap, as an algebra map over
the separably closed ground field. -/
noncomputable def pic0FiniteStageRestrictionLeft
    (U V : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageChartRing C U →ₐ[k] Pic0FiniteStageOverlapRing C U V := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact
    { J.left.resHom (pic0FiniteStageAffineOverlap_le_left C U V) with
      commutes' := fun r =>
        J.left.overAlgebraMap_apply_res k
          (homOfLE (pic0FiniteStageAffineOverlap_le_left C U V)).op r }

/-- Restriction from the right chart to its exact pairwise overlap, as an algebra map over
the separably closed ground field. -/
noncomputable def pic0FiniteStageRestrictionRight
    (U V : Pic0FiniteStageChartIndex C) :
    Pic0FiniteStageChartRing C V →ₐ[k] Pic0FiniteStageOverlapRing C U V := by
  let J := (pic0_sepClosed_representableBy (C := C)).1
  letI : J.left.Over (Spec (.of k)) := ⟨J.hom⟩
  exact
    { J.left.resHom (pic0FiniteStageAffineOverlap_le_right C U V) with
      commutes' := fun r =>
        J.left.overAlgebraMap_apply_res k
          (homOfLE (pic0FiniteStageAffineOverlap_le_right C U V)).op r }

/-- A finite tag for both restriction maps associated to every ordered chart pair. -/
abbrev Pic0FiniteStageRestrictionIndex :=
  (Pic0FiniteStageChartIndex C × Pic0FiniteStageChartIndex C) ⊕
    (Pic0FiniteStageChartIndex C × Pic0FiniteStageChartIndex C)

/-- The source-ring tag of a canonical atlas restriction map. -/
def Pic0FiniteStageRestrictionSource :
    Pic0FiniteStageRestrictionIndex C → Pic0FiniteStageRingIndex C
  | Sum.inl UV => Sum.inl UV.1
  | Sum.inr UV => Sum.inl UV.2

/-- The target-ring tag of a canonical atlas restriction map. -/
def Pic0FiniteStageRestrictionTarget :
    Pic0FiniteStageRestrictionIndex C → Pic0FiniteStageRingIndex C
  | Sum.inl UV => Sum.inr UV
  | Sum.inr UV => Sum.inr UV

/-- Every left and right restriction map in the exact finite affine atlas, packaged as one
finite dependent family. -/
noncomputable def pic0FiniteStageRestriction
    (i : Pic0FiniteStageRestrictionIndex C) :
    Pic0FiniteStageRing C (Pic0FiniteStageRestrictionSource C i) →ₐ[k]
      Pic0FiniteStageRing C (Pic0FiniteStageRestrictionTarget C i) := by
  rcases i with ⟨U, V⟩ | ⟨U, V⟩
  · exact pic0FiniteStageRestrictionLeft C U V
  · exact pic0FiniteStageRestrictionRight C U V

set_option synthInstance.maxHeartbeats 200000 in
-- The generic family theorem elaborates a dependent presentation for every finite tag.
/-- All chart rings and all exact pair-overlap rings are simultaneously defined over one
finite subextension of an algebraic field extension `k/F`.  This is the complete object layer
for the chosen affine gluing datum; its restriction maps and equations must still be spread out. -/
theorem exists_finSubext_pic0FiniteStageAtlas_ring_models
    {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k] :
    ∃ L : DatG0.FinSubext F k,
      ∀ i : Pic0FiniteStageRingIndex C,
        ∃ n m : ℕ, ∃ relation : Fin m → MvPolynomial (Fin n) L.1,
          Nonempty
            (k ⊗[L.1] DatG0.FiniteRelationAlgebra L.1 n m relation ≃ₐ[k]
              Pic0FiniteStageRing C i) := by
  letI (i : Pic0FiniteStageRingIndex C) :
      Algebra.FinitePresentation k (Pic0FiniteStageRing C i) :=
    finitePresentation_pic0FiniteStageRing C i
  exact DatG0.exists_finSubext_finitePresentation_algebra_model_finite
    (fun i : Pic0FiniteStageRingIndex C => Pic0FiniteStageRing C i)

end

end AlgebraicGeometry
