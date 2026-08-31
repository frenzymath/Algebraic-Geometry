/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Projective.FiniteMapGenerators
import AlgebraicJacobian.Projective.ProjectiveCoordinateRelativeChart

/-!
# Gluing finite-map projective coordinates

Aligned twisted coordinates on the two inverse images of the standard charts
of `P1` define compatible normalized maps to one integral projective space.
They glue over the source, and pairing the glued map with the structural
morphism gives a map to relative projective space over the base field.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.P1FiniteMap.FiniteMapGenerators

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
variable {pi : C.left ⟶ P1 k}
variable (G : P1FiniteMap.FiniteMapGenerators pi)

/-- The common homogeneous coordinate index. -/
abbrev ProjectiveIndex : Type u := Fin (G.d + 1) ⊕ G.LiftedIndex

/-- The complete homogeneous coordinate family on the first source chart. -/
def projectiveCoordinates0 :
    G.ProjectiveIndex → Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 0) :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0
    G.d (pullbackCoord0 pi) G.liftedAA

/-- The complete homogeneous coordinate family on the second source chart. -/
def projectiveCoordinates1 :
    G.ProjectiveIndex → Γ(C.left, pi ⁻¹ᵁ P1.chartOpen k 1) :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1
    G.d (pullbackCoord1 pi) G.liftedBB

@[simp]
theorem projectiveCoordinates0_zero :
    G.projectiveCoordinates0
      (Sum.inl ⟨0, Nat.zero_lt_succ G.d⟩) = 1 :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0_zero
    G.d (pullbackCoord0 pi) G.liftedAA

@[simp]
theorem projectiveCoordinates1_last :
    G.projectiveCoordinates1
      (Sum.inl ⟨G.d, Nat.lt_succ_self G.d⟩) = 1 :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1_last
    G.d (pullbackCoord1 pi) G.liftedBB

/-- The lifted generator families retain their overlap equation. -/
theorem lifted_compatible (i : G.LiftedIndex) :
    sourceRestriction0 pi (G.liftedAA i) =
      sourceRestriction0 pi (pullbackCoord0 pi) ^ G.d *
        sourceRestriction1 pi (G.liftedBB i) :=
  G.compatible i.down

/-- The normalized projective-coordinate map on the first source chart. -/
def localProjectiveMap0 :
    (pi ⁻¹ᵁ P1.chartOpen k 0).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule
        G.ProjectiveIndex (ULift.{u} ℤ)) :=
  ProjectiveSpace.Coordinates.fromOpen (pi ⁻¹ᵁ P1.chartOpen k 0)
    (Sum.inl ⟨0, Nat.zero_lt_succ G.d⟩) G.projectiveCoordinates0
    G.projectiveCoordinates0_zero

/-- The normalized projective-coordinate map on the second source chart. -/
def localProjectiveMap1 :
    (pi ⁻¹ᵁ P1.chartOpen k 1).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule
        G.ProjectiveIndex (ULift.{u} ℤ)) :=
  ProjectiveSpace.Coordinates.fromOpen (pi ⁻¹ᵁ P1.chartOpen k 1)
    (Sum.inl ⟨G.d, Nat.lt_succ_self G.d⟩) G.projectiveCoordinates1
    G.projectiveCoordinates1_last

/-- The two local coordinate maps agree after restriction to the pulled-back
overlap. -/
theorem localProjectiveMap_compat :
    C.left.homOfLE inf_le_left ≫ G.localProjectiveMap0 =
      C.left.homOfLE inf_le_right ≫ G.localProjectiveMap1 := by
  exact AlgebraicJacobian.TwoChart.TwistedCoordinates.fromOpen_compat
    (pi ⁻¹ᵁ P1.chartOpen k 0) (pi ⁻¹ᵁ P1.chartOpen k 1)
    (pullbackCoord0 pi) (pullbackCoord1 pi) (sourceRestriction_mul pi)
    G.d G.liftedAA G.liftedBB G.lifted_compatible

/-- The two pulled-back standard opens, indexed in the ambient universe. -/
abbrev projectiveOpen (_G : P1FiniteMap.FiniteMapGenerators pi)
    (b : ULift.{u} Bool) : C.left.Opens :=
  bif b.down then pi ⁻¹ᵁ P1.chartOpen k 0 else pi ⁻¹ᵁ P1.chartOpen k 1

/-- The two pulled-back opens cover the source. -/
theorem iSup_projectiveOpen : (⨆ b, G.projectiveOpen b) = ⊤ := by
  have hpull :
      (pi ⁻¹ᵁ P1.chartOpen k 0) ⊔ (pi ⁻¹ᵁ P1.chartOpen k 1) = ⊤ := by
    change pi ⁻¹ᵁ (P1.chartOpen k 0 ⊔ P1.chartOpen k 1) = ⊤
    rw [P1.chartOpen_sup]
    rfl
  apply top_unique
  rw [← hpull]
  apply sup_le
  · simpa [projectiveOpen] using
      le_iSup (fun b : ULift.{u} Bool => G.projectiveOpen b) ⟨true⟩
  · simpa [projectiveOpen] using
      le_iSup (fun b : ULift.{u} Bool => G.projectiveOpen b) ⟨false⟩

/-- The open cover used to glue the two coordinate maps. -/
def projectiveOpenCover : C.left.OpenCover :=
  C.left.openCoverOfIsOpenCover G.projectiveOpen G.iSup_projectiveOpen

/-- The family of local coordinate maps over the two-open cover. -/
def localProjectiveFamily (b : ULift.{u} Bool) :
    (G.projectiveOpen b).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule
        G.ProjectiveIndex (ULift.{u} ℤ)) :=
  match b with
  | ⟨true⟩ => G.localProjectiveMap0
  | ⟨false⟩ => G.localProjectiveMap1

/-- The local family satisfies the pullback compatibility required for
scheme-morphism gluing. -/
theorem localProjectiveFamily_compat (b b' : ULift.{u} Bool) :
    pullback.fst (G.projectiveOpenCover.f b) (G.projectiveOpenCover.f b') ≫
        G.localProjectiveFamily b =
      pullback.snd (G.projectiveOpenCover.f b) (G.projectiveOpenCover.f b') ≫
        G.localProjectiveFamily b' := by
  rcases b with ⟨b⟩
  rcases b' with ⟨b'⟩
  cases b <;> cases b'
  · change pullback.fst (pi ⁻¹ᵁ P1.chartOpen k 1).ι
          (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.localProjectiveMap1 =
        pullback.snd (pi ⁻¹ᵁ P1.chartOpen k 1).ι
          (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.localProjectiveMap1
    have hfs : pullback.fst (pi ⁻¹ᵁ P1.chartOpen k 1).ι
          (pi ⁻¹ᵁ P1.chartOpen k 1).ι =
        pullback.snd (pi ⁻¹ᵁ P1.chartOpen k 1).ι
          (pi ⁻¹ᵁ P1.chartOpen k 1).ι := by
      rw [← cancel_mono (pi ⁻¹ᵁ P1.chartOpen k 1).ι]
      exact pullback.condition
    rw [hfs]
  · change pullback.fst (pi ⁻¹ᵁ P1.chartOpen k 1).ι
          (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.localProjectiveMap1 =
        pullback.snd (pi ⁻¹ᵁ P1.chartOpen k 1).ι
          (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.localProjectiveMap0
    have hpb := (isPullback_opens_inf
      (pi ⁻¹ᵁ P1.chartOpen k 0) (pi ⁻¹ᵁ P1.chartOpen k 1)).flip
    rw [← cancel_epi hpb.isoPullback.hom, ← Category.assoc,
      ← Category.assoc, hpb.isoPullback_hom_fst,
      hpb.isoPullback_hom_snd]
    exact G.localProjectiveMap_compat.symm
  · change pullback.fst (pi ⁻¹ᵁ P1.chartOpen k 0).ι
          (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.localProjectiveMap0 =
        pullback.snd (pi ⁻¹ᵁ P1.chartOpen k 0).ι
          (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.localProjectiveMap1
    have hpb := isPullback_opens_inf
      (pi ⁻¹ᵁ P1.chartOpen k 0) (pi ⁻¹ᵁ P1.chartOpen k 1)
    rw [← cancel_epi hpb.isoPullback.hom, ← Category.assoc,
      ← Category.assoc, hpb.isoPullback_hom_fst,
      hpb.isoPullback_hom_snd]
    exact G.localProjectiveMap_compat
  · change pullback.fst (pi ⁻¹ᵁ P1.chartOpen k 0).ι
          (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.localProjectiveMap0 =
        pullback.snd (pi ⁻¹ᵁ P1.chartOpen k 0).ι
          (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.localProjectiveMap0
    have hfs : pullback.fst (pi ⁻¹ᵁ P1.chartOpen k 0).ι
          (pi ⁻¹ᵁ P1.chartOpen k 0).ι =
        pullback.snd (pi ⁻¹ᵁ P1.chartOpen k 0).ι
          (pi ⁻¹ᵁ P1.chartOpen k 0).ι := by
      rw [← cancel_mono (pi ⁻¹ᵁ P1.chartOpen k 0).ι]
      exact pullback.condition
    rw [hfs]

/-- The global integral projective-coordinate map obtained by gluing. -/
def toProjInt :
    C.left ⟶ Proj (MvPolynomial.homogeneousSubmodule
      G.ProjectiveIndex (ULift.{u} ℤ)) :=
  G.projectiveOpenCover.glueMorphisms G.localProjectiveFamily
    G.localProjectiveFamily_compat

/-- The glued map restricts to the first normalized coordinate map. -/
theorem open0_toProjInt :
    (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.toProjInt =
      G.localProjectiveMap0 := by
  have h := Scheme.Cover.ι_glueMorphisms G.projectiveOpenCover
    G.localProjectiveFamily G.localProjectiveFamily_compat
    (⟨true⟩ : ULift.{u} Bool)
  change (pi ⁻¹ᵁ P1.chartOpen k 0).ι ≫ G.toProjInt =
    G.localProjectiveMap0 at h
  exact h

/-- The glued map restricts to the second normalized coordinate map. -/
theorem open1_toProjInt :
    (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.toProjInt =
      G.localProjectiveMap1 := by
  have h := Scheme.Cover.ι_glueMorphisms G.projectiveOpenCover
    G.localProjectiveFamily G.localProjectiveFamily_compat
    (⟨false⟩ : ULift.{u} Bool)
  change (pi ⁻¹ᵁ P1.chartOpen k 1).ι ≫ G.toProjInt =
    G.localProjectiveMap1 at h
  exact h

/-- The global relative projective-coordinate morphism over the base field. -/
def toProjectiveSpace : C.left ⟶ ℙ(G.ProjectiveIndex; Spec (.of k)) :=
  pullback.lift C.hom G.toProjInt (Subsingleton.elim _ _)

@[reassoc]
theorem toProjectiveSpace_over :
    G.toProjectiveSpace ≫
        (ℙ(G.ProjectiveIndex; Spec (.of k)) ↘ Spec (.of k)) = C.hom := by
  rw [ProjectiveSpace.over_eq_fst]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem toProjectiveSpace_toProjInt :
    G.toProjectiveSpace ≫
        ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (.of k)) =
      G.toProjInt := by
  rw [ProjectiveSpace.toProjInt_eq_snd]
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.P1FiniteMap.FiniteMapGenerators
