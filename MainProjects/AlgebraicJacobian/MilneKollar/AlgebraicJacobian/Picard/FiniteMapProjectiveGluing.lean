/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteMapProjectiveCoordinates

/-!
# Gluing finite-map projective coordinates

Compatible twisted coordinate maps on the two pulled-back Laurent charts glue
to an integral projective-coordinate map on the whole source. Pairing that map
with the structural morphism gives a morphism to relative projective space over
the base field. The relative lift, rather than the absolute map to integral
`Proj`, is the candidate immersion used to prove projectivity.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]
variable {Y C : Over (Spec (CommRingCat.of k))}

namespace LaurentChartData.FiniteMapGenerators

variable {D : LaurentChartData Y} {pi : C ⟶ Y}
variable (G : D.FiniteMapGenerators pi)

/-- The two pulled-back Laurent opens, indexed in the ambient universe. -/
abbrev projectiveOpen (_G : D.FiniteMapGenerators pi)
    (b : ULift.{u} Bool) : C.left.Opens :=
  bif b.down then pi.left ⁻¹ᵁ D.V₀ else pi.left ⁻¹ᵁ D.V₁

/-- The two pulled-back opens cover the source. -/
theorem iSup_projectiveOpen : (⨆ b, G.projectiveOpen b) = ⊤ := by
  have hpull : (pi.left ⁻¹ᵁ D.V₀) ⊔ (pi.left ⁻¹ᵁ D.V₁) = ⊤ := by
    change pi.left ⁻¹ᵁ (D.V₀ ⊔ D.V₁) = ⊤
    rw [D.cover]
    rfl
  apply top_unique
  rw [← hpull]
  apply sup_le
  · simpa [projectiveOpen] using
      le_iSup (fun b : ULift.{u} Bool => G.projectiveOpen b) ⟨true⟩
  · simpa [projectiveOpen] using
      le_iSup (fun b : ULift.{u} Bool => G.projectiveOpen b) ⟨false⟩

/-- The open cover used to glue the two projective-coordinate morphisms. -/
def projectiveOpenCover : C.left.OpenCover :=
  C.left.openCoverOfIsOpenCover G.projectiveOpen G.iSup_projectiveOpen

/-- The family of local projective-coordinate morphisms over the two-open
cover. -/
def localProjectiveFamily (b : ULift.{u} Bool) :
    (G.projectiveOpen b).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ)) :=
  match b with
  | ⟨true⟩ => G.localProjectiveMap0
  | ⟨false⟩ => G.localProjectiveMap1

/-- The local family satisfies the pullback compatibility required by scheme
morphism gluing. -/
theorem localProjectiveFamily_compat (b b' : ULift.{u} Bool) :
    pullback.fst (G.projectiveOpenCover.f b) (G.projectiveOpenCover.f b') ≫
        G.localProjectiveFamily b =
      pullback.snd (G.projectiveOpenCover.f b) (G.projectiveOpenCover.f b') ≫
        G.localProjectiveFamily b' := by
  rcases b with ⟨b⟩
  rcases b' with ⟨b'⟩
  cases b <;> cases b'
  · change pullback.fst (pi.left ⁻¹ᵁ D.V₁).ι (pi.left ⁻¹ᵁ D.V₁).ι ≫
        G.localProjectiveMap1 =
      pullback.snd (pi.left ⁻¹ᵁ D.V₁).ι (pi.left ⁻¹ᵁ D.V₁).ι ≫
        G.localProjectiveMap1
    have hfs : pullback.fst (pi.left ⁻¹ᵁ D.V₁).ι (pi.left ⁻¹ᵁ D.V₁).ι =
        pullback.snd (pi.left ⁻¹ᵁ D.V₁).ι (pi.left ⁻¹ᵁ D.V₁).ι := by
      rw [← cancel_mono (pi.left ⁻¹ᵁ D.V₁).ι]
      exact pullback.condition
    rw [hfs]
  · change pullback.fst (pi.left ⁻¹ᵁ D.V₁).ι (pi.left ⁻¹ᵁ D.V₀).ι ≫
        G.localProjectiveMap1 =
      pullback.snd (pi.left ⁻¹ᵁ D.V₁).ι (pi.left ⁻¹ᵁ D.V₀).ι ≫
        G.localProjectiveMap0
    have hpb := (isPullback_opens_inf
      (pi.left ⁻¹ᵁ D.V₀) (pi.left ⁻¹ᵁ D.V₁)).flip
    rw [← cancel_epi hpb.isoPullback.hom, ← Category.assoc,
      ← Category.assoc, hpb.isoPullback_hom_fst,
      hpb.isoPullback_hom_snd]
    exact G.localProjectiveMap_compat.symm
  · change pullback.fst (pi.left ⁻¹ᵁ D.V₀).ι (pi.left ⁻¹ᵁ D.V₁).ι ≫
        G.localProjectiveMap0 =
      pullback.snd (pi.left ⁻¹ᵁ D.V₀).ι (pi.left ⁻¹ᵁ D.V₁).ι ≫
        G.localProjectiveMap1
    have hpb := isPullback_opens_inf
      (pi.left ⁻¹ᵁ D.V₀) (pi.left ⁻¹ᵁ D.V₁)
    rw [← cancel_epi hpb.isoPullback.hom, ← Category.assoc,
      ← Category.assoc, hpb.isoPullback_hom_fst,
      hpb.isoPullback_hom_snd]
    exact G.localProjectiveMap_compat
  · change pullback.fst (pi.left ⁻¹ᵁ D.V₀).ι (pi.left ⁻¹ᵁ D.V₀).ι ≫
        G.localProjectiveMap0 =
      pullback.snd (pi.left ⁻¹ᵁ D.V₀).ι (pi.left ⁻¹ᵁ D.V₀).ι ≫
        G.localProjectiveMap0
    have hfs : pullback.fst (pi.left ⁻¹ᵁ D.V₀).ι (pi.left ⁻¹ᵁ D.V₀).ι =
        pullback.snd (pi.left ⁻¹ᵁ D.V₀).ι (pi.left ⁻¹ᵁ D.V₀).ι := by
      rw [← cancel_mono (pi.left ⁻¹ᵁ D.V₀).ι]
      exact pullback.condition
    rw [hfs]

/-- The global integral projective-coordinate map obtained by gluing. -/
def toProjInt :
    C.left ⟶
      Proj (MvPolynomial.homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ)) :=
  G.projectiveOpenCover.glueMorphisms G.localProjectiveFamily
    G.localProjectiveFamily_compat

/-- The glued map restricts to the first normalized coordinate map. -/
theorem open0_toProjInt :
    (pi.left ⁻¹ᵁ D.V₀).ι ≫ G.toProjInt = G.localProjectiveMap0 := by
  have h := Scheme.Cover.ι_glueMorphisms G.projectiveOpenCover
    G.localProjectiveFamily G.localProjectiveFamily_compat
    (⟨true⟩ : ULift.{u} Bool)
  change (pi.left ⁻¹ᵁ D.V₀).ι ≫ G.toProjInt =
    G.localProjectiveMap0 at h
  exact h

/-- The glued map restricts to the second normalized coordinate map. -/
theorem open1_toProjInt :
    (pi.left ⁻¹ᵁ D.V₁).ι ≫ G.toProjInt = G.localProjectiveMap1 := by
  have h := Scheme.Cover.ι_glueMorphisms G.projectiveOpenCover
    G.localProjectiveFamily G.localProjectiveFamily_compat
    (⟨false⟩ : ULift.{u} Bool)
  change (pi.left ⁻¹ᵁ D.V₁).ι ≫ G.toProjInt =
    G.localProjectiveMap1 at h
  exact h

/-- The global relative projective-coordinate morphism over the base field. -/
def toProjectiveSpace : C.left ⟶ ℙ(G.ProjectiveIndex; Spec (CommRingCat.of k)) :=
  pullback.lift C.hom G.toProjInt (Subsingleton.elim _ _)

@[reassoc]
theorem toProjectiveSpace_over :
    G.toProjectiveSpace ≫ (ℙ(G.ProjectiveIndex; Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) = C.hom := by
  rw [ProjectiveSpace.over_eq_fst]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem toProjectiveSpace_toProjInt :
    G.toProjectiveSpace ≫
        ProjectiveSpace.toProjInt G.ProjectiveIndex (Spec (CommRingCat.of k)) =
      G.toProjInt := by
  rw [ProjectiveSpace.toProjInt_eq_snd]
  exact pullback.lift_snd _ _ _

end LaurentChartData.FiniteMapGenerators

end AlgebraicGeometry.Adelic
