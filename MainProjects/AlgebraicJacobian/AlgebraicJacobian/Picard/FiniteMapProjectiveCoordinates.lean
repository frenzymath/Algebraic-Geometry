/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.FiniteMapLaurentGenerators

/-!
# Projective coordinate maps for a finite morphism

This file turns the aligned Laurent-chart generators of a finite morphism into
actual morphisms from the two pulled-back affine opens to one integral
projective space. The two morphisms agree on the overlap, without any
projectivity or rational-point hypothesis.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]
variable {Y C : Over (Spec (CommRingCat.of k))}

namespace LaurentChartData.FiniteMapGenerators

variable {D : LaurentChartData Y} {pi : C ⟶ Y}
variable (G : D.FiniteMapGenerators pi)

/-- The common homogeneous coordinate index. The extra generators use the
universe-lifted finite index supplied by `FiniteMapGenerators`. -/
abbrev ProjectiveIndex : Type u := Fin (G.d + 1) ⊕ G.LiftedIndex

/-- The complete homogeneous coordinate family on the first source chart. -/
def projectiveCoordinates0 :
    G.ProjectiveIndex → Γ(C.left, pi.left ⁻¹ᵁ D.V₀) :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0
    G.d (D.pullbackX pi) G.liftedAA

/-- The complete homogeneous coordinate family on the second source chart. -/
def projectiveCoordinates1 :
    G.ProjectiveIndex → Γ(C.left, pi.left ⁻¹ᵁ D.V₁) :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1
    G.d (D.pullbackY pi) G.liftedBB

@[simp]
theorem projectiveCoordinates0_zero :
    G.projectiveCoordinates0
      (Sum.inl ⟨0, Nat.zero_lt_succ G.d⟩) = 1 :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart0_zero
    G.d (D.pullbackX pi) G.liftedAA

@[simp]
theorem projectiveCoordinates1_last :
    G.projectiveCoordinates1
      (Sum.inl ⟨G.d, Nat.lt_succ_self G.d⟩) = 1 :=
  AlgebraicJacobian.TwoChart.TwistedCoordinates.chart1_last
    G.d (D.pullbackY pi) G.liftedBB

/-- The lifted generator families retain the aligned overlap equation. -/
theorem lifted_compatible (i : G.LiftedIndex) :
    D.sourceRestriction0 pi (G.liftedAA i) =
      D.sourceRestriction0 pi (D.pullbackX pi) ^ G.d *
        D.sourceRestriction1 pi (G.liftedBB i) := by
  exact G.compatible i.down

/-- The normalized projective coordinate morphism on the first source chart. -/
def localProjectiveMap0 :
    (pi.left ⁻¹ᵁ D.V₀).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ)) :=
  ProjectiveSpace.Coordinates.fromOpen (pi.left ⁻¹ᵁ D.V₀)
    (Sum.inl ⟨0, Nat.zero_lt_succ G.d⟩) G.projectiveCoordinates0
    G.projectiveCoordinates0_zero

/-- The normalized projective coordinate morphism on the second source chart. -/
def localProjectiveMap1 :
    (pi.left ⁻¹ᵁ D.V₁).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule G.ProjectiveIndex (ULift.{u} ℤ)) :=
  ProjectiveSpace.Coordinates.fromOpen (pi.left ⁻¹ᵁ D.V₁)
    (Sum.inl ⟨G.d, Nat.lt_succ_self G.d⟩) G.projectiveCoordinates1
    G.projectiveCoordinates1_last

/-- The two local projective morphisms agree after restriction to the pulled-
back overlap. This is the compatibility equation for `Cover.glueMorphisms`. -/
theorem localProjectiveMap_compat :
    C.left.homOfLE inf_le_left ≫ G.localProjectiveMap0 =
      C.left.homOfLE inf_le_right ≫ G.localProjectiveMap1 := by
  exact AlgebraicJacobian.TwoChart.TwistedCoordinates.fromOpen_compat
    (pi.left ⁻¹ᵁ D.V₀) (pi.left ⁻¹ᵁ D.V₁)
    (D.pullbackX pi) (D.pullbackY pi) (D.sourceRestriction_mul pi)
    G.d G.liftedAA G.liftedBB G.lifted_compatible

end LaurentChartData.FiniteMapGenerators

end AlgebraicGeometry.Adelic
