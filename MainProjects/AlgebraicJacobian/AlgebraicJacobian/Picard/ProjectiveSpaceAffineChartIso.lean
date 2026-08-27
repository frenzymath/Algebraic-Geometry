/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.ProjectiveSpaceAffineChartRing
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The standard projective chart is affine space

This file upgrades the standard-chart ring calculation to geometry. The chart
`D_+(X_none)` in relative projective space is canonically affine space over the
base. Consequently affine space has its standard open immersion into relative
projective space.
-/

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : Type u) [Finite n] (S : Scheme.{u})

namespace affineChart

/-- On the integral models, the spectrum of the polynomial ring is the
standard projective chart. -/
def specAwayIso :
    Spec (.of (Away
      (homogeneousSubmodule (Option n) (ULift.{u} ℤ)) (X none))) ≅
      Spec (.of (MvPolynomial n (ULift.{u} ℤ))) :=
  (Scheme.Spec.mapIso
    ((AffineChartRing.awayAlgEquiv (ULift.{u} ℤ) n).toRingEquiv.toCommRingCatIso.op)).symm

private def integralChartIncl :
    Spec (.of (Away
      (homogeneousSubmodule (Option n) (ULift.{u} ℤ)) (X none))) ⟶
      Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ)) :=
  Proj.awayι (homogeneousSubmodule (Option n) (ULift.{u} ℤ))
    (X none) (isHomogeneous_X _ _) Nat.zero_lt_one

private def flattenIso :
    affineChart n S ≅
      pullback (terminal.from S)
        (integralChartIncl n ≫
          terminal.from (Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ)))) :=
  pullbackLeftPullbackSndIso
    (terminal.from S)
    (terminal.from (Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ))))
    (integralChartIncl n)

private def changeChartHom :
    pullback (terminal.from S)
        (integralChartIncl n ≫
          terminal.from (Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ)))) ⟶
      𝔸(n; S) :=
  pullback.map
    (terminal.from S)
    (integralChartIncl n ≫
      terminal.from (Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ))))
    (terminal.from S)
    (terminal.from (Spec (.of (MvPolynomial n (ULift.{u} ℤ)))))
    (𝟙 S) (specAwayIso n).hom (𝟙 (⊤_ Scheme)) (by simp) (by simp)

private instance : IsIso (changeChartHom n S) := by
  dsimp [changeChartHom]
  apply pullback.map_isIso

@[reassoc]
private theorem changeChartHom_over :
    changeChartHom n S ≫ (𝔸(n; S) ↘ S) =
      pullback.fst (terminal.from S)
        (integralChartIncl n ≫
          terminal.from (Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ)))) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Category.comp_id]

omit [Finite n] in
@[reassoc]
private theorem flattenIso_hom_over :
    (flattenIso n S).hom ≫
        pullback.fst (terminal.from S)
          (integralChartIncl n ≫
            terminal.from (Proj (homogeneousSubmodule (Option n) (ULift.{u} ℤ)))) =
      pullback.fst (ProjectiveSpace.toProjInt (Option n) S) (integralChartIncl n) ≫
        (ℙ(Option n; S) ↘ S) :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- The standard chart `D_+(X_none)` of relative projective space is affine
space over the base. -/
def isoAffineSpace : affineChart n S ≅ 𝔸(n; S) := by
  exact flattenIso n S ≪≫ asIso (changeChartHom n S)

@[reassoc]
theorem isoAffineSpace_hom_over :
    (isoAffineSpace n S).hom ≫ (𝔸(n; S) ↘ S) = affineChart n S ↘ S := by
  change ((flattenIso n S ≪≫ asIso (changeChartHom n S)).hom) ≫
      (𝔸(n; S) ↘ S) = affineChart n S ↘ S
  rw [Iso.trans_hom, Category.assoc, asIso_hom, changeChartHom_over,
    flattenIso_hom_over]
  rfl

end affineChart

/-- The standard open immersion of affine space into relative projective
space, sending `(x_i)` to `[1 : x_i]`. -/
def standardOpenImmersion : 𝔸(n; S) ⟶ ℙ(Option n; S) :=
  (affineChart.isoAffineSpace n S).inv ≫ affineChart.incl n S

instance : IsOpenImmersion (standardOpenImmersion n S) :=
  IsOpenImmersion.comp _ _

@[reassoc]
theorem standardOpenImmersion_over :
    standardOpenImmersion n S ≫ (ℙ(Option n; S) ↘ S) = 𝔸(n; S) ↘ S := by
  rw [standardOpenImmersion, Category.assoc, ← affineChart.over_eq,
    ← affineChart.isoAffineSpace_hom_over]
  simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.ProjectiveSpace
