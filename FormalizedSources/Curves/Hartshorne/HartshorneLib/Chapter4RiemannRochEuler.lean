/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4SmoothProperConsequences
import HartshorneLib.Chapter4ChiBase

/-!
# Euler characteristic form of Riemann--Roch for a proper smooth integral curve

The cohomological product-formula ledger gives the change of `χ` with divisor
degree.  The only remaining normalization is `χ (𝒪_X) = 1 - h¹ (𝒪_X)`,
obtained from the global-sections description of degree-zero cohomology.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

attribute [local instance] Scheme.overModule

private noncomputable def overAlgebraMapTopLinear :
    k →ₗ[k] X.left.presheaf.obj (Opposite.op (⊤ : X.left.Opens)) where
  toFun := X.left.overAlgebraMap k ⊤
  map_add' := map_add _
  map_smul' r s := by
    simp only [RingHom.id_apply, smul_eq_mul, map_mul, Scheme.overModule_smul_def]

omit [SmoothOfRelativeDimension 1 X.hom] in
private theorem bijective_overAlgebraMapTop :
    Function.Bijective (X.left.overAlgebraMap k (⊤ : X.left.Opens)) := by
  letI : Field (X.left.presheaf.obj (Opposite.op (⊤ : X.left.Opens))) :=
    (AlgebraicGeometry.isField_of_universallyClosed k X.hom).toField
  letI : Algebra k
      (X.left.presheaf.obj (Opposite.op (⊤ : X.left.Opens))) :=
    (X.left.overAlgebraMap k (⊤ : X.left.Opens)).toAlgebra
  have hintegral :
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact AlgebraicGeometry.isIntegral_appTop_of_universallyClosed X.hom
  have hcomp : Function.Bijective
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral _ hintegral
  have h_kts : X.left.overAlgebraMap k (⊤ : X.left.Opens) =
      (X.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    ext y
    simp only [Scheme.overAlgebraMap, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    exact congrFun (congrArg (fun f => f.hom)
      (X.left.presheaf.map_id (Opposite.op (⊤ : X.left.Opens)))) _
  rw [h_kts]
  exact hcomp

omit [SmoothOfRelativeDimension 1 X.hom] in
theorem h0_moduleKSheaf_eq_one :
    CategoryTheory.Sheaf.h0 (X.left.moduleKSheaf k) = 1 := by
  let e : CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k
      (X.left.moduleKSheaf k) 0 ≃ₗ[k] k :=
    (CategoryTheory.Sheaf.HModule.linearEquiv₀
      (J := Opens.grothendieckTopology (X.left : TopCat))
      (R := k) (T := (⊤ : X.left.Opens))
      (Preorder.isTerminalTop (TopologicalSpace.Opens X.left.toTopCat))
      (X.left.moduleKSheaf k)).trans
      (LinearEquiv.ofBijective (overAlgebraMapTopLinear (k := k) (X := X))
        (bijective_overAlgebraMapTop (k := k) (X := X))).symm
  rw [CategoryTheory.Sheaf.h0, e.finrank_eq, Module.finrank_self]

theorem chi_divisorSheaf_eq_one_sub_h1_add_degree
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      1 - (CategoryTheory.Sheaf.h1 (X.left.moduleKSheaf k) : ℤ) +
        CurveDivisor.degree D := by
  have hbase := chi_divisorSheaf_eq_base_add_degree_of_smoothProperIntegralCurve
    (X := X) D
  have hzero := chi_divisorSheaf_zero (X := X)
  have h0 := h0_moduleKSheaf_eq_one (k := k) (X := X)
  rw [hzero] at hbase
  simp only [CategoryTheory.Sheaf.chi] at hbase
  rw [h0] at hbase
  exact hbase

end
end Hartshorne
