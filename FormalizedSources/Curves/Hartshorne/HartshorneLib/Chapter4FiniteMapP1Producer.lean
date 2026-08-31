/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4P1FinitenessAPI
import HartshorneLib.Chapter4TwoCoverFiniteness

/-!
# Finite-map cohomology on the projective line

The canonical Laurent action on the overlap of the two standard charts is induced by a
finite morphism to `P1`.  This file proves the resulting two-chart finiteness theorem,
including the scalar compatibility and localization windows needed by the Cech ladder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace

namespace Hartshorne
open AlgebraicGeometry

attribute [local instance] Scheme.overModule

namespace FiniteMapP1Producer

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} (π : Y ⟶ P1 k)

local notation "Astd" => homogeneousSubmodule (Fin 2) k

private lemma preimage_overlap_eq :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 =
      π ⁻¹ᵁ Proj.basicOpen Astd (X 0 * X 1) := by
  rw [← Scheme.Hom.preimage_inf, P1.chartOpen_inf k]

private lemma preimage_overlap_le :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 ≤
      π ⁻¹ᵁ Proj.basicOpen Astd (X 0 * X 1) :=
  (preimage_overlap_eq π).le

private noncomputable def overlapLaurentHom :
    LaurentPolynomial k →+* Γ(Y, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
  ((π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom).comp
    (P1.overlapSectionsEquiv k).symm.toRingHom

private lemma overlapLaurentHom_T_one :
    overlapLaurentHom π (LaurentPolynomial.T 1) =
      (Y.presheaf.map (homOfLE (inf_le_left : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 0)).op).hom
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1))) := by
  change (π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
      ((P1.overlapSectionsEquiv k).symm (LaurentPolynomial.T 1)) = _
  rw [P1.overlapSectionsEquiv_symm_T]
  calc
    (π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
        (((P1 k).presheaf.map (homOfLE (P1.overlap_le_left k)).op).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1))) =
      ((P1 k).presheaf.map (homOfLE (P1.overlap_le_left k)).op ≫
          π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)) := rfl
    _ = (π.appLE (P1.chartOpen k 0) _ ((preimage_overlap_le π).trans
          ((Opens.map π.base).map (homOfLE (P1.overlap_le_left k))).le)).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)) := by
        rw [Scheme.Hom.map_appLE]
    _ = (π.app (P1.chartOpen k 0) ≫
          Y.presheaf.map (homOfLE (inf_le_left : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 0)).op).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)) := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    _ = _ := rfl

private lemma overlapLaurentHom_T_neg_one :
    overlapLaurentHom π (LaurentPolynomial.T (-1)) =
      (Y.presheaf.map (homOfLE (inf_le_right : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 1)).op).hom
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0))) := by
  change (π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
      ((P1.overlapSectionsEquiv k).symm (LaurentPolynomial.T (-1))) = _
  rw [P1.overlapSectionsEquiv_symm_T_neg]
  calc
    (π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
        (((P1 k).presheaf.map (homOfLE (P1.overlap_le_right k)).op).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0))) =
      ((P1 k).presheaf.map (homOfLE (P1.overlap_le_right k)).op ≫
          π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)) := rfl
    _ = (π.appLE (P1.chartOpen k 1) _ ((preimage_overlap_le π).trans
          ((Opens.map π.base).map (homOfLE (P1.overlap_le_right k))).le)).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)) := by
        rw [Scheme.Hom.map_appLE]
    _ = (π.app (P1.chartOpen k 1) ≫
          Y.presheaf.map (homOfLE (inf_le_right : _ ⊓ _ ≤ π ⁻¹ᵁ P1.chartOpen k 1)).op).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)) := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    _ = _ := rfl

private lemma overlapLaurentHom_algebraMap [Y.Over (Spec (.of k))]
    (hπ : π ≫ P1.structureMap k = Y ↘ Spec (.of k)) (r : k) :
    overlapLaurentHom π (algebraMap k (LaurentPolynomial k) r) =
      Y.overAlgebraMap k (π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) r := by
  letI : (P1 k).Over (Spec (.of k)) := ⟨P1.structureMap k⟩
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (P1.structureMap k).appTop ≫
      (P1 k).presheaf.map (homOfLE (le_top : Proj.basicOpen Astd (X 0 * X 1) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap k (Away Astd (X 0 * X 1))) ≫
        Proj.awayToSection Astd (X 0 * X 1) := by
    rw [P1.structureMap_appTop_awayToSection k (P1.X_mul_X_mem k) two_pos,
      Iso.inv_hom_id_assoc]
  have hPA : (P1 k).overAlgebraMap k (Proj.basicOpen Astd (X 0 * X 1)) r =
      (Proj.awayToSection Astd (X 0 * X 1)).hom
        (algebraMap k (Away Astd (X 0 * X 1)) r) :=
    congr((CommRingCat.Hom.hom $hcomp) r)
  have hLHS := π.appLE_overAlgebraMap hπ (preimage_overlap_le π) r
  change (π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _ (preimage_overlap_le π)).hom
      ((P1.overlapSectionsEquiv k).symm (algebraMap k (LaurentPolynomial k) r)) = _
  rw [P1.overlapSectionsEquiv_symm_algebraMap, ← hPA]
  exact hLHS

private lemma preimage_inf_eq_basicOpen_left :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 =
      Y.basicOpen ((π.app (P1.chartOpen k 0)).hom
        ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1))) := by
  have h : π ⁻¹ᵁ ((P1 k).basicOpen
        ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1))) =
      Y.basicOpen ((π.app (P1.chartOpen k 0)).hom
        ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1))) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord k 0 1, Scheme.Hom.preimage_inf] at h
  exact h

private lemma preimage_inf_eq_basicOpen_right :
    π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1 =
      Y.basicOpen ((π.app (P1.chartOpen k 1)).hom
        ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0))) := by
  have h : π ⁻¹ᵁ ((P1 k).basicOpen
        ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0))) =
      Y.basicOpen ((π.app (P1.chartOpen k 1)).hom
        ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0))) :=
    Scheme.preimage_basicOpen π _
  rw [P1.basicOpen_awayToSection_chartCoord k 1 0, Scheme.Hom.preimage_inf] at h
  rw [← h, inf_comm]

/-! The main consumer below supplies the four Laurent-window conditions to the canonical
two-open Cech finiteness theorem. -/

/-- A finite morphism to the standard projective line charts yields finite degree-one
cohomology, provided the chart-overlap Laurent windows are discharged by localization. -/
theorem moduleFinite_hModule_one_of_isFinite_toP1
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    (π : Z ⟶ P1 k) [IsFinite π]
    (hπ : π ≫ P1.structureMap k = Z ↘ Spec (.of k)) :
    Module.Finite k
      (Sheaf.HModule (Opens.grothendieckTopology (Z : TopCat)) k
        (Z.moduleKSheaf k) 1) := by
  classical
  letI : Algebra (LaurentPolynomial k)
      Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
    (overlapLaurentHom π).toAlgebra
  haveI : IsScalarTower k (LaurentPolynomial k)
      Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) := by
    refine ⟨fun a b n => ?_⟩
    rw [Algebra.smul_def ((a • b : LaurentPolynomial k)) n, Algebra.smul_def b n,
      Scheme.overModule_smul_def, RingHom.algebraMap_toAlgebra, Algebra.smul_def a b,
      map_mul, overlapLaurentHom_algebraMap π hπ, mul_assoc]
  have hV₀ : IsAffineOpen (π ⁻¹ᵁ P1.chartOpen k 0) :=
    AlgebraicGeometry.isAffineOpen_preimage_chartOpen π 0
  have hV₁ : IsAffineOpen (π ⁻¹ᵁ P1.chartOpen k 1) :=
    AlgebraicGeometry.isAffineOpen_preimage_chartOpen π 1
  letI : Module.Finite (LaurentPolynomial k)
      Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) := by
    have h1 : ((Z.presheaf.map (homOfLE (preimage_overlap_le π)).op).hom).Finite := by
      refine RingHom.Finite.of_surjective _ ?_
      rw [show homOfLE (preimage_overlap_le π) =
          eqToHom (preimage_overlap_eq π) from Subsingleton.elim _ _]
      exact ((ConcreteCategory.isIso_iff_bijective
        (Z.presheaf.map (eqToHom (preimage_overlap_eq π)).op)).mp inferInstance).2
    have h2 : ((π.appLE (Proj.basicOpen Astd (X 0 * X 1)) _
        (preimage_overlap_le π)).hom).Finite :=
      h1.comp (AlgebraicGeometry.finite_app_overlap π)
    exact h2.comp (P1.overlapSectionsEquiv k).symm.finite
  have hstab₀ : ∀ x ∈ LinearMap.range
      (CechTwoCover.leftRestriction k Z
        (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)),
      (LaurentPolynomial.T 1 : LaurentPolynomial k) • x ∈
        LinearMap.range (CechTwoCover.leftRestriction k Z
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    rintro x ⟨s, rfl⟩
    refine ⟨(π.app (P1.chartOpen k 0)).hom
      ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)) * s, ?_⟩
    change (Z.presheaf.map (homOfLE inf_le_left).op).hom
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)) * s) = _
    rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      overlapLaurentHom_T_one]
    rfl
  have hstab₁ : ∀ x ∈ LinearMap.range
      (CechTwoCover.rightRestriction k Z
        (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)),
      (LaurentPolynomial.T (-1) : LaurentPolynomial k) • x ∈
        LinearMap.range (CechTwoCover.rightRestriction k Z
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    rintro x ⟨s, rfl⟩
    refine ⟨(π.app (P1.chartOpen k 1)).hom
      ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)) * s, ?_⟩
    change (Z.presheaf.map (homOfLE inf_le_right).op).hom
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)) * s) = _
    rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      overlapLaurentHom_T_neg_one]
    rfl
  have hloc₀ : ∀ n : Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1),
      ∃ m : ℕ, ((LaurentPolynomial.T 1 : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (CechTwoCover.leftRestriction k Z
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    intro n
    have key : ∃ (m : ℕ) (a : Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0)),
        n * ((Z.presheaf.map (homOfLE inf_le_left).op).hom
            ((π.app (P1.chartOpen k 0)).hom
              ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)))) ^ m =
          (Z.presheaf.map (homOfLE inf_le_left).op).hom a := by
      letI : Algebra Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0)
          Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
        ((Z.presheaf.map (homOfLE inf_le_left).op).hom).toAlgebra
      haveI := hV₀.isLocalization_of_eq_basicOpen
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1)))
        (homOfLE inf_le_left) (preimage_inf_eq_basicOpen_left π)
      obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
        ((π.app (P1.chartOpen k 0)).hom
          ((Proj.awayToSection Astd (X 0)).hom (P1.chartCoord k 0 1))) n
      rw [RingHom.algebraMap_toAlgebra] at ha
      exact ⟨m, a, ha⟩
    obtain ⟨m, a, ha⟩ := key
    refine ⟨m, a, ?_⟩
    change (Z.presheaf.map (homOfLE inf_le_left).op).hom a = _
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow,
      overlapLaurentHom_T_one, ← ha, mul_comm]
  have hloc₁ : ∀ n : Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1),
      ∃ m : ℕ, ((LaurentPolynomial.T (-1) : LaurentPolynomial k) ^ m) • n ∈
        LinearMap.range (CechTwoCover.rightRestriction k Z
          (π ⁻¹ᵁ P1.chartOpen k 0) (π ⁻¹ᵁ P1.chartOpen k 1)) := by
    intro n
    have key : ∃ (m : ℕ) (a : Γ(Z, π ⁻¹ᵁ P1.chartOpen k 1)),
        n * ((Z.presheaf.map (homOfLE inf_le_right).op).hom
            ((π.app (P1.chartOpen k 1)).hom
              ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)))) ^ m =
          (Z.presheaf.map (homOfLE inf_le_right).op).hom a := by
      letI : Algebra Γ(Z, π ⁻¹ᵁ P1.chartOpen k 1)
          Γ(Z, π ⁻¹ᵁ P1.chartOpen k 0 ⊓ π ⁻¹ᵁ P1.chartOpen k 1) :=
        ((Z.presheaf.map (homOfLE inf_le_right).op).hom).toAlgebra
      haveI := hV₁.isLocalization_of_eq_basicOpen
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0)))
        (homOfLE inf_le_right) (preimage_inf_eq_basicOpen_right π)
      obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
        ((π.app (P1.chartOpen k 1)).hom
          ((Proj.awayToSection Astd (X 1)).hom (P1.chartCoord k 1 0))) n
      rw [RingHom.algebraMap_toAlgebra] at ha
      exact ⟨m, a, ha⟩
    obtain ⟨m, a, ha⟩ := key
    refine ⟨m, a, ?_⟩
    change (Z.presheaf.map (homOfLE inf_le_right).op).hom a = _
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow,
      overlapLaurentHom_T_neg_one, ← ha, mul_comm]
  exact CechTwoCover.moduleFinite_hModule_one_of_isFinite_affineCover
    k Z π (P1.chartOpen k 0) (P1.chartOpen k 1) (P1.chartOpen_sup k)
    (P1.isAffineOpen_chartOpen k 0) (P1.isAffineOpen_chartOpen k 1)
    hstab₀ hstab₁ hloc₀ hloc₁

end FiniteMapP1Producer
end Hartshorne
