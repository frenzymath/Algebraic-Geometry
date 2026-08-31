/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter2Chi
import HartshorneLib.Chapter4DivisorClass
import HartshorneLib.Chapter4DivisorMultiplication

/-!
# Multiplication isomorphisms of divisor sheaves

A nonzero rational function `g` identifies the divisor sheaves attached to `D`
and `D - div(g)`.  The sectionwise map is multiplication by `g`; the
bound-shift lemma from `Chapter4DivisorMultiplication` supplies well-definedness
and the inverse is multiplication by `g⁻¹`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

attribute [local instance] functionFieldOverModule Scheme.overModule

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! ## Multiplication on the function field -/

noncomputable def mulByUnit (g : X.left.functionFieldˣ) :
    X.left.functionField ≃ₗ[k] X.left.functionField where
  toFun s := (g : X.left.functionField) * s
  map_add' a b := mul_add _ _ _
  map_smul' r s := by
    simp only [RingHom.id_apply, functionFieldOverModule_smul_def]
    exact mul_left_comm _ _ _
  invFun s := (↑g⁻¹ : X.left.functionField) * s
  left_inv s := by
    change (↑g⁻¹ : X.left.functionField) * ((g : X.left.functionField) * s) = s
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv s := by
    change (g : X.left.functionField) * ((↑g⁻¹ : X.left.functionField) * s) = s
    rw [← mul_assoc, Units.mul_inv, one_mul]

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
@[simp] lemma mulByUnit_apply (g : X.left.functionFieldˣ) (s : X.left.functionField) :
    mulByUnit (k := k) g s = (g : X.left.functionField) * s := rfl

/-! ## Sectionwise maps -/

noncomputable def divisorMulApp (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    {U : X.left.Opens} (hU : (U : Set X.left).Nonempty) :
    divisorSections D U →ₗ[k]
      divisorSections (D - principalDivisor g) U :=
  LinearMap.codRestrict _
    ((mulByUnit (k := k) g).toLinearMap ∘ₗ (divisorSections D U).subtype)
    (fun s => by
      rw [divisorSections_of_nonempty hU]
      have hs : (s : X.left.functionField) ∈ boundedSections D U := by
        rw [← divisorSections_of_nonempty hU]
        exact s.2
      exact (mem_boundedSections_mul_iff g D (s : X.left.functionField)).mpr hs)

@[simp] lemma divisorMulApp_coe (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    {U : X.left.Opens} (hU : (U : Set X.left).Nonempty)
    (s : divisorSections D U) :
    ((divisorMulApp (k := k) g D hU s :
        divisorSections (D - principalDivisor g) U) : X.left.functionField) =
      (g : X.left.functionField) * (s : X.left.functionField) := rfl

open Classical in
noncomputable def divisorMulPresheafApp (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    (U : X.left.Opens) :
    divisorSections D U →ₗ[k] divisorSections (D - principalDivisor g) U :=
  if hU : (U : Set X.left).Nonempty then divisorMulApp g D hU else 0

lemma divisorMulPresheafApp_of_nonempty (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    {U : X.left.Opens} (hU : (U : Set X.left).Nonempty) :
    divisorMulPresheafApp (k := k) g D U = divisorMulApp g D hU :=
  dif_pos hU

lemma divisorMulPresheafApp_coe_of_nonempty (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    {U : X.left.Opens} (hU : (U : Set X.left).Nonempty)
    (s : divisorSections D U) :
    ((divisorMulPresheafApp (k := k) g D U s :
        divisorSections (D - principalDivisor g) U) : X.left.functionField) =
      (g : X.left.functionField) * (s : X.left.functionField) := by
  rw [divisorMulPresheafApp_of_nonempty g D hU, divisorMulApp_coe]

lemma divisorMulPresheafApp_bijective (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    (U : X.left.Opens) :
    Function.Bijective (divisorMulPresheafApp (k := k) g D U) := by
  by_cases hU : (U : Set X.left).Nonempty
  · rw [divisorMulPresheafApp_of_nonempty g D hU]
    refine ⟨fun a b hab => ?_, fun t => ?_⟩
    · apply Subtype.ext
      have hval : (g : X.left.functionField) * (a : X.left.functionField) =
          (g : X.left.functionField) * (b : X.left.functionField) := by
        have h := congrArg (Subtype.val) hab
        rwa [divisorMulApp_coe, divisorMulApp_coe] at h
      exact mul_left_cancel₀ (Units.ne_zero g) hval
    · have htmem : (t : X.left.functionField) ∈
          boundedSections (D - principalDivisor g) U := by
        rw [← divisorSections_of_nonempty hU]
        exact t.2
      have hpre : (↑g⁻¹ : X.left.functionField) * (t : X.left.functionField) ∈
          boundedSections D U := by
        rw [← mem_boundedSections_mul_iff g D, ← mul_assoc, Units.mul_inv, one_mul]
        exact htmem
      refine ⟨⟨(↑g⁻¹ : X.left.functionField) * (t : X.left.functionField), ?_⟩, ?_⟩
      · rw [divisorSections_of_nonempty hU]
        exact hpre
      · apply Subtype.ext
        rw [divisorMulApp_coe, ← mul_assoc, Units.mul_inv, one_mul]
  · haveI := divisorSections_subsingleton_of_empty (D := D) hU
    haveI := divisorSections_subsingleton_of_empty
      (D := D - principalDivisor g) hU
    exact ⟨fun a b _ => Subsingleton.elim a b,
      fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-! ## Presheaf and sheaf isomorphisms -/

noncomputable def divisorMulPresheaf (g : X.left.functionFieldˣ) (D : CurveDivisor k X) :
    divisorPresheaf D ⟶ divisorPresheaf (D - principalDivisor g) where
  app U := ModuleCat.ofHom (divisorMulPresheafApp g D U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hV : (V.unop : Set X.left).Nonempty
    · have hU : (U.unop : Set X.left).Nonempty := hV.mono (leOfHom i.unop)
      apply Subtype.ext
      change ((divisorMulPresheafApp g D V.unop
          (divisorSectionsRes (D := D) (leOfHom i.unop) s) :
            divisorSections (D - principalDivisor g) V.unop) : X.left.functionField) =
        ((divisorSectionsRes (D := D - principalDivisor g) (leOfHom i.unop)
          (divisorMulPresheafApp g D U.unop s) :
            divisorSections (D - principalDivisor g) V.unop) : X.left.functionField)
      rw [divisorMulPresheafApp_coe_of_nonempty g D hV,
        divisorSectionsRes_coe (leOfHom i.unop) hV,
        divisorSectionsRes_coe (leOfHom i.unop) hV,
        divisorMulPresheafApp_coe_of_nonempty g D hU]
    · haveI := divisorPresheaf_obj_subsingleton
        (D := D - principalDivisor g) (W := V.unop) hV
      exact Subsingleton.elim _ _

lemma divisorMulPresheaf_app_isIso (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    (U : (X.left.Opens)ᵒᵖ) : IsIso ((divisorMulPresheaf g D).app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact divisorMulPresheafApp_bijective g D U.unop

noncomputable def divisorMulPresheafIso (g : X.left.functionFieldˣ) (D : CurveDivisor k X) :
    divisorPresheaf D ≅ divisorPresheaf (D - principalDivisor g) :=
  NatIso.ofComponents
    (fun U => by
      letI := divisorMulPresheaf_app_isIso g D U
      exact asIso ((divisorMulPresheaf g D).app U))
    (fun i => (divisorMulPresheaf g D).naturality i)

noncomputable def mulEquivDivisorSheaf (g : X.left.functionFieldˣ) (D : CurveDivisor k X) :
    divisorSheaf D ≅ divisorSheaf (D - principalDivisor g) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (divisorMulPresheafIso g D)

theorem divisorVal_mulEquiv {U : X.left.Opens}
    (g : X.left.functionFieldˣ) (D : CurveDivisor k X)
    (hU : (U : Set X.left).Nonempty)
    (s : (divisorPresheaf D).obj (op U)) :
    divisorVal ((divisorMulPresheaf g D).app (op U) s) =
      (g : X.left.functionField) * divisorVal s :=
  divisorMulPresheafApp_coe_of_nonempty g D hU s

theorem chi_divisorSheaf_sub_principalDivisor (g : X.left.functionFieldˣ)
    (D : CurveDivisor k X) :
    CategoryTheory.Sheaf.chi (divisorSheaf (D - principalDivisor g)) =
      CategoryTheory.Sheaf.chi (divisorSheaf D) :=
  CategoryTheory.Sheaf.chi_congr (mulEquivDivisorSheaf g D).symm

theorem chi_divisorSheaf_eq_of_linearlyEquivalent
    {D E : CurveDivisor k X} (h : LinearlyEquivalent D E) :
    CategoryTheory.Sheaf.chi (divisorSheaf D) =
      CategoryTheory.Sheaf.chi (divisorSheaf E) := by
  obtain ⟨g, hg⟩ := (linearlyEquivalent_iff_exists D E).mp h
  have heq : D - principalDivisor g = E := by
    rw [← hg]
    abel
  rw [← heq]
  exact CategoryTheory.Sheaf.chi_congr (mulEquivDivisorSheaf g D)

end Hartshorne
