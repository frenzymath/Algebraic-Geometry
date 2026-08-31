/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorDevissage
import HartshorneLib.Chapter4JumpDimension
import HartshorneLib.Chapter4PrincipalDivisors

/-!
# Short exactness of the divisor dévissage complex

This is the source-faithful exactness and local-surjectivity package for
`0 ⟶ 𝒪(D - x) ⟶ 𝒪(D) ⟶ sky_x J ⟶ 0`.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Hartshorne

attribute [local instance] functionFieldOverModule Scheme.overModule

open scoped Classical

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X : Over (Spec (CommRingCat.of k))} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]

/-! ## Local surjectivity -/

lemma devissageπ_app_eq_restrict {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) {U W : X.left.Opens} (hxU : x ∈ U) (hxW : x ∈ W) (i : W ⟶ U)
    (t : (skyModule (X := X) x (jumpModule hx D)).obj.obj (op U))
    (s : (divisorPresheaf D).obj (op W))
    (hst : jumpProj hx D W hxW s =
      (eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxU)).hom t) :
    ((devissageπ hx D).hom.app (op W)).hom s =
      ((skyModule (X := X) x (jumpModule hx D)).obj.map i.op).hom t := by
  rw [devissageπ_app_hom_apply_of_mem hx D (op W) hxW s, hst,
    skyModule_map_eq (X := X) (jumpModule hx D) i.op hxU hxW,
    ← eqToHom_trans (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxU)
      (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxW).symm]
  rfl

lemma imageSieve_of_not_mem {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) {U W : X.left.Opens} (i : W ⟶ U) (hxW : x ∉ W)
    (t : (skyModule (X := X) x (jumpModule hx D)).obj.obj (op U)) :
    (Presheaf.imageSieve (devissageπ hx D).hom t) i := by
  haveI := skyModule_obj_subsingleton (X := X) (jumpModule hx D) hxW
  exact ⟨0, Subsingleton.elim _ _⟩

lemma devissage_local_lift [QuasiCompact X.hom] {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)
    {U : X.left.Opens} (hxU : x ∈ U)
    (t : (skyModule (X := X) x (jumpModule hx D)).obj.obj (op U)) :
    ∃ (W : X.left.Opens) (i : W ⟶ U),
      (Presheaf.imageSieve (devissageπ hx D).hom t) i ∧ x ∈ W := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    ((eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxU)).hom t)
  have hgP : (y : X.left.functionField) ∈ pointLattice hx (CurveDivisor.coeffAt hx D) := y.2
  by_cases hg0 : (y : X.left.functionField) = 0
  · refine ⟨U, 𝟙 U, ⟨(0 : divisorSections D U), ?_⟩, hxU⟩
    have hst : jumpProj hx D U hxU (0 : divisorSections D U) =
        (eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxU)).hom t := by
      have hy0 : y = 0 := Subtype.ext hg0
      rw [map_zero, ← hy, hy0]
      rfl
    exact devissageπ_app_eq_restrict hx D hxU hxU (𝟙 U) t _ hst
  · set g : X.left.functionField := (y : X.left.functionField) with hg_def
    set gu : X.left.functionFieldˣ := Units.mk0 g hg0 with hgu
    have hguv : (gu : X.left.functionField) = g := rfl
    set Bad : Set X.left := {z | ∃ (hz : z ≠ genericPoint X.left),
        ¬ (orderAt X.hom hz g ≤ divisorBound D hz)} with hBad
    have hfin : Bad.Finite := by
      apply Set.Finite.subset
        ((orderZAt_support_finite X.hom gu).image Subtype.val |>.union
          ((show PointDivisor X.left from D).support.finite_toSet.image Subtype.val))
      intro z hz
      obtain ⟨hzne, hzbad⟩ := hz
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      have hord1 : orderZAt X.hom hzne gu = 1 := by
        by_contra hne
        exact hc1 ⟨⟨z, hzne⟩, hne, rfl⟩
      have hsupp : (show PointDivisor X.left from D).toFun ⟨z, hzne⟩ = 0 := by
        by_contra hne
        exact hc2 ⟨⟨z, hzne⟩, Finsupp.mem_support_iff.mpr hne, rfl⟩
      have hsupp' : CurveDivisor.coeffAt hzne D = 0 := by
        change (show PointDivisor X.left from D).toFun ⟨z, hzne⟩ = 0
        exact hsupp
      apply hzbad
      have hordg : orderAt X.hom hzne g = 1 := by
        rw [← hguv, ← orderZAt_eq_one_iff]; exact hord1
      rw [divisorBound_eq_coeffAt, hordg, hsupp']
      simp
    have hBadClosed : IsClosed Bad := by
      rw [← Set.biUnion_of_singleton Bad]
      exact hfin.isClosed_biUnion
        (fun z hz => smoothCurve_isClosed_singleton_of_ne_genericPoint X.hom hz.choose)
    set W : X.left.Opens := U ⊓ ⟨Badᶜ, hBadClosed.isOpen_compl⟩ with hW
    have hxbound : orderAt X.hom hx g ≤ divisorBound D hx := by
      rw [divisorBound_eq_coeffAt]
      exact (mem_pointLattice (X := X) hx).mp hgP
    have hxBad : x ∉ Bad := fun ⟨_, hbad⟩ => hbad hxbound
    have hxW : x ∈ W := ⟨hxU, hxBad⟩
    have hWne : (W : Set X.left).Nonempty := ⟨x, hxW⟩
    have hgmem : g ∈ divisorSections D W := by
      rw [mem_divisorSections_of_nonempty hWne]
      intro z hz hzW
      by_contra h
      exact hzW.2 ⟨hz, h⟩
    refine ⟨W, homOfLE inf_le_left, ⟨⟨g, hgmem⟩, ?_⟩, hxW⟩
    have hst : jumpProj hx D W hxW ⟨g, hgmem⟩ =
        (eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxU)).hom t := by
      rw [jumpProj_apply, ← hy]
    exact devissageπ_app_eq_restrict hx D hxU hxW (homOfLE inf_le_left) t _ hst

instance devissageπ_isLocallySurjective [QuasiCompact X.hom] {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X.left : TopCat))
      (devissageπ hx D).hom where
  imageSieve_mem {U} t := by
    intro p hp
    by_cases hxU : x ∈ U
    · by_cases hpx : p = x
      · subst hpx
        obtain ⟨W, i, hsieve, hxW⟩ := devissage_local_lift hx D hxU t
        exact ⟨W, i, hsieve, hxW⟩
      · refine ⟨U ⊓ ⟨{x}ᶜ,
            (smoothCurve_isClosed_singleton_of_ne_genericPoint X.hom hx).isOpen_compl⟩,
          homOfLE inf_le_left, imageSieve_of_not_mem hx D (homOfLE inf_le_left) ?_ t,
          ⟨hp, hpx⟩⟩
        exact fun hxW => hxW.2 rfl
    · exact ⟨U, 𝟙 U, imageSieve_of_not_mem hx D _ hxU t, hp⟩

instance devissageSES_epi_g [QuasiCompact X.hom] {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    Epi (devissageSES hx D).g := by
  have hls : Sheaf.IsLocallySurjective (devissageπ hx D) :=
    devissageπ_isLocallySurjective hx D
  exact (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u} k) (devissageπ hx D)).mp hls

/-! ## Middle exactness -/

lemma jumpProj_eq_zero_iff {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) {W : X.left.Opens} (hxW : x ∈ W)
    (s : divisorSections D W) :
    jumpProj hx D W hxW s = 0 ↔
      (s : X.left.functionField) ∈ pointLattice hx (CurveDivisor.coeffAt hx D - 1) := by
  constructor
  · intro h
    rw [jumpProj_apply] at h
    have hm : (⟨(s : X.left.functionField), divisorSections_le_pointLattice hx D W hxW s.2⟩ :
        pointLattice hx (CurveDivisor.coeffAt hx D)) ∈
      (pointLattice hx (CurveDivisor.coeffAt hx D - 1)).submoduleOf
        (pointLattice hx (CurveDivisor.coeffAt hx D)) :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    exact hm
  · intro h
    rw [jumpProj_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr h

lemma divisorBound_devissageDivisor_of_ne {x z : X.left}
    (hx : x ≠ genericPoint X.left) (hz : z ≠ genericPoint X.left)
    (hzx : (⟨z, hz⟩ : {p : X.left // p ≠ genericPoint X.left}) ≠ ⟨x, hx⟩)
    (D : CurveDivisor k X) :
    divisorBound (CurveDivisor.devissageDivisor hx D) hz = divisorBound D hz := by
  rw [divisorBound_eq_coeffAt, divisorBound_eq_coeffAt,
    CurveDivisor.devissageDivisor_eq_sub, CurveDivisor.coeffAt_sub]
  have hsingle : CurveDivisor.coeffAt hz (CurveDivisor.single hx 1) = 0 := by
    change (Finsupp.single (⟨x, hx⟩ : {p : X.left // p ≠ genericPoint X.left}) 1)
      ⟨z, hz⟩ = 0
    rw [Finsupp.single_apply]
    split <;> simp_all
  rw [hsingle]
  simp

lemma coe_mem_divisorSections_devissage {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) {W : X.left.Opens} (hxW : x ∈ W)
    (s : divisorSections D W)
    (hmem : (s : X.left.functionField) ∈ pointLattice hx (CurveDivisor.coeffAt hx D - 1)) :
    (s : X.left.functionField) ∈ divisorSections (CurveDivisor.devissageDivisor hx D) W := by
  have hne : (W : Set X.left).Nonempty := ⟨x, hxW⟩
  rw [mem_divisorSections_of_nonempty hne]
  intro z hz hzW
  by_cases hzx : (⟨z, hz⟩ : {p : X.left // p ≠ genericPoint X.left}) = ⟨x, hx⟩
  · have hzeq : z = x := congrArg Subtype.val hzx
    subst z
    rw [divisorBound_eq_coeffAt, devissageDivisor_coeffAt hx D]
    exact (mem_pointLattice (X := X) hx).mp hmem
  · rw [divisorBound_devissageDivisor_of_ne hx hz hzx D]
    exact (mem_divisorSections_of_nonempty hne).mp s.2 z hz hzW

lemma divisorSections_le_devissage_of_not_mem {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) {W : X.left.Opens} (hxW : x ∉ W) :
    divisorSections D W ≤ divisorSections (CurveDivisor.devissageDivisor hx D) W := by
  by_cases hne : (W : Set X.left).Nonempty
  · rw [divisorSections_of_nonempty hne, divisorSections_of_nonempty hne]
    intro v hv z hz hzW
    have hzx : (⟨z, hz⟩ : {p : X.left // p ≠ genericPoint X.left}) ≠ ⟨x, hx⟩ := by
      intro h
      have hzeq : z = x := congrArg Subtype.val h
      exact hxW (hzeq ▸ hzW)
    rw [divisorBound_devissageDivisor_of_ne hx hz hzx D]
    exact hv z hz hzW
  · rw [divisorSections_of_empty hne]
    exact bot_le

lemma devissageSES_map_exact {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (W : (X.left.Opens)ᵒᵖ) :
    ((devissageSES hx D).map (sheafToPresheaf (Opens.grothendieckTopology
      (X.left : TopCat)) (ModuleCat.{u} k) ⋙ (evaluation _ (ModuleCat.{u} k)).obj W)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro s hs
  change (divisorSections D (unop W) : Type _) at s
  have hgs : ((devissageπ hx D).hom.app W).hom s = 0 := hs
  have hmem : ((s : X.left.functionField) ∈
      divisorSections (CurveDivisor.devissageDivisor hx D) (unop W)) := by
    by_cases hxW : x ∈ (unop W : X.left.Opens)
    · have hjump : jumpProj hx D (unop W) hxW s = 0 := by
        have heq := hgs
        rw [devissageπ_app_hom_apply_of_mem hx D W hxW s] at heq
        have hinj : Function.Injective (eqToHom (skyModule_obj_of_mem'
            (X := X) (jumpModule hx D) hxW).symm).hom :=
          (ModuleCat.mono_iff_injective _).mp inferInstance
        apply hinj
        rw [heq, map_zero]
      exact coe_mem_divisorSections_devissage hx D hxW s
        ((jumpProj_eq_zero_iff hx D hxW s).mp hjump)
    · exact divisorSections_le_devissage_of_not_mem hx D hxW s.2
  refine ⟨⟨(s : X.left.functionField), hmem⟩, ?_⟩
  apply Subtype.ext
  change (((divisorSheafLE (devissageDivisor_le hx D)).hom.app W).hom
      ⟨(s : X.left.functionField), hmem⟩).1 = (s : X.left.functionField)
  rw [divisorSheafLE_hom]
  rfl

theorem devissageSES_exact {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : (devissageSES hx D).Exact := by
  have hsec : ∀ W : (X.left.Opens)ᵒᵖ,
      IsLimit (KernelFork.ofι
        ((devissageSES hx D).map (sheafToPresheaf (Opens.grothendieckTopology
          (X.left : TopCat)) (ModuleCat.{u} k) ⋙ (evaluation _ (ModuleCat.{u} k)).obj W)).f
        ((devissageSES hx D).map (sheafToPresheaf (Opens.grothendieckTopology
          (X.left : TopCat)) (ModuleCat.{u} k) ⋙
          (evaluation _ (ModuleCat.{u} k)).obj W)).zero) := by
    intro W
    haveI : Mono ((devissageSES hx D).map (sheafToPresheaf
        (Opens.grothendieckTopology (X.left : TopCat)) (ModuleCat.{u} k) ⋙
          (evaluation _ (ModuleCat.{u} k)).obj W)).f :=
      (ModuleCat.mono_iff_injective _).mpr
        (by
          let Fsec : CategoryTheory.Sheaf (Opens.grothendieckTopology
              (X.left : TopCat)) (ModuleCat.{u} k) ⥤ ModuleCat.{u} k :=
            sheafToPresheaf (Opens.grothendieckTopology (X.left : TopCat))
              (ModuleCat.{u} k) ⋙ (evaluation _ (ModuleCat.{u} k)).obj W
          have hmono : Mono (Fsec.map (devissageSES hx D).f) := Fsec.map_mono _
          rw [← ModuleCat.mono_iff_injective]
          exact hmono)
    exact (devissageSES_map_exact hx D W).fIsKernel
  have hlim : IsLimit (KernelFork.ofι (devissageSES hx D).f (devissageSES hx D).zero) := by
    apply isLimitOfReflects (sheafToPresheaf (Opens.grothendieckTopology (X.left : TopCat))
      (ModuleCat.{u} k))
    refine (Limits.isLimitMapConeForkEquiv' _ (devissageSES hx D).zero).symm ?_
    apply evaluationJointlyReflectsLimits
    intro W
    exact (Limits.isLimitMapConeForkEquiv' ((evaluation _ (ModuleCat.{u} k)).obj W) _).symm
      (hsec W)
  exact (devissageSES hx D).exact_of_f_is_kernel hlim

theorem devissageSES_shortExact [QuasiCompact X.hom] {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    (devissageSES hx D).ShortExact where
  exact := devissageSES_exact hx D
  mono_f := devissageSES_mono_f hx D
  epi_g := devissageSES_epi_g hx D

end Hartshorne
