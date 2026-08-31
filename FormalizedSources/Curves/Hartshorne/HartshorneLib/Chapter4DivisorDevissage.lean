/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorInduction
import HartshorneLib.Chapter4DivisorSheaf
import HartshorneLib.Chapter4Skyscraper

/-!
# One-point dévissage of divisor sheaves

For a non-generic point `x` on a smooth integral curve, this file packages the
one-point valuation filtration used in the standard divisor dévissage.  The
quotient between the bounds at `D x` and `D x - 1` is the jump module, and a
section of `𝒪(D)` over an open containing `x` has a canonical class in it.

The construction is deliberately kept independent of the still-open global
product formula.  It is the local input for the short exact sequence
`𝒪(D - x) → 𝒪(D) → sky_x J`.
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

/-! ## The one-point lattice -/

noncomputable def pointLattice {x : X.left} (hx : x ≠ genericPoint X.left)
    (n : ℤ) : Submodule k X.left.functionField where
  carrier := {g | orderAt X.hom hx g ≤
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}
  zero_mem' := by
    rw [Set.mem_setOf_eq, map_zero]
    exact zero_le
  add_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    exact le_trans (Valuation.map_add _ g h) (max_le hg hh)
  smul_mem' := by
    intro r g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    rw [functionFieldOverModule_smul_def k X.left, map_mul]
    calc
      orderAt X.hom hx (functionFieldOverAlgebraMap k X.left r) *
          orderAt X.hom hx g ≤ 1 * orderAt X.hom hx g := by
        gcongr
        exact orderAt_functionFieldOverAlgebraMap_le_one hx r
      _ = orderAt X.hom hx g := one_mul _
      _ ≤ ((Multiplicative.ofAdd n : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := hg

omit [IsAlgClosed k] [IsProper X.hom] in
lemma mem_pointLattice {x : X.left} (hx : x ≠ genericPoint X.left)
    {n : ℤ} {g : X.left.functionField} :
    g ∈ pointLattice (X := X) hx n ↔
      orderAt X.hom hx g ≤
        ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  Iff.rfl

/- Increasing the integer bound enlarges the one-point lattice. -/
omit [IsAlgClosed k] [IsProper X.hom] in
lemma pointLattice_mono {x : X.left} (hx : x ≠ genericPoint X.left)
    {m n : ℤ} (h : m ≤ n) :
    pointLattice (X := X) hx m ≤ pointLattice (X := X) hx n := by
  intro g hg
  rw [mem_pointLattice] at hg ⊢
  exact le_trans hg (by exact_mod_cast Multiplicative.ofAdd_le.mpr h)

/-! ## The jump module -/

lemma divisorBound_eq_coeffAt {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    divisorBound D hx =
      ((Multiplicative.ofAdd (CurveDivisor.coeffAt hx D) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := rfl

noncomputable def jumpModule {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : ModuleCat.{u} k :=
  ModuleCat.of k
    (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D) ⧸
      (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1)).submoduleOf
        (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D)))

lemma divisorSections_le_pointLattice {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)
    (U : X.left.Opens) (hxU : x ∈ U) :
    divisorSections D U ≤
      pointLattice (X := X) hx (CurveDivisor.coeffAt hx D) := by
  have hne : (U : Set X.left).Nonempty := ⟨x, hxU⟩
  intro g hg
  rw [mem_divisorSections_of_nonempty hne] at hg
  rw [mem_pointLattice]
  have hgx := hg x hx hxU
  rwa [divisorBound_eq_coeffAt hx D] at hgx

/-- Projection of a divisor section to the one-point jump quotient. -/
noncomputable def jumpProj {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (U : X.left.Opens) (hxU : x ∈ U) :
    divisorSections D U →ₗ[k] jumpModule hx D := by
  change divisorSections D U →ₗ[k]
    (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D) ⧸
      (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1)).submoduleOf
        (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D)))
  exact (Submodule.mkQ
      ((pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1)).submoduleOf
        (pointLattice (X := X) hx (CurveDivisor.coeffAt hx D)))).comp
    (Submodule.inclusion (divisorSections_le_pointLattice hx D U hxU))

lemma jumpProj_apply {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (U : X.left.Opens) (hxU : x ∈ U)
    (s : divisorSections D U) :
    jumpProj hx D U hxU s =
      Submodule.Quotient.mk ⟨(s : X.left.functionField),
        divisorSections_le_pointLattice hx D U hxU s.2⟩ := rfl

lemma jumpProj_eq_of_coe_eq {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) {U V : X.left.Opens}
    (hxU : x ∈ U) (hxV : x ∈ V)
    (s : divisorSections D U) (t : divisorSections D V)
    (h : (s : X.left.functionField) = (t : X.left.functionField)) :
    jumpProj hx D U hxU s = jumpProj hx D V hxV t := by
  rw [jumpProj_apply, jumpProj_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext h)

/-! ## The skyscraper target -/

omit [IsAlgClosed k] [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] in
lemma skyModule_obj_of_mem' {x : X.left} (M : ModuleCat.{u} k)
    {W : (X.left.Opens)ᵒᵖ} (h : x ∈ W.unop) :
    (skyModule (X := X) x M).obj.obj W = M :=
  skyModule_obj_of_mem x M h

omit [IsAlgClosed k] [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] in
lemma skyModule_map_eq {x : X.left} (M : ModuleCat.{u} k)
    {U V : (X.left.Opens)ᵒᵖ} (i : U ⟶ V)
    (hU : x ∈ U.unop) (hV : x ∈ V.unop) :
    (skyModule (X := X) x M).obj.map i =
      eqToHom ((skyModule_obj_of_mem' (X := X) M hU).trans
        (skyModule_obj_of_mem' (X := X) M hV).symm) := by
  change (skyscraperSheaf x M).obj.map i = _
  rw [skyscraperSheaf_obj_map]
  exact dif_pos hV

omit [IsAlgClosed k] [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] in
lemma skyModule_obj_subsingleton {x : X.left} (M : ModuleCat.{u} k)
    {V : X.left.Opens} (hV : x ∉ V) :
    Subsingleton ((skyModule (X := X) x M).obj.obj (op V)) := by
  rw [skyModule_obj_of_not_mem x M hV]
  exact ModuleCat.subsingleton_of_isZero terminalIsTerminal.isZero

/-! ## The local projection as a sheaf morphism -/

noncomputable def skyComponent {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (W : (X.left.Opens)ᵒᵖ) :
    (divisorPresheaf D).obj W ⟶
      (skyModule (X := X) x (jumpModule hx D)).obj.obj W :=
  if h : x ∈ W.unop then
    ModuleCat.ofHom (jumpProj hx D W.unop h) ≫
      eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) h).symm
  else 0

lemma skyComponent_of_mem {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (W : (X.left.Opens)ᵒᵖ) (hxW : x ∈ W.unop) :
    skyComponent hx D W =
      ModuleCat.ofHom (jumpProj hx D W.unop hxW) ≫
        eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxW).symm := by
  rw [skyComponent]
  exact dif_pos hxW

lemma skyComponent_hom_apply_of_mem {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)
    (W : (X.left.Opens)ᵒᵖ) (hxW : x ∈ W.unop)
    (s : (divisorPresheaf D).obj W) :
    (skyComponent hx D W).hom s =
      (eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxW).symm).hom
        (jumpProj hx D W.unop hxW s) := by
  rw [skyComponent_of_mem hx D W hxW]
  rfl

omit [IsAlgClosed k] [IsIntegral X.left] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] in
lemma eqToHom_comp_skyModule_map {x : X.left} (M : ModuleCat.{u} k)
    {U V : (X.left.Opens)ᵒᵖ} (i : U ⟶ V)
    (hU : x ∈ U.unop) (hV : x ∈ V.unop) :
    eqToHom (skyModule_obj_of_mem' (X := X) M hU).symm ≫
        (skyModule (X := X) x M).obj.map i =
      eqToHom (skyModule_obj_of_mem' (X := X) M hV).symm := by
  rw [skyModule_map_eq (X := X) M i hU hV, eqToHom_trans]

noncomputable def devissagePresheafπ {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X) :
    divisorPresheaf D ⟶ (skyModule (X := X) x (jumpModule hx D)).obj where
  app W := skyComponent hx D W
  naturality := by
    intro U V i
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := leOfHom i.unop hV
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change (skyComponent hx D V).hom
          (((divisorPresheaf D).map i).hom s) =
        ((skyModule (X := X) x (jumpModule hx D)).obj.map i).hom
          ((skyComponent hx D U).hom s)
      rw [skyComponent_hom_apply_of_mem hx D V hV,
        skyComponent_hom_apply_of_mem hx D U hU]
      have hjump : jumpProj hx D V.unop hV (((divisorPresheaf D).map i).hom s) =
          jumpProj hx D U.unop hU s := by
        refine jumpProj_eq_of_coe_eq hx D hV hU _ s ?_
        exact divisorSectionsRes_coe (leOfHom i.unop) ⟨x, hV⟩ s
      rw [hjump]
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (eqToHom_comp_skyModule_map (X := X) (jumpModule hx D) i hU hV)) _).symm
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      haveI := skyModule_obj_subsingleton (X := X) (jumpModule hx D) hV
      exact Subsingleton.elim _ _

noncomputable def devissageπ {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    divisorSheaf D ⟶ skyModule (X := X) x (jumpModule hx D) :=
  (fullyFaithfulSheafToPresheaf _ _).preimage (devissagePresheafπ hx D)

lemma devissageπ_hom {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    (devissageπ hx D).hom = devissagePresheafπ hx D :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage
    (X := divisorSheaf D) (Y := skyModule (X := X) x (jumpModule hx D))
    (devissagePresheafπ hx D)

lemma devissageπ_app {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (W : (X.left.Opens)ᵒᵖ) :
    (devissageπ hx D).hom.app W = skyComponent hx D W := by
  rw [devissageπ_hom]
  rfl

lemma devissageπ_app_hom_apply_of_mem {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)
    (W : (X.left.Opens)ᵒᵖ) (hxW : x ∈ W.unop)
    (s : (divisorPresheaf D).obj W) :
    ((devissageπ hx D).hom.app W).hom s =
      (eqToHom (skyModule_obj_of_mem' (X := X) (jumpModule hx D) hxW).symm).hom
        (jumpProj hx D W.unop hxW s) := by
  rw [← skyComponent_hom_apply_of_mem hx D W hxW s]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (devissageπ_app hx D W)) s

/-! ## The composite with the order inclusion -/

lemma devissageDivisor_coeffAt {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    CurveDivisor.coeffAt hx (CurveDivisor.devissageDivisor hx D) =
      CurveDivisor.coeffAt hx D - 1 := by
  rw [CurveDivisor.devissageDivisor_eq_sub, CurveDivisor.coeffAt_sub]
  have hs : CurveDivisor.coeffAt hx (CurveDivisor.single hx 1) = 1 := by
    change (Finsupp.single (⟨x, hx⟩ :
      {p : X.left // p ≠ genericPoint X.left}) 1) ⟨x, hx⟩ = 1
    exact Finsupp.single_eq_same
  rw [hs]

lemma devissageDivisor_le {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : CurveDivisor.devissageDivisor hx D ≤ D := by
  rw [CurveDivisor.devissageDivisor_eq_sub]
  rw [CurveDivisor.le_iff_coeffAt]
  intro z hz
  rw [CurveDivisor.coeffAt_sub]
  have hsingle : 0 ≤ CurveDivisor.coeffAt hz (CurveDivisor.single hx 1) := by
    change 0 ≤ (Finsupp.single (⟨x, hx⟩ :
      {p : X.left // p ≠ genericPoint X.left}) 1) ⟨z, hz⟩
    rw [Finsupp.single_apply]
    split <;> norm_num
  omega

lemma coe_mem_pointLattice_of_devissageSection {x : X.left}
    (hx : x ≠ genericPoint X.left) (D : CurveDivisor k X)
    (W : X.left.Opens) (hxW : x ∈ W)
    (s : divisorSections (CurveDivisor.devissageDivisor hx D) W) :
    (s : X.left.functionField) ∈
      pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1) := by
  have hne : (W : Set X.left).Nonempty := ⟨x, hxW⟩
  have hb := (mem_divisorSections_of_nonempty hne).mp s.2 x hx hxW
  rw [divisorBound_eq_coeffAt hx (CurveDivisor.devissageDivisor hx D),
    devissageDivisor_coeffAt hx D] at hb
  rw [mem_pointLattice]
  exact hb

lemma divisorSheafLE_hom {D₁ D₂ : CurveDivisor k X} (h : D₁ ≤ D₂) :
    (divisorSheafLE h).hom = divisorPresheafLE h :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage
    (X := divisorSheaf D₁) (Y := divisorSheaf D₂) (divisorPresheafLE h)

lemma skyComponent_of_not_mem {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) (W : (X.left.Opens)ᵒᵖ) (hxW : x ∉ W.unop) :
    skyComponent hx D W = 0 := by
  rw [skyComponent]
  exact dif_neg hxW

lemma devissage_comp_eq_zero {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    divisorSheafLE (devissageDivisor_le hx D) ≫ devissageπ hx D = 0 := by
  ext W s
  change ((devissageπ hx D).hom.app W).hom
      (((divisorSheafLE (devissageDivisor_le hx D)).hom.app W).hom s) = 0
  by_cases hxW : x ∈ W.unop
  · have hmem :
        (((divisorSheafLE (devissageDivisor_le hx D)).hom.app W).hom s).1 ∈
          pointLattice (X := X) hx (CurveDivisor.coeffAt hx D - 1) := by
      rw [divisorSheafLE_hom]
      exact coe_mem_pointLattice_of_devissageSection hx D W.unop hxW s
    have hzero : jumpProj hx D W.unop hxW
        (((divisorSheafLE (devissageDivisor_le hx D)).hom.app W).hom s) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [devissageπ_app_hom_apply_of_mem hx D W hxW, hzero, map_zero]
  · rw [devissageπ_app, skyComponent_of_not_mem hx D W hxW]
    rfl

noncomputable def devissageSES {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (X.left : TopCat))
      (ModuleCat.{u} k)) :=
  ShortComplex.mk (divisorSheafLE (devissageDivisor_le hx D))
    (devissageπ hx D) (devissage_comp_eq_zero hx D)

instance devissageSES_mono_f {x : X.left} (hx : x ≠ genericPoint X.left)
    (D : CurveDivisor k X) : Mono (devissageSES hx D).f :=
  divisorSheafLE_mono (devissageDivisor_le hx D)

end Hartshorne
