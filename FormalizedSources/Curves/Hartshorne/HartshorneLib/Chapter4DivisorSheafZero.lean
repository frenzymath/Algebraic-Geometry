/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4DivisorSheaf

/-!
# The zero-divisor sheaf

The zero divisor has no poles, so its sheaf of bounded rational functions is
canonically the structure sheaf.  We construct the comparison sectionwise,
using the generic-point germ and gluing local regular representatives.
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

/-! ## Generic-point and stalk seams -/

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
lemma genericPoint_mem_of_nonempty {U : X.left.Opens} (hU : (U : Set X.left).Nonempty) :
    genericPoint X.left ∈ U :=
  ((genericPoint_spec X.left).mem_open_set_iff (U := (↑U : Set X.left)) U.isOpen).mpr
    (by simpa using hU)

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
lemma germ_generic_eq_algebraMap_germ {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) {x : X.left} (hxU : x ∈ U) (s : Γ(X.left, U)) :
    (X.left.presheaf.germ U (genericPoint X.left) hηU).hom s =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField
        ((X.left.presheaf.germ U x hxU).hom s) := by
  have hspec : genericPoint X.left ⤳ x :=
    (genericPoint_spec X.left).specializes (Set.mem_univ x)
  have hcomp := X.left.presheaf.germ_stalkSpecializes (U := U) (y := x) hxU hspec
  have happ := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) s
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  exact happ.symm

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
lemma germ_generic_overAlgebraMap {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) (r : k) :
    (X.left.presheaf.germ U (genericPoint X.left) hηU).hom
        (X.left.overAlgebraMap k U r) = functionFieldOverAlgebraMap k X.left r := by
  have hres := X.left.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤))
    (genericPoint X.left) hηU (X.left.overAlgebraMap k ⊤ r)
  rw [X.left.overAlgebraMap_apply_res k (homOfLE (le_top : U ≤ ⊤)).op r] at hres
  rw [hres]
  rfl

/-! ## The sectionwise comparison -/

noncomputable def germGenericLinear {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) : Γ(X.left, U) →ₗ[k] X.left.functionField where
  toFun := (X.left.presheaf.germ U (genericPoint X.left) hηU).hom
  map_add' := map_add _
  map_smul' r s := by
    simp only [RingHom.id_apply, Scheme.overModule_smul_def, map_mul,
      germ_generic_overAlgebraMap hηU r, functionFieldOverModule_smul_def]

lemma germGenericLinear_mem {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) (s : Γ(X.left, U)) :
    germGenericLinear hηU s ∈ divisorSections (X := X) (0 : CurveDivisor k X) U := by
  rw [mem_divisorSections_of_nonempty (⟨genericPoint X.left, hηU⟩ : (U : Set X.left).Nonempty)]
  intro x hx hxU
  rw [divisorBound_zero hx]
  change orderAt X.hom hx
    ((X.left.presheaf.germ U (genericPoint X.left) hηU).hom s) ≤ 1
  rw [germ_generic_eq_algebraMap_germ hηU hxU s]
  exact orderAt_algebraMap_stalk_le_one hx _

noncomputable def moduleToDivisorZeroApp {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) :
    Γ(X.left, U) →ₗ[k] divisorSections (X := X) (0 : CurveDivisor k X) U :=
  LinearMap.codRestrict _ (germGenericLinear hηU) (germGenericLinear_mem hηU)

lemma moduleToDivisorZeroApp_coe {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) (s : Γ(X.left, U)) :
    ((moduleToDivisorZeroApp (X := X) hηU s :
        divisorSections (X := X) (0 : CurveDivisor k X) U) : X.left.functionField) =
      (X.left.presheaf.germ U (genericPoint X.left) hηU).hom s := rfl

open Classical in
noncomputable def moduleToDivisorZeroPresheafApp (U : X.left.Opens) :
    Γ(X.left, U) →ₗ[k] divisorSections (X := X) (0 : CurveDivisor k X) U :=
  if hU : (U : Set X.left).Nonempty then
    moduleToDivisorZeroApp (X := X) (genericPoint_mem_of_nonempty hU)
  else 0

lemma moduleToDivisorZeroPresheafApp_of_nonempty {U : X.left.Opens}
    (hU : (U : Set X.left).Nonempty) :
    moduleToDivisorZeroPresheafApp (X := X) U =
      moduleToDivisorZeroApp (X := X) (genericPoint_mem_of_nonempty hU) :=
  dif_pos hU

lemma moduleToDivisorZeroPresheafApp_coe_of_nonempty {U : X.left.Opens}
    (hU : (U : Set X.left).Nonempty) (s : Γ(X.left, U)) :
    ((moduleToDivisorZeroPresheafApp (X := X) U s :
        divisorSections (X := X) (0 : CurveDivisor k X) U) : X.left.functionField) =
      (X.left.presheaf.germ U (genericPoint X.left)
        (genericPoint_mem_of_nonempty hU)).hom s := by
  rw [moduleToDivisorZeroPresheafApp_of_nonempty hU]
  rfl

/-! ## Local representability and gluing -/

omit [IsAlgClosed k] [IsProper X.hom] in
lemma exists_stalk_of_order_le_one {x : X.left} (hx : x ≠ genericPoint X.left)
    {g : X.left.functionField}
    (hg : orderAt X.hom hx g ≤ 1) :
    ∃ y : X.left.presheaf.stalk x,
      algebraMap (X.left.presheaf.stalk x) X.left.functionField y = g := by
  letI := smoothCurve_stalk_isDiscreteValuationRing X.hom hx
  letI := smoothCurve_stalk_isDedekindDomain X.hom hx
  set v₀ : IsDedekindDomain.HeightOneSpectrum (X.left.presheaf.stalk x) :=
    ⟨IsLocalRing.maximalIdeal (X.left.presheaf.stalk x),
      (IsLocalRing.maximalIdeal.isMaximal (X.left.presheaf.stalk x)).isPrime,
      IsDiscreteValuationRing.not_a_field (X.left.presheaf.stalk x)⟩
  have hord : orderAt X.hom hx = v₀.valuation X.left.functionField := rfl
  have hall : ∀ v : IsDedekindDomain.HeightOneSpectrum (X.left.presheaf.stalk x),
      v.valuation X.left.functionField g ≤ 1 := by
    intro v
    have hvv : v = v₀ :=
      IsDedekindDomain.HeightOneSpectrum.ext
        (IsLocalRing.eq_maximalIdeal v.isMaximal)
    rw [hvv, ← hord]
    exact hg
  exact RingHom.mem_range.mp
    (IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      X.left.functionField g hall)

lemma exists_local_section {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U)
    {g : X.left.functionField}
    (hg : g ∈ divisorSections (X := X) (0 : CurveDivisor k X) U)
    {x : X.left} (hxU : x ∈ U) :
    ∃ (W : X.left.Opens) (_ : x ∈ W) (_ : W ≤ U) (s : Γ(X.left, W))
      (hηW : genericPoint X.left ∈ W),
      (X.left.presheaf.germ W (genericPoint X.left) hηW).hom s = g := by
  by_cases hx : x = genericPoint X.left
  · obtain ⟨W₀, hηW₀, s₀, hs₀⟩ :=
      X.left.presheaf.exists_germ_eq (x := genericPoint X.left) g
    have hxW : x ∈ W₀ ⊓ U := hx ▸ ⟨hηW₀, hηU⟩
    have hηW : genericPoint X.left ∈ W₀ ⊓ U := ⟨hηW₀, hηU⟩
    refine ⟨W₀ ⊓ U, hxW, inf_le_right,
      (X.left.presheaf.map (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)).op).hom s₀, hηW, ?_⟩
    rw [X.left.presheaf.germ_res_apply
      (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)) (genericPoint X.left) hηW s₀]
    exact hs₀
  · have hord : orderAt X.hom hx g ≤ 1 := by
      have hmem := (mem_divisorSections_of_nonempty
        (X := X) (D := (0 : CurveDivisor k X))
        (⟨genericPoint X.left, hηU⟩ : (U : Set X.left).Nonempty)).mp hg x hx hxU
      rwa [divisorBound_zero hx] at hmem
    obtain ⟨y, hy⟩ := exists_stalk_of_order_le_one hx hord
    obtain ⟨W₀, hxW₀, s₀, hs₀⟩ := X.left.presheaf.exists_germ_eq (x := x) y
    have hxW : x ∈ W₀ ⊓ U := ⟨hxW₀, hxU⟩
    have hηW : genericPoint X.left ∈ W₀ ⊓ U :=
      genericPoint_mem_of_nonempty ⟨x, hxW⟩
    refine ⟨W₀ ⊓ U, hxW, inf_le_right,
      (X.left.presheaf.map (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)).op).hom s₀, hηW, ?_⟩
    rw [germ_generic_eq_algebraMap_germ hηW hxW,
      X.left.presheaf.germ_res_apply
        (homOfLE (inf_le_left : W₀ ⊓ U ≤ W₀)) x hxW s₀, hs₀]
    exact hy

lemma exists_section_germ_eq {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) {g : X.left.functionField}
    (hg : g ∈ divisorSections (X := X) (0 : CurveDivisor k X) U) :
    ∃ s : Γ(X.left, U),
      (X.left.presheaf.germ U (genericPoint X.left) hηU).hom s = g := by
  choose W hxW hWU s hηW hs using
    fun p : ↥U => exists_local_section (X := X) hηU hg (x := p.1) p.2
  have hcover : U ≤ ⨆ p, W p := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.left.sheaf.obj W s := by
    intro p q
    have hη : genericPoint X.left ∈ W p ⊓ W q := ⟨hηW p, hηW q⟩
    apply germ_injective_of_isIntegral X.left (genericPoint X.left) hη
    change (X.left.presheaf.germ (W p ⊓ W q) (genericPoint X.left) hη).hom
          ((X.left.presheaf.map (Opens.infLELeft (W p) (W q)).op).hom (s p)) =
      (X.left.presheaf.germ (W p ⊓ W q) (genericPoint X.left) hη).hom
          ((X.left.presheaf.map (Opens.infLERight (W p) (W q)).op).hom (s q))
    rw [X.left.presheaf.germ_res_apply (Opens.infLELeft (W p) (W q))
          (genericPoint X.left) hη (s p),
      X.left.presheaf.germ_res_apply (Opens.infLERight (W p) (W q))
          (genericPoint X.left) hη (s q), hs p, hs q]
  obtain ⟨sU, hsU, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.left.sheaf W U
    (fun p => homOfLE (hWU p)) hcover s hcompat
  refine ⟨sU, ?_⟩
  set p₀ : ↥U := ⟨genericPoint X.left, hηU⟩
  have hsU' : (X.left.presheaf.map (homOfLE (hWU p₀)).op).hom sU = s p₀ := hsU p₀
  have key := X.left.presheaf.germ_res_apply (homOfLE (hWU p₀))
    (genericPoint X.left) (hηW p₀) sU
  have heq : (X.left.presheaf.germ U (genericPoint X.left) hηU).hom sU =
      (X.left.presheaf.germ (W p₀) (genericPoint X.left) (hηW p₀)).hom (s p₀) := by
    rw [← hsU']
    exact key.symm
  rw [heq]
  exact hs p₀

/-! ## Isomorphism of presheaves and sheaves -/

lemma moduleToDivisorZeroApp_injective {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) :
    Function.Injective (moduleToDivisorZeroApp (X := X) hηU) := by
  intro a b hab
  apply germ_injective_of_isIntegral X.left (genericPoint X.left) hηU
  exact Subtype.ext_iff.mp hab

lemma moduleToDivisorZeroApp_surjective {U : X.left.Opens}
    (hηU : genericPoint X.left ∈ U) :
    Function.Surjective (moduleToDivisorZeroApp (X := X) hηU) := by
  intro t
  obtain ⟨s, hs⟩ := exists_section_germ_eq (X := X) hηU t.2
  exact ⟨s, Subtype.ext hs⟩

lemma moduleToDivisorZeroPresheafApp_bijective (U : X.left.Opens) :
    Function.Bijective (moduleToDivisorZeroPresheafApp (X := X) U) := by
  by_cases hU : (U : Set X.left).Nonempty
  · rw [moduleToDivisorZeroPresheafApp_of_nonempty (X := X) hU]
    exact ⟨moduleToDivisorZeroApp_injective (X := X) _,
      moduleToDivisorZeroApp_surjective (X := X) _⟩
  · have hbot : U = ⊥ := by
      apply Opens.ext
      rw [Set.not_nonempty_iff_eq_empty.mp hU, Opens.coe_bot]
    haveI hsub_dom : Subsingleton Γ(X.left, U) := by rw [hbot]; infer_instance
    haveI hsub_cod : Subsingleton
        (divisorSections (X := X) (0 : CurveDivisor k X) U) :=
      divisorSections_subsingleton_of_empty hU
    exact ⟨fun a b _ => Subsingleton.elim a b,
      fun y => ⟨0, Subsingleton.elim _ _⟩⟩

noncomputable def moduleToDivisorZeroPresheaf :
    X.left.moduleKPresheaf k ⟶ divisorPresheaf (X := X) (0 : CurveDivisor k X) where
  app U := ModuleCat.ofHom (moduleToDivisorZeroPresheafApp (X := X) U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    by_cases hV : (V.unop : Set X.left).Nonempty
    · have hU : (U.unop : Set X.left).Nonempty := hV.mono (leOfHom i.unop)
      apply Subtype.ext
      change ((moduleToDivisorZeroPresheafApp (X := X) V.unop ((X.left.presheaf.map i).hom s) :
          divisorSections (X := X) (0 : CurveDivisor k X) V.unop) : X.left.functionField) =
        ((divisorSectionsRes (X := X) (D := (0 : CurveDivisor k X)) (leOfHom i.unop)
          (moduleToDivisorZeroPresheafApp (X := X) U.unop s) :
            divisorSections (X := X) (0 : CurveDivisor k X) V.unop) : X.left.functionField)
      rw [moduleToDivisorZeroPresheafApp_coe_of_nonempty (X := X) hV,
        divisorSectionsRes_coe (X := X) (D := (0 : CurveDivisor k X))
          (leOfHom i.unop) hV,
        moduleToDivisorZeroPresheafApp_coe_of_nonempty (X := X) hU]
      have hgr := X.left.presheaf.germ_res_apply i.unop (genericPoint X.left)
        (genericPoint_mem_of_nonempty (X := X) hV) s
      simpa using hgr
    · letI := divisorPresheaf_obj_subsingleton (X := X)
        (D := (0 : CurveDivisor k X)) (W := V.unop) hV
      exact Subsingleton.elim _ _

lemma moduleToDivisorZeroPresheaf_app_isIso (U : (X.left.Opens)ᵒᵖ) :
    IsIso ((moduleToDivisorZeroPresheaf (X := X)).app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact moduleToDivisorZeroPresheafApp_bijective (X := X) U.unop

noncomputable def moduleToDivisorZeroPresheafIso :
    X.left.moduleKPresheaf k ≅ divisorPresheaf (X := X) (0 : CurveDivisor k X) :=
  NatIso.ofComponents
    (fun U => by
      letI := moduleToDivisorZeroPresheaf_app_isIso (X := X) U
      exact asIso ((moduleToDivisorZeroPresheaf (X := X)).app U))
    (fun i => (moduleToDivisorZeroPresheaf (X := X)).naturality i)

noncomputable def moduleKSheafDivisorSheafZeroIso :
    X.left.moduleKSheaf k ≅ divisorSheaf (X := X) (0 : CurveDivisor k X) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (moduleToDivisorZeroPresheafIso (X := X))

noncomputable def divisorSheafZeroIso :
    divisorSheaf (X := X) (0 : CurveDivisor k X) ≅ X.left.moduleKSheaf k :=
  (moduleKSheafDivisorSheafZeroIso (X := X)).symm

end Hartshorne
