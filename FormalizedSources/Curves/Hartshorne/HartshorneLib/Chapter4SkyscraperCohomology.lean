/-
Copyright (c) 2026 The Hartshorne formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Hartshorne Contributors
-/

import HartshorneLib.Chapter4Skyscraper

/-!
# Degree-one cohomology of skyscraper sheaves

The degree-zero skyscraper API is in `Chapter4Skyscraper`.  This file ports the
flasque Cech argument showing that the degree-one `HModule` of a skyscraper is
subsingleton.
-/

set_option autoImplicit false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]

theorem exists_app_eq_of_cokernelπ_app_eq_zero {F G : Sheaf J (ModuleCat.{u} R)}
    (ι : F ⟶ G) [Mono ι] (U : Cᵒᵖ) (c : G.obj.obj U)
    (hc : ((cokernel.π ι).hom.app U).hom c = 0) :
    ∃ a : F.obj.obj U, (ι.hom.app U).hom a = c := by
  let Fsec : Sheaf J (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    sheafToPresheaf J (ModuleCat.{u} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj U
  have hker := Abelian.monoIsKernelOfCokernel
    (CokernelCofork.ofπ (cokernel.π ι) (cokernel.condition ι)) (cokernelIsCokernel ι)
  have hkerU := isLimitForkMapOfIsLimit' Fsec _ hker
  let z : ModuleCat.of R R ⟶ Fsec.obj G :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ c)
  have hz : z ≫ Fsec.map (cokernel.π ι) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change ((cokernel.π ι).hom.app U).hom ((1 : R) • c) = _
    rw [one_smul]
    exact hc
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hkerU z hz
  have happ : (ι.hom.app U).hom (l.hom (1 : R)) = (1 : R) • c :=
    congrArg (fun m : ModuleCat.of R R ⟶ Fsec.obj G ↦ m.hom (1 : R)) hl
  rw [one_smul] at happ
  exact ⟨l.hom (1 : R), happ⟩

theorem app_injective_of_mono {F G : Sheaf J (ModuleCat.{u} R)} (ι : F ⟶ G) [Mono ι]
    (U : Cᵒᵖ) : Function.Injective (ι.hom.app U).hom := by
  let Fsec : Sheaf J (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    sheafToPresheaf J (ModuleCat.{u} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj U
  have hmono : Mono (Fsec.map ι) := Fsec.map_mono ι
  rw [← ModuleCat.mono_iff_injective]
  exact hmono

end Sheaf
end CategoryTheory

namespace Hartshorne

noncomputable section
open scoped Classical

variable {k : Type u} [CommRing k]
variable {X : Over (Spec (CommRingCat.of k))}

private lemma skyModule_map_isIso (x : X.left) (M : ModuleCat.{u} k) {U V : X.left.Opens}
    (i : (op U : (X.left.Opens)ᵒᵖ) ⟶ op V) (hV : x ∈ V) :
    IsIso ((skyModule (X := X) x M).obj.map i) := by
  change IsIso ((skyscraperSheaf x M).obj.map i)
  rw [skyscraperSheaf_obj_map, dif_pos hV]
  exact CategoryTheory.instIsIsoEqToHom _

private lemma skyModule_subsingleton_of_not_mem (x : X.left) (M : ModuleCat.{u} k)
    {U : X.left.Opens} (h : x ∉ U) :
    Subsingleton ((skyModule (X := X) x M).obj.obj (op U)) := by
  rw [skyModule_obj_of_not_mem (X := X) x M h]
  exact ModuleCat.subsingleton_of_isZero terminalIsTerminal.isZero

private theorem cokernelπ_app_top_surjective (x : X.left) (M : ModuleCat.{u} k)
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology (X.left : TopCat))
      (ModuleCat.{u} k)}
    (ι : skyModule (X := X) x M ⟶ G) [Mono ι]
    (q : (cokernel ι).obj.obj (op ⊤)) :
    ∃ s : G.obj.obj (op ⊤), ((cokernel.π ι).hom.app (op ⊤)).hom s = q := by
  classical
  haveI hfl : TopCat.Presheaf.IsFlasque (skyModule (X := X) x M).obj :=
    isFlasque_skyscraperSheaf_of_hasZeroObject x M
  have hres_res : ∀ (F : CategoryTheory.Sheaf
      (Opens.grothendieckTopology (X.left : TopCat)) (ModuleCat.{u} k))
      {A B D : X.left.Opens} (h₁ : B ≤ A) (h₂ : D ≤ B) (t : F.obj.obj (op A)),
      (F.obj.map (homOfLE h₂).op).hom ((F.obj.map (homOfLE h₁).op).hom t) =
        (F.obj.map (homOfLE (h₂.trans h₁)).op).hom t := by
    intro F A B D h₁ h₂ t
    have hcomp : F.obj.map (homOfLE h₁).op ≫ F.obj.map (homOfLE h₂).op =
        F.obj.map (homOfLE (h₂.trans h₁)).op := by
      rw [← F.obj.map_comp, ← op_comp, homOfLE_comp]
    calc
      (F.obj.map (homOfLE h₂).op).hom ((F.obj.map (homOfLE h₁).op).hom t) =
          ((F.obj.map (homOfLE h₁).op ≫ F.obj.map (homOfLE h₂).op)).hom t := rfl
      _ = (F.obj.map (homOfLE (h₂.trans h₁)).op).hom t := by rw [hcomp]
  have hres_nat : ∀ {F F' : CategoryTheory.Sheaf
      (Opens.grothendieckTopology (X.left : TopCat)) (ModuleCat.{u} k)}
      (φ : F ⟶ F') {A B : X.left.Opens} (h : B ≤ A) (t : F.obj.obj (op A)),
      (φ.hom.app (op B)).hom ((F.obj.map (homOfLE h).op).hom t) =
        (F'.obj.map (homOfLE h).op).hom ((φ.hom.app (op A)).hom t) := by
    intro F F' φ A B h t
    have hnat := congrArg ModuleCat.Hom.hom (φ.hom.naturality (homOfLE h).op)
    exact DFunLike.congr_fun hnat t
  have _hls : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (X.left : TopCat)) (cokernel.π ι).hom :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u} k)
      (cokernel.π ι)).mpr inferInstance
  have hloc : ∀ p : X.left, ∃ W : X.left.Opens, p ∈ W ∧ ∃ t : G.obj.obj (op W),
      ((cokernel.π ι).hom.app (op W)).hom t =
        ((cokernel ι).obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom q := by
    intro p
    obtain ⟨W, g, hg, hpW⟩ := Presheaf.imageSieve_mem
      (Opens.grothendieckTopology (X.left : TopCat)) (cokernel.π ι).hom q p
      (Opens.mem_top p)
    obtain ⟨t, ht⟩ := hg
    exact ⟨W, hpW, t, ht⟩
  choose W hmem s hs using hloc
  have hcov : (⨆ p, W p) = ⊤ := by
    apply le_antisymm le_top
    intro p _
    exact Opens.mem_iSup.mpr ⟨p, hmem p⟩
  have hker : ∀ p p', ((cokernel.π ι).hom.app (op (W p ⊓ W p'))).hom
      ((G.obj.map (homOfLE (inf_le_left : W p ⊓ W p' ≤ W p)).op).hom (s p) -
        (G.obj.map (homOfLE (inf_le_right : W p ⊓ W p' ≤ W p')).op).hom (s p')) = 0 := by
    intro p p'
    rw [map_sub, hres_nat (cokernel.π ι) (inf_le_left : W p ⊓ W p' ≤ W p) (s p),
      hres_nat (cokernel.π ι) (inf_le_right : W p ⊓ W p' ≤ W p') (s p'), hs p, hs p',
      hres_res (cokernel ι) (le_top : W p ≤ ⊤) (inf_le_left : W p ⊓ W p' ≤ W p),
      hres_res (cokernel ι) (le_top : W p' ≤ ⊤) (inf_le_right : W p ⊓ W p' ≤ W p'),
      sub_self]
  choose a ha using fun p p' => Sheaf.exists_app_eq_of_cokernelπ_app_eq_zero ι
    (op (W p ⊓ W p')) _ (hker p p')
  have hcoc : ∀ p p' l, ((skyModule (X := X) x M).obj.map
        (homOfLE (inf_le_inf_right (W l) (inf_le_left : W p ⊓ W p' ≤ W p))).op).hom (a p l) =
      ((skyModule (X := X) x M).obj.map
          (homOfLE (inf_le_left : W p ⊓ W p' ⊓ W l ≤ W p ⊓ W p')).op).hom (a p p') +
        ((skyModule (X := X) x M).obj.map
            (homOfLE (inf_le_inf_right (W l) (inf_le_right : W p ⊓ W p' ≤ W p'))).op).hom
          (a p' l) := by
    intro p p' l
    apply Sheaf.app_injective_of_mono ι (op (W p ⊓ W p' ⊓ W l))
    have h1 := hres_nat ι (inf_le_inf_right (W l) (inf_le_left : W p ⊓ W p' ≤ W p)) (a p l)
    have h2 := hres_nat ι (inf_le_left : W p ⊓ W p' ⊓ W l ≤ W p ⊓ W p') (a p p')
    have h3 := hres_nat ι (inf_le_inf_right (W l) (inf_le_right : W p ⊓ W p' ≤ W p')) (a p' l)
    simp only [map_add]
    rw [h1, h2, h3, ha p l, ha p p', ha p' l]
    simp only [map_sub, hres_res]
    abel
  choose b hb using fun p => (ModuleCat.epi_iff_surjective
      ((skyModule (X := X) x M).obj.map (homOfLE (inf_le_left : W p ⊓ W x ≤ W p)).op)).mp
      (hfl.epi (homOfLE (inf_le_left : W p ⊓ W x ≤ W p)).op) (a p x)
  replace hb : ∀ p, ((skyModule (X := X) x M).obj.map
      (homOfLE (inf_le_left : W p ⊓ W x ≤ W p)).op).hom (b p) = a p x := hb
  have hinj : ∀ A : X.left.Opens, Function.Injective
      ((skyModule (X := X) x M).obj.map (homOfLE (inf_le_left : A ⊓ W x ≤ A)).op).hom := by
    intro A
    by_cases hx : x ∈ A
    · haveI := skyModule_map_isIso x M (homOfLE (inf_le_left : A ⊓ W x ≤ A)).op ⟨hx, hmem x⟩
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    · haveI := skyModule_subsingleton_of_not_mem x M hx
      exact fun u v _ => Subsingleton.elim u v
  have hab : ∀ p p', a p p' =
      ((skyModule (X := X) x M).obj.map (homOfLE (inf_le_left : W p ⊓ W p' ≤ W p)).op).hom (b p) -
        ((skyModule (X := X) x M).obj.map
          (homOfLE (inf_le_right : W p ⊓ W p' ≤ W p')).op).hom (b p') := by
    intro p p'
    apply hinj (W p ⊓ W p')
    have hc := hcoc p p' x
    rw [← hb p, ← hb p'] at hc
    rw [hres_res (skyModule (X := X) x M) (inf_le_left : W p ⊓ W x ≤ W p)
          (inf_le_inf_right (W x) (inf_le_left : W p ⊓ W p' ≤ W p)),
        hres_res (skyModule (X := X) x M) (inf_le_left : W p' ⊓ W x ≤ W p')
          (inf_le_inf_right (W x) (inf_le_right : W p ⊓ W p' ≤ W p'))] at hc
    rw [map_sub, hres_res (skyModule (X := X) x M) (inf_le_left : W p ⊓ W p' ≤ W p)
          (inf_le_left : W p ⊓ W p' ⊓ W x ≤ W p ⊓ W p'),
        hres_res (skyModule (X := X) x M) (inf_le_right : W p ⊓ W p' ≤ W p')
          (inf_le_left : W p ⊓ W p' ⊓ W x ≤ W p ⊓ W p'), eq_sub_iff_add_eq]
    exact hc.symm
  let tloc : ∀ p, G.obj.obj (op (W p)) :=
    fun p => s p - (ι.hom.app (op (W p))).hom (b p)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj W tloc := by
    intro p p'
    change (G.obj.map (homOfLE (inf_le_left : W p ⊓ W p' ≤ W p)).op).hom
        (s p - (ι.hom.app (op (W p))).hom (b p)) =
      (G.obj.map (homOfLE (inf_le_right : W p ⊓ W p' ≤ W p')).op).hom
        (s p' - (ι.hom.app (op (W p'))).hom (b p'))
    rw [map_sub, map_sub, ← hres_nat ι (inf_le_left : W p ⊓ W p' ≤ W p) (b p),
      ← hres_nat ι (inf_le_right : W p ⊓ W p' ≤ W p') (b p'),
      sub_eq_sub_iff_sub_eq_sub, ← map_sub, ← hab p p']
    exact (ha p p').symm
  obtain ⟨gl, hgl, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X.left : TopCat)) (C := ModuleCat.{u} k) G W ⊤
    (fun p => homOfLE (le_top : W p ≤ ⊤)) (le_of_eq hcov.symm) tloc hcompat
  refine ⟨gl, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X.left : TopCat)) (C := ModuleCat.{u} k)
    (cokernel ι) W ⊤ (fun p => homOfLE (le_top : W p ≤ ⊤)) (le_of_eq hcov.symm)
  intro p
  change ((cokernel ι).obj.map (homOfLE (le_top : W p ≤ ⊤)).op).hom
      (((cokernel.π ι).hom.app (op ⊤)).hom gl) =
    ((cokernel ι).obj.map (homOfLE (le_top : W p ≤ ⊤)).op).hom q
  rw [← hres_nat (cokernel.π ι) (le_top : W p ≤ ⊤) gl]
  have hgl' : (G.obj.map (homOfLE (le_top : W p ≤ ⊤)).op).hom gl = tloc p := hgl p
  rw [hgl']
  change ((cokernel.π ι).hom.app (op (W p))).hom
    (s p - (ι.hom.app (op (W p))).hom (b p)) = _
  have hπι : ((cokernel.π ι).hom.app (op (W p))).hom
      ((ι.hom.app (op (W p))).hom (b p)) = 0 :=
    congrArg (fun m : skyModule (X := X) x M ⟶ cokernel ι =>
      (m.hom.app (op (W p))).hom (b p)) (cokernel.condition ι)
  rw [map_sub, hs p, hπι, sub_zero]

instance skyModule_subsingleton_hModule_one (x : X.left) (M : ModuleCat.{u} k) :
    Subsingleton (CategoryTheory.Sheaf.HModule
      (Opens.grothendieckTopology (X.left : TopCat)) k
      (skyModule (X := X) x M) 1) := by
  change Subsingleton (Abelian.Ext
    (CategoryTheory.Sheaf.constModuleSheaf
      (Opens.grothendieckTopology (X.left : TopCat)) k)
    (skyModule (X := X) x M) 1)
  apply Abelian.Ext.subsingleton_one_of_injective_of_surjective
    (Injective.ι (skyModule (X := X) x M))
  intro φ
  obtain ⟨sglob, hsglob⟩ := cokernelπ_app_top_surjective x M
    (Injective.ι (skyModule (X := X) x M))
    (CategoryTheory.Sheaf.constModuleSheafHomEquiv
      (isTerminalTop : IsTerminal (⊤ : X.left.Opens))
      (cokernel (Injective.ι (skyModule (X := X) x M))) φ)
  refine ⟨(CategoryTheory.Sheaf.constModuleSheafHomEquiv
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens))
    (Injective.under (skyModule (X := X) x M))).symm sglob, ?_⟩
  apply (CategoryTheory.Sheaf.constModuleSheafHomEquiv
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens))
    (cokernel (Injective.ι (skyModule (X := X) x M)))).injective
  have hnat := CategoryTheory.Sheaf.constModuleSheafHomEquiv_naturality
    (isTerminalTop : IsTerminal (⊤ : X.left.Opens))
    ((CategoryTheory.Sheaf.constModuleSheafHomEquiv
      (isTerminalTop : IsTerminal (⊤ : X.left.Opens))
      (Injective.under (skyModule (X := X) x M))).symm sglob)
    (cokernel.π (Injective.ι (skyModule (X := X) x M)))
  rw [hnat, LinearEquiv.apply_symm_apply]
  exact hsglob

end
end Hartshorne
