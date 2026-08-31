/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.AffineStalkLocalization

/-!
# Affine-open transport for stalk reconstruction

This file transports the `Spec`-level reconstruction theorem of
`AffineStalkLocalization` to an affine open of an arbitrary scheme.  Restriction
along `IsAffineOpen.fromSpec` identifies sections on the affine open with top
sections on its spectrum model.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical spectrum chart identifies the restriction of an affine-open
coordinate function to its image with the corresponding spectrum section. -/
lemma fromSpec_restrict_ring_section_top
    {U : X.Opens} (hU : IsAffineOpen U)
    (eT : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U) (r : Γ(X, U)) :
    (X.presheaf.map (eqToHom eT).op).hom r =
      (hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv.hom
        ((Scheme.ΓSpecIso Γ(X, U)).inv.hom r) := by
  have hfwd := fromSpec_image_top_section_coherence hU eT
  haveI : IsIso (X.presheaf.map (eqToHom eT.symm).op) := inferInstance
  apply (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom eT.symm).op)).1
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp,
    eqToHom_trans, eqToHom_refl, op_id, X.presheaf.map_id]
  change r =
    (X.presheaf.map (eqToHom eT.symm).op).hom
      ((hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv.hom
        ((Scheme.ΓSpecIso Γ(X, U)).inv.hom r))
  rw [hfwd, CommRingCat.comp_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The section-ring comparison for the canonical spectrum chart commutes with
restriction from the affine open to every open of its spectrum model. -/
lemma fromSpec_restrict_ring_section
    {U : X.Opens} (hU : IsAffineOpen U)
    (V : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    let j := hU.fromSpec
    let eT : j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
      (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
    let hVU : j ''ᵁ V ≤ U := (j.image_mono le_top).trans_eq eT
    (j.appIso V).inv.hom
        (((Spec Γ(X, U)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso Γ(X, U)).inv.hom r)) =
      (X.presheaf.map (homOfLE hVU).op).hom r := by
  let j := hU.fromSpec
  let eT : j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  let hVU : j ''ᵁ V ≤ U := (j.image_mono le_top).trans_eq eT
  have hnat := j.appIso_inv_naturality
    (homOfLE (le_top : V ≤ (⊤ : (Spec Γ(X, U)).Opens))).op
  have happ := ConcreteCategory.congr_hom hnat
    ((Scheme.ΓSpecIso Γ(X, U)).inv.hom r)
  simp only [CategoryTheory.comp_apply] at happ
  rw [← fromSpec_restrict_ring_section_top hU eT r] at happ
  refine happ.trans ?_
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Sections over an affine open, mapped to top sections after restricting the
module to the canonical spectrum chart. -/
noncomputable def fromSpecRestrictTopHom
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    let R := Γ(X, U)
    let j := hU.fromSpec
    M.val.obj (op U) ⟶
      (moduleSpecΓFunctor (R := R)).obj ((restrictFunctor j).obj M) := by
  let R := Γ(X, U)
  let j := hU.fromSpec
  let F := (restrictFunctor j).obj M
  have eT : j ''ᵁ (⊤ : (Spec R).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  let q : Γ(M, U) ⟶ Γ(M, j ''ᵁ (⊤ : (Spec R).Opens)) :=
    M.presheaf.map (eqToHom eT).op
  have hqRing : ∀ r : R,
      (X.presheaf.map (eqToHom eT).op).hom r =
        (j.appIso (⊤ : (Spec R).Opens)).inv.hom
          ((Scheme.ΓSpecIso R).inv.hom r) :=
    fromSpec_restrict_ring_section_top hU eT
  exact ConcreteCategory.ofHom (C := ModuleCat R)
    { toFun := q.hom
      map_add' := q.hom.map_add
      map_smul' := fun r m => by
        rw [Scheme.Modules.smul_Spec_def (M := F)]
        change M.val.map (eqToHom eT).op (r • m) =
          (j.appIso (⊤ : (Spec R).Opens)).inv.hom
            ((Scheme.ΓSpecIso R).inv.hom r) • q.hom m
        have hmap := Scheme.Modules.map_smul M (eqToHom eT) r m
        change M.val.map (eqToHom eT).op (r • m) =
          (X.presheaf.map (eqToHom eT).op).hom r • q.hom m at hmap
        rw [hmap, hqRing] }

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along the spectrum chart does not change the section module
over the corresponding affine open. -/
theorem fromSpecRestrictTopHom_isIso
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (fromSpecRestrictTopHom M hU) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let R := Γ(X, U)
  let j := hU.fromSpec
  have eT : j ''ᵁ (⊤ : (Spec R).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  change Function.Bijective
    (ConcreteCategory.hom (M.presheaf.map (eqToHom eT).op))
  haveI : IsIso (M.presheaf.map (eqToHom eT).op) := inferInstance
  exact ConcreteCategory.bijective_of_isIso _

/-- A stalk over the canonical spectrum chart, regarded as a module over the
coordinate ring of the affine open through the ambient germ map. -/
noncomputable abbrev affineOpenStalkModule
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum.Top Γ(X, U)) :
    Module Γ(X, U)
      (↑(TopCat.Presheaf.stalk M.val.presheaf (hU.fromSpec p)) : Type u) := by
  letI : Module (X.presheaf.stalk (hU.fromSpec p))
      (↑(TopCat.Presheaf.stalk M.val.presheaf (hU.fromSpec p)) : Type u) :=
    presheafStalkModule M.val (hU.fromSpec p)
  have hpU : (hU.fromSpec p : X) ∈ U := by
    change hU.fromSpec p ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self p
  exact Module.compHom _ (X.presheaf.germ U (hU.fromSpec p) hpU).hom

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along the canonical spectrum chart identifies its stalk at a
prime with the ambient stalk, linearly over the affine-open coordinate ring. -/
noncomputable def fromSpecRestrictStalkLinearEquiv
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum.Top Γ(X, U)) :
    let F := (restrictFunctor hU.fromSpec).obj M
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk F.val.presheaf p) : Type u) :=
      moduleSpecStalkModule F p
    letI : Module Γ(X, U)
        (↑(TopCat.Presheaf.stalk M.val.presheaf (hU.fromSpec p)) : Type u) :=
      affineOpenStalkModule M hU p
    (↑(TopCat.Presheaf.stalk F.val.presheaf p) : Type u) ≃ₗ[Γ(X, U)]
      (↑(TopCat.Presheaf.stalk M.val.presheaf (hU.fromSpec p)) : Type u) := by
  let R := Γ(X, U)
  let j := hU.fromSpec
  let F := (restrictFunctor hU.fromSpec).obj M
  have hpU : j p ∈ U := by
    have : j p ∈ Set.range j := Set.mem_range_self p
    rwa [hU.range_fromSpec] at this
  let StF := (↑(TopCat.Presheaf.stalk F.val.presheaf p) : Type u)
  let StM := (↑(TopCat.Presheaf.stalk M.val.presheaf (j p)) : Type u)
  letI : Module R StF := moduleSpecStalkModule F p
  letI : Module (X.presheaf.stalk (j p)) StM :=
    presheafStalkModule M.val (j p)
  letI : Module R StM :=
    Module.compHom _ (X.presheaf.germ U (j p) hpU).hom
  let e : StF ≃+ StM :=
    ((restrictStalkNatIso j p).app M).addCommGroupIsoToAddEquiv
  exact e.toLinearEquiv (fun r z => by
    obtain ⟨V, hpV, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq F.val.presheaf z
    rw [← hs]
    letI : Module Γ(Spec R, V) (F.val.obj (op V) : Type u) :=
      (F.val.obj (op V)).isModule
    change (F.val.obj (op V) : Type u) at s
    let aTop : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv.hom r
    let aV : Γ(Spec R, V) :=
      ((Spec R).presheaf.map (homOfLE le_top).op).hom aTop
    have ha : ((Spec R).presheaf.germ V p hpV).hom aV =
        (((Scheme.ΓSpecIso R).inv ≫
          (Spec R).presheaf.germ ⊤ p trivial).hom r) := by
      change ((Spec R).presheaf.germ V p hpV).hom
          (((Spec R).presheaf.map (homOfLE le_top).op).hom
            ((Scheme.ΓSpecIso R).inv.hom r)) =
        ((Spec R).presheaf.germ ⊤ p trivial).hom
          ((Scheme.ΓSpecIso R).inv.hom r)
      exact TopCat.Presheaf.germ_res_apply
        (Spec R).presheaf (homOfLE le_top) p hpV
          ((Scheme.ΓSpecIso R).inv.hom r)
    change e
        ((((Scheme.ΓSpecIso R).inv ≫
          (Spec R).presheaf.germ ⊤ p trivial).hom r) •
          (TopCat.Presheaf.germ F.val.presheaf V p hpV).hom s) =
      r • e ((TopCat.Presheaf.germ F.val.presheaf V p hpV).hom s)
    rw [← ha]
    erw [← PresheafOfModules.germ_smul F.val p V hpV aV s]
    have hcompat1 := congrArg (fun q => q.hom (aV • s))
      (germ_restrictStalkNatIso_hom_app j p M hpV)
    have hcompat2 := congrArg (fun q => q.hom s)
      (germ_restrictStalkNatIso_hom_app j p M hpV)
    change e ((TopCat.Presheaf.germ F.val.presheaf V p hpV).hom (aV • s)) =
      (M.presheaf.germ (j ''ᵁ V) (j p) (by simpa using hpV)).hom (aV • s)
      at hcompat1
    change e ((TopCat.Presheaf.germ F.val.presheaf V p hpV).hom s) =
      (M.presheaf.germ (j ''ᵁ V) (j p) (by simpa using hpV)).hom s
      at hcompat2
    rw [hcompat1]
    have hsm := smul_restrictAppIso_hom_apply j M V aV s
    change
      (M.presheaf.germ (j ''ᵁ V) (j p) (by simpa using hpV)).hom
          ((restrictAppIso j M V).hom.hom (aV • s)) =
        r • e ((TopCat.Presheaf.germ F.val.presheaf V p hpV).hom s)
    rw [hsm]
    erw [PresheafOfModules.germ_smul M.val (j p) (j ''ᵁ V)
      (by simpa using hpV) ((j.appIso V).inv.hom aV)
      ((restrictAppIso j M V).hom.hom s)]
    rw [hcompat2]
    let c : (X.presheaf.stalk (j p) : Type u) :=
      (X.presheaf.germ U (j p) hpU).hom r
    let ms : StM :=
      (M.presheaf.germ (j ''ᵁ V) (j p) (by simpa using hpV)).hom s
    change _ = c • ms
    have eT : j ''ᵁ (⊤ : (Spec R).Opens) = U :=
      (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
    let hVU : j ''ᵁ V ≤ U :=
      (Scheme.Hom.image_mono j le_top).trans eT.le
    let cV : (X.presheaf.stalk (j p) : Type u) :=
      (X.presheaf.germ (j ''ᵁ V) (j p) (by simpa using hpV)).hom
        ((j.appIso V).inv.hom aV)
    have hc : cV = c := by
      change
        (X.presheaf.germ (j ''ᵁ V) (j p) (by simpa using hpV)).hom
            ((j.appIso V).inv.hom
              (((Spec R).presheaf.map (homOfLE le_top).op).hom
                ((Scheme.ΓSpecIso R).inv.hom r))) =
          (X.presheaf.germ U (j p) hpU).hom r
      rw [fromSpec_restrict_ring_section hU V r]
      exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU)
        (j p) (by simpa using hpV) r
    change cV • _ = c • ms
    rw [hc]
    rfl)

/-- The point of an affine open corresponding to a prime has that same prime
under `IsAffineOpen.primeIdealOf`. -/
lemma primeIdealOf_fromSpec_apply
    {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum.Top Γ(X, U)) (hpU : (hU.fromSpec p : X) ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec p, hpU⟩ = p := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf]

set_option backward.isDefEq.respectTransparency false in
/-- The affine-chart stalk equivalence carries the germ of a transported top
section back to the original germ on the affine open. -/
theorem fromSpecRestrictStalkLinearEquiv_moduleSpecGerm
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum.Top Γ(X, U)) (m : Γ(M, U)) :
    let R := Γ(X, U)
    let j := hU.fromSpec
    let F := (restrictFunctor j).obj M
    let hpU : j p ∈ U := by
      have : j p ∈ Set.range j := Set.mem_range_self p
      rwa [hU.range_fromSpec] at this
    let xU : U := ⟨j p, hpU⟩
    letI : Module R
        (↑(TopCat.Presheaf.stalk F.val.presheaf p) : Type u) :=
      moduleSpecStalkModule F p
    letI : Module R
        (↑(TopCat.Presheaf.stalk M.val.presheaf (j p)) : Type u) :=
      affineOpenStalkModule M hU p
    fromSpecRestrictStalkLinearEquiv M hU p
        (moduleSpecGermLinearMap F p ((fromSpecRestrictTopHom M hU).hom m)) =
      presheafGermLinearMap M.val xU m := by
  let R := Γ(X, U)
  let j := hU.fromSpec
  let F := (restrictFunctor j).obj M
  have hpU : j p ∈ U := by
    have : j p ∈ Set.range j := Set.mem_range_self p
    rwa [hU.range_fromSpec] at this
  let xU : U := ⟨j p, hpU⟩
  letI : Module R
      (↑(TopCat.Presheaf.stalk F.val.presheaf p) : Type u) :=
    moduleSpecStalkModule F p
  letI : Module (X.presheaf.stalk (j p))
      (↑(TopCat.Presheaf.stalk M.val.presheaf (j p)) : Type u) :=
    presheafStalkModule M.val (j p)
  letI : Module R
      (↑(TopCat.Presheaf.stalk M.val.presheaf (j p)) : Type u) :=
    affineOpenStalkModule M hU p
  have eT : j ''ᵁ (⊤ : (Spec R).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  have hcompat := congrArg
    (fun q => q.hom ((M.presheaf.map (eqToHom eT).op).hom m))
    (germ_restrictStalkNatIso_hom_app j p M (by trivial))
  change fromSpecRestrictStalkLinearEquiv M hU p
      ((TopCat.Presheaf.germ F.val.presheaf ⊤ p trivial).hom
        ((M.presheaf.map (eqToHom eT).op).hom m)) =
    (M.presheaf.germ U (j p) hpU).hom m
  change fromSpecRestrictStalkLinearEquiv M hU p
      ((TopCat.Presheaf.germ F.val.presheaf ⊤ p trivial).hom
        ((M.presheaf.map (eqToHom eT).op).hom m)) =
    (M.presheaf.germ (j ''ᵁ ⊤) (j p) (by simp)).hom
      ((M.presheaf.map (eqToHom eT).op).hom m) at hcompat
  rw [hcompat]
  exact TopCat.Presheaf.germ_res_apply M.presheaf (eqToHom eT)
    (j p) (by simp) m

/-- On every affine open, the canonical map from the objectwise tensor of
sections to the sections of the sheaf tensor product is an isomorphism. -/
theorem tensorSectionHom_isIso
    (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (tensorSectionHom A B U) := by
  let R := Γ(X, U)
  let j := hU.fromSpec
  let M := tensorObj A B
  let F := (restrictFunctor j).obj M
  let N := (tensorPresheaf A B).obj (op U)
  let f : N ⟶ moduleSpecΓFunctor.obj F :=
    tensorSectionHom A B U ≫ fromSpecRestrictTopHom M hU
  have hf : IsIso f := by
    apply isIso_moduleSpec_hom_of_isLocalizedModule_stalk F N f
    intro p
    letI : Module R
        (↑(TopCat.Presheaf.stalk F.val.presheaf p) : Type u) :=
      moduleSpecStalkModule F p
    have hpU : j p ∈ U := by
      have : j p ∈ Set.range j := Set.mem_range_self p
      rwa [hU.range_fromSpec] at this
    let xU : U := ⟨j p, hpU⟩
    letI : Module (X.presheaf.stalk (j p))
        (↑(TopCat.Presheaf.stalk M.val.presheaf (j p)) : Type u) :=
      presheafStalkModule M.val (j p)
    letI : Module R
        (↑(TopCat.Presheaf.stalk M.val.presheaf (j p)) : Type u) :=
      affineOpenStalkModule M hU p
    let e := fromSpecRestrictStalkLinearEquiv M hU p
    let g := (moduleSpecGermLinearMap F p).comp f.hom
    let gX := (presheafGermLinearMap M.val xU).comp
      (tensorSectionHom A B U).hom
    have hloc : IsLocalizedModule
        (hU.primeIdealOf xU).asIdeal.primeCompl gX :=
      isLocalizedModule_tensorSectionHom_stalk A B hU xU
    have hp : hU.primeIdealOf xU = p :=
      primeIdealOf_fromSpec_apply hU p hpU
    rw [hp] at hloc
    have heq : e.toLinearMap.comp g = gX := by
      apply LinearMap.ext
      intro m
      change fromSpecRestrictStalkLinearEquiv M hU p
          (moduleSpecGermLinearMap F p
            ((fromSpecRestrictTopHom M hU).hom
              ((tensorSectionHom A B U).hom m))) =
        presheafGermLinearMap M.val xU
          ((tensorSectionHom A B U).hom m)
      exact fromSpecRestrictStalkLinearEquiv_moduleSpecGerm M hU p _
    letI : IsLocalizedModule p.asIdeal.primeCompl gX := hloc
    have htransport : IsLocalizedModule p.asIdeal.primeCompl
        (e.symm.toLinearMap.comp gX) :=
      IsLocalizedModule.of_linearEquiv p.asIdeal.primeCompl gX e.symm
    have hcancel : e.symm.toLinearMap.comp gX =
        (moduleSpecGermLinearMap F p).comp f.hom := by
      change e.symm.toLinearMap.comp gX = g
      rw [← heq]
      apply LinearMap.ext
      intro m
      simp
    exact hcancel ▸ htransport
  haveI : IsIso (fromSpecRestrictTopHom M hU) :=
    fromSpecRestrictTopHom_isIso M hU
  haveI : IsIso
      (tensorSectionHom A B U ≫ fromSpecRestrictTopHom M hU) := by
    change IsIso f
    exact hf
  exact IsIso.of_isIso_comp_right
    (tensorSectionHom A B U) (fromSpecRestrictTopHom M hU)

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf tensor product of two quasi-coherent modules is quasi-coherent. -/
theorem tensorObj_isQuasicoherent
    (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent] :
    (tensorObj A B).IsQuasicoherent := by
  apply isQuasicoherent_of_isLocalizedModule_basicOpen
  intro U hU f
  let i : X.basicOpen f ⟶ U := homOfLE (X.basicOpen_le f)
  letI : Module Γ(X, U)
      ((tensorPresheaf A B).obj (op (X.basicOpen f)) : Type u) :=
    Module.compHom _ (X.presheaf.map i.op).hom
  letI : Module Γ(X, U)
      (Γ(tensorObj A B, X.basicOpen f) : Type u) :=
    Module.compHom _ (X.presheaf.map i.op).hom
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f)
      (Γ(tensorObj A B, X.basicOpen f) : Type u) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let gP : ((tensorPresheaf A B).obj (op U) : Type u) →ₗ[Γ(X, U)]
      ((tensorPresheaf A B).obj (op (X.basicOpen f)) : Type u) :=
    { toFun := fun x => (tensorPresheaf A B).map i.op x
      map_add' := map_add _
      map_smul' := fun r x => PresheafOfModules.map_smul
        (tensorPresheaf A B) i.op r x }
  have hlocP : IsLocalizedModule (Submonoid.powers f) gP :=
    isLocalizedModule_tensorPresheaf_basicOpen A B hU f
  haveI : IsIso (tensorSectionHom A B U) := tensorSectionHom_isIso A B hU
  haveI : IsIso (tensorSectionHom A B (X.basicOpen f)) :=
    tensorSectionHom_isIso A B (hU.basicOpen f)
  let eU : ((tensorPresheaf A B).obj (op U) : Type u) ≃ₗ[Γ(X, U)]
      (Γ(tensorObj A B, U) : Type u) :=
    (asIso (tensorSectionHom A B U)).toLinearEquiv
  let eD_S := (asIso (tensorSectionHom A B (X.basicOpen f))).toLinearEquiv
  let eD : ((tensorPresheaf A B).obj (op (X.basicOpen f)) : Type u) ≃ₗ[Γ(X, U)]
      (Γ(tensorObj A B, X.basicOpen f) : Type u) :=
    { eD_S.toEquiv with
      map_add' := eD_S.map_add
      map_smul' := fun r x => by
        change eD_S ((X.presheaf.map i.op).hom r • x) =
          (X.presheaf.map i.op).hom r • eD_S x
        exact eD_S.map_smul ((X.presheaf.map i.op).hom r) x }
  letI : IsLocalizedModule (Submonoid.powers f) gP := hlocP
  have htarget : IsLocalizedModule (Submonoid.powers f)
      (eD.toLinearMap.comp gP) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers f) gP eD
  letI : IsLocalizedModule (Submonoid.powers f)
      (eD.toLinearMap.comp gP) := htarget
  have hboth : IsLocalizedModule (Submonoid.powers f)
      ((eD.toLinearMap.comp gP).comp eU.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
      (eD.toLinearMap.comp gP) eU.symm
  have heq : (eD.toLinearMap.comp gP).comp eU.symm.toLinearMap =
      restrictBasicOpenₗ (tensorObj A B) f := by
    apply LinearMap.ext
    intro x
    let y := eU.symm x
    change eD (gP y) = restrictBasicOpenₗ (tensorObj A B) f x
    have hnat := tensorSectionHom_naturality_apply A B i.op y
    change eD (gP y) = restrictBasicOpenₗ (tensorObj A B) f (eU y) at hnat
    exact hnat.trans (congrArg (restrictBasicOpenₗ (tensorObj A B) f)
      (eU.apply_symm_apply x))
  exact heq ▸ hboth

end AlgebraicGeometry.Scheme.Modules
