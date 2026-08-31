/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationBase

/-!
# Sub-brick A — Leg (Layer 0): WPCIproj infrastructure, `interLegHom`, `interLegHom_interProj`

Wide-pullback/coproduct distributivity helpers (`section WPCIproj`),
generic reassociation lemmas (`entry_chain`, `glue_chain`), the face morphism
`interLegHom` between intersection-open legs, and `interLegHom_interProj`.

The backbone and restriction-chain results live in the split files
`CechSectionIdentificationLegMid1`, `CechSectionIdentificationLegMid2`, and
`CechSectionIdentificationLegTop`. Depends on `CechSectionIdentificationBase`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-- Precomposition preserves equality of morphisms. Kept opaque so large categorical
prefixes do not get duplicated in downstream proof terms. -/
private lemma precomp_eq_of_eq {C : Type*} [Category C] {W Y Z : C}
    (e : W ⟶ Y) {f g : Y ⟶ Z} (h : f = g) : e ≫ f = e ≫ g :=
  congrArg (fun w => e ≫ w) h

/-! ### The `coreIso_comm` chain (`lem:coreIso_comm_leg` → `lem:coreIso_comm_coface` →
`lem:coreIso_comm_sum` → `lem:coreIso_comm`), built bottom-up per the iter-072 effort-break. -/

/-- Application of a finite sum of `Ab`-morphisms distributes over the sum.  (Local copy of
the `CechAcyclic` private helper `ab_hom_finsetSum_apply`.) -/
lemma abHom_finsetSum_apply {A B : Ab.{u}} {κ : Type*}
    (s : Finset κ) (f : κ → (A ⟶ B)) (t : ToType A) :
    ConcreteCategory.hom (∑ i ∈ s, f i) t = ∑ i ∈ s, ConcreteCategory.hom (f i) t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

/-! ### Geometric seam for `coreIso_comm_leg`

The per-leg coface naturality is proved by unwinding `coreIso_objIso` to the push–pull
map of the **backbone inclusion** `backboneIncl 𝒰 p τ : Over.mk j_τ ⟶ Y_p` (the morphism
produced by `pushPull_sigma_iso_π`), and then computing geometrically:

1. the backbone inclusion followed by the `l`-th wide-pullback projection is the
   canonical component map `interProj` (`backboneIncl_proj` — the Stub-1 unwinding);
2. hence the nerve coface `δ^nerve_k` restricts on the `σ'`-summand to the open
   inclusion `interLegHom : U_{σ'} ⊆ U_{σ'∘δᵏ}` (`backboneIncl_nerveδ`, by `hom_ext`
   through the projections);
3. the evaluated push–pull of that open inclusion acts on the identified leg sections
   as the plain `F`-restriction (`pushPull_interLegHom_sections`). -/

/-- The `τ`-summand inclusion `Over.mk j_τ ⟶ Y_p` of the degree-`p` Čech backbone:
the coproduct inclusion composed with the two backbone identifications read backwards.
By `pushPull_sigma_iso_π`, its push–pull map is the `τ`-projection of
`pushPull_sigma_iso`. -/
noncomputable def backboneIncl (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (p : ℕ)
    (τ : Fin (p + 1) → 𝒰.I₀) :
    Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) ⟶
      (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p)) :=
  coprodOverIncl (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ ≫
    (overSigmaDescIso (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom)).inv ≫
    (cechBackbone_left_sigma 𝒰 p).inv

/-- `pushPull_sigma_iso_π`, rephrased through `backboneIncl`. -/
lemma pushPull_sigma_iso_π_incl (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (p : ℕ)
    (τ : Fin (p + 1) → 𝒰.I₀) :
    (pushPull_sigma_iso 𝒰 F p).hom ≫
        Pi.π (fun σ : Fin (p + 1) → 𝒰.I₀ =>
          pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) τ =
      pushPullMap F (backboneIncl 𝒰 p τ) :=
  pushPull_sigma_iso_π 𝒰 F p τ

/-- The over-level `l`-th wide-pullback projection of the degree-`p` backbone, landing
in the cover-arrow object `Over.mk (Sigma.desc 𝒰.f)`. -/
noncomputable def backboneProj (𝒰 : X.OpenCover) (p : ℕ) (l : Fin (p + 1)) :
    (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p)) ⟶
      Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (WidePullback.π (fun _ : Fin (p + 1) => Sigma.desc 𝒰.f) l)
    (WidePullback.π_arrow _ l)

/-- Morphisms into the degree-`p` backbone are determined by the `p + 1` over-level
wide-pullback projections: the backbone is the slice product of cover-arrow copies
(`widePullback_overX_isLimit`). -/
lemma backbone_hom_ext (𝒰 : X.OpenCover) (p : ℕ) {A : Over X}
    {u v : A ⟶ (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p))}
    (h : ∀ l : Fin (p + 1), u ≫ backboneProj 𝒰 p l = v ≫ backboneProj 𝒰 p l) : u = v := by
  apply Over.OverMorphism.ext
  apply WidePullback.hom_ext (fun _ : Fin (p + 1) => Sigma.desc 𝒰.f)
  · intro l
    exact congrArg CommaMorphism.left (h l)
  · exact (Over.w u).trans (Over.w v).symm

/-- The Čech-nerve simplicial face intertwines the backbone projections: the geometric
coface followed by the `l`-th projection is the `δᵏ l`-th projection. -/
lemma nerveδ_backboneProj (𝒰 : X.OpenCover) (p : ℕ) (k : Fin (p + 2)) (l : Fin (p + 1)) :
    (coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op) ≫ backboneProj 𝒰 p l =
      backboneProj 𝒰 (p + 1) ((SimplexCategory.δ k).toOrderHom l) := by
  apply Over.OverMorphism.ext
  exact WidePullback.lift_π (fun _ : Fin (p + 1) => Sigma.desc 𝒰.f) _ _ _ l

/-- The evaluated Čech-nerve coface is the push–pull map of the geometric backbone
simplicial face (definitional unwinding of `CechNerve`). -/
lemma cechNerve_drop_δ (𝒰 : X.OpenCover) (F : X.Modules) {p : ℕ} (k : Fin (p + 2)) :
    (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k =
      pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op)) := by
  change (cechNerveCosimplicial 𝒰 F).map (SimplexCategory.δ k) = _
  rfl

/-- The canonical lift of the intersection-open inclusion `U_τ ↪ X` against the
`τ l`-th cover member (an open immersion). -/
noncomputable def coverInterToMember (𝒰 : X.OpenCover) {p : ℕ}
    (τ : Fin (p + 1) → 𝒰.I₀) (l : Fin (p + 1)) :
    Scheme.Opens.toScheme (coverInterOpen 𝒰 τ) ⟶ 𝒰.X (τ l) :=
  IsOpenImmersion.lift (𝒰.f (τ l)) (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) (by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact SetLike.coe_subset_coe.mpr (iInf_le (fun j => coverOpen 𝒰 (τ j)) l))

/-- Factorization property of `coverInterToMember`. -/
lemma coverInterToMember_fac (𝒰 : X.OpenCover) {p : ℕ} (τ : Fin (p + 1) → 𝒰.I₀)
    (l : Fin (p + 1)) :
    coverInterToMember 𝒰 τ l ≫ 𝒰.f (τ l) = Scheme.Opens.ι (coverInterOpen 𝒰 τ) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The canonical `l`-th component of the `τ`-leg in the cover-arrow object: lift to the
`τ l`-th member, then include into the coproduct. -/
noncomputable def interProj (𝒰 : X.OpenCover) {p : ℕ} (τ : Fin (p + 1) → 𝒰.I₀)
    (l : Fin (p + 1)) :
    Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) ⟶ Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (coverInterToMember 𝒰 τ l ≫ Sigma.ι 𝒰.X (τ l)) (by
    change (coverInterToMember 𝒰 τ l ≫ Sigma.ι 𝒰.X (τ l)) ≫ Sigma.desc 𝒰.f =
      Scheme.Opens.ι (coverInterOpen 𝒰 τ)
    rw [Category.assoc, Sigma.ι_desc]
    exact coverInterToMember_fac 𝒰 τ l)

/-- Mono-target rigidity in the slice: two over-`X` morphisms into `Over.mk g` with `g`
a monomorphism agree.  (Used to absorb the reindexing isos of the Stub-1 chain.) -/
lemma over_hom_ext_mono {A : Over X} {B : Scheme.{u}} {g : B ⟶ X} [Mono g]
    (u v : A ⟶ Over.mk g) : u = v :=
  Over.OverMorphism.ext ((cancel_mono g).mp ((Over.w u).trans (Over.w v).symm))

/-! ### The Stub-1 unwinding: projections of the `widePullback_coproduct_iso` inclusions.

Abstract lemmas (any finitary pre-extensive category): the composite of a `σ`-summand
inclusion with the inverse of the distributivity iso `widePullback_coproduct_iso` and an
over-level wide-pullback projection is the canonical `l`-th factor projection followed by
the `σ l`-th descent inclusion.  This is the geometric content of `backboneIncl_proj`. -/

section WPCIproj

open CategoryTheory.FinitaryPreExtensive

variable {C : Type*} [Category C]

/-- Head projection of the inverse of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_inv_π_zero [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C) :
    (prodFinSuccIso W).inv ≫ Pi.π W 0 = Limits.prod.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk (0 : Fin (n + 1)))

/-- Tail projections of the inverse of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_inv_π_succ [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C)
    (i : Fin n) :
    (prodFinSuccIso W).inv ≫ Pi.π W i.succ =
      Limits.prod.snd ≫ Pi.π (fun j : Fin n => W j.succ) i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk i.succ)

/-- Head projection of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_hom_fst [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C) :
    (prodFinSuccIso W).hom ≫ Limits.prod.fst = Pi.π W 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk (0 : Fin (n + 1)))

/-- Tail projections of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_hom_snd_π [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C)
    (i : Fin n) :
    (prodFinSuccIso W).hom ≫ Limits.prod.snd ≫ Pi.π (fun j : Fin n => W j.succ) i =
      Pi.π W i.succ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i.succ)

/-- ι-compatibility of a `Sigma.mapIso` inverse. -/
@[reassoc]
lemma ι_sigmaMapIso_inv {β : Type*} {f g : β → C} [HasCoproductsOfShape β C]
    (w : ∀ b, f b ≅ g b) (b : β) :
    Limits.Sigma.ι g b ≫ (Limits.Sigma.mapIso w).inv = (w b).inv ≫ Limits.Sigma.ι f b := by
  have h := ι_colimMap (F := Discrete.functor g) (G := Discrete.functor f)
    (Discrete.natIso (F := Discrete.functor f) (G := Discrete.functor g)
      (fun j => w j.as)).inv ⟨b⟩
  exact h

/-- ι-compatibility of the nested-coproduct flatten/reindex
`coproduct_fibrePower_reindex`. -/
@[reassoc]
private lemma ι_fibrePower_reindex_inv {ι : Type} [Finite ι] [HasFiniteCoproducts C]
    {p : ℕ} (F : (Fin (p + 2) → ι) → C) (i : ι) (t : Fin (p + 1) → ι) :
    Limits.Sigma.ι F (Fin.cons i t) ≫ (coproduct_fibrePower_reindex p F).inv =
      Limits.Sigma.ι (fun τ : Fin (p + 1) → ι => F (Fin.cons i τ)) t ≫
        Limits.Sigma.ι (fun i : ι => ∐ fun τ : Fin (p + 1) → ι => F (Fin.cons i τ)) i := by
  simp only [coproduct_fibrePower_reindex, Iso.trans_inv, Sigma.whiskerEquiv,
    Iso.refl_hom, Category.comp_id, sigmaSigmaIso_inv, Equiv.symm_trans_apply]
  refine Eq.trans (Limits.Sigma.ι_comp_map'_assoc _ _ _ _) ?_
  exact Eq.trans (Category.id_comp _)
    (Limits.Sigma.ι_desc _ ((⟨i, t⟩ : Σ _ : ι, Fin (p + 1) → ι)))

/-- ι-compatibility of a `Sigma.whiskerEquiv` inverse (the reindex layers of the
Stub-1 chain). -/
@[reassoc]
private lemma ι_whiskerEquiv_inv {β γ : Type*} {f : β → C} {g : γ → C}
    [HasCoproduct f] [HasCoproduct g] (e : β ≃ γ) (w : ∀ b, g (e b) ≅ f b) (c : γ) :
    Limits.Sigma.ι g c ≫ (Sigma.whiskerEquiv e w).inv =
      (eqToHom (by rw [e.apply_symm_apply]) ≫ (w (e.symm c)).hom) ≫
        Limits.Sigma.ι f (e.symm c) :=
  Limits.Sigma.ι_comp_map' _ _ _

variable [HasPullbacks C] [FinitaryPreExtensive C] {ι : Type} [Finite ι]
  [HasFiniteCoproducts C]

/-- `coprodFirst_distrib` is compatible with the second projection (counterpart of the
recorded `cf_hom_fst`). -/
private lemma cf_hom_snd {S : C} (B : C) (b : B ⟶ S) {Y : ι → C} (g : (i : ι) → Y i ⟶ S) :
    (coprodFirst_distrib B b g).hom ≫ pullback.snd (Limits.Sigma.desc g) b =
      Limits.Sigma.desc (fun i => pullback.snd (g i) b) := by
  rw [coprodFirst_distrib]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [pullbackSymmetry_hom_comp_snd, pcd_hom_fst]
  refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
    Limits.Sigma.ι_desc, pullbackSymmetry_hom_comp_fst]

/-- ι-compatibility of `coprodFirst_distrib`: the `i`-th coproduct inclusion of the
distributed pullbacks corresponds to the canonical pullback comparison along `Sigma.ι`. -/
private lemma ι_cf_hom {S : C} (B : C) (b : B ⟶ S) {Y : ι → C} (g : (i : ι) → Y i ⟶ S)
    (i : ι) :
    Limits.Sigma.ι (fun i => pullback (g i) b) i ≫ (coprodFirst_distrib B b g).hom =
      pullback.map (g i) b (Limits.Sigma.desc g) b (Limits.Sigma.ι Y i) (𝟙 B) (𝟙 S)
        (by rw [Category.comp_id, Limits.Sigma.ι_desc]) (by simp) := by
  apply pullback.hom_ext
  · rw [Category.assoc, cf_hom_fst, Limits.Sigma.ι_desc, pullback.lift_fst]
  · rw [Category.assoc, cf_hom_snd, Limits.Sigma.ι_desc, pullback.lift_snd, Category.comp_id]

omit [HasPullbacks C] in
/-- The slice structure map of a coproduct, through the coproduct comparison of
`Over.forget` (local copy of the `CechSectionIdentificationBase` private helper). -/
private lemma overSigmaHomEq {S : C} (A : ι → Over S) :
    (∐ A).hom = (PreservesCoproduct.iso (Over.forget S) A).hom ≫
      Limits.Sigma.desc (fun i => (A i).hom) := by
  haveI : HasColimit (Discrete.functor A ⋙ Over.forget S) :=
    hasColimit_of_iso (F := Discrete.functor (fun i => (A i).left))
      (Discrete.natIso (fun i => Iso.refl _))
  refine (PreservesCoproduct.iso (Over.forget S) A).inv_comp_eq.mp ?_
  rw [PreservesCoproduct.inv_hom]
  refine Limits.Sigma.hom_ext _ _ (fun i => ?_)
  rw [ι_comp_sigmaComparison_assoc]
  change (Limits.Sigma.ι A i).left ≫ (∐ A).hom = _
  rw [Limits.Sigma.ι_desc]
  exact Over.w (Limits.Sigma.ι A i)

/-- ι-compatibility of the slice distributivity `overProd_coproduct_distrib`: the `i`-th
inclusion of the distributed products corresponds to `Sigma.ι ⨯ 𝟙`. -/
@[reassoc]
private lemma ι_overProd_distrib_inv {S : C} [HasBinaryProducts (Over S)]
    (A : ι → Over S) (B : Over S) (i : ι) :
    Limits.Sigma.ι (fun i => A i ⨯ B) i ≫ (overProd_coproduct_distrib A B).inv =
      Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B) := by
  rw [Iso.comp_inv_eq]
  refine Eq.symm ?_
  apply Over.OverMorphism.ext
  -- step 1: the slice `prod.map` corresponds to the `pullback.map` of the `ι`-square.
  have h1 : (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
        (Over.prodLeftIsoPullback (∐ A) B).hom =
      (Over.prodLeftIsoPullback (A i) B).hom ≫
        pullback.map (A i).hom B.hom (∐ A).hom B.hom (Limits.Sigma.ι A i).left
          (𝟙 B.left) (𝟙 S) (by rw [Category.comp_id]; exact (Over.w _).symm) (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, Category.assoc,
        pullback.lift_fst, ← Over.comp_left, Limits.prod.map_fst, Over.comp_left,
        ← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, Category.assoc,
        pullback.lift_snd, Category.comp_id, ← Over.comp_left, Limits.prod.map_snd,
        Category.comp_id, Over.prodLeftIsoPullback_hom_snd]
  -- step 2: the coproduct comparison of `Over.forget` on inclusions.
  have h0 : Limits.Sigma.ι (fun j => (A j).left) i ≫
        (PreservesCoproduct.iso (Over.forget S) A).inv = (Limits.Sigma.ι A i).left := by
    rw [PreservesCoproduct.inv_hom]
    exact ι_comp_sigmaComparison (Over.forget S) A i
  have hpA : (Limits.Sigma.ι A i).left ≫
        (PreservesCoproduct.iso (Over.forget S) A).hom =
      Limits.Sigma.ι (fun j => (A j).left) i := by
    refine Eq.trans (congrArg
      (fun w => w ≫ (PreservesCoproduct.iso (Over.forget S) A).hom) h0.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun w => Limits.Sigma.ι (fun j => (A j).left) i ≫ w)
      ((PreservesCoproduct.iso (Over.forget S) A).inv_hom_id)) ?_
    exact Category.comp_id _
  -- the two stacked pullback comparisons compose to the `Sigma.ι`-square
  have h2 : pullback.map (A i).hom B.hom (∐ A).hom B.hom (Limits.Sigma.ι A i).left
        (𝟙 B.left) (𝟙 S) (by rw [Category.comp_id]; exact (Over.w _).symm) (by simp) ≫
      pullback.map (∐ A).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
        (PreservesCoproduct.iso (Over.forget S) A).hom (𝟙 B.left) (𝟙 S)
        (by rw [Category.comp_id]; exact overSigmaHomEq A) (by simp) =
      pullback.map (A i).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
        (Limits.Sigma.ι (fun j => (A j).left) i) (𝟙 B.left) (𝟙 S)
        (by rw [Category.comp_id, Limits.Sigma.ι_desc]) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact congrArg (fun w => pullback.fst (A i).hom B.hom ≫ w) hpA
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  -- step 3: the fused comparison is the inclusion of the distributed pullback factor.
  have h3 : pullback.map (A i).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
        (Limits.Sigma.ι (fun j => (A j).left) i) (𝟙 B.left) (𝟙 S)
        (by rw [Category.comp_id, Limits.Sigma.ι_desc]) (by simp) ≫
      (coprodFirst_distrib B.left B.hom fun j => (A j).hom).inv =
      Limits.Sigma.ι (fun j => pullback (A j).hom B.hom) i := by
    rw [Iso.comp_inv_eq]
    exact (ι_cf_hom B.left B.hom (fun j => (A j).hom) i).symm
  -- step 4: collapse the coproduct comparison of `Over.forget` on the target.
  have h4 : Limits.Sigma.ι (fun j => (A j ⨯ B).left) i ≫
        (PreservesCoproduct.iso (Over.forget S) (fun i => A i ⨯ B)).inv =
      (Limits.Sigma.ι (fun i => A i ⨯ B) i).left := by
    rw [PreservesCoproduct.inv_hom]
    exact ι_comp_sigmaComparison (Over.forget S) (fun i => A i ⨯ B) i
  have c1 : (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
        ((overProd_coproduct_distrib A B).hom).left =
      (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
          (Over.prodLeftIsoPullback (∐ A) B).hom ≫
          pullback.map (∐ A).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
            (PreservesCoproduct.iso (Over.forget S) A).hom (𝟙 B.left) (𝟙 S)
            (by rw [Category.comp_id]; exact overSigmaHomEq A) (by simp) ≫
          (coprodFirst_distrib B.left B.hom fun j => (A j).hom).inv ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv := rfl
  have c2 : (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
          (Over.prodLeftIsoPullback (∐ A) B).hom ≫
          pullback.map (∐ A).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
            (PreservesCoproduct.iso (Over.forget S) A).hom (𝟙 B.left) (𝟙 S)
            (by rw [Category.comp_id]; exact overSigmaHomEq A) (by simp) ≫
          (coprodFirst_distrib B.left B.hom fun j => (A j).hom).inv ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv =
      (Over.prodLeftIsoPullback (A i) B).hom ≫
          Limits.Sigma.ι (fun j => pullback (A j).hom B.hom) i ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv := by
    rw [← Category.assoc, h1]
    simp only [Category.assoc]
    rw [reassoc_of% h2, reassoc_of% h3]
  have c3 : (Over.prodLeftIsoPullback (A i) B).hom ≫
          Limits.Sigma.ι (fun j => pullback (A j).hom B.hom) i ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv =
      Limits.Sigma.ι (fun j => (A j ⨯ B).left) i ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv := by
    rw [reassoc_of% (Limits.Sigma.ι_map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) i),
      Iso.hom_inv_id_assoc]
  exact c1.trans (c2.trans (c3.trans h4))

/-- ι-compatibility of the right-handed slice distributivity. -/
@[reassoc]
private lemma ι_overProd_distrib_right_inv {S : C} [HasBinaryProducts (Over S)]
    (A : Over S) (Y : ι → Over S) (i : ι) :
    Limits.Sigma.ι (fun i => A ⨯ Y i) i ≫ (overProd_coproduct_distrib_right A Y).inv =
      Limits.prod.map (𝟙 A) (Limits.Sigma.ι Y i) := by
  rw [overProd_coproduct_distrib_right]
  simp only [Iso.trans_inv, ← Category.assoc]
  rw [ι_sigmaMapIso_inv (fun i => Limits.prod.braiding (Y i) A) i]
  simp only [Category.assoc]
  rw [ι_overProd_distrib_inv_assoc (C := C) (S := S) Y A i]
  -- residual braiding algebra:
  -- `(br (Y i) A).inv ≫ prod.map ι 𝟙 ≫ (br A (∐Y)).inv = prod.map 𝟙 ι`
  refine (Iso.inv_comp_eq _).mpr ?_
  refine (Iso.comp_inv_eq _).mpr ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine Eq.trans (congrArg (fun w => (Limits.prod.braiding (Y i) A).hom ≫ w)
    (braid_natural (𝟙 A) (Limits.Sigma.ι Y i))) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun w => w ≫ Limits.prod.map (Limits.Sigma.ι Y i) (𝟙 A))
      (Limits.prod.symmetry (Y i) A)).trans (Category.id_comp _))

variable {S : C} {Z : ι → C} [HasFiniteWidePullbacks C]
  [HasFiniteProducts (Over S)] [HasFiniteCoproducts (Over S)]

/-- The over-level `l`-th wide-pullback projection of the constant-`Sigma.desc` fibre
power. -/
noncomputable def overWPproj (f : (i : ι) → Z i ⟶ S) (m : ℕ) (l : Fin m) :
    Over.mk (WidePullback.base (fun _ : Fin m => Limits.Sigma.desc f)) ⟶
      Over.mk (Limits.Sigma.desc f) :=
  Over.homMk (WidePullback.π (fun _ : Fin m => Limits.Sigma.desc f) l)
    (WidePullback.π_arrow _ l)

/-- The `i`-th descent inclusion. -/
noncomputable def overDescIncl (f : (i : ι) → Z i ⟶ S) (i : ι) :
    Over.mk (f i) ⟶ Over.mk (Limits.Sigma.desc f) :=
  Over.homMk (Limits.Sigma.ι Z i) (Limits.Sigma.ι_desc f i)

omit [HasPullbacks C] [FinitaryPreExtensive C] [HasFiniteWidePullbacks C]
  [HasFiniteProducts (Over S)] [HasFiniteCoproducts (Over S)] in
/-- The descent iso `overSigmaDescIso` sends coproduct inclusions to `overDescIncl`. -/
@[reassoc]
private lemma ι_overSigmaDescIso_hom (f : (i : ι) → Z i ⟶ S) (i : ι) :
    Limits.Sigma.ι (fun i => Over.mk (f i)) i ≫ (overSigmaDescIso f).hom =
      overDescIncl f i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
    (overSigmaDescIsColimit f) (Discrete.mk i)

omit [HasPullbacks C] [FinitaryPreExtensive C] [HasFiniteCoproducts (Over S)] in
/-- Inverse projections of the slice-product identification of the fibre power. -/
@[reassoc]
private lemma wpEqProd_inv_overWPproj (f : (i : ι) → Z i ⟶ S) (m : ℕ) (l : Fin m) :
    (widePullback_overX_eq_prod (fun _ : Fin m => Limits.Sigma.desc f)).inv ≫
      overWPproj f m l = Pi.π (fun _ : Fin m => Over.mk (Limits.Sigma.desc f)) l :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk l)

omit [HasPullbacks C] [FinitaryPreExtensive C] [HasFiniteCoproducts (Over S)] in
/-- Forward projections of the slice-product identification of the fibre power. -/
@[reassoc]
private lemma wpEqProd_hom_π (f : (i : ι) → Z i ⟶ S) (m : ℕ) (l : Fin m) :
    (widePullback_overX_eq_prod (fun _ : Fin m => Limits.Sigma.desc f)).hom ≫
      Pi.π (fun _ : Fin m => Over.mk (Limits.Sigma.desc f)) l = overWPproj f m l :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk l)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The successor case unfolds seven distributivity isos; its nested fibre powers exceed
-- the default kernel reduction budget.
/-- **Inclusion/projection characterization of the wide-fibre-power distributivity**
(the abstract Stub-1 unwinding): the `σ`-summand inclusion composed with the inverse of
`widePullback_coproduct_iso` and the `l`-th over-level wide-pullback projection is the
`l`-th factor projection followed by the `σ l`-th descent inclusion. -/
private lemma ι_wpci_inv_overWPproj (f : (i : ι) → Z i ⟶ S) (p : ℕ) :
    ∀ (σ : Fin (p + 1) → ι) (l : Fin (p + 1)),
    Limits.Sigma.ι (fun σ' : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (σ' k))) σ ≫
        (widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l =
      Pi.π (fun k => Over.mk (f (σ k))) l ≫ overDescIncl f (σ l) := by
  induction p with
  | zero =>
    intro σ l
    obtain rfl : l = 0 := Subsingleton.elim (α := Fin 1) l 0
    obtain ⟨i0, rfl⟩ : ∃ i0, σ = fun _ => i0 :=
      ⟨σ 0, funext fun j => congrArg σ (Subsingleton.elim (α := Fin 1) j 0)⟩
    simp only [widePullback_coproduct_iso, widePullback_coproduct_iso_zero, Iso.trans_inv,
      Iso.symm_inv, Category.assoc, Sigma.whiskerEquiv, Limits.Sigma.ι_comp_map'_assoc]
    rw [wpEqProd_inv_overWPproj]
    have hb := IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit (Discrete.functor (fun _ : Fin 1 => Over.mk (Limits.Sigma.desc f))))
      (limitConeOfUnique (fun _ : Fin 1 => Over.mk (Limits.Sigma.desc f))).isLimit
      (Discrete.mk (0 : Fin 1))
    refine Eq.trans (Category.id_comp _) ?_
    refine Eq.trans (congrArg (fun w => (productUniqueIso fun k : Fin 1 =>
        Over.mk (f ((Equiv.funUnique (Fin 1) ι).symm
          ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) k))).hom ≫ w)
      ((reassoc_of% (ι_overSigmaDescIso_hom f
        ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0))) _)) ?_
    refine Eq.trans (congrArg (fun w => (productUniqueIso fun k : Fin 1 =>
        Over.mk (f ((Equiv.funUnique (Fin 1) ι).symm
          ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) k))).hom ≫
      overDescIncl f ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) ≫ w) hb) ?_
    exact Eq.trans (congrArg (fun w => (productUniqueIso fun k : Fin 1 =>
        Over.mk (f ((Equiv.funUnique (Fin 1) ι).symm
          ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) k))).hom ≫ w)
      (Category.comp_id _)) rfl
  | succ p ih =>
    intro σ l
    obtain ⟨i, t, rfl⟩ : ∃ i t, σ = Fin.cons i t :=
      ⟨σ 0, Fin.tail σ, (Fin.cons_self_tail σ).symm⟩
    simp only [widePullback_coproduct_iso, Iso.trans_inv, Category.assoc]
    rw [reassoc_of% (ι_fibrePower_reindex_inv
      (fun σ' : Fin (p + 2) → ι => ∏ᶜ fun k => Over.mk (f (σ' k))) i t)]
    have he7 := ι_sigmaMapIso_inv (β := ι)
      (f := fun j : ι => ∐ fun τ : Fin (p + 1) → ι =>
        Over.mk (f (Fin.cons (α := fun _ => ι) j τ 0)) ⨯
          ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k.succ)))
      (g := fun j : ι => ∐ fun τ : Fin (p + 1) → ι =>
        ∏ᶜ fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k)))
      (fun j : ι => Limits.Sigma.mapIso
        (f := fun τ : Fin (p + 1) → ι =>
          Over.mk (f (Fin.cons (α := fun _ => ι) j τ 0)) ⨯
            ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k.succ)))
        (g := fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k)))
        (fun τ : Fin (p + 1) → ι =>
          (prodFinSuccIso (fun k : Fin (p + 2) =>
            Over.mk (f (Fin.cons (α := fun _ => ι) j τ k)))).symm)) i
    refine Eq.trans (congrArg (fun w => Limits.Sigma.ι
      (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i τ k))) t ≫ w)
      ((reassoc_of% he7) _)) ?_
    have he7' := ι_sigmaMapIso_inv (β := Fin (p + 1) → ι)
      (f := fun τ : Fin (p + 1) → ι =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i τ 0)) ⨯
          ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k.succ)))
      (g := fun τ : Fin (p + 1) → ι =>
        ∏ᶜ fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k)))
      (fun τ : Fin (p + 1) → ι =>
        (prodFinSuccIso (fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i τ k)))).symm) t
    refine Eq.trans ((reassoc_of% he7') _) ?_
    have hA5 := ι_sigmaMapIso_inv (fun j : ι =>
      overProd_coproduct_distrib_right (Over.mk (f j))
        (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k)))) i
    refine Eq.trans (congrArg (fun w =>
      (prodFinSuccIso fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
      Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i τ 0)) ⨯
          ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k.succ))) t ≫ w)
      ((reassoc_of% hA5) _)) ?_
    refine Eq.trans (congrArg (fun w =>
      (prodFinSuccIso fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
      ((reassoc_of% (ι_overProd_distrib_right_inv (Over.mk (f i))
        (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) t)) _)) ?_
    refine Eq.trans (congrArg (fun w =>
      (prodFinSuccIso fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
      Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
        ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫ w)
      ((reassoc_of% (ι_overProd_distrib_inv (fun j : ι => Over.mk (f j))
        (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) i)) _)) ?_
    induction l using Fin.cases with
    | zero =>
      have htail : (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫
          (widePullback_overX_eq_prod (fun _ : Fin (p + 2) => Limits.Sigma.desc f)).inv ≫
          overWPproj f (p + 2) 0 =
          Limits.prod.fst ≫ (overSigmaDescIso f).hom := by
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫ w)
          (wpEqProd_inv_overWPproj f (p + 2) 0)) ?_
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫ w)
          (prodFinSuccIso_inv_π_zero
            (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f)))) ?_
        exact Limits.prod.map_fst _ _
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫
        Limits.prod.map (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k)))) ≫ w) htail) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫ w)
        (Limits.prod.map_fst_assoc (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))))
          ((overSigmaDescIso f).hom))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
        (Limits.prod.map_fst_assoc (𝟙 (Over.mk (f i)))
          (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) t)
          (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i ≫ (overSigmaDescIso f).hom))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ Limits.prod.fst ≫ w)
        ((Category.id_comp _).trans (ι_overSigmaDescIso_hom f i))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg (fun w => w ≫ overDescIncl f i)
        (prodFinSuccIso_hom_fst (fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))))
    | succ l' =>
      have htail : (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫
          (widePullback_overX_eq_prod (fun _ : Fin (p + 2) => Limits.Sigma.desc f)).inv ≫
          overWPproj f (p + 2) l'.succ =
          Limits.prod.snd ≫ (widePullback_coproduct_iso f p).inv ≫
            overWPproj f (p + 1) l' := by
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫ w)
          (wpEqProd_inv_overWPproj f (p + 2) l'.succ)) ?_
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫ w)
          (prodFinSuccIso_inv_π_succ
            (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f)) l')) ?_
        refine Eq.trans (Limits.prod.map_snd_assoc _ _ _) ?_
        refine congrArg (fun w => Limits.prod.snd ≫ w) ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        exact congrArg (fun w => (widePullback_coproduct_iso f p).inv ≫ w)
          (wpEqProd_hom_π f (p + 1) l')
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫
        Limits.prod.map (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k)))) ≫ w) htail) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫ w)
        (Limits.prod.map_snd_assoc (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))))
          ((widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l'))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
        (Limits.prod.map_snd_assoc (𝟙 (Over.mk (f i)))
          (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) t)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) ≫
            (widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l'))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ Limits.prod.snd ≫ w)
        ((congrArg (fun w => Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
            ∏ᶜ fun k => Over.mk (f (τ k))) t ≫ w) (Category.id_comp _)).trans
          (ih t l'))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
        (Category.assoc _ _ _).symm) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg (fun w => w ≫ overDescIncl f (t l'))
        (prodFinSuccIso_hom_snd_π (fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))) l')

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Reindexing the nested product family and synthesizing its coproduct structure exceed defaults.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Combo: reindex layer + distributivity layer in one step.**  The `τ`-summand inclusion
through the universe-reduction reindex `Sigma.whiskerEquiv` and the distributivity inverse,
projected onto the `l`-th over-level wide-pullback factor, is the canonical projection
followed by the `E (τ l)`-th descent inclusion (with a single product-relabel transport). -/
lemma ι_reindex_wpci_inv_overWPproj {ι₀ : Type*} {Z' : ι₀ → C}
    (g : (i : ι₀) → Z' i ⟶ S) (E : ι₀ ≃ ι) (p : ℕ)
    [HasCoproduct (fun τ' : Fin (p + 1) → ι₀ => ∏ᶜ fun k => Over.mk (g (τ' k)))]
    (τ : Fin (p + 1) → ι₀) (l : Fin (p + 1)) :
    Limits.Sigma.ι (fun τ' : Fin (p + 1) → ι₀ => ∏ᶜ fun k => Over.mk (g (τ' k))) τ ≫
        (Sigma.whiskerEquiv (Equiv.arrowCongr (Equiv.refl (Fin (p + 1))) E.symm)
          (fun _ : Fin (p + 1) → ι => Iso.refl _)).inv ≫
        (widePullback_coproduct_iso (fun j : ι => g (E.symm j)) p).inv ≫
        overWPproj (fun j : ι => g (E.symm j)) (p + 1) l =
      eqToHom (congrArg (fun fam : Fin (p + 1) → ι₀ =>
          ∏ᶜ fun k => Over.mk (g (fam k)))
        (funext (fun k => (E.symm_apply_apply (τ k)).symm))) ≫
      Pi.π (fun k => Over.mk (g (E.symm (E (τ k))))) l ≫
      overDescIncl (fun j : ι => g (E.symm j)) (E (τ l)) := by
  refine Eq.trans ((ι_whiskerEquiv_inv_assoc
      (f := fun σ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (g (E.symm (σ k))))
      (g := fun τ' : Fin (p + 1) → ι₀ => ∏ᶜ fun k => Over.mk (g (τ' k)))
      (Equiv.arrowCongr (Equiv.refl (Fin (p + 1))) E.symm)
      (fun σ : Fin (p + 1) → ι => Iso.refl _) τ)
    ((widePullback_coproduct_iso (fun j : ι => g (E.symm j)) p).inv ≫
      overWPproj (fun j : ι => g (E.symm j)) (p + 1) l)) ?_
  refine Eq.trans (precomp_eq_of_eq (eqToHom (congrArg (fun fam : Fin (p + 1) → ι₀ =>
        ∏ᶜ fun k => Over.mk (g (fam k)))
      (funext (fun k => (E.symm_apply_apply (τ k)).symm))))
    (Category.id_comp _)) ?_
  exact precomp_eq_of_eq (eqToHom (congrArg (fun fam : Fin (p + 1) → ι₀ =>
        ∏ᶜ fun k => Over.mk (g (fam k)))
      (funext (fun k => (E.symm_apply_apply (τ k)).symm))))
    (ι_wpci_inv_overWPproj (fun j : ι => g (E.symm j)) p
      ((Equiv.arrowCongr (Equiv.refl (Fin (p + 1))) E.symm).symm τ) l)

end WPCIproj

/-- Generic reassociation entry: collapse the first two factors of a three-factor composite
against a projection. -/
lemma entry_chain {C : Type*} [Category C] {Y₀ Y₁ Y₂ Y₃ T : C}
    (a : Y₀ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (ci : Y₂ ⟶ Y₃) (pr : Y₃ ⟶ T) (s : Y₀ ⟶ Y₂)
    (h : a ≫ b = s) : (a ≫ b ≫ ci) ≫ pr = s ≫ (ci ≫ pr) := by
  rw [← h]; simp only [Category.assoc]

/-- Generic five-layer glue: peels the backbone-identification layers against their
characterizing equations in one reassociation pass (clean abstract context, so the
rewrites are reliable). -/
lemma glue_chain {C : Type*} [Category C] {Y S₁ S₂ S₃ S₄ S₅ S₆ T₁ T₂ U V : C}
    (i : Y ⟶ S₁) (em : S₁ ⟶ S₂) (dm : S₂ ⟶ S₃) (cm : S₃ ⟶ S₄) (bm : S₄ ⟶ S₅)
    (am : S₅ ⟶ S₆) (pr : S₆ ⟶ T₂) (pr₀ : S₅ ⟶ T₂) (h₀ : am ≫ pr = pr₀)
    (w₁ : Y ⟶ T₁) (i' : T₁ ⟶ S₂) (h₁ : i ≫ em = w₁ ≫ i')
    (oWP : S₄ ⟶ U) (R : U ⟶ T₂) (h₂ : bm ≫ pr₀ = oWP ≫ R)
    (mid : T₁ ⟶ V) (incl : V ⟶ U) (h₃ : i' ≫ dm ≫ cm ≫ oWP = mid ≫ incl)
    (cai : V ⟶ T₂) (h₄ : incl ≫ R = cai) :
    i ≫ (((((em ≫ dm) ≫ cm) ≫ bm) ≫ am) ≫ pr) = (w₁ ≫ mid) ≫ cai := by
  simp only [Category.assoc] at h₃ ⊢
  rw [h₀, h₂, reassoc_of% h₁, reassoc_of% h₃, h₄, ← Category.assoc]

/-- The face morphism between intersection-open legs: deleting the `k`-th index of `σ'`
enlarges the intersection, giving the open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}`. -/
noncomputable def interLegHom (𝒰 : X.OpenCover) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀)
    (k : Fin (p + 2)) :
    Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ⟶
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom))) :=
  Over.homMk (X.homOfLE (le_iInf (fun l => iInf_le (fun j => coverOpen 𝒰 (σ' j))
      ((SimplexCategory.δ k).toOrderHom l))))
    (Scheme.homOfLE_ι _ _)

/-- The face morphism intertwines the canonical component maps: projecting the `σ'`-leg
onto its `δᵏ l`-th component agrees with first including `U_{σ'} ⊆ U_{σ'∘δᵏ}` and then
projecting onto the `l`-th component.  Both lifts agree after the mono `𝒰.f _`. -/
lemma interLegHom_interProj (𝒰 : X.OpenCover) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀)
    (k : Fin (p + 2)) (l : Fin (p + 1)) :
    interLegHom 𝒰 σ' k ≫ interProj 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) l =
      interProj 𝒰 σ' ((SimplexCategory.δ k).toOrderHom l) := by
  have hfac : X.homOfLE (le_iInf (fun l' => iInf_le (fun j => coverOpen 𝒰 (σ' j))
        ((SimplexCategory.δ k).toOrderHom l'))) ≫
        coverInterToMember 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) l =
      coverInterToMember 𝒰 σ' ((SimplexCategory.δ k).toOrderHom l) := by
    haveI : IsOpenImmersion (𝒰.f (σ' ((SimplexCategory.δ k).toOrderHom l))) := inferInstance
    refine IsOpenImmersion.lift_uniq (𝒰.f (σ' ((SimplexCategory.δ k).toOrderHom l)))
      (Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ?_ _ ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun w => X.homOfLE (le_iInf (fun l' => iInf_le
        (fun j => coverOpen 𝒰 (σ' j)) ((SimplexCategory.δ k).toOrderHom l'))) ≫ w)
      (coverInterToMember_fac 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) l)).trans ?_
    exact Scheme.homOfLE_ι _ _
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun w => w ≫ Sigma.ι 𝒰.X (σ' ((SimplexCategory.δ k).toOrderHom l))) hfac)

end AlgebraicGeometry
