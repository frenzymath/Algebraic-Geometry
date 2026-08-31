/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.AffineVanishing

/-!
# Skyscraper sheaves of `K`-modules and their cohomology

For a scheme `X` over `Spec K`, a point `x : X`, and a `K`-module `M`, this file builds the
**skyscraper sheaf** `skyModule x M` of `K`-modules on the small Zariski site of `X`
(concentrated at `x`, with value `M`) and computes its cohomology in degrees `0` and `1`:

* `skyModuleGammaEquiv : Sheaf.HModule (skyModule x M) 0 ≃ₗ[K] M` — its degree-zero cohomology
  is `M` on the nose, `K`-linearly (global sections of a skyscraper sheaf are its value).
* `skyModule_subsingleton_hModule_one : Subsingleton (Sheaf.HModule (skyModule x M) 1)` — its
  degree-one cohomology vanishes.

## Vehicle and proof route

The sheaf is `mathlib`'s `skyscraperSheaf x M`, transported to the site
`Opens.grothendieckTopology (X : TopCat)` (which is *definitionally* the target category), and
sealed behind an opaque `def` so that later rewrites never unfold the raw `if`/`terminal`-tower;
the `simp` lemmas `skyModule_obj_of_mem`/`skyModule_obj_of_not_mem` expose its behaviour.

The degree-one vanishing rests on the general `Ext¹`-vanishing criterion
`Abelian.Ext.subsingleton_one_of_injective_of_surjective` (used exactly as in
`AlgebraicGeometry.Scheme.subsingleton_moduleKSheaf_hModule_one`): embed `skyModule x M` into its
injective hull and lift global sections along the cokernel. The lift
(`cokernelπ_app_top_surjective`) is the skyscraper analogue of
`IsAffineOpen.cokernel_app_surjective`: a section of the cokernel over `⊤` lifts locally (the
projection is a locally surjective epimorphism), the differences of the local lifts form a Čech
`1`-cocycle valued in the skyscraper, and — because a **skyscraper sheaf is flasque**
(`isFlasque_skyscraperSheaf_of_hasZeroObject`) and supported at the single point `x` — that
cocycle is an *elementwise* coboundary (its value at `x`), so no quasi-compactness / finite
subcover and no affine Čech argument are needed. The corrected local lifts glue.
-/

set_option autoImplicit false
-- We work with a single ambient classical decidability instance for open-membership `x ∈ U`
-- (needed by `skyscraperSheaf`); the section variable `[X.Over (Spec (.of K))]` is part of the
-- binding signature but not every declaration uses it.
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

open scoped Classical

variable {K : Type u} [CommRing K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- The **skyscraper sheaf** of `K`-modules on the small Zariski site of `X` supported at the
point `x`, with value `M`: sections over an open `U` are `M` if `x ∈ U` and the zero module
otherwise. Realised as `mathlib`'s `skyscraperSheaf`, which is *definitionally* an object of the
target sheaf category; kept opaque so downstream rewriting goes through the `simp` lemmas
`skyModule_obj_of_mem`/`skyModule_obj_of_not_mem` rather than the raw `if`/`terminal`-tower. -/
def skyModule (x : X) (M : ModuleCat.{u} K) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K) :=
  skyscraperSheaf x M

/-- Sections of the skyscraper sheaf over `U`: `M` if `x ∈ U`, and the terminal (zero) object
otherwise. -/
lemma skyModule_obj (x : X) (M : ModuleCat.{u} K) (U : X.Opens) :
    (skyModule x M).obj.obj (op U) = if x ∈ U then M else terminal (ModuleCat.{u} K) :=
  rfl

/-- Over an open containing `x`, the skyscraper sheaf takes the value `M`. -/
@[simp]
lemma skyModule_obj_of_mem (x : X) (M : ModuleCat.{u} K) {U : X.Opens} (h : x ∈ U) :
    (skyModule x M).obj.obj (op U) = M := by
  rw [skyModule_obj, if_pos h]

/-- Over an open avoiding `x`, the skyscraper sheaf takes the terminal (zero) value. -/
@[simp]
lemma skyModule_obj_of_not_mem (x : X) (M : ModuleCat.{u} K) {U : X.Opens} (h : x ∉ U) :
    (skyModule x M).obj.obj (op U) = terminal (ModuleCat.{u} K) := by
  rw [skyModule_obj, if_neg h]

/-- **Degree-zero cohomology of a skyscraper sheaf is its value**, `K`-linearly: `H⁰ ≃ₗ[K] M`.
Global sections (`H⁰`) live over the terminal open `⊤`, which contains `x`, so the value is `M`. -/
def skyModuleGammaEquiv (x : X) (M : ModuleCat.{u} K) :
    Sheaf.HModule (skyModule x M) 0 ≃ₗ[K] M :=
  (Sheaf.HModule.linearEquiv₀ (Opens.grothendieckTopology (X : TopCat))
      (isTerminalTop : IsTerminal (⊤ : X.Opens)) (skyModule x M)).trans
    (eqToIso (skyModule_obj_of_mem x M (Opens.mem_top x))).toLinearEquiv

/-- A restriction map of the skyscraper sheaf between two opens both containing `x` is an
isomorphism (definitionally an `eqToHom`). -/
private lemma skyModule_map_isIso (x : X) (M : ModuleCat.{u} K) {U V : X.Opens}
    (i : (op U : (X.Opens)ᵒᵖ) ⟶ op V) (hV : x ∈ V) :
    IsIso ((skyModule x M).obj.map i) := by
  change IsIso ((skyscraperSheaf x M).obj.map i)
  rw [skyscraperSheaf_obj_map, dif_pos hV]
  exact CategoryTheory.instIsIsoEqToHom _

/-- Over an open avoiding `x`, the module of sections of the skyscraper sheaf is trivial. -/
private lemma skyModule_subsingleton_of_not_mem (x : X) (M : ModuleCat.{u} K) {U : X.Opens}
    (h : x ∉ U) : Subsingleton ((skyModule x M).obj.obj (op U)) := by
  rw [skyModule_obj_of_not_mem x M h]
  exact ModuleCat.subsingleton_of_isZero terminalIsTerminal.isZero

/-- **Sections surjectivity over `⊤` for a skyscraper kernel.** For a monomorphism
`ι : skyModule x M ⟶ G` of sheaves of `K`-modules, every global section of `cokernel ι` lifts
to a global section of `G`. Skyscraper analogue of `IsAffineOpen.cokernel_app_surjective`; since
the skyscraper is flasque, the Čech 1-cocycle of differences is an *elementwise* coboundary
(the value at the single support point `x`), so no finite subcover / affine argument is needed. -/
private theorem cokernelπ_app_top_surjective (x : X) (M : ModuleCat.{u} K)
    {G : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K)}
    (ι : skyModule x M ⟶ G) [Mono ι]
    (q : (cokernel ι).obj.obj (op ⊤)) :
    ∃ s : G.obj.obj (op ⊤), ((cokernel.π ι).hom.app (op ⊤)).hom s = q := by
  classical
  haveI hfl : TopCat.Presheaf.IsFlasque (skyModule x M).obj :=
    isFlasque_skyscraperSheaf_of_hasZeroObject x M
  -- restriction composition (inlined `secRes_secRes`)
  have hres_res : ∀ (F : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K))
      {A B D : X.Opens} (h₁ : B ≤ A) (h₂ : D ≤ B) (t : F.obj.obj (op A)),
      (F.obj.map (homOfLE h₂).op).hom ((F.obj.map (homOfLE h₁).op).hom t) =
        (F.obj.map (homOfLE (h₂.trans h₁)).op).hom t := by
    intro F A B D h₁ h₂ t
    have hcomp : F.obj.map (homOfLE h₁).op ≫ F.obj.map (homOfLE h₂).op =
        F.obj.map (homOfLE (h₂.trans h₁)).op := by
      rw [← F.obj.map_comp, ← op_comp, homOfLE_comp]
    calc (F.obj.map (homOfLE h₂).op).hom ((F.obj.map (homOfLE h₁).op).hom t)
        = ((F.obj.map (homOfLE h₁).op ≫ F.obj.map (homOfLE h₂).op)).hom t := rfl
      _ = (F.obj.map (homOfLE (h₂.trans h₁)).op).hom t := by rw [hcomp]
  -- restriction naturality (inlined `secRes_naturality`)
  have hres_nat : ∀ {F F' : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} K)}
      (φ : F ⟶ F') {A B : X.Opens} (h : B ≤ A) (t : F.obj.obj (op A)),
      (φ.hom.app (op B)).hom ((F.obj.map (homOfLE h).op).hom t) =
        (F'.obj.map (homOfLE h).op).hom ((φ.hom.app (op A)).hom t) := by
    intro F F' φ A B h t
    have hnat := congrArg ModuleCat.Hom.hom (φ.hom.naturality (homOfLE h).op)
    exact DFunLike.congr_fun hnat t
  -- (a) `cokernel.π ι` is an epi, hence locally surjective.
  have _hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      (cokernel.π ι).hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u} K) (cokernel.π ι)).mpr inferInstance
  -- (b) each point has a neighbourhood carrying a local lift of `q`.
  have hloc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ ∃ t : G.obj.obj (op W),
      ((cokernel.π ι).hom.app (op W)).hom t =
        ((cokernel ι).obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom q := by
    intro p
    obtain ⟨W, g, hg, hpW⟩ := Presheaf.imageSieve_mem
      (Opens.grothendieckTopology (X : TopCat)) (cokernel.π ι).hom q p (Opens.mem_top p)
    obtain ⟨t, ht⟩ := hg
    exact ⟨W, hpW, t, ht⟩
  choose W hmem s hs using hloc
  -- (c) the neighbourhoods cover `X`.
  have hcov : (⨆ p, W p) = ⊤ := by
    apply le_antisymm le_top
    intro p _
    exact Opens.mem_iSup.mpr ⟨p, hmem p⟩
  -- (d) differences of local lifts come from the skyscraper.
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
  -- (e) the `a p p'` form a Čech 1-cocycle.
  have hcoc : ∀ p p' l, ((skyModule x M).obj.map
        (homOfLE (inf_le_inf_right (W l) (inf_le_left : W p ⊓ W p' ≤ W p))).op).hom (a p l) =
      ((skyModule x M).obj.map
          (homOfLE (inf_le_left : W p ⊓ W p' ⊓ W l ≤ W p ⊓ W p')).op).hom (a p p') +
        ((skyModule x M).obj.map
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
  -- (f) elementwise coboundary, pivoting on the support point `x`.
  choose b hb using fun p => (ModuleCat.epi_iff_surjective
      ((skyModule x M).obj.map (homOfLE (inf_le_left : W p ⊓ W x ≤ W p)).op)).mp
      (hfl.epi (homOfLE (inf_le_left : W p ⊓ W x ≤ W p)).op) (a p x)
  replace hb : ∀ p, ((skyModule x M).obj.map
      (homOfLE (inf_le_left : W p ⊓ W x ≤ W p)).op).hom (b p) = a p x := hb
  -- restriction to `A ⊓ W x` is injective (iso if `x ∈ A`, else the source is trivial).
  have hinj : ∀ A : X.Opens, Function.Injective
      ((skyModule x M).obj.map (homOfLE (inf_le_left : A ⊓ W x ≤ A)).op).hom := by
    intro A
    by_cases hx : x ∈ A
    · haveI := skyModule_map_isIso x M (homOfLE (inf_le_left : A ⊓ W x ≤ A)).op ⟨hx, hmem x⟩
      exact (ModuleCat.mono_iff_injective _).mp inferInstance
    · haveI := skyModule_subsingleton_of_not_mem x M hx
      exact fun u v _ => Subsingleton.elim u v
  -- the pivotal module identity: `a p p'` is the coboundary of `b`.
  have hab : ∀ p p', a p p' =
      ((skyModule x M).obj.map (homOfLE (inf_le_left : W p ⊓ W p' ≤ W p)).op).hom (b p) -
        ((skyModule x M).obj.map (homOfLE (inf_le_right : W p ⊓ W p' ≤ W p')).op).hom (b p') := by
    intro p p'
    apply hinj (W p ⊓ W p')
    have hc := hcoc p p' x
    rw [← hb p, ← hb p'] at hc
    rw [hres_res (skyModule x M) (inf_le_left : W p ⊓ W x ≤ W p)
          (inf_le_inf_right (W x) (inf_le_left : W p ⊓ W p' ≤ W p)),
        hres_res (skyModule x M) (inf_le_left : W p' ⊓ W x ≤ W p')
          (inf_le_inf_right (W x) (inf_le_right : W p ⊓ W p' ≤ W p'))] at hc
    rw [map_sub, hres_res (skyModule x M) (inf_le_left : W p ⊓ W p' ≤ W p)
          (inf_le_left : W p ⊓ W p' ⊓ W x ≤ W p ⊓ W p'),
        hres_res (skyModule x M) (inf_le_right : W p ⊓ W p' ≤ W p')
          (inf_le_left : W p ⊓ W p' ⊓ W x ≤ W p ⊓ W p'), eq_sub_iff_add_eq]
    exact hc.symm
  -- (g) corrected local sections and their compatibility.
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
  -- (h) glue and check locally that the glued section maps to `q`.
  obtain ⟨gl, hgl, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X : TopCat)) (C := ModuleCat.{u} K) G W ⊤
    (fun p => homOfLE (le_top : W p ≤ ⊤)) (le_of_eq hcov.symm) tloc hcompat
  refine ⟨gl, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} K)
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
    congrArg (fun m : skyModule x M ⟶ cokernel ι =>
      (m.hom.app (op (W p))).hom (b p)) (cokernel.condition ι)
  rw [map_sub, hs p, hπι, sub_zero]

/-- **Degree-one cohomology of a skyscraper sheaf vanishes.** This is the keystone: for any
`K`-module `M` and point `x`, `H¹(X, skyModule x M) = 0`.

Embed `skyModule x M` into its injective hull and apply the `Ext¹`-vanishing criterion (as in
`Scheme.subsingleton_moduleKSheaf_hModule_one`): it remains to lift global sections along the
cokernel of the embedding, which is provided by `cokernelπ_app_top_surjective`. -/
instance skyModule_subsingleton_hModule_one (x : X) (M : ModuleCat.{u} K) :
    Subsingleton (Sheaf.HModule (skyModule x M) 1) := by
  apply Abelian.Ext.subsingleton_one_of_injective_of_surjective
    (Injective.ι (skyModule x M))
  intro φ
  obtain ⟨sglob, hsglob⟩ := cokernelπ_app_top_surjective x M
    (Injective.ι (skyModule x M))
    (Sheaf.constModuleSheafHomEquiv (Opens.grothendieckTopology (X : TopCat))
      (isTerminalTop : IsTerminal (⊤ : X.Opens))
      (cokernel (Injective.ι (skyModule x M))) φ)
  refine ⟨(Sheaf.constModuleSheafHomEquiv (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) (Injective.under (skyModule x M))).symm sglob, ?_⟩
  apply (Sheaf.constModuleSheafHomEquiv (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens))
    (cokernel (Injective.ι (skyModule x M)))).injective
  rw [Sheaf.constModuleSheafHomEquiv_naturality
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) _
    (cokernel.π (Injective.ι (skyModule x M))),
    LinearEquiv.apply_symm_apply]
  exact hsglob

end

end AlgebraicGeometry
