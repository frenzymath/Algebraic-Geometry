/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Ledger.ModuleKSheaf
import AlgebraicJacobian.RiemannRoch.Ledger.AffineCech
import AlgebraicJacobian.RiemannRoch.Ledger.OverOpen

/-!
# Degree-one cohomology vanishing on affine opens

The keystone of the genus lane: for a scheme `X` over `Spec k` and an affine open
`U ≤ X`, the structure sheaf, viewed as a sheaf of `k`-modules on the small Zariski site,
has vanishing degree-one cohomology of `U`:
`Subsingleton (Sheaf.HModule' (X.moduleKSheaf k) U 1)`
(`AlgebraicGeometry.IsAffineOpen.subsingleton_moduleKSheaf_hModule'_one`), and for `X`
itself affine, vanishing degree-one cohomology of the site:
`Subsingleton (Sheaf.HModule (X.moduleKSheaf k) 1)`
(`AlgebraicGeometry.Scheme.subsingleton_moduleKSheaf_hModule_one`).

## Proof architecture

`H¹'(U) = Ext¹(k[U], 𝒪ₖ)` and `H¹ = Ext¹(k_X, 𝒪ₖ)` in the Grothendieck abelian category
of sheaves of `k`-modules, so it suffices to have
(`Abelian.Ext.subsingleton_one_of_injective_of_surjective`, proved here for any abelian
category with `HasExt`):

* a monomorphism `ι : 𝒪ₖ ⟶ G` with `G` injective — supplied by `Injective.under`
  (the category is Grothendieck abelian, hence has enough injectives); and
* surjectivity of `Hom(L, G) ⟶ Hom(L, cokernel ι)` for `L = k[U]` resp. `L = k_X` —
  since morphisms out of `k[U]` (resp. `k_X`) compute sections over `U` (resp. `⊤`),
  this is surjectivity of `G(U) ⟶ (cokernel ι)(U)` on sections over the affine open
  (`IsAffineOpen.cokernel_app_surjective`), which is the geometric content:

a section `q` of `cokernel ι` over `U` lifts locally to `G` (epimorphisms of sheaves are
locally surjective), on a finite cover of `U` by basic opens (affine opens are
quasi-compact); the differences of the local lifts are a Čech 1-cocycle with values
in `𝒪ₖ` (kernel-exactness of sections), which on an affine open is a coboundary
(`IsAffineOpen.exists_cech_cobounding`, Serre's argument); correcting the local lifts by
the coboundary makes them glue to a lift of `q` over `U`.

No flasque/Godement machinery and no derived-functor comparison is needed: injectivity
enters only through `Ext¹(L, G) = 0` for `G` injective.
-/

set_option autoImplicit false

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace CategoryTheory

namespace Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Vanishing criterion for `Ext¹`: if `A` admits a monomorphism `ι` into an injective
object such that every morphism `L ⟶ cokernel ι` lifts along `cokernel.π ι`, then
`Ext¹(L, A) = 0`. -/
theorem subsingleton_one_of_injective_of_surjective {A I : C} (ι : A ⟶ I) [Mono ι]
    [Injective I] (L : C)
    (hsurj : ∀ φ : L ⟶ cokernel ι, ∃ ψ : L ⟶ I, ψ ≫ cokernel.π ι = φ) :
    Subsingleton (Abelian.Ext L A 1) := by
  suffices h : ∀ z : Abelian.Ext L A 1, z = 0 from ⟨fun x y ↦ (h x).trans (h y).symm⟩
  intro z
  have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι) }
  have h1 : z.comp (mk₀ ι) (add_zero 1) = 0 := eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ L hS z h1 (zero_add 1)
  obtain ⟨ψ, hψ⟩ := hsurj (homEquiv₀ x₃)
  have hx₃' : mk₀ (ψ ≫ cokernel.π ι) = x₃ := by
    rw [hψ, mk₀_homEquiv₀_apply]
  calc z = x₃.comp hS.extClass (zero_add 1) := hx₃.symm
    _ = ((mk₀ ψ).comp (mk₀ (cokernel.π ι)) (zero_add 0)).comp hS.extClass (zero_add 1) := by
          rw [mk₀_comp_mk₀, hx₃']
    _ = (mk₀ ψ).comp ((mk₀ (cokernel.π ι)).comp hS.extClass (zero_add 1)) (zero_add 1) :=
          comp_assoc _ _ _ rfl rfl rfl
    _ = 0 := by rw [hS.comp_extClass]; simp

end Abelian.Ext

namespace Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Type u} [CommRing R] [HasSheafify J (ModuleCat.{u} R)]

/-- Sections of a short exact sequence of sheaves of modules are exact at the middle-left:
an element of `G(U)` killed by `cokernel.π ι` comes from `F(U)` when `ι : F ⟶ G` is a
monomorphism of sheaves. (Evaluation of sheaves is left exact.) -/
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

/-- Evaluation of sheaves of modules preserves monomorphisms: the component of a
monomorphism of sheaves is injective. -/
theorem app_injective_of_mono {F G : Sheaf J (ModuleCat.{u} R)} (ι : F ⟶ G) [Mono ι]
    (U : Cᵒᵖ) : Function.Injective (ι.hom.app U).hom := by
  let Fsec : Sheaf J (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    sheafToPresheaf J (ModuleCat.{u} R) ⋙ (evaluation Cᵒᵖ (ModuleCat.{u} R)).obj U
  have hmono : Mono (Fsec.map ι) := Fsec.map_mono ι
  rw [← ModuleCat.mono_iff_injective]
  exact hmono

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry

section SectionsRestriction

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
variable (G : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k))

/-- Restriction of sections of a sheaf of modules along an inclusion of opens. -/
private noncomputable def secRes {U V : X.Opens} (h : V ≤ U) :
    G.obj.obj (op U) →ₗ[k] G.obj.obj (op V) :=
  (G.obj.map (homOfLE h).op).hom

private lemma secRes_secRes {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : G.obj.obj (op U)) :
    secRes G h₂ (secRes G h₁ s) = secRes G (h₂.trans h₁) s := by
  have hcomp : G.obj.map (homOfLE h₁).op ≫ G.obj.map (homOfLE h₂).op =
      G.obj.map (homOfLE (h₂.trans h₁)).op := by
    rw [← G.obj.map_comp, ← op_comp, homOfLE_comp]
  calc secRes G h₂ (secRes G h₁ s)
      = ((G.obj.map (homOfLE h₁).op ≫ G.obj.map (homOfLE h₂).op)).hom s := rfl
    _ = secRes G (h₂.trans h₁) s := by rw [hcomp]; rfl

private lemma secRes_naturality {F G : Sheaf (Opens.grothendieckTopology (X : TopCat))
    (ModuleCat.{u} k)} (φ : F ⟶ G) {U V : X.Opens} (h : V ≤ U) (s : F.obj.obj (op U)) :
    (φ.hom.app (op V)).hom (secRes F h s) = secRes G h ((φ.hom.app (op U)).hom s) := by
  have hnat := congrArg ModuleCat.Hom.hom (φ.hom.naturality (homOfLE h).op)
  exact DFunLike.congr_fun hnat s

/-- On the structure sheaf as a sheaf of modules, `secRes` is restriction of scheme
sections. -/
private lemma secRes_moduleKSheaf [X.Over (Spec (.of k))] {U V : X.Opens} (h : V ≤ U)
    (s : Γ(X, U)) :
    secRes (X.moduleKSheaf k) h s = X.resHom h s := rfl

end SectionsRestriction

section AffineVanishing

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {U : X.Opens}

namespace IsAffineOpen

set_option backward.isDefEq.respectTransparency false in
/-- **Sections surjectivity over an affine open.** For a monomorphism `ι : 𝒪ₖ ⟶ G` out
of the structure sheaf (as a sheaf of `k`-modules) of a scheme and an affine open `U`,
every section of `cokernel ι` over `U` lifts to a section of `G` over `U`.

This is the geometric heart of the degree-one vanishing: local lifts on a finite basic
cover of `U` differ by a Čech 1-cocycle in `𝒪ₖ`, which is a coboundary by
`IsAffineOpen.exists_cech_cobounding`; the corrected lifts glue. -/
theorem cokernel_app_surjective (hU : IsAffineOpen U)
    {G : Sheaf (Opens.grothendieckTopology (X : TopCat)) (ModuleCat.{u} k)}
    (ι : X.moduleKSheaf k ⟶ G) [Mono ι]
    (q : (cokernel ι).obj.obj (op U)) :
    ∃ s : G.obj.obj (op U),
      ((cokernel.π ι).hom.app (op U)).hom s = q := by
  classical
  -- (a) `cokernel.π ι` is an epimorphism, hence locally surjective.
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      (cokernel.π ι).hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{u} k) (cokernel.π ι)).mpr
      inferInstance
  -- (b) each point of `U` has a basic open neighbourhood carrying a local lift of `q`.
  have hloc : ∀ x : (U : Set X), ∃ f₀ : Γ(X, U), ↑x ∈ X.basicOpen f₀ ∧
      ∃ s : G.obj.obj (op (X.basicOpen f₀)),
        ((cokernel.π ι).hom.app (op (X.basicOpen f₀))).hom s =
          secRes (cokernel ι) (X.basicOpen_le f₀) q := by
    intro x
    obtain ⟨V, g, hg, hxV⟩ := Presheaf.imageSieve_mem
      (Opens.grothendieckTopology (X : TopCat)) (cokernel.π ι).hom q x x.2
    obtain ⟨s, hs⟩ := hg
    obtain ⟨f₀, hle, hxf₀⟩ := hU.exists_basicOpen_le (⟨(x : X), hxV⟩ : V) x.2
    refine ⟨f₀, hxf₀, secRes G hle s, ?_⟩
    have hnat := secRes_naturality (cokernel.π ι) hle s
    rw [hnat]
    have hs' : ((cokernel.π ι).hom.app (op V)).hom s = secRes (cokernel ι) g.le q := hs
    rw [hs', secRes_secRes]
  choose f₀ hmem s₀ hs₀ using hloc
  -- (c) finite subcover by quasi-compactness of the affine open.
  obtain ⟨FS, hFS⟩ := hU.isCompact.elim_finite_subcover
    (fun x : (U : Set X) ↦ (X.basicOpen (f₀ x) : Set X))
    (fun x ↦ (X.basicOpen (f₀ x)).isOpen)
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  let f : Fin FS.card → Γ(X, U) := fun i ↦ f₀ (FS.equivFin.symm i)
  have hcov : ⨆ i, X.basicOpen (f i) = U := by
    apply le_antisymm (iSup_le fun i ↦ X.basicOpen_le (f i))
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hFS hx)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨hyF, hxy⟩ := hy
    exact Opens.mem_iSup.mpr ⟨FS.equivFin ⟨y, hyF⟩, by simpa [f] using hxy⟩
  let s : ∀ i, G.obj.obj (op (X.basicOpen (f i))) := fun i ↦ s₀ (FS.equivFin.symm i)
  have hs : ∀ i, ((cokernel.π ι).hom.app (op (X.basicOpen (f i)))).hom (s i) =
      secRes (cokernel ι) (X.basicOpen_le (f i)) q := fun i ↦ hs₀ (FS.equivFin.symm i)
  -- (d) the differences of the local lifts come from the structure sheaf.
  have hker : ∀ i j, ((cokernel.π ι).hom.app
      (op (X.basicOpen (f i) ⊓ X.basicOpen (f j)))).hom
      (secRes G inf_le_left (s i) - secRes G inf_le_right (s j)) = 0 := by
    intro i j
    have h1 := secRes_naturality (cokernel.π ι)
      (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f i)) (s i)
    have h2 := secRes_naturality (cokernel.π ι)
      (inf_le_right : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f j)) (s j)
    rw [map_sub, h1, h2, hs i, hs j, secRes_secRes, secRes_secRes, sub_self]
  choose a ha using fun i j ↦ Sheaf.exists_app_eq_of_cokernelπ_app_eq_zero ι
    (op (X.basicOpen (f i) ⊓ X.basicOpen (f j))) _ (hker i j)
  -- (e) the `a i j` form a Čech 1-cocycle.
  have hcoc : ∀ i j l,
      X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_left) (a i l) =
        X.resHom inf_le_left (a i j) +
          X.resHom (inf_le_inf_right (X.basicOpen (f l)) inf_le_right) (a j l) := by
    intro i j l
    apply Sheaf.app_injective_of_mono ι
      (op (X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l)))
    have h1 := secRes_naturality ι
      (inf_le_inf_right (X.basicOpen (f l)) inf_le_left :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f i) ⊓ X.basicOpen (f l)) (a i l)
    have h2 := secRes_naturality ι
      (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
        X.basicOpen (f i) ⊓ X.basicOpen (f j)) (a i j)
    have h3 := secRes_naturality ι
      (inf_le_inf_right (X.basicOpen (f l)) inf_le_right :
        X.basicOpen (f i) ⊓ X.basicOpen (f j) ⊓ X.basicOpen (f l) ≤
          X.basicOpen (f j) ⊓ X.basicOpen (f l)) (a j l)
    rw [← secRes_moduleKSheaf (k := k) (X := X)
        (inf_le_inf_right (X.basicOpen (f l)) inf_le_left) (a i l),
      ← secRes_moduleKSheaf (k := k) (X := X)
        (inf_le_left : _ ≤ X.basicOpen (f i) ⊓ X.basicOpen (f j)) (a i j),
      ← secRes_moduleKSheaf (k := k) (X := X)
        (inf_le_inf_right (X.basicOpen (f l)) inf_le_right) (a j l)]
    simp only [map_add]
    rw [h1, h2, h3, ha i l, ha i j, ha j l]
    simp only [map_sub, secRes_secRes]
    abel
  -- (f) cobound the cocycle and correct the local lifts.
  obtain ⟨b, hb⟩ := hU.exists_cech_cobounding f hcov a hcoc
  let tloc : ∀ i, G.obj.obj (op (X.basicOpen (f i))) :=
    fun i ↦ s i - (ι.hom.app (op (X.basicOpen (f i)))).hom (b i)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj (fun i ↦ X.basicOpen (f i)) tloc := by
    intro i j
    change secRes G (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ _) (tloc i) =
      secRes G inf_le_right (tloc j)
    have h1 := secRes_naturality ι
      (inf_le_left : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f i)) (b i)
    have h2 := secRes_naturality ι
      (inf_le_right : X.basicOpen (f i) ⊓ X.basicOpen (f j) ≤ X.basicOpen (f j)) (b j)
    change secRes G _ (s i - (ι.hom.app (op (X.basicOpen (f i)))).hom (b i)) =
      secRes G _ (s j - (ι.hom.app (op (X.basicOpen (f j)))).hom (b j))
    rw [map_sub, map_sub, ← h1, ← h2, secRes_moduleKSheaf, secRes_moduleKSheaf,
      sub_eq_sub_iff_sub_eq_sub, ← map_sub, ← hb i j]
    exact (ha i j).symm
  obtain ⟨gl, hgl, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := (X : TopCat)) (C := ModuleCat.{u} k) G (fun i ↦ X.basicOpen (f i)) U
    (fun i ↦ homOfLE (X.basicOpen_le (f i))) (le_of_eq hcov.symm) tloc hcompat
  refine ⟨gl, ?_⟩
  -- (g) the glued section maps to `q` by separation.
  apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := ModuleCat.{u} k)
    (cokernel ι) (fun i ↦ X.basicOpen (f i)) U (fun i ↦ homOfLE (X.basicOpen_le (f i)))
    (le_of_eq hcov.symm)
  intro i
  change secRes (cokernel ι) (X.basicOpen_le (f i))
      (((cokernel.π ι).hom.app (op U)).hom gl) =
    secRes (cokernel ι) (X.basicOpen_le (f i)) q
  have h1 := secRes_naturality (cokernel.π ι) (X.basicOpen_le (f i)) gl
  rw [← h1]
  have hgl' : secRes G (X.basicOpen_le (f i)) gl = tloc i := hgl i
  rw [hgl']
  change ((cokernel.π ι).hom.app (op (X.basicOpen (f i)))).hom
    (s i - (ι.hom.app (op (X.basicOpen (f i)))).hom (b i)) = _
  have hπι : ((cokernel.π ι).hom.app (op (X.basicOpen (f i)))).hom
      ((ι.hom.app (op (X.basicOpen (f i)))).hom (b i)) = 0 :=
    congrArg (fun m : X.moduleKSheaf k ⟶ cokernel ι ↦
      (m.hom.app (op (X.basicOpen (f i)))).hom (b i)) (cokernel.condition ι)
  rw [map_sub, hs i, hπι, sub_zero]

/-- **Degree-one cohomology vanishing on affine opens** (Serre): for a scheme `X` over
`Spec k` and an affine open `U`, the structure sheaf as a sheaf of `k`-modules on the
small Zariski site of `X` has vanishing `H¹` of `U` (in the sense of `Sheaf.HModule'`,
cohomology of an object of the site). -/
theorem subsingleton_moduleKSheaf_hModule'_one (hU : IsAffineOpen U) :
    Subsingleton (Sheaf.HModule' (X.moduleKSheaf k) U 1) := by
  apply Abelian.Ext.subsingleton_one_of_injective_of_surjective
    (Injective.ι (X.moduleKSheaf k))
  intro φ
  obtain ⟨sglob, hsglob⟩ := hU.cokernel_app_surjective k (Injective.ι (X.moduleKSheaf k))
    (Sheaf.freeModuleSheafHomEquiv (cokernel (Injective.ι (X.moduleKSheaf k))) φ)
  refine ⟨(Sheaf.freeModuleSheafHomEquiv (Injective.under (X.moduleKSheaf k))).symm
    sglob, ?_⟩
  apply (Sheaf.freeModuleSheafHomEquiv
    (cokernel (Injective.ι (X.moduleKSheaf k)))).injective
  rw [Sheaf.freeModuleSheafHomEquiv_comp, LinearEquiv.apply_symm_apply]
  exact hsglob

end IsAffineOpen

/-- **Degree-one cohomology vanishing on affine schemes** (Serre): for an affine scheme
`X` over `Spec k`, the structure sheaf as a sheaf of `k`-modules on the small Zariski
site has vanishing `H¹`. -/
instance Scheme.subsingleton_moduleKSheaf_hModule_one (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsAffine X] :
    Subsingleton (Sheaf.HModule (X.moduleKSheaf k) 1) := by
  apply Abelian.Ext.subsingleton_one_of_injective_of_surjective
    (Injective.ι (X.moduleKSheaf k))
  intro φ
  obtain ⟨sglob, hsglob⟩ := (isAffineOpen_top X).cokernel_app_surjective k
    (Injective.ι (X.moduleKSheaf k))
    (Sheaf.constModuleSheafHomEquiv (Opens.grothendieckTopology (X : TopCat))
      (isTerminalTop : IsTerminal (⊤ : X.Opens))
      (cokernel (Injective.ι (X.moduleKSheaf k))) φ)
  refine ⟨(Sheaf.constModuleSheafHomEquiv (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens))
    (Injective.under (X.moduleKSheaf k))).symm sglob, ?_⟩
  apply (Sheaf.constModuleSheafHomEquiv (Opens.grothendieckTopology (X : TopCat))
    (isTerminalTop : IsTerminal (⊤ : X.Opens))
    (cokernel (Injective.ι (X.moduleKSheaf k)))).injective
  rw [Sheaf.constModuleSheafHomEquiv_naturality
    (isTerminalTop : IsTerminal (⊤ : X.Opens)) _
    (cokernel.π (Injective.ι (X.moduleKSheaf k))),
    LinearEquiv.apply_symm_apply]
  exact hsglob

end AffineVanishing

end AlgebraicGeometry
