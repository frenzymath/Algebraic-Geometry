/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.SectionsBridge
import AlgebraicJacobian.Cohomology.CechCoboundarySplitting

/-!
# Degree-one affine vanishing: `H¹(U, 𝒪_C) = 0` for affine opens

For a `Spec k`-scheme `C : Over (Spec (CommRingCat.of k))` and an **affine** open
`U` of `C.left`, the degree-one derived-functor cohomology of the structure sheaf
of `k`-modules vanishes:
`Subsingleton (HModule' k (toModuleKSheaf C) 1 U)`
(`subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen`).

This is the degree-one case of Serre's affine vanishing (Stacks 01XB, in the
`ModuleCat k`-sheaf-site flavour of the `HModule'` lane), obtained WITHOUT the
full Čech-to-derived comparison, by a single dimension shift through an
injective embedding (the degree-1 truncation of Hartshorne III.2.7 /
Stacks 01X8):

1. Embed `F := toModuleKSheaf C` into an injective sheaf `I` (the sheaf
   category is Grothendieck abelian, `CechComparisonGate.lean`), with cokernel
   `Q`, giving a short exact `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`.
2. The second-variable `Ext` long exact sequence
   (`Abelian.Ext.covariant_sequence_exact₁`) and `Ext`-vanishing on injectives
   (`Abelian.Ext.eq_zero_of_injective`) reduce
   `Subsingleton (Ext¹(P_U, F))` to surjectivity of
   `Hom(P_U, I) ⟶ Hom(P_U, Q)`
   (`subsingleton_hModule'_one_of_surjective_app`).
3. The H⁰-sections bridge (`HModule'_zero_sectionsLinearEquiv` and its
   naturality-in-the-sheaf companion, `SectionsBridge.lean`) converts that to
   surjectivity of the section map `Γ(U, I) ⟶ Γ(U, Q)`.
4. `I ⟶ Q` is an epimorphism of sheaves, hence locally surjective
   (`Sheaf.isLocallySurjective_iff_epi'`); since `U` is affine (in particular
   quasi-compact with a basis of basic opens), a section of `Q` over `U` lifts
   to `I` on a **finite** basic-open cover `D(gᵢ)` of `U`
   (`IsAffineOpen.exists_finite_basicOpen_lifts_of_epi`).
5. The pairwise differences of the local lifts form a Čech 1-cocycle with
   values in `F = ker(I ⟶ Q)` (sections of a sheaf kernel are computed
   sectionwise: `ShortComplex.ShortExact.exists_app_preimage`); through the
   section-identification kit of `CechCoboundarySplitting.lean` this cocycle
   lives in the localised module complex of Stacks 01EW and **splits**
   (`IsAffineOpen.exists_dDiff_eq_of_dDiff_eq_zero`).
6. Correcting the local lifts by the splitting makes them agree on overlaps;
   they glue to a section of `I` over `U` (`TopCat.Sheaf.existsUnique_gluing'`)
   whose image in `Q` is the given section, because `Q` is separated
   (`TopCat.Sheaf.eq_of_locally_eq'`).

Universe note: everything here stays at `HModule' = Abelian.Ext.{u}` (the
`Type u` carrier); the `HasExt.{u}` instance is
`CategoryTheory.IsGrothendieckAbelian.hasExt` (cf. `CechComparisonGate.lean`,
`hasExt_moduleKSheaf`).  Consumers that feed the Mayer–Vietoris LES at
`Ext.{u+1}` must transport through `Abelian.Ext.chgUnivLinearEquiv` as usual
(`MayerVietorisCover.lean`); no such transport happens in this file.

See `blueprint/src/chapters/Cohomology_StructureSheafModuleK.tex`.
-/

set_option autoImplicit false

universe u v w

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

/-! ## Elementwise helpers for `ModuleCat`-valued (pre)sheaves -/

namespace CategoryTheory

variable {k : Type u} [Field k]

/-- Elementwise naturality for a natural transformation of `ModuleCat`-valued
functors, in the `.hom`-application style of the `HModule'` lane: the square
`φ.app` versus `F.map`/`G.map` commutes on elements. -/
lemma NatTrans.app_hom_map_hom_apply {C : Type v} [Category.{w} C]
    {F G : C ⥤ ModuleCat.{u} k} (φ : F ⟶ G) {A B : C} (h : A ⟶ B) (x : F.obj A) :
    (φ.app B).hom ((F.map h).hom x) = (G.map h).hom ((φ.app A).hom x) := by
  calc (φ.app B).hom ((F.map h).hom x)
      = (F.map h ≫ φ.app B).hom x := by rw [ModuleCat.hom_comp]; rfl
    _ = (φ.app A ≫ G.map h).hom x := by rw [φ.naturality h]
    _ = (G.map h).hom ((φ.app A).hom x) := by rw [ModuleCat.hom_comp]; rfl

end CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- Double restriction of a section of a `ModuleCat`-valued presheaf on the
opens of a space collapses to the single restriction along the composite
inclusion. -/
lemma map_homOfLE_map_homOfLE_apply {T : TopCat.{u}}
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{u} k) {V W Z : Opens T}
    (hVW : V ≤ W) (hWZ : W ≤ Z) (z : P.obj (Opposite.op Z)) :
    (P.map (homOfLE hVW).op).hom ((P.map (homOfLE hWZ).op).hom z)
      = (P.map (homOfLE (hVW.trans hWZ)).op).hom z := by
  have h1 : P.map (homOfLE hWZ).op ≫ P.map (homOfLE hVW).op
      = P.map (homOfLE (hVW.trans hWZ)).op := by
    rw [← P.map_comp, ← op_comp, homOfLE_comp]
  calc (P.map (homOfLE hVW).op).hom ((P.map (homOfLE hWZ).op).hom z)
      = (P.map (homOfLE hWZ).op ≫ P.map (homOfLE hVW).op).hom z := by
        rw [ModuleCat.hom_comp]; rfl
    _ = (P.map (homOfLE (hVW.trans hWZ)).op).hom z := by rw [h1]

/-- Restricting a local lift of a section: if `t` over `V` lifts the
restriction of `q` (a section over `U ⊇ V`) along `φ`, then so does the
restriction of `t` to any `W ⊆ V`.  Packaged as a single lemma so consumers
can instantiate it by unification (avoiding rewrites across definitionally
equal spellings of the opens). -/
lemma app_hom_restrict_lift {T : TopCat.{u}} {P R : (Opens T)ᵒᵖ ⥤ ModuleCat.{u} k}
    (φ : P ⟶ R) {U V W : Opens T} (hWV : W ≤ V) (hVU : V ≤ U) (hWU : W ≤ U)
    {q : R.obj (Opposite.op U)} {t : P.obj (Opposite.op V)}
    (ht : (φ.app (Opposite.op V)).hom t = (R.map (homOfLE hVU).op).hom q) :
    (φ.app (Opposite.op W)).hom ((P.map (homOfLE hWV).op).hom t)
      = (R.map (homOfLE hWU).op).hom q := by
  rw [NatTrans.app_hom_map_hom_apply φ ((homOfLE hWV).op) t, ht,
    map_homOfLE_map_homOfLE_apply]

/-- Telescoping helper: the alternating `Fin 3`-sum of differences of a
doubly-indexed family vanishes once the six face terms are matched pairwise —
the abstract shape of the degree-2 Čech cocycle identity for a difference
1-cochain.  Stated over an arbitrary additive group so that the `Fin`-literal
bookkeeping happens in a clean context (no dependent restriction maps). -/
lemma sum_neg_one_pow_zsmul_sub_three_eq_zero {M : Type w} [AddCommGroup M]
    (g : Fin 3 → Fin 2 → M)
    (h2 : g 0 1 = g 1 1) (h1 : g 0 0 = g 2 1) (h0 : g 1 0 = g 2 0) :
    (∑ j : Fin 3, (-1 : ℤ) ^ (j : ℕ) • (g j 1 - g j 0)) = 0 := by
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq,
    one_smul, neg_one_zsmul, h2, h1, h0]
  abel

/-- Compatibility converter for gluing: to check that two sections agree after
restriction to `V ⊓ W` (the `TopCat.Presheaf.IsCompatible` shape), it suffices
to check agreement on any open `O` that *equals* `V ⊓ W` — with the
restriction maps along arbitrary chosen inclusion proofs.  This absorbs the
propositional-but-not-syntactic identifications of overlap opens (e.g.
`D(gᵢ·gⱼ) = D(gᵢ) ⊓ D(gⱼ)`) produced by the Čech kit. -/
lemma map_infLELeft_eq_map_infLERight_of_restrict_eq {T : TopCat.{u}}
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{u} k) {V W O : Opens T} (hO : O = V ⊓ W)
    {a : P.obj (Opposite.op V)} {b : P.obj (Opposite.op W)} (hVO : O ≤ V) (hWO : O ≤ W)
    (h : (P.map (homOfLE hVO).op).hom a = (P.map (homOfLE hWO).op).hom b) :
    (P.map (Opens.infLELeft V W).op).hom a
      = (P.map (Opens.infLERight V W).op).hom b := by
  subst hO
  exact h

end AlgebraicGeometry

/-! ## Left exactness of the sections functor on sheaves of `k`-modules

For a short exact sequence of sheaves `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` on any site, the
sections functor `Γ(V, ·) = (sheafToPresheaf ⋙ evaluation at V)` preserves the
kernel: `Γ(V, F) ⟶ Γ(V, I)` is injective with image exactly
`ker (Γ(V, I) ⟶ Γ(V, Q))`.  (It does NOT preserve the cokernel — that failure
is `H¹`.)  Both statements are instances of the fact that `sheafToPresheaf`
(a limit-creating inclusion) and evaluation preserve finite limits. -/

namespace CategoryTheory

variable {k : Type u} [Field k] {C : Type v} [Category.{u, v} C]
  {J : GrothendieckTopology C} [HasSheafify J (ModuleCat.{u} k)]

/-- **Sections of the kernel** (left exactness of `Γ(V, ·)`, existence part).
For a short exact sequence `S` of sheaves of `k`-modules on a site and any
object `V`, a section of `S.X₂` over `V` killed by `S.g` is in the image of
`S.f`.

**Statement audit (genus-lane wave 1', 2026-07-09): TRUE at stated
generality.**  Arbitrary site, arbitrary short exact `S`; the sections functor
is the composite of the limit-creating `sheafToPresheaf` with an evaluation,
hence preserves the kernel fork of `hS`
(`ShortComplex.Exact.map_of_mono_of_preservesKernel`); exactness of the mapped
complex in `ModuleCat` is elementwise (`ShortComplex.moduleCat_exact_iff`). -/
theorem ShortComplex.ShortExact.exists_app_preimage
    {S : ShortComplex (Sheaf J (ModuleCat.{u} k))} (hS : S.ShortExact) (V : C)
    (x : S.X₂.obj.obj (Opposite.op V))
    (hx : (S.g.hom.app (Opposite.op V)).hom x = 0) :
    ∃ y : S.X₁.obj.obj (Opposite.op V), (S.f.hom.app (Opposite.op V)).hom y = x := by
  haveI := hS.mono_f
  have hexact : (S.map (sheafToPresheaf J (ModuleCat.{u} k) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (Opposite.op V))).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  exact hexact x hx

/-- **Sections of a subsheaf embed** (left exactness of `Γ(V, ·)`, uniqueness
part): a monomorphism of sheaves of `k`-modules is injective on sections over
every object.

**Statement audit: TRUE at stated generality** — `sheafToPresheaf ⋙ evaluation`
preserves limits, hence monomorphisms; mono = injective in `ModuleCat`. -/
theorem Sheaf.app_hom_injective_of_mono
    {F G : Sheaf J (ModuleCat.{u} k)} (φ : F ⟶ G) [Mono φ] (V : C) :
    Function.Injective ((φ.hom.app (Opposite.op V)).hom) := by
  have hmono : Mono ((sheafToPresheaf J (ModuleCat.{u} k) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (Opposite.op V)).map φ) :=
    (sheafToPresheaf J (ModuleCat.{u} k) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{u} k)).obj (Opposite.op V)).map_mono φ
  exact (ModuleCat.mono_iff_injective _).mp hmono

end CategoryTheory

/-! ## Step 2: reduction of `Ext¹` vanishing to section-level surjectivity -/

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

section DimensionShift

variable {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
  [HasExt.{u} (Sheaf J (ModuleCat.{u} k))]

/-- **Dimension shift**: for a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of
sheaves of `k`-modules with `I` injective, if the section map
`Γ(U, I) ⟶ Γ(U, Q)` is surjective then `H¹(U, F) = Ext¹(P_U, F)` vanishes.

Blueprint: in the exact sequence
`Hom(P_U, I) → Hom(P_U, Q) →^δ Ext¹(P_U, F) → Ext¹(P_U, I) = 0`
(second-variable `Ext` LES, `Abelian.Ext.covariant_sequence_exact₁`;
vanishing on the injective `I` by `Abelian.Ext.eq_zero_of_injective`),
`δ` is surjective, and it kills everything as soon as
`Hom(P_U, I) → Hom(P_U, Q)` is onto — which the H⁰-sections bridge
(`HModule'_zero_sectionsLinearEquiv` + naturality in the sheaf,
`SectionsBridge.lean`) identifies with `Γ(U, I) → Γ(U, Q)`.
This is the degree-1 truncation of the Hartshorne III.2.7 / Stacks 01X8
dimension-shifting induction.

**Statement audit (genus-lane wave 1', 2026-07-09): TRUE at stated
generality.**  Arbitrary site at `Category.{u, v}`, arbitrary short exact `S`
with `S.X₂` injective; the `HasExt.{u}` pin matches the `Type u` ascription of
the `HModule'` abbrev (universe caution of `CechAcyclicInstance.lean:80-88`:
the vanishing stays at `Ext.{u}`; no `chgUniv` transport happens here). -/
theorem subsingleton_hModule'_one_of_surjective_app
    {S : ShortComplex (Sheaf J (ModuleCat.{u} k))} (hS : S.ShortExact)
    [Injective S.X₂] (U : C)
    (hsurj : Function.Surjective ((S.g.hom.app (Opposite.op U)).hom)) :
    Subsingleton (HModule' k S.X₁ 1 U) := by
  suffices h : ∀ x : HModule' k S.X₁ 1 U, x = 0 by
    exact subsingleton_of_forall_eq 0 h
  intro x
  -- `x` maps to `Ext¹(P_U, I) = 0`, so it comes from `Hom(P_U, Q)` via `δ`
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
    (Abelian.Ext.eq_zero_of_injective _) rfl
  -- lift the corresponding section of `Q` to `I` and push back through `mk₀ S.g`
  obtain ⟨sI, hsI⟩ := hsurj (HModule'_zero_sectionsLinearEquiv k S.X₃ U x₃)
  have hx₂ : ((HModule'_zero_sectionsLinearEquiv k S.X₂ U).symm sI).comp
      (Abelian.Ext.mk₀ S.g) (add_zero 0) = x₃ := by
    apply (HModule'_zero_sectionsLinearEquiv k S.X₃ U).injective
    rw [HModule'_zero_sectionsLinearEquiv_naturality_hom, LinearEquiv.apply_symm_apply, hsI]
  -- hence `x = x₂ ∘ (g ∘ extClass) = x₂ ∘ 0 = 0`
  rw [← hx₃, ← hx₂, Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
    Abelian.Ext.comp_zero]

end DimensionShift

/-! ## Step 3: finite basic-open local lifts along a sheaf epimorphism -/

/-- **Finite basic-open local surjectivity** over an affine open: for an
epimorphism `p : I ⟶ Q` of sheaves of `k`-modules on a scheme `X` and an
affine open `U`, every section of `Q` over `U` lifts to `I` on a finite family
of basic opens `D(gᵢ)` covering `U`.

Blueprint: `Epi p` gives local surjectivity
(`Sheaf.isLocallySurjective_iff_epi'`, mathlib `Sites/EpiMono.lean`); each
point of `U` has an open neighbourhood carrying a lift, which shrinks to a
basic open of `U` (`IsAffineOpen.exists_basicOpen_le`); quasi-compactness of
the affine `U` (`IsAffineOpen.isCompact`) extracts a finite subfamily.

**Statement audit (genus-lane wave 1', 2026-07-09): TRUE at stated
generality.**  Any scheme `X` (no noetherian/separatedness hypotheses), any
sheaf epi of `ModuleCat k`-sheaves; affineness of `U` is used exactly twice
(basic-open basis + quasi-compactness).  The `Balanced`/`HasSheafCompose`
instances the epi-to-locally-surjective lever needs synthesize on this site
(probe-confirmed). -/
theorem IsAffineOpen.exists_finite_basicOpen_lifts_of_epi
    {X : Scheme.{u}}
    {I Q : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)}
    (p : I ⟶ Q) [Epi p]
    {U : TopologicalSpace.Opens X.toTopCat} (hU : IsAffineOpen U)
    (q : Q.obj.obj (Opposite.op U)) :
    ∃ (ι : Type u) (_ : Finite ι) (gs : ι → Γ(X, U)),
      (⨆ i, X.basicOpen (gs i)) = U ∧
      ∀ i, ∃ t : I.obj.obj (Opposite.op (X.basicOpen (gs i))),
        (p.hom.app (Opposite.op (X.basicOpen (gs i)))).hom t
          = (Q.obj.map (homOfLE (X.basicOpen_le (gs i))).op).hom q := by
  -- epi ⟹ locally surjective
  haveI hloc : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := p)).mpr inferInstance
  have hsieve := Presheaf.imageSieve_mem (Opens.grothendieckTopology X.toTopCat)
    p.hom (U := Opposite.op U) q
  -- pointwise: a basic open around each point of `U` carrying a lift
  have hpoint : ∀ x : U, ∃ r : Γ(X, U), (x : X.toTopCat) ∈ X.basicOpen r ∧
      ∃ t : I.obj.obj (Opposite.op (X.basicOpen r)),
        (p.hom.app (Opposite.op (X.basicOpen r))).hom t
          = (Q.obj.map (homOfLE (X.basicOpen_le r)).op).hom q := by
    intro x
    obtain ⟨V, fVU, hsect, hxV⟩ := hsieve x.1 x.2
    obtain ⟨tV, htV⟩ := hsect
    obtain ⟨r, hrV, hxr⟩ := hU.exists_basicOpen_le ⟨x.1, hxV⟩ x.2
    refine ⟨r, hxr, (I.obj.map (homOfLE hrV).op).hom tV, ?_⟩
    exact app_hom_restrict_lift p.hom hrV fVU.le (X.basicOpen_le r) htV
  choose r hxr hlift using hpoint
  -- quasi-compactness: finite subcover by the chosen basic opens
  obtain ⟨T, hT⟩ := hU.isCompact.elim_finite_subcover
    (fun x : U => (X.basicOpen (r x) : Set X))
    (fun x => (X.basicOpen (r x)).isOpen)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxr ⟨y, hy⟩⟩)
  refine ⟨{x : U // x ∈ T}, inferInstance, fun i => r i.1, le_antisymm ?_ ?_,
    fun i => hlift i.1⟩
  · exact iSup_le fun i => X.basicOpen_le (r i.1)
  · intro y hy
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp (hT hy)
    exact Opens.mem_iSup.mpr ⟨⟨x, hxT⟩, hyx⟩

/-! ## Step 4: the geometric heart — section-level surjectivity onto the
cokernel of an embedding of the structure sheaf, over an affine open -/

variable {k}

/-- Restriction maps of `toModuleKSheaf C` are the structure-sheaf restriction
maps on elements.  Definitional (`toModuleKPresheaf` is `ModuleCat.of` applied
to the structure presheaf). -/
lemma toModuleKSheaf_obj_map_apply {C : Over (Spec (CommRingCat.of k))}
    {V W : TopologicalSpace.Opens C.left.toTopCat} (h : W ≤ V)
    (x : (toModuleKSheaf C).obj.obj (Opposite.op V)) :
    ((toModuleKSheaf C).obj.map (homOfLE h).op).hom x
      = (C.left.presheaf.map (homOfLE h).op).hom x :=
  rfl

variable (k)

/-- **The geometric heart of the degree-one affine vanishing**: for a short
exact sequence `0 ⟶ 𝒪_C ⟶ I ⟶ Q ⟶ 0` of sheaves of `k`-modules whose kernel
is the structure sheaf `toModuleKSheaf C`, the section map
`Γ(U, I) ⟶ Γ(U, Q)` is **surjective** for every affine open `U ⊆ C.left`.

Blueprint (Serre; Stacks 01XB at degree 1, via the 01EW module complex): a
section `q` of `Q` over `U` lifts to `I` on a finite basic-open cover `D(gᵢ)`
of `U` (step 3).  The differences of the lifts on overlaps `D(gᵢgⱼ)` are killed
by `I ⟶ Q`, hence come from sections `w_{ij}` of the kernel (sections of the
kernel are computed sectionwise); under the section-identification kit these
form a Čech 1-cocycle of the localised module complex `∏_σ Γ(U)_{g_σ}`, which
splits (`exists_dDiff_eq_of_dDiff_eq_zero`, Stacks 01EW for the affine `U`).
Correcting the lifts by the splitting makes them compatible; the corrected
family glues (sheaf condition of `I`) to a section of `I` over `U`, whose image
in `Q` agrees with `q` locally, hence equals `q` (separatedness of `Q`).

**Statement audit (genus-lane wave 1', 2026-07-09): TRUE at stated
generality.**  Any `Spec k`-scheme `C` (no properness/noetherian/integrality —
none are used), any short exact sequence with kernel the structure sheaf, any
affine open.  The kernel being `toModuleKSheaf C` (not an arbitrary sheaf) is
load-bearing exactly once: sections of the KERNEL over the basic opens
`D(g_σ)` must be the localisations `Γ(U)_{g_σ}` for the 01EW splitting — this
is the quasi-coherence input, supplied here by
`IsAffineOpen.dCoeffSectionsLinearEquiv` for the structure sheaf. -/
theorem IsAffineOpen.surjective_app_of_shortExact_toModuleKSheaf
    {C : Over (Spec (CommRingCat.of k))}
    {I Q : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {f : toModuleKSheaf C ⟶ I} {p : I ⟶ Q} {w : f ≫ p = 0}
    (hS : (ShortComplex.mk f p w).ShortExact)
    {U : TopologicalSpace.Opens C.left.toTopCat} (hU : IsAffineOpen U) :
    Function.Surjective ((p.hom.app (Opposite.op U)).hom) := by
  intro q
  haveI : Epi p := hS.epi_g
  haveI hmono : Mono f := hS.mono_f
  -- Step 3: finite basic-open cover with local lifts
  obtain ⟨ι, hfin, gs, hcov, hlift⟩ :=
    IsAffineOpen.exists_finite_basicOpen_lifts_of_epi k p hU q
  haveI := hfin
  choose ti hti using hlift
  -- canonical inclusions of the Čech overlap opens (`≤` pinned at the site
  -- spelling `Opens C.left.toTopCat`, so that `homOfLE`-restrictions and
  -- direct `Opposite.op` writes live in the same category instance)
  have hle : ∀ (m : ℕ) (σ : Fin (m + 1) → ι) (j : Fin (m + 1)),
      @LE.le (TopologicalSpace.Opens C.left.toTopCat) _
        (C.left.basicOpen (CechLocalized.sprod gs σ))
        (C.left.basicOpen (gs (σ j))) := by
    intro m σ j
    exact Scheme.basicOpen_le_basicOpen_of_dvd
      (Finset.dvd_prod_of_mem (fun m => gs (σ m)) (Finset.mem_univ j))
  -- restriction of a local lift, with `p`-image the restriction of `q`
  have hti_res : ∀ (i : ι) {W : TopologicalSpace.Opens C.left.toTopCat}
      (hW : W ≤ C.left.basicOpen (gs i)),
      (p.hom.app (Opposite.op W)).hom ((I.obj.map (homOfLE hW).op).hom (ti i))
        = (Q.obj.map (homOfLE (hW.trans (C.left.basicOpen_le (gs i)))).op).hom q :=
    fun i {W} hW => app_hom_restrict_lift p.hom hW (C.left.basicOpen_le (gs i))
      (hW.trans (C.left.basicOpen_le (gs i))) (hti i)
  -- `p ∘ f = 0` on elements
  have hpf : ∀ (V : TopologicalSpace.Opens C.left.toTopCat)
      (y : (toModuleKSheaf C).obj.obj (Opposite.op V)),
      (p.hom.app (Opposite.op V)).hom ((f.hom.app (Opposite.op V)).hom y) = 0 := by
    intro V y
    have h0 : (f ≫ p).hom.app (Opposite.op V) = 0 := by rw [w]; rfl
    calc (p.hom.app (Opposite.op V)).hom ((f.hom.app (Opposite.op V)).hom y)
        = ((f ≫ p).hom.app (Opposite.op V)).hom y := rfl
      _ = (0 : (toModuleKSheaf C).obj.obj (Opposite.op V) ⟶
            Q.obj.obj (Opposite.op V)).hom y := by rw [h0]
      _ = 0 := rfl
  -- Step 5a: differences of the lifts come from the kernel (the structure sheaf)
  have hdiff : ∀ σ : Fin 2 → ι,
      ∃ wσ : (toModuleKSheaf C).obj.obj
          (Opposite.op (C.left.basicOpen (CechLocalized.sprod gs σ))),
        (f.hom.app (Opposite.op (C.left.basicOpen (CechLocalized.sprod gs σ)))).hom wσ
          = (I.obj.map (homOfLE (hle 1 σ 1)).op).hom (ti (σ 1))
            - (I.obj.map (homOfLE (hle 1 σ 0)).op).hom (ti (σ 0)) := by
    intro σ
    apply hS.exists_app_preimage
    exact (map_sub _ _ _).trans
      ((congrArg₂ (· - ·) (hti_res (σ 1) (hle 1 σ 1)) (hti_res (σ 0) (hle 1 σ 0))).trans
        (sub_eq_zero.mpr rfl))
  choose wsec hwsec using hdiff
  -- images of the kernel 1-cochain under `f`, restricted anywhere
  have hface : ∀ (τ' : Fin 2 → ι) {V : TopologicalSpace.Opens C.left.toTopCat}
      (hV : V ≤ C.left.basicOpen (CechLocalized.sprod gs τ')),
      (f.hom.app (Opposite.op V)).hom
          ((C.left.presheaf.map (homOfLE hV).op).hom (wsec τ'))
        = (I.obj.map (homOfLE (hV.trans (hle 1 τ' 1))).op).hom (ti (τ' 1))
          - (I.obj.map (homOfLE (hV.trans (hle 1 τ' 0))).op).hom (ti (τ' 0)) := by
    intro τ' V hV
    calc (f.hom.app (Opposite.op V)).hom
          ((C.left.presheaf.map (homOfLE hV).op).hom (wsec τ'))
        = (f.hom.app (Opposite.op V)).hom
            (((toModuleKSheaf C).obj.map (homOfLE hV).op).hom (wsec τ')) := rfl
      _ = (I.obj.map (homOfLE hV).op).hom
            ((f.hom.app (Opposite.op (C.left.basicOpen
              (CechLocalized.sprod gs τ')))).hom (wsec τ')) :=
          NatTrans.app_hom_map_hom_apply f.hom ((homOfLE hV).op) (wsec τ')
      _ = (I.obj.map (homOfLE hV).op).hom
            ((I.obj.map (homOfLE (hle 1 τ' 1)).op).hom (ti (τ' 1))
              - (I.obj.map (homOfLE (hle 1 τ' 0)).op).hom (ti (τ' 0))) :=
          congrArg ((I.obj.map (homOfLE hV).op).hom) (hwsec τ')
      _ = (I.obj.map (homOfLE (hV.trans (hle 1 τ' 1))).op).hom (ti (τ' 1))
            - (I.obj.map (homOfLE (hV.trans (hle 1 τ' 0))).op).hom (ti (τ' 0)) :=
          (map_sub _ _ _).trans (congrArg₂ (· - ·)
            (map_homOfLE_map_homOfLE_apply _ _ _ _)
            (map_homOfLE_map_homOfLE_apply _ _ _ _))
  -- Step 5b(i): the alternating sum of restricted kernel sections vanishes
  -- (checked after applying the injective `f.app`, where it telescopes)
  have hkey : ∀ τ : Fin 3 → ι,
      (∑ j : Fin 3, ((-1 : ℤ) ^ (j : ℕ) •
        (C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
          (CechLocalized.sprod_succAbove_dvd gs τ j))).op).hom
          (wsec (τ ∘ j.succAbove)))) = 0 := by
    intro τ
    apply Sheaf.app_hom_injective_of_mono f
      (C.left.basicOpen (CechLocalized.sprod gs τ))
    refine Eq.trans ?_ (map_zero _).symm
    refine (map_sum _ _ _).trans ?_
    refine (Finset.sum_congr rfl fun (j : Fin 3) _ => (map_zsmul _ _ _).trans
      (congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • z)
        (hface (τ ∘ j.succAbove) (Scheme.basicOpen_le_basicOpen_of_dvd
          (CechLocalized.sprod_succAbove_dvd gs τ j))))).trans ?_
    exact sum_neg_one_pow_zsmul_sub_three_eq_zero
      (fun j b => (I.obj.map (homOfLE ((Scheme.basicOpen_le_basicOpen_of_dvd
        (CechLocalized.sprod_succAbove_dvd gs τ j)).trans
        (hle 1 (τ ∘ j.succAbove) b))).op).hom (ti ((τ ∘ j.succAbove) b)))
      rfl rfl rfl
  -- Step 5b(ii): the transported 1-cochain is a cocycle of the 01EW module complex
  have hcocycle : SectionCechModule.dDiff gs (↥Γ(C.left, U)) 2
      (fun σ => (hU.dCoeffSectionsLinearEquiv gs σ).symm (wsec σ)) = 0 := by
    funext τ
    apply (hU.dCoeffSectionsLinearEquiv gs τ).injective
    refine Eq.trans ?_ (map_zero _).symm
    have e1 : (hU.dCoeffSectionsLinearEquiv gs τ)
        (SectionCechModule.dDiff gs (↥Γ(C.left, U)) 2
          (fun σ => (hU.dCoeffSectionsLinearEquiv gs σ).symm (wsec σ)) τ)
        = ∑ j : Fin 3, ((-1 : ℤ) ^ (j : ℕ) •
            (C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
              (CechLocalized.sprod_succAbove_dvd gs τ j))).op).hom
              (wsec (τ ∘ j.succAbove))) := by
      rw [SectionCechModule.dDiff_apply, map_sum]
      exact Finset.sum_congr rfl fun (j : Fin 3) _ => by
        rw [map_zsmul, hU.dCoeffSectionsLinearEquiv_dCoface,
          LinearEquiv.apply_symm_apply]
    exact e1.trans (hkey τ)
  -- Step 5c: split the cocycle (Stacks 01EW over the affine `U`)
  obtain ⟨tt, htt⟩ := hU.exists_dDiff_eq_of_dDiff_eq_zero gs hcov (↥Γ(C.left, U)) _ hcocycle
  -- the section-level splitting relation on each pair overlap
  have hrel : ∀ σ : Fin 2 → ι,
      (C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
          (CechLocalized.sprod_succAbove_dvd gs σ 0))).op).hom
          (hU.dCoeffSectionsLinearEquiv gs (σ ∘ (0 : Fin 2).succAbove)
            (tt (σ ∘ (0 : Fin 2).succAbove)))
        - (C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
            (CechLocalized.sprod_succAbove_dvd gs σ 1))).op).hom
            (hU.dCoeffSectionsLinearEquiv gs (σ ∘ (1 : Fin 2).succAbove)
              (tt (σ ∘ (1 : Fin 2).succAbove)))
        = wsec σ := by
    intro σ
    have h := congrFun htt σ
    rw [SectionCechModule.dDiff_one_apply] at h
    have h2 := congrArg (hU.dCoeffSectionsLinearEquiv gs σ) h
    rw [map_sub, hU.dCoeffSectionsLinearEquiv_dCoface,
      hU.dCoeffSectionsLinearEquiv_dCoface] at h2
    simpa only [LinearEquiv.apply_symm_apply] using h2
  -- transport of the section-read of `tt` along index equalities
  have htsec_congr : ∀ {τ τ' : Fin 1 → ι} (_ : τ = τ')
      {V : TopologicalSpace.Opens C.left.toTopCat}
      (hV : V ≤ C.left.basicOpen (CechLocalized.sprod gs τ))
      (hV' : V ≤ C.left.basicOpen (CechLocalized.sprod gs τ')),
      (C.left.presheaf.map (homOfLE hV).op).hom
          (hU.dCoeffSectionsLinearEquiv gs τ (tt τ))
        = (C.left.presheaf.map (homOfLE hV').op).hom
            (hU.dCoeffSectionsLinearEquiv gs τ' (tt τ')) := by
    rintro τ _ rfl V hV hV'
    rfl
  -- the corrected local lifts over the singleton overlap opens
  have hsprod_single : ∀ i : ι,
      CechLocalized.sprod gs (fun _ : Fin 1 => i) = gs i := by
    intro i; simp [CechLocalized.sprod]
  have hWle : ∀ i : ι, @LE.le (TopologicalSpace.Opens C.left.toTopCat) _
      (C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i)))
      (C.left.basicOpen (gs i)) :=
    fun i => le_of_eq (by rw [hsprod_single i])
  have hWU : ∀ i : ι, @LE.le (TopologicalSpace.Opens C.left.toTopCat) _
      (C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i))) U :=
    fun i => C.left.basicOpen_le _
  have hsupW : (⨆ i, C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i)))
      = U :=
    (iSup_congr fun i => congrArg C.left.basicOpen (hsprod_single i)).trans hcov
  -- pair-overlap identification `D(g_σ) = W (σ 0) ⊓ W (σ 1)` for `σ = ![i, j]`
  have hsprod_pair : ∀ i j : ι, CechLocalized.sprod gs ![i, j] = gs i * gs j := by
    intro i j
    simp [CechLocalized.sprod, Fin.prod_univ_two]
  have hO : ∀ i j : ι, C.left.basicOpen (CechLocalized.sprod gs ![i, j])
      = C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i))
        ⊓ C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => j)) := by
    intro i j
    rw [hsprod_pair i j, hsprod_single i, hsprod_single j, Scheme.basicOpen_mul]
  -- index normalisations for `σ = ![i, j]`
  have hcomp0 : ∀ i j : ι, (![i, j] ∘ (0 : Fin 2).succAbove) = (fun _ : Fin 1 => j) := by
    intro i j
    rw [SectionCechModule.comp_succAbove_zero]
    funext m
    simp
  have hcomp1 : ∀ i j : ι, (![i, j] ∘ (1 : Fin 2).succAbove) = (fun _ : Fin 1 => i) := by
    intro i j
    rw [SectionCechModule.comp_succAbove_one]
    funext m
    simp
  -- inclusion of the pair overlap into the singleton opens
  have hOle : ∀ (i j : ι) (m : Fin 1 → ι) (_ : CechLocalized.sprod gs m ∣
      CechLocalized.sprod gs ![i, j]),
      @LE.le (TopologicalSpace.Opens C.left.toTopCat) _
        (C.left.basicOpen (CechLocalized.sprod gs ![i, j]))
        (C.left.basicOpen (CechLocalized.sprod gs m)) :=
    fun _ _ _ hdvd => Scheme.basicOpen_le_basicOpen_of_dvd hdvd
  -- the section-read of the splitting cochain over the singleton opens
  let tsec : ∀ i : ι, (toModuleKSheaf C).obj.obj (Opposite.op (C.left.basicOpen
      (CechLocalized.sprod gs (fun _ : Fin 1 => i)))) :=
    fun i => hU.dCoeffSectionsLinearEquiv gs (fun _ : Fin 1 => i) (tt (fun _ : Fin 1 => i))
  -- the corrected family
  let s' : ∀ i : ι, I.obj.obj (Opposite.op (C.left.basicOpen
      (CechLocalized.sprod gs (fun _ : Fin 1 => i)))) :=
    fun i =>
      (I.obj.map (homOfLE (hWle i)).op).hom (ti i)
        - (f.hom.app (Opposite.op (C.left.basicOpen
              (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom (tsec i)
  -- expansion of a restricted corrected section, in canonical form
  have hexp : ∀ (a : ι) (τ' : Fin 1 → ι) (hτ' : τ' = (fun _ : Fin 1 => a))
      {O' : TopologicalSpace.Opens C.left.toTopCat}
      (hO' : O' ≤ C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => a)))
      (hOτ' : O' ≤ C.left.basicOpen (CechLocalized.sprod gs τ')),
      (I.obj.map (homOfLE hO').op).hom (s' a)
        = (I.obj.map (homOfLE (hO'.trans (hWle a))).op).hom (ti a)
          - (f.hom.app (Opposite.op O')).hom
              ((C.left.presheaf.map (homOfLE hOτ').op).hom
                (hU.dCoeffSectionsLinearEquiv gs τ' (tt τ'))) := by
    intro a τ' hτ' O' hO' hOτ'
    calc (I.obj.map (homOfLE hO').op).hom (s' a)
        = (I.obj.map (homOfLE hO').op).hom
            ((I.obj.map (homOfLE (hWle a)).op).hom (ti a)
              - (f.hom.app (Opposite.op (C.left.basicOpen
                  (CechLocalized.sprod gs (fun _ : Fin 1 => a))))).hom (tsec a)) := rfl
      _ = (I.obj.map (homOfLE hO').op).hom
            ((I.obj.map (homOfLE (hWle a)).op).hom (ti a))
          - (I.obj.map (homOfLE hO').op).hom
              ((f.hom.app (Opposite.op (C.left.basicOpen
                (CechLocalized.sprod gs (fun _ : Fin 1 => a))))).hom (tsec a)) :=
          map_sub _ _ _
      _ = (I.obj.map (homOfLE (hO'.trans (hWle a))).op).hom (ti a)
          - (f.hom.app (Opposite.op O')).hom
              (((toModuleKSheaf C).obj.map (homOfLE hO').op).hom (tsec a)) :=
          congrArg₂ (· - ·) (map_homOfLE_map_homOfLE_apply _ _ _ _)
            (NatTrans.app_hom_map_hom_apply f.hom _ _).symm
      _ = (I.obj.map (homOfLE (hO'.trans (hWle a))).op).hom (ti a)
          - (f.hom.app (Opposite.op O')).hom
              ((C.left.presheaf.map (homOfLE hOτ').op).hom
                (hU.dCoeffSectionsLinearEquiv gs τ' (tt τ'))) :=
          congrArg (fun z => (I.obj.map (homOfLE (hO'.trans (hWle a))).op).hom (ti a)
              - (f.hom.app (Opposite.op O')).hom z)
            (htsec_congr hτ'.symm hO' hOτ')
  -- Step 6a: compatibility of the corrected family
  have hcompat : TopCat.Presheaf.IsCompatible I.obj
      (fun i : ι => C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i))) s' := by
    intro i j
    have hd0 : CechLocalized.sprod gs (fun _ : Fin 1 => j) ∣
        CechLocalized.sprod gs ![i, j] := by
      rw [← hcomp0 i j]; exact CechLocalized.sprod_succAbove_dvd gs ![i, j] 0
    have hd1 : CechLocalized.sprod gs (fun _ : Fin 1 => i) ∣
        CechLocalized.sprod gs ![i, j] := by
      rw [← hcomp1 i j]; exact CechLocalized.sprod_succAbove_dvd gs ![i, j] 1
    apply map_infLELeft_eq_map_infLERight_of_restrict_eq I.obj (hO i j)
      (hOle i j _ hd1) (hOle i j _ hd0)
    -- both sides in canonical form
    have hL := hexp i (![i, j] ∘ (1 : Fin 2).succAbove) (hcomp1 i j)
      (hOle i j _ hd1) (Scheme.basicOpen_le_basicOpen_of_dvd
        (CechLocalized.sprod_succAbove_dvd gs ![i, j] 1))
    have hR := hexp j (![i, j] ∘ (0 : Fin 2).succAbove) (hcomp0 i j)
      (hOle i j _ hd0) (Scheme.basicOpen_le_basicOpen_of_dvd
        (CechLocalized.sprod_succAbove_dvd gs ![i, j] 0))
    -- `f` applied to the splitting relation, in difference form
    have key : (f.hom.app (Opposite.op (C.left.basicOpen
          (CechLocalized.sprod gs ![i, j])))).hom
          ((C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
            (CechLocalized.sprod_succAbove_dvd gs ![i, j] 0))).op).hom
            (hU.dCoeffSectionsLinearEquiv gs (![i, j] ∘ (0 : Fin 2).succAbove)
              (tt (![i, j] ∘ (0 : Fin 2).succAbove))))
        - (f.hom.app (Opposite.op (C.left.basicOpen
            (CechLocalized.sprod gs ![i, j])))).hom
            ((C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
              (CechLocalized.sprod_succAbove_dvd gs ![i, j] 1))).op).hom
              (hU.dCoeffSectionsLinearEquiv gs (![i, j] ∘ (1 : Fin 2).succAbove)
                (tt (![i, j] ∘ (1 : Fin 2).succAbove))))
        = (I.obj.map (homOfLE (hle 1 ![i, j] 1)).op).hom (ti (![i, j] 1))
          - (I.obj.map (homOfLE (hle 1 ![i, j] 0)).op).hom (ti (![i, j] 0)) :=
      (map_sub _ _ _).symm.trans
        ((congrArg ((f.hom.app (Opposite.op (C.left.basicOpen
          (CechLocalized.sprod gs ![i, j])))).hom) (hrel ![i, j])).trans (hwsec ![i, j]))
    calc (I.obj.map (homOfLE (hOle i j _ hd1)).op).hom (s' i)
        = (I.obj.map (homOfLE ((hOle i j _ hd1).trans (hWle i))).op).hom (ti i)
          - (f.hom.app (Opposite.op (C.left.basicOpen
              (CechLocalized.sprod gs ![i, j])))).hom
              ((C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
                (CechLocalized.sprod_succAbove_dvd gs ![i, j] 1))).op).hom
                (hU.dCoeffSectionsLinearEquiv gs (![i, j] ∘ (1 : Fin 2).succAbove)
                  (tt (![i, j] ∘ (1 : Fin 2).succAbove)))) := hL
      _ = (I.obj.map (homOfLE ((hOle i j _ hd0).trans (hWle j))).op).hom (ti j)
          - (f.hom.app (Opposite.op (C.left.basicOpen
              (CechLocalized.sprod gs ![i, j])))).hom
              ((C.left.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
                (CechLocalized.sprod_succAbove_dvd gs ![i, j] 0))).op).hom
                (hU.dCoeffSectionsLinearEquiv gs (![i, j] ∘ (0 : Fin 2).succAbove)
                  (tt (![i, j] ∘ (0 : Fin 2).succAbove)))) :=
          sub_eq_sub_iff_add_eq_add.mpr
            ((add_comm _ _).trans (sub_eq_sub_iff_add_eq_add.mp key))
      _ = (I.obj.map (homOfLE (hOle i j _ hd0)).op).hom (s' j) := hR.symm
  -- Step 6b: glue the corrected family in `I`
  obtain ⟨sglue, hsglue, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (C := ModuleCat.{u} k) (X := C.left.toTopCat) I
    (fun i : ι => C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i))) U
    (fun i => homOfLE (hWU i)) (le_of_eq hsupW.symm) s' hcompat
  refine ⟨sglue, ?_⟩
  -- Step 6c: the glued section maps to `q` — check locally, `Q` is separated
  apply TopCat.Sheaf.eq_of_locally_eq' (C := ModuleCat.{u} k) (X := C.left.toTopCat) Q
    (fun i : ι => C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i))) U
    (fun i => homOfLE (hWU i)) (le_of_eq hsupW.symm)
  intro i
  have hps : (p.hom.app (Opposite.op (C.left.basicOpen
      (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom (s' i)
      = (Q.obj.map (homOfLE (hWU i)).op).hom q := by
    change (p.hom.app (Opposite.op (C.left.basicOpen
        (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom
        ((I.obj.map (homOfLE (hWle i)).op).hom (ti i)
          - (f.hom.app (Opposite.op (C.left.basicOpen
              (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom (tsec i))
        = (Q.obj.map (homOfLE (hWU i)).op).hom q
    refine (map_sub _ _ _).trans ?_
    refine (congrArg₂ (· - ·) (hti_res i (hWle i)) (hpf _ _)).trans ?_
    exact sub_zero _
  calc (Q.obj.map (homOfLE (hWU i)).op).hom ((p.hom.app (Opposite.op U)).hom sglue)
      = (p.hom.app (Opposite.op (C.left.basicOpen
          (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom
          ((I.obj.map (homOfLE (hWU i)).op).hom sglue) :=
        (NatTrans.app_hom_map_hom_apply p.hom ((homOfLE (hWU i)).op) sglue).symm
    _ = (p.hom.app (Opposite.op (C.left.basicOpen
          (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom (s' i) :=
        congrArg ((p.hom.app (Opposite.op (C.left.basicOpen
          (CechLocalized.sprod gs (fun _ : Fin 1 => i))))).hom) (hsglue i)
    _ = (Q.obj.map (homOfLE (hWU i)).op).hom q := hps

/-! ## Step 5: the degree-one affine vanishing -/

/-- **Degree-one affine vanishing** (the genus-lane target): for a
`Spec k`-scheme `C` and an **affine** open `U` of `C.left`, the degree-one
derived-functor cohomology of the structure sheaf of `k`-modules vanishes:
`H¹(U, 𝒪_C) = HModule' k (toModuleKSheaf C) 1 U` is a subsingleton.

Blueprint: Serre's affine vanishing in degree one (Stacks 01XB for the
structure sheaf, via the Stacks 01EW Čech splitting on the affine `U`),
assembled by a single dimension shift through an injective embedding
`0 ⟶ 𝒪_C ⟶ I ⟶ Q ⟶ 0` (the sheaf category is Grothendieck abelian, so has
enough injectives): `Ext¹(P_U, 𝒪) = 0` iff `Γ(U, I) ⟶ Γ(U, Q)` is onto
(`subsingleton_hModule'_one_of_surjective_app` + the H⁰-sections bridge),
which is `IsAffineOpen.surjective_app_of_shortExact_toModuleKSheaf`.

**Statement audit (genus-lane wave 1', 2026-07-09): TRUE at stated
generality.**  Any `Spec k`-scheme `C` — no properness, noetherianness,
integrality, or curve hypotheses (the classical statement needs only `U`
affine; quasi-compactness/quasi-separatedness of `U` are automatic).  This is
the `i = 1` clause of the `IsAffineHModuleVanishing k C (toModuleKSheaf C)`
gate (`Carriers.lean:222`); the `i ≥ 2` clauses need the full dimension-shift
induction (the cokernel `Q` is no longer a structure sheaf) and remain open.
Universe: the statement lives at `Abelian.Ext.{u}` (the `Type u` `HModule'`
carrier); the `HasExt.{u}` instance synthesizes via
`IsGrothendieckAbelian.hasExt` — consumers feeding the `Ext.{u+1}`
Mayer–Vietoris LES transport through `Abelian.Ext.chgUnivLinearEquiv`. -/
theorem subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen
    (C : Over (Spec (CommRingCat.of k)))
    {U : TopologicalSpace.Opens C.left.toTopCat} (hU : IsAffineOpen U) :
    Subsingleton (HModule' k (toModuleKSheaf C) 1 U) := by
  -- the canonical injective presentation of the structure sheaf
  let S : ShortComplex (Sheaf (Opens.grothendieckTopology C.left.toTopCat)
      (ModuleCat.{u} k)) :=
    ShortComplex.mk _ _ (cokernel.condition (Injective.ι (toModuleKSheaf C)))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  haveI : Injective S.X₂ := Injective.injective_under (toModuleKSheaf C)
  exact subsingleton_hModule'_one_of_surjective_app k hS U
    (IsAffineOpen.surjective_app_of_shortExact_toModuleKSheaf k hS hU)

end AlgebraicGeometry.Scheme
