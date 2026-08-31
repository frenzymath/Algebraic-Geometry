/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.LineBundleCoherence

/-!
# Base-change bricks for the kernel of a base-flat quotient

Standalone bricks for `Scheme.Modules.pullback_kernel_isLocallyTrivial`
(blueprint `lem:relative_divisor_base_change`, `Picard/DivFunctorDef.lean`):
the base-change comparison of the invertible kernel ideal of a relative
effective divisor.

## Contents

* `Module.Flat.rTensor_injective_of_exact` — **Stacks 00HL**, the Tor-free
  algebra heart: if `0 → A → B → C → 0` is exact with `C` flat, then
  `A ⊗ N → B ⊗ N` stays injective for every module `N`.  Proof by a free
  presentation of `N` and an elementwise 3×3 chase — no `Tor` needed.
* `Scheme.Modules.unit_isQuasicoherent` — the unit module `𝒪_X` is
  quasi-coherent (instance; via the canonical one-generator presentation
  `LineBundle.unitPresentation` of `Picard/LineBundleCoherence.lean`).
* `Scheme.Modules.pullbackKernelComparison` — the kernel–pullback comparison
  `g'^*(ker q) ⟶ ker (g'^* q)` (the mathlib `kernelComparison` at the module
  pullback, which preserves zero morphisms being a left adjoint).
* `Scheme.LineBundle.IsLocallyTrivial.trivialization_of_le` — a trivialising
  chart restricts along any smaller open (the Stacks 01HH chart chase of
  `IsLocallyTrivial.pullback`, specialised to an inclusion `V ≤ U`), and the
  chart-shrinking corollary `exists_affine_trivializing_le`.

## References

Blueprint: `lem:relative_divisor_base_change`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Sources: Stacks 00HL (flat cokernel keeps the sub after tensoring),
Stacks 01HH (pullback of invertibles), Kleiman, "The Picard scheme" §3.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

/-! ## §1. The algebra heart (Stacks 00HL)

If `0 → A → B → C → 0` is a short exact sequence of `R`-modules with `C`
flat, then for every `R`-module `N` the induced map `A ⊗ N → B ⊗ N` is still
injective (equivalently `Tor_1^R(C, N) = 0`, but the proof below is Tor-free:
a free presentation `0 → K → F₀ → N → 0` and an elementwise 3×3 chase). -/

/-- **The 3×3 chase behind Stacks 00HL**, over an arbitrary presentation
`K —ι→ F₀ —π→ N → 0` with `F₀` flat: if `f : A → B` is injective, `(f, g)` is
exact with `g` surjective and `C = coker f` flat, then
`f ⊗ 𝟙_N : A ⊗ N → B ⊗ N` is injective.

In the 3×3 diagram with rows `• ⊗ K → • ⊗ F₀ → • ⊗ N → 0` (exact by
right-exactness of `⊗`) and columns `A ⊗ • → B ⊗ • → C ⊗ •`, an element
`x ∈ ker (A ⊗ N → B ⊗ N)` lifts to `y ∈ A ⊗ F₀`; its image `y' ∈ B ⊗ F₀`
dies in `B ⊗ N`, hence comes from `z ∈ B ⊗ K`; the image of `z` in `C ⊗ K`
dies in `C ⊗ F₀` (because `g ∘ f = 0`) and `C ⊗ K → C ⊗ F₀` is injective
(`C` flat, `ι` injective), so `z` comes from `w ∈ A ⊗ K`; correcting `y` by
`w` gives an element of `ker (A ⊗ F₀ → B ⊗ F₀) = 0` (`F₀` flat), so
`y = ι w` and `x = π (ι w) = 0`. -/
private theorem Module.Flat.rTensor_injective_of_exact_aux
    {R : Type*} [CommRing R] {A B C K F₀ N : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup K] [AddCommGroup F₀] [AddCommGroup N]
    [Module R A] [Module R B] [Module R C]
    [Module R K] [Module R F₀] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (ι : K →ₗ[R] F₀) (π : F₀ →ₗ[R] N)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hC : Module.Flat R C)
    (hF₀ : Module.Flat R F₀)
    (hι : Function.Injective ι) (hexact : Function.Exact ι π)
    (hπ : Function.Surjective π) :
    Function.Injective (f.rTensor N) := by
  -- rows: right-exactness of `• ⊗`
  have rowB : Function.Exact (ι.lTensor B) (π.lTensor B) :=
    _root_.lTensor_exact B hexact hπ
  have hπA : Function.Surjective (π.lTensor A) := LinearMap.lTensor_surjective A hπ
  -- columns: right-exactness of `⊗ K`, flat injectivity for `C ⊗ •`, `• ⊗ F₀`
  have colK : Function.Exact (f.rTensor K) (g.rTensor K) :=
    _root_.rTensor_exact K hfg hg
  have hCι : Function.Injective (ι.lTensor C) :=
    haveI := hC
    Module.Flat.lTensor_preserves_injective_linearMap (M := C) ι hι
  have hfF₀ : Function.Injective (f.rTensor F₀) :=
    haveI := hF₀
    Module.Flat.rTensor_preserves_injective_linearMap (M := F₀) f hf
  -- the chase
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hπA x
  -- the middle image `f ⊗ F₀ (y)` dies in `B ⊗ N`
  have comm1 : (π.lTensor B).comp (f.rTensor F₀) = (f.rTensor N).comp (π.lTensor A) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have h1 : (π.lTensor B) ((f.rTensor F₀) y) = 0 := by
    have e := LinearMap.congr_fun comm1 y
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
    rw [e, hx]
  -- so it comes from `z ∈ B ⊗ K`
  obtain ⟨z, hz⟩ := (rowB _).mp h1
  -- the image of `z` in `C ⊗ K` vanishes (`C` flat kills it in `C ⊗ F₀`)
  have comm2 : (g.rTensor F₀).comp (ι.lTensor B) =
      (ι.lTensor C).comp (g.rTensor K) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hgf : (g.rTensor F₀).comp (f.rTensor F₀) = 0 := by
    rw [← LinearMap.rTensor_comp, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero]
  have h2 : (ι.lTensor C) ((g.rTensor K) z) = 0 := by
    have e := LinearMap.congr_fun comm2 z
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
    rw [← e, hz]
    have e' := LinearMap.congr_fun hgf y
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at e'
  have h3 : (g.rTensor K) z = 0 :=
    (injective_iff_map_eq_zero _).mp hCι _ h2
  -- exactness of the `⊗ K` column: `z` comes from `w ∈ A ⊗ K`
  obtain ⟨w, hw⟩ := (colK z).mp h3
  -- correct `y` by `w`: the difference dies in `B ⊗ F₀`, hence vanishes
  have comm3 : (f.rTensor F₀).comp (ι.lTensor A) =
      (ι.lTensor B).comp (f.rTensor K) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have h4 : (f.rTensor F₀) (y - (ι.lTensor A) w) = 0 := by
    rw [map_sub]
    have e := LinearMap.congr_fun comm3 w
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
    rw [e, hw, hz, sub_self]
  have h5 : y = (ι.lTensor A) w := by
    have := (injective_iff_map_eq_zero _).mp hfF₀ _ h4
    rwa [sub_eq_zero] at this
  -- conclude: `x = π (ι w) = 0`
  have h6 : (π.lTensor A).comp (ι.lTensor A) = 0 := by
    rw [← LinearMap.lTensor_comp, hexact.linearMap_comp_eq_zero, LinearMap.lTensor_zero]
  rw [h5]
  have e := LinearMap.congr_fun h6 w
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at e

/-- **Stacks 00HL** (flat cokernel ⟹ tensoring preserves the kernel): if
`f : A → B` is injective, `g : B → C` is surjective, `(f, g)` is exact and
`C` is flat, then `f ⊗ 𝟙_N : A ⊗ N → B ⊗ N` is injective for every `N`.
Equivalently `Tor_1^R(C, N) = 0`, but the proof is Tor-free: instantiate the
3×3 chase `rTensor_injective_of_exact_aux` at the free presentation
`0 → ker π → (N →₀ R) —π→ N → 0` (`Finsupp.linearCombination` at `id`),
whose middle term is free, hence flat. -/
theorem Module.Flat.rTensor_injective_of_exact
    {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hC : Module.Flat R C)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective (f.rTensor N) := by
  classical
  exact Module.Flat.rTensor_injective_of_exact_aux
    (K := LinearMap.ker (Finsupp.linearCombination R (_root_.id : N → N)))
    (F₀ := (N →₀ R))
    (LinearMap.ker (Finsupp.linearCombination R (_root_.id : N → N))).subtype
    (Finsupp.linearCombination R (_root_.id : N → N))
    hf hfg hg hC inferInstance
    (Submodule.injective_subtype _)
    ((Finsupp.linearCombination R (_root_.id : N → N)).exact_subtype_ker_map)
    (Finsupp.linearCombination_id_surjective R N)

/-- **Stacks 00HL, left-tensor form**: if `f : A → B` is injective, `g : B → C` is
surjective, `(f, g)` is exact and `C` is flat, then `𝟙_N ⊗ f : N ⊗ A → N ⊗ B` is
injective for every `N`.  Conjugate of `Module.Flat.rTensor_injective_of_exact` by the
tensor commutativity isomorphism (`LinearMap.comm_comp_rTensor_comp_comm_eq`): the
left-tensored map factors as `comm ∘ (f.rTensor N) ∘ comm`, a composite of the injective
`f.rTensor N` with the two commutativity equivalences. -/
theorem Module.Flat.lTensor_injective_of_exact
    {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hC : Module.Flat R C)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) := by
  have hr : Function.Injective (f.rTensor N) :=
    Module.Flat.rTensor_injective_of_exact hf hfg hg hC N
  rw [← LinearMap.comm_comp_rTensor_comp_comm_eq f, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (TensorProduct.comm R B N).injective.comp
    (hr.comp (TensorProduct.comm R N A).injective)

namespace AlgebraicGeometry

namespace Scheme

/-! ## §2. The unit module is quasi-coherent -/

/-- **The unit module `𝒪_X` is quasi-coherent** (instance).  Witness: the
canonical one-generator/no-relation presentation
`LineBundle.unitPresentation` of `Picard/LineBundleCoherence.lean`. -/
instance Modules.unit_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (LineBundle.unitPresentation (R := X.ringCatSheaf)).isQuasicoherent

/-! ## §3. The kernel–pullback comparison map -/

/-- **The kernel–pullback comparison map** `g'^*(ker q) ⟶ ker (g'^* q)`
(the abstract `CategoryTheory.Limits.kernelComparison` at the module pullback
functor; the pullback preserves zero morphisms, being a left adjoint —
`Scheme.Modules.pullbackPushforwardAdjunction` — between abelian categories).
It is characterised by `κ ≫ ker(g'^*q).ι = g'^*(ker q .ι)`
(`kernelComparison_comp_ι`).  `Scheme.Modules.pullback_kernel_isLocallyTrivial`
(blueprint `lem:relative_divisor_base_change`) proves it is an isomorphism
when the cokernel of `ker q ⟶ E` is flat over the base of a cartesian
square. -/
noncomputable def Modules.pullbackKernelComparison
    {X' X : Scheme.{u}} (g' : X' ⟶ X) {E F : X.Modules} (q : E ⟶ F) :
    (Scheme.Modules.pullback g').obj (Limits.kernel q) ⟶
      Limits.kernel ((Scheme.Modules.pullback g').map q) :=
  kernelComparison q (Scheme.Modules.pullback g')

@[reassoc (attr := simp)]
lemma Modules.pullbackKernelComparison_comp_ι
    {X' X : Scheme.{u}} (g' : X' ⟶ X) {E F : X.Modules} (q : E ⟶ F) :
    Modules.pullbackKernelComparison g' q ≫
        Limits.kernel.ι ((Scheme.Modules.pullback g').map q) =
      (Scheme.Modules.pullback g').map (Limits.kernel.ι q) :=
  kernelComparison_comp_ι q (Scheme.Modules.pullback g')

/-- **The kernel–pullback comparison is an epimorphism whenever `q` is an
epimorphism.**  This is the categorical (right-exact) half of the isomorphism
claim in `Scheme.Modules.pullback_kernel_isLocallyTrivial`: the module pullback
`g'^*` is a left adjoint
(`Scheme.Modules.pullbackPushforwardAdjunction`), hence preserves cokernels, so
applied to the short exact sequence `0 → ker q → E → F → 0` (`q` epi, so `F` is
the cokernel of `ker q ↪ E`) it stays right exact: `g'^*(ker q) → g'^*E →
g'^*F → 0` is exact.  Exactness at `g'^*E` says precisely that the kernel lift
`g'^*(ker q) → ker (g'^* q)` — which is `pullbackKernelComparison g' q` — is an
epimorphism.  (The remaining monomorphism half is the genuine flat-base-change
content, requiring `F` flat over the base, and is handled in
`pullback_kernel_isLocallyTrivial`.) -/
lemma Modules.epi_pullbackKernelComparison
    {X' X : Scheme.{u}} (g' : X' ⟶ X) {E F : X.Modules} (q : E ⟶ F) [Epi q] :
    Epi (Modules.pullbackKernelComparison g' q) := by
  haveI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g') :=
    (Scheme.Modules.pullbackPushforwardAdjunction g').leftAdjoint_preservesColimits
  have hSG := (CategoryTheory.ShortComplex.exact_kernel q).map_of_epi_of_preservesCokernel
    (Scheme.Modules.pullback g') ‹Epi q› inferInstance
  exact hSG.epi_kernelLift

/-- **Basis-local criterion for monomorphisms of `𝒪_X`-modules.**  If `B` is a basis of
opens of `X` and `φ : M ⟶ N` is injective on sections over every basic open `B i`, then
`φ` is a monomorphism.  Companion of the basis-local iso criterion
`Modules.isIso_of_isIso_app_of_isBasis` (`AlgebraicJacobian.Cohomology.FlatBaseChange`):
basis injectivity gives stalkwise injectivity
(`TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis`), hence the underlying morphism of
sheaves of abelian groups is a monomorphism (`TopCat.Presheaf.mono_of_stalk_mono`), and the
faithful forgetful functor `Scheme.Modules.toPresheaf` reflects it. -/
theorem Modules.mono_of_injective_app_of_isBasis {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type*} {B : ι → X.Opens} (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (φ : M ⟶ N) (h : ∀ i, Function.Injective (φ.app (B i))) : Mono φ := by
  have happ : ∀ U ∈ Set.range B,
      Function.Injective (((Scheme.Modules.toPresheaf X).map φ).app (Opposite.op U)) := by
    rintro U ⟨i, rfl⟩; exact h i
  have hstalk : ∀ x : X, Function.Injective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map ((Scheme.Modules.toPresheaf X).map φ)) :=
    fun x => TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB happ x
  let MS : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let NS : TopCat.Sheaf Ab.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let fS : MS ⟶ NS := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  haveI : ∀ x, Mono ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fS.1) := fun x =>
    (AddCommGrpCat.mono_iff_injective _).mpr (hstalk x)
  haveI hmS : Mono fS := TopCat.Presheaf.mono_of_stalk_mono fS
  haveI : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ fS).mp hmS
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map ‹_›

/-- **The kernel–pullback comparison is an isomorphism as soon as `g'^*` keeps
the kernel inclusion `ker q ↪ E` monic.**  Combining the always-available
epimorphism half (`epi_pullbackKernelComparison`, `q` epi) with the
monomorphism half, `X'.Modules` being abelian (hence balanced) upgrades
`pullbackKernelComparison g' q` to an isomorphism: `κ` is monic because
`κ ≫ ker(g'^*q).ι = g'^*(ker q .ι)` (`pullbackKernelComparison_comp_ι`) is monic
(the hypothesis, with `ker(g'^*q).ι` monic), and epi + mono ⟹ iso.

This isolates the *entire* remaining content of
`Scheme.Modules.pullback_kernel_isLocallyTrivial` into the single flat-base-change
fact `Mono (g'^*(ker q .ι))` — that the right-exact pullback preserves the
injection `ker q ↪ E` because the cokernel `F` is flat over the base
(Stacks 00HL, `Module.Flat.rTensor_injective_of_exact`, affine-locally through the
base-change section calculus). -/
lemma Modules.isIso_pullbackKernelComparison_of_mono
    {X' X : Scheme.{u}} (g' : X' ⟶ X) {E F : X.Modules} (q : E ⟶ F) [Epi q]
    (hmono : Mono ((Scheme.Modules.pullback g').map (Limits.kernel.ι q))) :
    IsIso (Modules.pullbackKernelComparison g' q) := by
  haveI := Modules.epi_pullbackKernelComparison g' q
  haveI : Mono (Modules.pullbackKernelComparison g' q ≫
      Limits.kernel.ι ((Scheme.Modules.pullback g').map q)) := by
    rw [Modules.pullbackKernelComparison_comp_ι]; exact hmono
  haveI : Mono (Modules.pullbackKernelComparison g' q) :=
    mono_of_mono _ (Limits.kernel.ι ((Scheme.Modules.pullback g').map q))
  exact isIso_of_mono_of_epi _

/-! ## §4. Shrinking a trivialising chart -/

namespace LineBundle

/-- **A trivialising chart restricts along any smaller open** (the Stacks
01HH chart chase of `IsLocallyTrivial.pullback`, specialised to the open
inclusion `V ≤ U`): if `M|_U ≅ 𝒪_U` and `V ≤ U`, then `M|_V ≅ 𝒪_V`.  The
witness is the `i1–i7` restriction/pullback chain along
`g := X.homOfLE hVU : V ⟶ U` — `g ≫ U.ι = V.ι`, so restriction to `V`
factors as pullback along `g` of the restriction to `U`, and the pullback of
the unit is the unit (`SheafOfModules.pullbackObjUnitToUnit`, an isomorphism
because `Opens.map g.base` is final). -/
lemma IsLocallyTrivial.trivialization_of_le {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (hVU : V ≤ U)
    (t : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    Nonempty (M.restrict V.ι ≅ SheafOfModules.unit (V : Scheme).ringCatSheaf) := by
  set g : (V : Scheme) ⟶ (U : Scheme) := X.homOfLE hVU with hg_def
  have hgι : g ≫ U.ι = V.ι := X.homOfLE_ι hVU
  haveI : (TopologicalSpace.Opens.map g.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  refine ⟨?_⟩
  -- 1: M.restrict V.ι ≅ (pullback V.ι).obj M
  let i1 := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M
  -- 2: ≅ (pullback (g ≫ U.ι)).obj M  (using V.ι = g ≫ U.ι)
  let i2 := (Scheme.Modules.pullbackCongr hgι.symm).app M
  -- 3: ≅ (pullback g).obj ((pullback U.ι).obj M)
  let i3 := ((Scheme.Modules.pullbackComp g U.ι).symm).app M
  -- 4: ≅ (pullback g).obj (unit_U)  (restrict back and trivialise)
  let i4 := (Scheme.Modules.pullback g).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ t)
  -- 5: ≅ unit_V  (pullback of the unit is the unit; iso since `Opens.map
  -- g.base` is final)
  let i5 := asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
  exact i1 ≪≫ i2 ≪≫ i3 ≪≫ i4 ≪≫ i5

/-- **Chart shrinking**: a locally trivial module has a trivialising *affine*
chart inside any open neighbourhood of any point.  Combines the defining
chart of `IsLocallyTrivial` with an affine shrink
(`exists_isAffineOpen_mem_and_subset`) and the restriction of the
trivialisation (`trivialization_of_le`). -/
lemma IsLocallyTrivial.exists_affine_trivializing_le
    {X : Scheme.{u}} {M : X.Modules} (hM : IsLocallyTrivial M)
    {x : X} {W : X.Opens} (hxW : x ∈ W) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧ V ≤ W ∧
      Nonempty (M.restrict V.ι ≅ SheafOfModules.unit (V : Scheme).ringCatSheaf) := by
  obtain ⟨U, hxU, hUaff, ⟨t⟩⟩ := hM x
  obtain ⟨V, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ W from ⟨hxU, hxW⟩)
  have hVUW : V ≤ U ⊓ W := hVle
  exact ⟨V, hxV, hVaff, hVUW.trans inf_le_right,
    IsLocallyTrivial.trivialization_of_le (hVUW.trans inf_le_left) t⟩

end LineBundle

end Scheme

end AlgebraicGeometry
