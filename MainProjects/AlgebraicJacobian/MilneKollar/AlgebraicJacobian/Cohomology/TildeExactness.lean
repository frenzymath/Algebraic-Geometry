/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Exactness of the tilde functor (Stacks 01HV) — Route-P step P3

Project-local supplement feeding `AlgebraicGeometry.qcoh_kernel_qcoh`.

For `X = Spec R`, the tilde functor `~ : ModuleCat R ⥤ (Spec R).Modules`,
`M ↦ M^~`, is exact.  The named target of this file is
`AlgebraicGeometry.tildePreservesFiniteLimits : PreservesFiniteLimits (tilde.functor R)`
(the *left*-exactness / kernel-preservation half).

## What is delivered (axiom-clean)

* `tilde_preservesFiniteColimits` — the *right*-exactness half: `~` is a left adjoint
  (`AlgebraicGeometry.tilde.adjunction`), hence preserves all colimits, in particular finite
  colimits.  This is one of the two halves of exactness.
* `tilde_toStalk_map_injective` — the *flatness core* in the only publicly-accessible form:
  for an injective `R`-module map `f : M ⟶ N`, the localised stalk map
  `M_𝔭 →ₗ[R] N_𝔭` (built from Mathlib's `IsLocalizedModule (tilde.toStalk · x)` instances) is
  injective.  This is the algebraic content that "localisation `R → R_𝔭` is flat" contributes
  to mono-preservation.

## What is delivered (axiom-clean), continued

* `tilde_stalkFunctor_map_toStalk` — the **germ-naturality** transport identity (the crux flagged
  by the planner).  For `f : M ⟶ N` and a point `x ↔ 𝔭`, the `Ab`-valued stalk map of `~f`
  (computed through the faithful, limit-preserving `Scheme.Modules.toPresheaf`) intertwines the two
  localisation maps `tilde.toStalk`: `toStalk M x ≫ (Ab-stalk map) = f ≫ toStalk N x`.  This
  identifies the otherwise opaque `Ab`-germ-induced stalk map with the localised module map of `f`
  on the image of `toStalk`.  Proven on the public `Ab`-stalk path (`stalkFunctor_map_germ_apply` +
  the `⊤`-section naturality `StructureSheaf.comapₗ_const`), avoiding the module-private handles.
* `tildePreservesFiniteLimits_of_toPresheaf` — the **categorical reduction**: since
  `Scheme.Modules.toPresheaf` reflects finite limits (faithful + preserves limits + reflects isos,
  and `(Spec R).Modules` has finite limits), `~` preserves finite limits as soon as the composite
  `~ ⋙ toPresheaf` does.  This is `Limits.preservesFiniteLimits_of_reflects_of_preserves`.

## `tildePreservesFiniteLimits` is CLOSED (run 0068)

The named target of this file is proved, and **not** by the stalk route this header used to
prescribe.  §2 does it over **basic opens** instead:

* basic opens are a basis of `Spec R` (`PrimeSpectrum.isBasis_basic_opens`), and over `D(r)` the
  sections of `M^~` are, *in Mathlib already*, a localisation of `M` at the powers of `r` —
  `AlgebraicGeometry.tilde.toOpen` carries an `IsLocalizedModule.Away` instance;
* so the section map of `~f` over `D(r)` **is** `IsLocalizedModule.map` of `f` (`sectMapₗ_eq`, by
  `IsLocalizedModule.ext` against the naturality square `tilde.toOpen_map_app`), and it is
  injective because localisation is flat (`IsLocalizedModule.map_injective`);
* basis injectivity gives stalkwise injectivity, hence mono, which `toPresheaf` reflects —
  `tilde_preservesMonomorphisms`;
* right exactness is free (left adjoint), and for an additive functor between abelian categories
  right exact + mono-preserving ⟹ left exact — `tildePreservesFiniteLimits`, with
  `tilde_preservesHomology` for the two halves together.

Two things the earlier plan got wrong, recorded because they cost the estimate: the stalk
*colimit* was never needed (the basis check happens before any stalk is formed), and the
"jointly-reflecting stalk family" step does not appear at all.  The `Ab`-vs-`ModuleCat` privacy
problem the header worried about is likewise irrelevant on this route — the `R`-linearity that
matters is on *sections*, where `Scheme.Modules.Hom.app_smul` supplies it directly (`sectMapₗ`).

The §1 stalk material is retained: it is the same mathematics at a point, and
`stalkMapₗ_injective` is still the sharpest per-point statement.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-! ## Project-local Mathlib supplement — exactness of the tilde functor -/

/-- **Right-exactness of `~`.**  The tilde functor `~ : ModuleCat R ⥤ (Spec R).Modules`
preserves finite colimits: it is a left adjoint (`AlgebraicGeometry.tilde.adjunction`), so it
preserves all colimits.  Project-local because the packaged statement is what the
kernel/cokernel quasi-coherence argument (Stacks `lemma-kernel-cokernel-quasi-coherent`)
consumes alongside the (still open) finite-limit half. -/
theorem tilde_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (tilde.functor R) := inferInstance

/-- **Flatness core of mono-preservation for `~`.**  For an injective `R`-module map
`f : M ⟶ N` and a point `x ↔ 𝔭` of `Spec R`, the induced localised map on stalks
`M_𝔭 →ₗ[R] N_𝔭` — assembled from Mathlib's `IsLocalizedModule (tilde.toStalk · x).hom`
instances via `IsLocalizedModule.map` — is injective.  This is exactly the contribution of
"localisation `R → R_𝔭` is flat" to the statement that `~` preserves monomorphisms (Stacks
01HV, exactness of `~`).  Stated with the publicly-accessible stalk-localisation map
`AlgebraicGeometry.tilde.toStalk`, the only such handle exported by Mathlib. -/
theorem tilde_toStalk_map_injective {M N : ModuleCat R} (f : M ⟶ N)
    (hf : Function.Injective f.hom) (x : PrimeSpectrum.Top R) :
    Function.Injective (IsLocalizedModule.map x.asIdeal.primeCompl
      (AlgebraicGeometry.tilde.toStalk M x).hom (AlgebraicGeometry.tilde.toStalk N x).hom f.hom) :=
  IsLocalizedModule.map_injective _ _ _ _ hf

/-- **Reduction of the named target.**  `tildePreservesFiniteLimits` follows once `~` is shown to
preserve every kernel `parallelPair f 0`; all the ambient typeclass hypotheses of
`Functor.preservesFiniteLimits_of_preservesKernels` are already discharged for
`tilde.functor R` (it is additive, `ModuleCat R` and `(Spec R).Modules` have the requisite
finite (co)products / zero objects).  Recorded project-locally so the remaining obligation is a
single, sharply-stated hypothesis for the continuation lane. -/
theorem tilde_preservesFiniteLimits_of_preservesKernels
    (H : ∀ {M N : ModuleCat R} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (tilde.functor R)) :
    PreservesFiniteLimits (tilde.functor R) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- **Germ-naturality of the localisation map `toStalk`.**  For an `R`-module map
`f : M ⟶ N` and a point `x ↔ 𝔭` of `Spec R`, the `Ab`-valued stalk map of `~f` (computed via the
faithful, limit-preserving forgetful functor `Scheme.Modules.toPresheaf`) intertwines the two
localisation maps `tilde.toStalk`: precomposing with `toStalk M x` and postcomposing `f` agree.

This is the load-bearing transport identity for mono/kernel preservation of `~`: it identifies the
otherwise opaque `Ab`-germ-induced stalk map with the localised module map of `f`.  Project-local
because Mathlib only exports the localisation handles `tilde.toStalk` and `toOpenₗ` and the section
naturality `comapₗ_const`; the germ-level statement is assembled here. -/
theorem tilde_stalkFunctor_map_toStalk {M N : ModuleCat R} (f : M ⟶ N)
    (x : PrimeSpectrum.Top R) (m : M) :
    (TopCat.Presheaf.stalkFunctor _ x).map
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (tilde.map f))
        ((tilde.toStalk M x).hom m)
      = (tilde.toStalk N x).hom (f.hom m) := by
  change (TopCat.Presheaf.stalkFunctor _ x).map
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (tilde.map f))
        (TopCat.Presheaf.germ (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf ⊤ x
          (by trivial) (StructureSheaf.toOpenₗ R M ⊤ m))
      = TopCat.Presheaf.germ (AlgebraicGeometry.moduleStructurePresheaf R N).presheaf ⊤ x
          (by trivial) (StructureSheaf.toOpenₗ R N ⊤ (f.hom m))
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x True.intro
    ((Scheme.Modules.toPresheaf (Spec (.of R))).map (tilde.map f)) (StructureSheaf.toOpenₗ R M ⊤ m)]
  congr 1
  simp only [Scheme.Modules.toPresheaf_map, Scheme.Modules.mapPresheaf_app,
    Scheme.Modules.Hom.app]
  rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.toOpenₗ_eq_const]
  simp only [AlgebraicGeometry.tilde.map, AlgebraicGeometry.SpecModulesToSheafFullyFaithful,
    CategoryTheory.NatTrans.comp_app, AlgebraicGeometry.tilde.modulesSpecToSheafIso,
    ModuleCat.hom_comp]
  erw [StructureSheaf.comapₗ_const (hb := le_of_eq PrimeSpectrum.basicOpen_one.symm)]
  rfl

/-- **Reduction of `tildePreservesFiniteLimits` to the presheaf level.**  The forgetful functor
`Scheme.Modules.toPresheaf` from `𝒪_{Spec R}`-modules to presheaves of abelian groups is faithful,
preserves limits, and reflects isomorphisms; hence (since `(Spec R).Modules` has finite limits) it
reflects finite limits.  Therefore, to show `~` preserves finite limits it suffices to show the
composite `~ ⋙ toPresheaf` does.  This isolates the remaining obligation of
`lem:tilde_preserves_kernels` to a statement about the abelian-presheaf-valued composite, whose
stalks are computed by `tilde_stalkFunctor_map_toStalk`.  Project-local categorical glue (it refutes
the earlier-feared "no right-exact + mono ⟹ left-exact" obstruction: the reduction is purely
`preservesFiniteLimits_of_reflects_of_preserves`). -/
theorem tildePreservesFiniteLimits_of_toPresheaf
    (H : PreservesFiniteLimits
      (tilde.functor R ⋙ Scheme.Modules.toPresheaf (Spec (.of R)))) :
    PreservesFiniteLimits (tilde.functor R) :=
  haveI := H
  Limits.preservesFiniteLimits_of_reflects_of_preserves (tilde.functor R)
    (Scheme.Modules.toPresheaf (Spec (.of R)))

/-! ## Project-local Mathlib supplement — R-linear packaging of the Ab-stalk map -/

/-- **Germ–scalar compatibility (`R`-linearity of the germ map).**  For `s` a section of `M^~`
over `U` and `r : R`, the germ at `x` of `(algebraMap R Γ(O_X,U) r) • s` equals `r •` the germ of
`s` (the `R`-action on the stalk being the localisation one through `tilde.toStalk R x`).  This is
the section-level half of "the `Ab`-stalk map of `~f` is `R`-linear".  Project-local because the
linear germ `StructureSheaf.germₗ` is not exported (no `public`); it is rebuilt here from the public
`PresheafOfModules.germ_smul` and `StructureSheaf.algebraMap_germ_apply`. -/
theorem tilde_germ_algebraMap_smul {M : ModuleCat R} (U : (Spec (.of R)).Opens)
    (x : PrimeSpectrum.Top R) (hxU : x ∈ U) (r : R) (s : Γ(AlgebraicGeometry.tilde M, U)) :
    (ConcreteCategory.hom
        ((AlgebraicGeometry.tilde M).presheaf.germ U x hxU))
        ((algebraMap R Γ(Spec (.of R), U) r) • s)
      = r • (ConcreteCategory.hom
        ((AlgebraicGeometry.tilde M).presheaf.germ U x hxU)) s := by
  erw [PresheafOfModules.germ_smul, StructureSheaf.algebraMap_germ_apply]
  rfl

/-- **Sub-step (A): the `Ab`-stalk map `σ_x` is `R`-linear.**  The stalk-functor image
`σ_x := (stalkFunctor Ab x).map (toPresheaf.map (~f))` is a priori only an `Ab`-morphism between
the stalks; this packages it as the genuine `R`-linear map `M_𝔭 →ₗ[R] N_𝔭`.  Project-local: the
`ModuleCat R`-valued stalk functor for `SheafOfModules` is not exported (its building blocks
`stalkIsoₗ`/`toStalkₗ'` are private), so the linear structure is reconstructed here on the public
`Ab` stalk via germ-linearity. -/
noncomputable def stalkMapₗ {M N : ModuleCat R} (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    (AlgebraicGeometry.tilde M).presheaf.stalk x →ₗ[R]
      (AlgebraicGeometry.tilde N).presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor _ x).map
    ((Scheme.Modules.toPresheaf (Spec (.of R))).map (AlgebraicGeometry.tilde.map f))
  map_add' a b := map_add _ a b
  map_smul' r ζ := by
    dsimp only [RingHom.id_apply]
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (AlgebraicGeometry.tilde M).presheaf ζ
    rw [← tilde_germ_algebraMap_smul U x hxU r s]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (AlgebraicGeometry.tilde.map f)),
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (AlgebraicGeometry.tilde.map f))]
    rw [Scheme.Modules.toPresheaf_map, Scheme.Modules.mapPresheaf_app]
    simp only [Opposite.unop_op]
    erw [Scheme.Modules.Hom.app_smul, tilde_germ_algebraMap_smul U x hxU r]
    rfl

/-- **Identification of `σ_x` with the localised module map.**  The `R`-linear `Ab`-stalk map
`stalkMapₗ f x` is exactly the localisation `M_𝔭 →ₗ[R] N_𝔭` of `f`, i.e.
`IsLocalizedModule.map _ (toStalk M x) (toStalk N x) f`.  Both are `R`-linear and agree on the image
of the localisation map `tilde.toStalk M x` (by `tilde_stalkFunctor_map_toStalk`), so they coincide
by `IsLocalizedModule.ext`.  Project-local: it packages the otherwise opaque germ-induced stalk map
as the concrete localised map, whose flatness-injectivity is `tilde_toStalk_map_injective`. -/
theorem stalkMapₗ_eq {M N : ModuleCat R} (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    stalkMapₗ f x = IsLocalizedModule.map x.asIdeal.primeCompl
      (AlgebraicGeometry.tilde.toStalk M x).hom (AlgebraicGeometry.tilde.toStalk N x).hom
      f.hom := by
  apply IsLocalizedModule.ext x.asIdeal.primeCompl (AlgebraicGeometry.tilde.toStalk M x).hom
    (fun s => IsLocalizedModule.map_units (AlgebraicGeometry.tilde.toStalk N x).hom s)
  ext m
  change stalkMapₗ f x ((AlgebraicGeometry.tilde.toStalk M x).hom m) = _
  rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  exact tilde_stalkFunctor_map_toStalk f x m

/-- **Stalkwise injectivity of `~f` for a monomorphism `f`.**  For an injective `R`-module map
`f`, the `R`-linear `Ab`-stalk map `σ_x = stalkMapₗ f x` of `~f` is injective at every point `x`.
This is the stalkwise-flatness contribution to mono-preservation of `~`, now stated on the genuine
linear stalk map: it combines the identification `stalkMapₗ_eq` with the localisation injectivity
`tilde_toStalk_map_injective`.  Project-local stepping stone toward `tildePreservesFiniteLimits`. -/
theorem stalkMapₗ_injective {M N : ModuleCat R} (f : M ⟶ N) (hf : Function.Injective f.hom)
    (x : PrimeSpectrum.Top R) : Function.Injective (stalkMapₗ f x) := by
  rw [stalkMapₗ_eq]
  exact tilde_toStalk_map_injective f hf x

/-! ## §2. `tildePreservesFiniteLimits`, CLOSED — via basic opens rather than stalks

The plan sketched in the header above (upgrade the *stalk* maps to a jointly-reflecting family)
is not the cheapest route and is not the one taken.  Basic opens are already a basis of
`Spec R`, and over a basic open `D(r)` the sections of `M^~` are *by Mathlib* a localisation of
`M` at the powers of `r` (`AlgebraicGeometry.tilde.toOpen` carries an
`IsLocalizedModule.Away` instance).  So the whole argument is one basis-local injectivity check
whose content is `IsLocalizedModule.map_injective` — localisation is flat — with no stalk
colimit anywhere.  The stalk material of §1 is retained: it is the same mathematics at a point,
and `stalkMapₗ_injective` remains the sharpest per-point statement.

Three steps: package the section map as `R`-linear (`sectMapₗ`), identify it with the localised
map (`sectMapₗ_eq`, by `IsLocalizedModule.ext` — both agree after `toOpen`, which is the
localisation map), and conclude. -/

section BasicOpen

variable {M N : ModuleCat.{u} R}

/-- **The section map of `~f` over a basic open, as an `R`-linear map.**  `Scheme.Modules.Hom.app`
is `Γ(Spec R, D(r))`-linear; restricting scalars along `algebraMap R Γ(Spec R, D(r))` makes it
`R`-linear, which is what the localisation API needs.  Companion of the stalk-level `stalkMapₗ`;
project-local for the same reason (the `ModuleCat R`-valued section functor is not exported). -/
noncomputable def sectMapₗ (f : M ⟶ N) (r : R) :
    Γ((tilde.functor R).obj M, PrimeSpectrum.basicOpen r) →ₗ[R]
      Γ((tilde.functor R).obj N, PrimeSpectrum.basicOpen r) where
  toFun := (Scheme.Modules.Hom.app ((tilde.functor R).map f) (PrimeSpectrum.basicOpen r))
  map_add' a b := map_add _ a b
  map_smul' c x := by
    dsimp only [RingHom.id_apply]
    exact Scheme.Modules.Hom.app_smul ((tilde.functor R).map f)
      (U := PrimeSpectrum.basicOpen r)
      (algebraMap R Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r) c) x

/-- **The section map over `D(r)` IS the localisation of `f` at the powers of `r`.**  Both are
`R`-linear maps out of `Γ(M^~, D(r))`, which `tilde.toOpen M (D r)` exhibits as a localisation
of `M`; they agree after precomposition with `toOpen` — that is exactly the naturality square
`tilde.toOpen_map_app` — so `IsLocalizedModule.ext` identifies them.  Project-local; the
section-level analogue of `stalkMapₗ_eq`. -/
theorem sectMapₗ_eq (f : M ⟶ N) (r : R) :
    sectMapₗ f r = IsLocalizedModule.map (Submonoid.powers r)
      (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom f.hom := by
  apply IsLocalizedModule.ext (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    (fun s => IsLocalizedModule.map_units (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom s)
  ext x
  change sectMapₗ f r ((tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom x)
      = IsLocalizedModule.map (Submonoid.powers r)
        (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom f.hom
        ((tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom x)
  rw [IsLocalizedModule.map_apply]
  exact congrArg (fun (m : M ⟶ _) => m.hom x) (tilde.toOpen_map_app f (PrimeSpectrum.basicOpen r))

/-- **`~` is injective on sections over every basic open**, for an injective `f`: by
`sectMapₗ_eq` the section map is the localisation of `f` at the powers of `r`, and localisation
preserves injectivity (`IsLocalizedModule.map_injective` — this is flatness of `R → R_r`). -/
theorem tilde_injective_app_basicOpen (f : M ⟶ N) (hf : Function.Injective f.hom) (r : R) :
    Function.Injective
      (Scheme.Modules.Hom.app ((tilde.functor R).map f) (PrimeSpectrum.basicOpen r)) := by
  have hloc := sectMapₗ_eq f r
  have hinj : Function.Injective (IsLocalizedModule.map (Submonoid.powers r)
      (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom f.hom) :=
    IsLocalizedModule.map_injective _ _ _ _ hf
  rw [← hloc] at hinj
  exact hinj

end BasicOpen

set_option backward.isDefEq.respectTransparency false in
/-- **`~` preserves monomorphisms** (Stacks 01HV, the mono half of exactness of the tilde
functor).  Basic opens are a basis of `Spec R` (`PrimeSpectrum.isBasis_basic_opens`), over each
of them `~f` is the localisation of `f` (`tilde_injective_app_basicOpen`), so basis injectivity
gives stalkwise injectivity, hence monomorphy of the underlying `Ab`-sheaf morphism, which the
faithful `Scheme.Modules.toPresheaf` reflects. -/
theorem tilde_preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    haveI := hf
    have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp hf
    have happ : ∀ U ∈ Set.range (fun r : R => PrimeSpectrum.basicOpen r),
        Function.Injective ((((Scheme.Modules.toPresheaf (Spec (.of R))).map
          ((tilde.functor R).map f)).app (Opposite.op U))) := by
      rintro U ⟨r, rfl⟩
      exact tilde_injective_app_basicOpen f hinj r
    let MS : TopCat.Sheaf Ab.{u} (Spec (.of R)) :=
      ⟨((tilde.functor R).obj M).presheaf, ((tilde.functor R).obj M).isSheaf⟩
    let NS : TopCat.Sheaf Ab.{u} (Spec (.of R)) :=
      ⟨((tilde.functor R).obj N).presheaf, ((tilde.functor R).obj N).isSheaf⟩
    let fS : MS ⟶ NS :=
      ⟨(Scheme.Modules.toPresheaf (Spec (.of R))).map ((tilde.functor R).map f)⟩
    haveI : ∀ x, Mono ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fS.1) := fun x =>
      (AddCommGrpCat.mono_iff_injective _).mpr
        (TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
          PrimeSpectrum.isBasis_basic_opens happ x)
    haveI hmS : Mono fS := TopCat.Presheaf.mono_of_stalk_mono fS
    haveI : Mono ((Scheme.Modules.toPresheaf (Spec (.of R))).map ((tilde.functor R).map f)) :=
      (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ fS).mp hmS
    exact (Scheme.Modules.toPresheaf (Spec (.of R))).mono_of_mono_map ‹_›

/-- **`~` is left exact** (Stacks 01HV; blueprint `lem:tilde_preserves_kernels`) — the named
target of this file, CLOSED.  `~` is additive and right exact (`tilde_preservesFiniteColimits`,
being a left adjoint) and preserves monomorphisms (`tilde_preservesMonomorphisms`); for an
additive functor between abelian categories those two force left exactness. -/
theorem tildePreservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) := by
  haveI := tilde_preservesMonomorphisms (R := R)
  rw [(tilde.functor R).preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro T hT
  have := hT.mono_f
  exact ⟨hT.exact.map_of_epi_of_preservesCokernel _ hT.epi_g inferInstance, inferInstance⟩

/-- **`~` is exact** (Stacks 01HV), both halves together. -/
theorem tilde_preservesHomology : (tilde.functor R).PreservesHomology :=
  haveI := tildePreservesFiniteLimits (R := R)
  Functor.preservesHomologyOfExact _

end AlgebraicGeometry
