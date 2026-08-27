/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.AffineDegreeOneVanishing
import AlgebraicJacobian.RiemannRoch.Adelic.GenusUnconditional
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Picard.RigidPushforward

/-!
# Degree-one affine vanishing for quasi-coherent modules and Čech cover-independence

The wave-5 keystone of the B3 lane: the degree-one affine vanishing
`H¹(U, M) = 0` (`HModule'`-form) for every affine open `U` and every
**quasi-coherent** sheaf of modules `M` on a `Spec k`-scheme, and the resulting
Čech **cover-independence** of `Ȟ¹`-vanishing on 2-affine covers.

## The bridge

The `HModule'` derived-functor machinery
(`Cohomology/StructureSheafModuleK/*`, `RiemannRoch/Adelic/GenusUnconditional`)
runs on sheaves of `k`-modules on the opens site; the B3 consumers work with
`X.Modules` (sheaves of `𝒪_X`-modules).  `toModuleKSheafOfModules` is the
dialect bridge: the underlying additive sheaf of `M : C.left.Modules`, with the
`k`-action restricted along the structure morphism (mirroring `toModuleKSheaf`
for the structure sheaf itself).  Sections, restriction maps and hence all
Čech difference maps agree **definitionally** with those of `M`.

## The vanishing

`subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent` mirrors the
structure-sheaf proof `subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen`
(`AffineDegreeOneVanishing.lean`) step by step; the single 𝒪-specific brick —
sections of the kernel over the basic opens `D(g_σ)` are the localisations
`Γ(M, U)_{g_σ}` — is replaced by the quasi-coherence keystone
`Scheme.Modules.isLocalizedModule_basicOpen` (Stacks 01HV(4)/01I8 at
affine-open generality, `Picard/QuotScheme.lean`), packaged here as the module
section-identification kit `IsAffineOpen.dCoeffModuleSectionsLinearEquiv`
(mirroring `IsAffineOpen.dCoeffSectionsLinearEquiv` of
`CechCoboundarySplitting.lean`).

## Cover-independence

With degree-1 vanishing on the two affine pieces of **every** 2-affine cover
`S`, the Mayer–Vietoris `(0,1)`-slice
(`AffineCoverMVSquare.hModuleOneEquivH1CokOfSubsingleton`,
`GenusUnconditional.lean`) identifies the concrete two-chart Čech cokernel
`S.H1Cok` with the cover-free `HModule k _ 1` — for every `S` at once.
Composing two such identifications makes `Ȟ¹`-vanishing (equivalently,
surjectivity of the difference-of-restrictions map) independent of the chosen
cover (`AffineCoverMVSquare.surjective_moduleSectionDiff_of_surjective`), and
the fibre wrapper `Scheme.Hom.FiberH1Vanishing.surjective_moduleSectionDiff`
turns the ∃-form `FiberH1Vanishing` hypothesis of the pinned B3 statement into
the surjectivity witness on any prescribed cover of the fibre curve — the
`hindep` obligation of
`fiberH1Vanishing_pushforward_finiteMapToP1BaseChange_of_coverIndependence`
(`Picard/RigidPushforwardTransfer.lean`).

Sources: Stacks 01XB (degree 1), 01EW (the Čech splitting), 01HV(4)/01I8
(quasi-coherent sections localise); Hartshorne III.2.7, III.4.5; Leray's
theorem for 2-covers with `H¹`-acyclic pieces.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k]

/-! ## The dialect bridge: the sheaf of `k`-modules underlying an `𝒪`-module

For a `Spec k`-scheme `C` and `M : C.left.Modules`, the sections `Γ(M, U)` are
modules over `Γ(C.left, U)`, hence `k`-modules by restriction along the
structure-morphism algebra map `k → Γ(C.left, U)`
(`toModuleKSheaf.algebraSection`).  Restriction maps are `k`-linear because
they are semilinear over the (algebra-map-preserving) ring restrictions.  This
mirrors `toModuleKPresheaf`/`toModuleKSheaf` with the structure sheaf replaced
by `M`. -/

/-- The `k`-module structure on the sections of a sheaf of modules on a
`Spec k`-scheme: restriction of the native `Γ(C.left, U)`-module structure
along the structure-morphism algebra map.  A `@[reducible] def` registered as
a local instance in this file (mirrors the discipline of
`Scheme.Hom.fiberSectionsModule`). -/
@[reducible] noncomputable def moduleKSections (C : Over (Spec (CommRingCat.of k)))
    (M : C.left.Modules) (U : TopologicalSpace.Opens C.left.toTopCat) :
    Module k Γ(M, U) :=
  Module.compHom _ (algebraMap k Γ(C.left, U))

attribute [local instance] moduleKSections

/-- The native `Γ(C.left, W)`-scalar action on `Γ(M, W)`, packaged as a
function whose binders carry the section-notation types (so that the `•`
elaborates against the `Γ`-spelled `Module` instance regardless of the
spelling of the argument terms). -/
private noncomputable def smulSection (C : Over (Spec (CommRingCat.of k))) (M : C.left.Modules)
    (W : TopologicalSpace.Opens C.left.toTopCat)
    (s : Γ(C.left, W)) (z : Γ(M, W)) : Γ(M, W) :=
  s • z

/-- The underlying additive presheaf of `M : C.left.Modules` as a presheaf of
`k`-modules (`toModuleKPresheaf` with the structure sheaf replaced by `M`):
objects are the section groups with the `moduleKSections` `k`-action, maps are
the restriction maps of `M`. -/
noncomputable def toModuleKPresheafOfModules (C : Over (Spec (CommRingCat.of k)))
    (M : C.left.Modules) :
    (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k Γ(M, U.unop)
  map {U V} f := ModuleCat.ofHom
    { toFun := fun x => M.presheaf.map f x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x =>
        (Scheme.Modules.map_smul M f.unop (algebraMap k Γ(C.left, U.unop) r) x).trans
          (congrArg
            (fun (s : Γ(C.left, V.unop)) =>
              smulSection C M V.unop s (M.presheaf.map (f.unop).op x))
            (AlgebraicGeometry.Scheme.toModuleKSheaf.algebraMap_naturality (C := C) f r)) }
  map_id U := by
    ext x
    simp only [ConcreteCategory.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk,
      ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    exact congrFun (congrArg (fun (φ : M.presheaf.obj U ⟶ M.presheaf.obj U) =>
      (ConcreteCategory.hom φ : _ → _)) (M.presheaf.map_id U)) x
  map_comp {U V W} f g := by
    ext x
    simp only [ConcreteCategory.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    exact congrFun (congrArg (fun (φ : M.presheaf.obj U ⟶ M.presheaf.obj W) =>
      (ConcreteCategory.hom φ : _ → _)) (M.presheaf.map_comp f g)) x

/-- The presheaf of `k`-modules of `toModuleKPresheafOfModules` is a sheaf:
its underlying type-valued presheaf is that of the (sheaf) `M`. -/
lemma toModuleKPresheafOfModules_isSheaf (C : Over (Spec (CommRingCat.of k)))
    (M : C.left.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology C.left.toTopCat)
      (toModuleKPresheafOfModules C M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget (ModuleCat.{u} k))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat.{u})).mp (Scheme.Modules.isSheaf M) using 1 <;> rfl

/-- **The dialect bridge**: a sheaf of `𝒪`-modules on a `Spec k`-scheme,
viewed as a sheaf of `k`-modules (`toModuleKSheaf` with the structure sheaf
replaced by `M`).  Sections and restriction maps agree definitionally with
those of `M`. -/
noncomputable def toModuleKSheafOfModules (C : Over (Spec (CommRingCat.of k)))
    (M : C.left.Modules) :
    Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k) :=
  ⟨toModuleKPresheafOfModules C M, toModuleKPresheafOfModules_isSheaf C M⟩

/-- Restriction maps of `toModuleKSheafOfModules C M` are the restriction maps
of `M` on elements.  Definitional. -/
lemma toModuleKSheafOfModules_obj_map_apply {C : Over (Spec (CommRingCat.of k))}
    (M : C.left.Modules) {V W : TopologicalSpace.Opens C.left.toTopCat} (h : W ≤ V)
    (x : (toModuleKSheafOfModules C M).obj.obj (Opposite.op V)) :
    ((toModuleKSheafOfModules C M).obj.map (homOfLE h).op).hom x
      = M.presheaf.map (homOfLE h).op x :=
  rfl

end AlgebraicGeometry.Scheme

/-! ## The quasi-coherent Čech section-identification kit

The module analogue of the structure-sheaf kit of
`CechCoboundarySplitting.lean` (`IsAffineOpen.dCoeffSectionsLinearEquiv` and
its `dCoface` compatibility): over an affine open `U`, the abstract localised
Čech coefficient `SectionCechModule.dCoeff g Γ(M, U) σ = Γ(M, U)_{g_σ}` of a
**quasi-coherent** `M : X.Modules` is `Γ(X, U)`-linearly the honest section
module `Γ(M, D(g_σ))`, with the Čech coface identified with the presheaf
restriction of `M`.  The quasi-coherence input is the gap2 keystone
`Scheme.Modules.isLocalizedModule_basicOpen` (Stacks 01HV(4)/01I8,
`Picard/QuotScheme.lean`).

The `Γ(X, U)`-module structure on `Γ(M, D(f))` is `Module.compHom` along the
canonical algebra map `Γ(X, U) → Γ(X, D(f))` (the presheaf restriction),
carried as a `letI` in each statement — the caller-supplied-instance
discipline of `restrictBasicOpenₗ`. -/

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {U : X.Opens}

/-- Double restriction of sections of a sheaf of modules collapses to the
single restriction (the `M.presheaf` analogue of
`map_homOfLE_map_homOfLE_apply`). -/
lemma Scheme.Modules.map_homOfLE_map_homOfLE_apply (M : X.Modules)
    {V W Z : X.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z) (z : Γ(M, Z)) :
    M.presheaf.map (homOfLE hVW).op (M.presheaf.map (homOfLE hWZ).op z)
      = M.presheaf.map (homOfLE (hVW.trans hWZ)).op z := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp, ← op_comp, homOfLE_comp]

/-- The presheaf restriction of `M` between nested basic-open section modules,
as a `Γ(X, U)`-linear map for the `compHom` module structures.  The module
analogue of `Scheme.basicOpenResAlgHom`. -/
noncomputable def Scheme.Modules.basicOpenResₗ (M : X.Modules) {f₁ f₂ : Γ(X, U)}
    (h : X.basicOpen f₂ ≤ X.basicOpen f₁) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f₁) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f₁))
    letI : Module Γ(X, U) Γ(M, X.basicOpen f₂) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f₂))
    Γ(M, X.basicOpen f₁) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f₂) :=
  letI : Module Γ(X, U) Γ(M, X.basicOpen f₁) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f₁))
  letI : Module Γ(X, U) Γ(M, X.basicOpen f₂) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f₂))
  { toFun := fun z => M.presheaf.map (homOfLE h).op z
    map_add' := fun z₁ z₂ => map_add _ z₁ z₂
    map_smul' := fun r z => by
      change M.presheaf.map (homOfLE h).op
            ((algebraMap Γ(X, U) Γ(X, X.basicOpen f₁) r) • z)
        = (algebraMap Γ(X, U) Γ(X, X.basicOpen f₂) r) •
            M.presheaf.map (homOfLE h).op z
      rw [Scheme.Modules.map_smul M (homOfLE h)
        (algebraMap Γ(X, U) Γ(X, X.basicOpen f₁) r) z]
      congr 1
      rw [Scheme.algebraMap_section_basicOpen, Scheme.algebraMap_section_basicOpen,
        ← CommRingCat.comp_apply, ← X.presheaf.map_comp, ← op_comp, homOfLE_comp] }

@[simp] lemma Scheme.Modules.basicOpenResₗ_apply (M : X.Modules) {f₁ f₂ : Γ(X, U)}
    (h : X.basicOpen f₂ ≤ X.basicOpen f₁) (z : Γ(M, X.basicOpen f₁)) :
    Scheme.Modules.basicOpenResₗ M h z = M.presheaf.map (homOfLE h).op z :=
  rfl

/-- **Čech coefficients of a quasi-coherent module are section modules**: over
an affine open `U`, the abstract Čech coefficient
`SectionCechModule.dCoeff g Γ(M, U) σ = Γ(M, U)_{g_σ}` of a quasi-coherent
`M : X.Modules` is `Γ(X, U)`-linearly the honest section module
`Γ(M, D(g_σ))`.  Sends `x/1` to the restriction of `x`
(`dCoeffModuleSectionsLinearEquiv_mk_one`) and intertwines the Čech coface
with the presheaf restriction of `M`
(`dCoeffModuleSectionsLinearEquiv_dCoface`).  This is the quasi-coherence
brick of the degree-one vanishing: the module analogue of
`IsAffineOpen.dCoeffSectionsLinearEquiv`, powered by the gap2 keystone
`Scheme.Modules.isLocalizedModule_basicOpen`. -/
noncomputable def IsAffineOpen.dCoeffModuleSectionsLinearEquiv (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type*} (g : ι → Γ(X, U))
    {m : ℕ} (σ : Fin m → ι) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ)))
    SectionCechModule.dCoeff g (Γ(M, U) : Type u) σ
      ≃ₗ[Γ(X, U)] Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
  letI : Module Γ(X, U) Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ)))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ))
      Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := Scheme.Modules.isLocalizedModule_basicOpen M hU (CechLocalized.sprod g σ)
  IsLocalizedModule.iso (Submonoid.powers (CechLocalized.sprod g σ))
    (Scheme.Modules.restrictBasicOpenₗ M (CechLocalized.sprod g σ))

/-- The quasi-coherent section identification sends the localisation structure
map `x ↦ x/1` to the presheaf restriction `Γ(M, U) → Γ(M, D(g_σ))`. -/
@[simp] lemma IsAffineOpen.dCoeffModuleSectionsLinearEquiv_mk_one (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type*} (g : ι → Γ(X, U))
    {m : ℕ} (σ : Fin m → ι) (x : Γ(M, U)) :
    hU.dCoeffModuleSectionsLinearEquiv M g σ (LocalizedModule.mk x 1)
      = M.presheaf.map
          (homOfLE (X.basicOpen_le (CechLocalized.sprod g σ))).op x := by
  letI : Module Γ(X, U) Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ)))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ))
      Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := Scheme.Modules.isLocalizedModule_basicOpen M hU (CechLocalized.sprod g σ)
  exact IsLocalizedModule.iso_mk_one _ _ x

/-- **Coface = restriction, quasi-coherent form**: under the section
identification `dCoeffModuleSectionsLinearEquiv`, the Čech coface
`dCoface : Γ(M, U)_{g_{σ∘dⱼ}} → Γ(M, U)_{g_σ}` is the presheaf restriction
`Γ(M, D(g_{σ∘dⱼ})) → Γ(M, D(g_σ))` of `M` along `D(g_σ) ⊆ D(g_{σ∘dⱼ})`. -/
lemma IsAffineOpen.dCoeffModuleSectionsLinearEquiv_dCoface (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type*} (g : ι → Γ(X, U))
    {m : ℕ} (σ : Fin (m + 1) → ι) (j : Fin (m + 1))
    (x : SectionCechModule.dCoeff g (Γ(M, U) : Type u) (σ ∘ j.succAbove)) :
    hU.dCoeffModuleSectionsLinearEquiv M g σ
        (SectionCechModule.dCoface g (Γ(M, U) : Type u) m σ j x)
      = M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
            (CechLocalized.sprod_succAbove_dvd g σ j))).op
          (hU.dCoeffModuleSectionsLinearEquiv M g (σ ∘ j.succAbove) x) := by
  letI : Module Γ(X, U) Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ)))
  letI : Module Γ(X, U) Γ(M, X.basicOpen (CechLocalized.sprod g (σ ∘ j.succAbove))) :=
    Module.compHom _
      (algebraMap Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g (σ ∘ j.succAbove))))
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g σ))
      Γ(M, X.basicOpen (CechLocalized.sprod g σ)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen (CechLocalized.sprod g (σ ∘ j.succAbove)))
      Γ(M, X.basicOpen (CechLocalized.sprod g (σ ∘ j.succAbove))) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI instσ := Scheme.Modules.isLocalizedModule_basicOpen M hU (CechLocalized.sprod g σ)
  haveI instτ := Scheme.Modules.isLocalizedModule_basicOpen M hU
    (CechLocalized.sprod g (σ ∘ j.succAbove))
  have hdvd := CechLocalized.sprod_succAbove_dvd g σ j
  have key : (hU.dCoeffModuleSectionsLinearEquiv M g σ).toLinearMap
        ∘ₗ SectionCechModule.dCoface g (Γ(M, U) : Type u) m σ j
      = (Scheme.Modules.basicOpenResₗ M (Scheme.basicOpen_le_basicOpen_of_dvd hdvd))
        ∘ₗ (hU.dCoeffModuleSectionsLinearEquiv M g (σ ∘ j.succAbove)).toLinearMap := by
    apply IsLocalizedModule.ext
      (Submonoid.powers (CechLocalized.sprod g (σ ∘ j.succAbove)))
      (LocalizedModule.mkLinearMap _ _)
      ((AwayComparison.Inverts.of_dvd hdvd
        (Scheme.Modules.restrictBasicOpenₗ M (CechLocalized.sprod g σ))).isUnit_powers)
    ext y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [show (LocalizedModule.mkLinearMap
          (Submonoid.powers (CechLocalized.sprod g (σ ∘ j.succAbove)))
          (Γ(M, U) : Type u)) y
        = LocalizedModule.mk y 1 from rfl]
    rw [show SectionCechModule.dCoface g (Γ(M, U) : Type u) m σ j (LocalizedModule.mk y 1)
        = LocalizedModule.mk y 1 from
      AwayComparison.comparison_apply
        (LocalizedModule.mkLinearMap
          (Submonoid.powers (CechLocalized.sprod g (σ ∘ j.succAbove))) (Γ(M, U) : Type u))
        (LocalizedModule.mkLinearMap
          (Submonoid.powers (CechLocalized.sprod g σ)) (Γ(M, U) : Type u))
        (AwayComparison.Inverts.of_dvd (CechLocalized.sprod_succAbove_dvd g σ j)
          (LocalizedModule.mkLinearMap
            (Submonoid.powers (CechLocalized.sprod g σ)) (Γ(M, U) : Type u)))
        y]
    rw [hU.dCoeffModuleSectionsLinearEquiv_mk_one M g σ y,
      hU.dCoeffModuleSectionsLinearEquiv_mk_one M g (σ ∘ j.succAbove) y,
      Scheme.Modules.basicOpenResₗ_apply]
    exact (Scheme.Modules.map_homOfLE_map_homOfLE_apply M _ _ y).symm
  exact DFunLike.congr_fun key x

end AlgebraicGeometry

/-! ## The geometric heart: section-level surjectivity onto the cokernel of an
injective embedding of a quasi-coherent module, over an affine open

Mirror of `IsAffineOpen.surjective_app_of_shortExact_toModuleKSheaf`
(`AffineDegreeOneVanishing.lean`) with the structure sheaf replaced by an
arbitrary quasi-coherent `M`: the single 𝒪-specific step — sections of the
kernel over the Čech basic opens are the localisations of `Γ(kernel, U)` — is
supplied by the quasi-coherent section-identification kit above. -/

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

variable (k) in
/-- **The geometric heart of the quasi-coherent degree-one affine vanishing**:
for a short exact sequence `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` of sheaves of `k`-modules
whose kernel is (the sheaf of `k`-modules underlying) a **quasi-coherent**
module `M` on a `Spec k`-scheme `C`, the section map `Γ(U, I) ⟶ Γ(U, Q)` is
surjective for every affine open `U ⊆ C.left`.

Blueprint (Serre; Stacks 01XB at degree 1, via the 01EW module complex): a
section `q` of `Q` over `U` lifts to `I` on a finite basic-open cover `D(gᵢ)`
of `U`; the differences of the lifts on overlaps come from sections `w_{ij}`
of the kernel; under the quasi-coherent section identification
(`dCoeffModuleSectionsLinearEquiv`, powered by the gap2 keystone
`isLocalizedModule_basicOpen`) these form a Čech 1-cocycle of the localised
module complex `∏_σ Γ(M, U)_{g_σ}`, which splits (Stacks 01EW,
`exists_dDiff_eq_of_dDiff_eq_zero` — the engine takes an *arbitrary*
`Γ(X, U)`-module, here `Γ(M, U)`).  Correcting the lifts by the splitting
makes them compatible; they glue in `I`, and the glued section maps to `q` by
separatedness of `Q`.

**Statement audit (QC-vanishing lane, wave 5, 2026-07-10): TRUE at stated
generality.**  Any `Spec k`-scheme `C`, any quasi-coherent `M` (this is the
honest generality of Stacks 01XB in degree 1: quasi-coherence is used exactly
once, for the localisation of kernel sections over the basic opens), any short
exact sequence with kernel `toModuleKSheafOfModules C M`, any affine open. -/
theorem IsAffineOpen.surjective_app_of_shortExact_toModuleKSheafOfModules
    {C : Over (Spec (CommRingCat.of k))} {M : C.left.Modules} [M.IsQuasicoherent]
    {I Q : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {f : toModuleKSheafOfModules C M ⟶ I} {p : I ⟶ Q} {w : f ≫ p = 0}
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
  -- canonical inclusions of the Čech overlap opens
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
      (y : (toModuleKSheafOfModules C M).obj.obj (Opposite.op V)),
      (p.hom.app (Opposite.op V)).hom ((f.hom.app (Opposite.op V)).hom y) = 0 := by
    intro V y
    have h0 : (f ≫ p).hom.app (Opposite.op V) = 0 := by rw [w]; rfl
    calc (p.hom.app (Opposite.op V)).hom ((f.hom.app (Opposite.op V)).hom y)
        = ((f ≫ p).hom.app (Opposite.op V)).hom y := rfl
      _ = (0 : (toModuleKSheafOfModules C M).obj.obj (Opposite.op V) ⟶
            Q.obj.obj (Opposite.op V)).hom y := by rw [h0]
      _ = 0 := rfl
  -- Step 5a: differences of the lifts come from the kernel (the module `M`)
  have hdiff : ∀ σ : Fin 2 → ι,
      ∃ wσ : (toModuleKSheafOfModules C M).obj.obj
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
          (M.presheaf.map (homOfLE hV).op (wsec τ'))
        = (I.obj.map (homOfLE (hV.trans (hle 1 τ' 1))).op).hom (ti (τ' 1))
          - (I.obj.map (homOfLE (hV.trans (hle 1 τ' 0))).op).hom (ti (τ' 0)) := by
    intro τ' V hV
    calc (f.hom.app (Opposite.op V)).hom
          (M.presheaf.map (homOfLE hV).op (wsec τ'))
        = (f.hom.app (Opposite.op V)).hom
            (((toModuleKSheafOfModules C M).obj.map (homOfLE hV).op).hom (wsec τ')) := rfl
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
  have hkey : ∀ τ : Fin 3 → ι,
      (∑ j : Fin 3, ((-1 : ℤ) ^ (j : ℕ) •
        M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
          (CechLocalized.sprod_succAbove_dvd gs τ j))).op
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
  have hcocycle : SectionCechModule.dDiff gs (Γ(M, U) : Type u) 2
      (fun σ => (hU.dCoeffModuleSectionsLinearEquiv M gs σ).symm (wsec σ)) = 0 := by
    funext τ
    apply (hU.dCoeffModuleSectionsLinearEquiv M gs τ).injective
    refine Eq.trans ?_ (map_zero _).symm
    have e1 : (hU.dCoeffModuleSectionsLinearEquiv M gs τ)
        (SectionCechModule.dDiff gs (Γ(M, U) : Type u) 2
          (fun σ => (hU.dCoeffModuleSectionsLinearEquiv M gs σ).symm (wsec σ)) τ)
        = ∑ j : Fin 3, ((-1 : ℤ) ^ (j : ℕ) •
            M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
              (CechLocalized.sprod_succAbove_dvd gs τ j))).op
              (wsec (τ ∘ j.succAbove))) := by
      rw [SectionCechModule.dDiff_apply, map_sum]
      exact Finset.sum_congr rfl fun (j : Fin 3) _ => by
        rw [map_zsmul, hU.dCoeffModuleSectionsLinearEquiv_dCoface,
          LinearEquiv.apply_symm_apply]
    exact e1.trans (hkey τ)
  -- Step 5c: split the cocycle (Stacks 01EW over the affine `U`)
  obtain ⟨tt, htt⟩ := hU.exists_dDiff_eq_of_dDiff_eq_zero gs hcov (Γ(M, U) : Type u) _ hcocycle
  -- the section-level splitting relation on each pair overlap
  have hrel : ∀ σ : Fin 2 → ι,
      M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
          (CechLocalized.sprod_succAbove_dvd gs σ 0))).op
          (hU.dCoeffModuleSectionsLinearEquiv M gs (σ ∘ (0 : Fin 2).succAbove)
            (tt (σ ∘ (0 : Fin 2).succAbove)))
        - M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
            (CechLocalized.sprod_succAbove_dvd gs σ 1))).op
            (hU.dCoeffModuleSectionsLinearEquiv M gs (σ ∘ (1 : Fin 2).succAbove)
              (tt (σ ∘ (1 : Fin 2).succAbove)))
        = wsec σ := by
    intro σ
    have h := congrFun htt σ
    rw [SectionCechModule.dDiff_one_apply] at h
    have h2 := congrArg (hU.dCoeffModuleSectionsLinearEquiv M gs σ) h
    rw [map_sub, hU.dCoeffModuleSectionsLinearEquiv_dCoface,
      hU.dCoeffModuleSectionsLinearEquiv_dCoface] at h2
    simpa only [LinearEquiv.apply_symm_apply] using h2
  -- transport of the section-read of `tt` along index equalities
  have htsec_congr : ∀ {τ τ' : Fin 1 → ι} (_ : τ = τ')
      {V : TopologicalSpace.Opens C.left.toTopCat}
      (hV : V ≤ C.left.basicOpen (CechLocalized.sprod gs τ))
      (hV' : V ≤ C.left.basicOpen (CechLocalized.sprod gs τ')),
      M.presheaf.map (homOfLE hV).op
          (hU.dCoeffModuleSectionsLinearEquiv M gs τ (tt τ))
        = M.presheaf.map (homOfLE hV').op
            (hU.dCoeffModuleSectionsLinearEquiv M gs τ' (tt τ')) := by
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
  let tsec : ∀ i : ι, (toModuleKSheafOfModules C M).obj.obj
      (Opposite.op (C.left.basicOpen (CechLocalized.sprod gs (fun _ : Fin 1 => i)))) :=
    fun i => hU.dCoeffModuleSectionsLinearEquiv M gs (fun _ : Fin 1 => i)
      (tt (fun _ : Fin 1 => i))
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
              (M.presheaf.map (homOfLE hOτ').op
                (hU.dCoeffModuleSectionsLinearEquiv M gs τ' (tt τ'))) := by
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
              (((toModuleKSheafOfModules C M).obj.map (homOfLE hO').op).hom (tsec a)) :=
          congrArg₂ (· - ·) (map_homOfLE_map_homOfLE_apply _ _ _ _)
            (NatTrans.app_hom_map_hom_apply f.hom _ _).symm
      _ = (I.obj.map (homOfLE (hO'.trans (hWle a))).op).hom (ti a)
          - (f.hom.app (Opposite.op O')).hom
              (M.presheaf.map (homOfLE hOτ').op
                (hU.dCoeffModuleSectionsLinearEquiv M gs τ' (tt τ'))) :=
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
          (M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
            (CechLocalized.sprod_succAbove_dvd gs ![i, j] 0))).op
            (hU.dCoeffModuleSectionsLinearEquiv M gs (![i, j] ∘ (0 : Fin 2).succAbove)
              (tt (![i, j] ∘ (0 : Fin 2).succAbove))))
        - (f.hom.app (Opposite.op (C.left.basicOpen
            (CechLocalized.sprod gs ![i, j])))).hom
            (M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
              (CechLocalized.sprod_succAbove_dvd gs ![i, j] 1))).op
              (hU.dCoeffModuleSectionsLinearEquiv M gs (![i, j] ∘ (1 : Fin 2).succAbove)
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
              (M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
                (CechLocalized.sprod_succAbove_dvd gs ![i, j] 1))).op
                (hU.dCoeffModuleSectionsLinearEquiv M gs (![i, j] ∘ (1 : Fin 2).succAbove)
                  (tt (![i, j] ∘ (1 : Fin 2).succAbove)))) := hL
      _ = (I.obj.map (homOfLE ((hOle i j _ hd0).trans (hWle j))).op).hom (ti j)
          - (f.hom.app (Opposite.op (C.left.basicOpen
              (CechLocalized.sprod gs ![i, j])))).hom
              (M.presheaf.map (homOfLE (Scheme.basicOpen_le_basicOpen_of_dvd
                (CechLocalized.sprod_succAbove_dvd gs ![i, j] 0))).op
                (hU.dCoeffModuleSectionsLinearEquiv M gs (![i, j] ∘ (0 : Fin 2).succAbove)
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

variable (k) in
/-- **Degree-one affine vanishing for quasi-coherent modules** (the wave-5
keystone; Stacks 01XB at degree 1, quasi-coherent coefficients): for a
`Spec k`-scheme `C`, a **quasi-coherent** `M : C.left.Modules`, and an
**affine** open `U` of `C.left`, the degree-one derived-functor cohomology of
the sheaf of `k`-modules underlying `M` vanishes:
`H¹(U, M) = HModule' k (toModuleKSheafOfModules C M) 1 U` is a subsingleton.

Assembled exactly as the structure-sheaf case
(`subsingleton_hModule'_one_toModuleKSheaf_of_isAffineOpen`): dimension shift
through an injective embedding `0 ⟶ M ⟶ I ⟶ Q ⟶ 0`
(`subsingleton_hModule'_one_of_surjective_app`), with the section-level
surjectivity supplied by
`IsAffineOpen.surjective_app_of_shortExact_toModuleKSheafOfModules`.

**Statement audit (QC-vanishing lane, wave 5, 2026-07-10): TRUE at stated
generality.**  Any `Spec k`-scheme, any quasi-coherent `M`, any affine open —
no properness/noetherian/invertibility hypotheses; this is the broadest form
the classical statement admits at degree 1 (for non-quasi-coherent sheaves it
is false: e.g. constant sheaves on a disconnected-fibre affine).  Universe:
the statement lives at `Abelian.Ext.{u}` (the `Type u` `HModule'` carrier),
as in the structure-sheaf case. -/
theorem subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent
    {C : Over (Spec (CommRingCat.of k))} (M : C.left.Modules) [M.IsQuasicoherent]
    {U : TopologicalSpace.Opens C.left.toTopCat} (hU : IsAffineOpen U) :
    Subsingleton (HModule' k (toModuleKSheafOfModules C M) 1 U) := by
  -- the canonical injective presentation of `M` as a sheaf of `k`-modules
  let S : ShortComplex (Sheaf (Opens.grothendieckTopology C.left.toTopCat)
      (ModuleCat.{u} k)) :=
    ShortComplex.mk _ _ (cokernel.condition (Injective.ι (toModuleKSheafOfModules C M)))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  haveI : Injective S.X₂ := Injective.injective_under (toModuleKSheafOfModules C M)
  exact subsingleton_hModule'_one_of_surjective_app k hS U
    (IsAffineOpen.surjective_app_of_shortExact_toModuleKSheafOfModules k hS hU)

/-! ## Čech cover-independence of `Ȟ¹`-vanishing for quasi-coherent modules

The every-cover comparison: with the degree-1 affine vanishing available on
the two pieces of **every** 2-affine cover `S`, the Mayer–Vietoris
`(0, 1)`-slice (`hModuleOneEquivH1CokOfSubsingleton`,
`GenusUnconditional.lean`) identifies each concrete Čech cokernel `S.H1Cok`
with the cover-free `HModule k _ 1`.  Composing two such identifications:
surjectivity of the difference-of-restrictions map on *some* cover forces it
on *every* cover. -/

/-- The Čech difference map of a 2-affine cover for the sheaf of `k`-modules
underlying `M` is the `X.Modules`-dialect difference map
(`AffineCoverMVSquare.moduleSectionDiff`, `Picard/RigidPushforward.lean`) on
elements.  Definitional. -/
lemma AffineCoverMVSquare.sectionDiff_toModuleKSheafOfModules_apply
    {C : Over (Spec (CommRingCat.of k))} (M : C.left.Modules)
    (S : C.left.AffineCoverMVSquare)
    (p : (toModuleKSheafOfModules C M).obj.obj (Opposite.op S.U₁)
      × (toModuleKSheafOfModules C M).obj.obj (Opposite.op S.U₂)) :
    S.sectionDiff (toModuleKSheafOfModules C M) p = S.moduleSectionDiff M p :=
  rfl

/-- Vanishing of the concrete Čech `Ȟ¹` of a sheaf of `k`-modules is
surjectivity of the difference-of-restrictions map (the
`Sheaf (ModuleCat k)`-dialect of
`AffineCoverMVSquare.subsingleton_moduleH1Cok_iff`). -/
lemma AffineCoverMVSquare.subsingleton_h1Cok_iff {X : Scheme.{u}}
    (S : X.AffineCoverMVSquare)
    (F : Sheaf (Opens.grothendieckTopology X.toTopCat) (ModuleCat.{u} k)) :
    Subsingleton (S.H1Cok F) ↔ Function.Surjective ⇑(S.sectionDiff F) := by
  rw [show Function.Surjective ⇑(S.sectionDiff F)
      ↔ LinearMap.range (S.sectionDiff F) = ⊤ from LinearMap.range_eq_top.symm]
  exact Submodule.Quotient.subsingleton_iff

/-- **Čech cover-independence of `Ȟ¹`-vanishing for quasi-coherent modules**
(the P2-interface obligation of the B3 lane, discharged): for a
quasi-coherent `M` on a `Spec k`-scheme, if the difference-of-restrictions
map of **some** 2-affine cover `V` is surjective, then it is surjective for
**every** 2-affine cover `W`.

Route (Leray for 2-covers with `H¹`-acyclic pieces, both ways): the degree-1
affine vanishing `subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent`
holds on the two pieces of *both* covers, so the Mayer–Vietoris `(0,1)`-slice
identifies both concrete Čech cokernels with the cover-free
`HModule k (toModuleKSheafOfModules C M) 1`:
`Ȟ¹(V) = 0 ⟺ H¹ = 0 ⟺ Ȟ¹(W) = 0`. -/
theorem AffineCoverMVSquare.surjective_moduleSectionDiff_of_surjective
    {C : Over (Spec (CommRingCat.of k))} (M : C.left.Modules) [M.IsQuasicoherent]
    {V : C.left.AffineCoverMVSquare}
    (h : Function.Surjective ⇑(V.moduleSectionDiff M))
    (W : C.left.AffineCoverMVSquare) :
    Function.Surjective ⇑(W.moduleSectionDiff M) := by
  set F := toModuleKSheafOfModules C M with hF
  -- the two Mayer–Vietoris identifications with the cover-free `H¹`
  have eV := V.hModuleOneEquivH1CokOfSubsingleton F
    (subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent k M V.isAffineOpen_U₁)
    (subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent k M V.isAffineOpen_U₂)
  have eW := W.hModuleOneEquivH1CokOfSubsingleton F
    (subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent k M W.isAffineOpen_U₁)
    (subsingleton_hModule'_one_of_isAffineOpen_of_isQuasicoherent k M W.isAffineOpen_U₂)
  -- surjectivity on `V` kills `Ȟ¹(V)`, hence `H¹`, hence `Ȟ¹(W)`
  have hV : Function.Surjective ⇑(V.sectionDiff F) := by
    intro c
    obtain ⟨p, hp⟩ := h c
    exact ⟨p, (V.sectionDiff_toModuleKSheafOfModules_apply M p).trans hp⟩
  haveI h1 : Subsingleton (V.H1Cok F) := (V.subsingleton_h1Cok_iff F).mpr hV
  haveI h2 : Subsingleton (HModule k F 1) := eV.toEquiv.subsingleton
  haveI h3 : Subsingleton (W.H1Cok F) := eW.symm.toEquiv.subsingleton
  have hW : Function.Surjective ⇑(W.sectionDiff F) := (W.subsingleton_h1Cok_iff F).mp h3
  intro c
  obtain ⟨p, hp⟩ := hW c
  exact ⟨p, (W.sectionDiff_toModuleKSheafOfModules_apply M p).symm.trans hp⟩

end AlgebraicGeometry.Scheme

/-! ## The fibre-curve wrapper: `FiberH1Vanishing` gives every-cover surjectivity

The consumer-facing form for the B3 `hH1` transfer: the ∃-form fibrewise
`h¹`-vanishing of the pinned B3 statements (`Scheme.Hom.FiberH1Vanishing`,
surjectivity on *some* 2-affine cover of the scheme-theoretic fibre) yields
the surjectivity witness on **any** prescribed 2-affine cover of the fibre —
the fibre `X_t` is a scheme over the residue field `κ(t)`, and the restricted
module `L_t` is quasi-coherent (pullback of quasi-coherent along the fibre
embedding, `pullback_isQuasicoherent_hom`). -/

namespace AlgebraicGeometry.Scheme

/-- The fibre restriction of a quasi-coherent module is quasi-coherent
(pullback along the fibre embedding; Stacks 01BG). -/
theorem Hom.fiberModule_isQuasicoherent {X S : Scheme.{u}} (q : X ⟶ S) (t : S)
    (L : X.Modules) [L.IsQuasicoherent] :
    (q.fiberModule t L).IsQuasicoherent :=
  pullback_isQuasicoherent_hom (q.fiberι t) L inferInstance

/-- **`FiberH1Vanishing` is cover-independent** (the `hindep` discharge shape):
for a quasi-coherent fibre restriction `L_t`, the ∃-form fibrewise
`h¹`-vanishing at `t` (surjective Čech difference map on *some* 2-affine cover
of the fibre `X_t`) yields the surjectivity witness on **every** 2-affine
cover `W` of `X_t`.  The fibre is a scheme over the residue field `κ(t)` via
`q.fiberToSpecResidueField t`, and quasi-coherent cover-independence
(`AffineCoverMVSquare.surjective_moduleSectionDiff_of_surjective`) applies
over that field. -/
theorem Hom.FiberH1Vanishing.surjective_moduleSectionDiff {X S : Scheme.{u}}
    {q : X ⟶ S} {L : X.Modules} {t : S}
    [(q.fiberModule t L).IsQuasicoherent]
    (h : q.FiberH1Vanishing L t) (W : (q.fiber t).AffineCoverMVSquare) :
    Function.Surjective ⇑(W.moduleSectionDiff (q.fiberModule t L)) := by
  obtain ⟨V, hV⟩ := h
  exact @AffineCoverMVSquare.surjective_moduleSectionDiff_of_surjective _ _
    (Over.mk (q.fiberToSpecResidueField t)) (q.fiberModule t L) ‹_› V hV W

end AlgebraicGeometry.Scheme
