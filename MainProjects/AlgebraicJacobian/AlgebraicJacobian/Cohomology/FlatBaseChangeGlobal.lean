/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Std.Tactic.BVDecide.LRAT.Internal.Clause
import AlgebraicJacobian.Cohomology.FlatBaseChange

/-!
# Flat base change for the pushforward, global (`H⁰`-as-equalizer) chain

This file builds the global ("FBC-B") leg of the `i = 0` flat-base-change package:
`H⁰(X, F) = Γ(X, F)` of a quasi-compact, quasi-separated scheme is the equalizer of
a *finite* affine cover, and flat base change commutes with that finite equalizer.

It is the companion of `AlgebraicJacobian.Cohomology.FlatBaseChange`, which it imports
read-only (using the affine global-sections comparison as a per-term black box).

**Provenance / scope.** This is the SORRY-FREE prefix salvaged (2026-06-24) from the
paused `FBC-B_SNAP-chain` subproject's `FlatBaseChangeGlobal.lean`. It contains the
reusable foundation only — the finite-cover equalizer presentation
(`gammaTopEquivEqLocus`), the base-changed equalizer comparison via Mathlib's
`LinearMap.tensorEqLocusEquiv` (`baseChangeGammaEquiv`), and supporting restriction
plumbing (`rhoU`, `gammaResA`, `leftRes`/`rightRes`/`toCover`, `pullbackGroundRingAlg`).
The downstream `sorry`-bearing assembly of the paused subproject
(`baseChange_sheafConditionFork_tensorIso`, `flatBaseChange_pushforward_isIso_of_isSeparated`,
the Mayer–Vietoris/`gammaTensorComparison` chain) was intentionally NOT salvaged; it
remains preserved in the paused subproject's git history. These foundations are reusable
for the Čech route's `cechComplex_baseChange_iso` ("flatness commutes with the finite
equalizer").

See `blueprint/src/chapters/Cohomology_FlatBaseChange.tex` (FBC-B section).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — finite affine covers with quasi-compact overlaps -/

/-- A quasi-compact scheme admits a *finite* affine open cover; when it is moreover
quasi-separated, every pairwise intersection of cover members is quasi-compact.

Project-local: packages `isCompact_iff_finite_and_eq_biUnion_affineOpens` (finite affine
subcover of `⊤`) with `quasiSeparatedSpace_iff_forall_affineOpens` (quasi-compact overlaps)
into the single combinatorial input feeding the finite sheaf-condition equalizer of the
`H⁰` flat-base-change argument. -/
theorem Scheme.exists_finite_affineCover_inter_isQuasiCompact (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ s : Set X.affineOpens, s.Finite ∧ (⨆ i ∈ s, (i : X.Opens)) = ⊤ ∧
      ∀ U ∈ s, ∀ V ∈ s, IsCompact ((U : Set X) ∩ (V : Set X)) := by
  obtain ⟨s, hs, he⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
      (by simpa using isCompact_univ (X := ↥X))
  refine ⟨s, hs, he.symm, ?_⟩
  intro U _ V _
  exact quasiSeparatedSpace_iff_forall_affineOpens.mp ‹_› U V

/-! ## Project-local Mathlib supplement — the global sections as a sheaf-condition equalizer -/

open TopCat.Presheaf SheafConditionEqualizerProducts in
/-- For `M : X.Modules` and any open cover `U : ι → X.Opens`, the sheaf-condition fork
of the underlying abelian-group presheaf of `M` is a limit (an equalizer of products):
```
Γ(M, ⨆ i, U i) ⟶ ∏ i, Γ(M, U i) ⇉ ∏ (i,j), Γ(M, U i ⊓ U j).
```
This is the equalizer-products form of the sheaf condition specialised to the abelian
presheaf `M.presheaf` of a sheaf of `𝒪_X`-modules. Combined with the finite affine cover
of `Scheme.exists_finite_affineCover_inter_isQuasiCompact` it computes `Γ(X, M) = Γ(M, ⊤)`
as a *finite* equalizer; that finiteness is what the flat-base-change argument needs to
commute `- ⊗_A B` past the equalizer.

Project-local: packages `M.isSheaf` through Mathlib's
`isSheaf_iff_isSheafEqualizerProducts` at the level of `X.Modules`. -/
noncomputable def Modules.gammaIsLimitSheafConditionFork {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    IsLimit (fork M.presheaf U) :=
  ((isSheaf_iff_isSheafEqualizerProducts M.presheaf).mp M.isSheaf U).some

open TopCat.Presheaf SheafConditionEqualizerProducts in
/-! ## Project-local Mathlib supplement — global sections as an `A`-module `eqLocus`

This block presents `Γ(X, M)` of a sheaf of modules as a `LinearMap.eqLocus` of two
`A`-linear maps over the ground ring `A = Γ(X, ⊤)`, the shape required by
`LinearMap.tensorEqLocusEquiv` (flat base change preserves finite equalizers). Every
section over an open `U` is viewed as an `A`-module by restriction of scalars along the
structure-sheaf restriction `A → Γ(X, U)`, and the structure-sheaf restriction maps of
`M` become `A`-linear maps between these. -/

/-- The ground ring `A = Γ(X, ⊤)` of a scheme, as a `CommRing` (taken from the
`CommRingCat`-valued structure presheaf so the `CommRing`/`Algebra` instances resolve). -/
abbrev groundRing (X : Scheme.{u}) : Type u := X.presheaf.obj (Opposite.op (⊤ : X.Opens))

/-- The structure-sheaf restriction ring hom `A = Γ(X, ⊤) → Γ(X, U)`. Project-local:
the `A`-algebra structure on the sections over `U` used to view them as `A`-modules. -/
noncomputable def rhoU (X : Scheme.{u}) (U : X.Opens) :
    groundRing X →+* (X.ringCatSheaf.obj.obj (Opposite.op U)) :=
  (X.ringCatSheaf.obj.map (homOfLE (le_top)).op).hom

/-- The sections `Γ(M, U)` of a sheaf of modules over an open `U`, regarded as an
`A`-module (`A = Γ(X, ⊤)`) by restriction of scalars along `rhoU`. Project-local: the
common `A`-module home for the global-sections equalizer presentation. -/
noncomputable abbrev gammaModA {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    ModuleCat (groundRing X) :=
  (ModuleCat.restrictScalars (rhoU X U)).obj (M.val.obj (Opposite.op U))

/-- Restriction-of-scalars transitivity: `(Γ(X,U) → Γ(X,V)) ∘ (A → Γ(X,U)) = (A → Γ(X,V))`.
Project-local glue making the structure-sheaf restriction maps `A`-linear. -/
theorem rhoU_comp {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    ((X.ringCatSheaf.obj.map (homOfLE h).op).hom).comp (rhoU X U) = rhoU X V := by
  ext a
  change (X.ringCatSheaf.obj.map (homOfLE h).op).hom (rhoU X U a) = rhoU X V a
  have e : (X.ringCatSheaf.obj.map (homOfLE (le_top) : V ⟶ ⊤).op)
      = (X.ringCatSheaf.obj.map (homOfLE (le_top) : U ⟶ ⊤).op)
          ≫ (X.ringCatSheaf.obj.map (homOfLE h).op) := by
    rw [← X.ringCatSheaf.obj.map_comp]; rfl
  simp only [rhoU, e, RingCat.hom_comp]; rfl

/-- The structure-sheaf restriction `Γ(M, U) → Γ(M, V)` (`V ≤ U`) as a morphism of
`A`-modules, built from `M.val.map` by restriction of scalars. -/
noncomputable def gammaResAHom {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    gammaModA M U ⟶ gammaModA M V :=
  (ModuleCat.restrictScalars (rhoU X U)).map (M.val.map (homOfLE h).op) ≫
    (ModuleCat.restrictScalarsComp'App (rhoU X U)
        (X.ringCatSheaf.obj.map (homOfLE h).op).hom (rhoU X V)
        (rhoU_comp h).symm (M.val.obj (Opposite.op V))).inv

/-- The structure-sheaf restriction `Γ(M, U) → Γ(M, V)` (`V ≤ U`) as an `A`-linear map.
Project-local: the building block of the `leftRes`/`rightRes` legs of the equalizer. -/
noncomputable def gammaResA {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    gammaModA M U →ₗ[groundRing X] gammaModA M V := (gammaResAHom M h).hom

@[simp] theorem gammaResA_apply {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (x : gammaModA M U) :
    gammaResA M h x = (M.val.map (homOfLE h).op).hom x := by
  simp only [gammaResA, gammaResAHom, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalarsComp'App_inv_apply]

/-- Functoriality of the `A`-linear restriction maps. -/
theorem gammaResA_comp {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (h1 : V ≤ U)
    (h2 : W ≤ V) (x : gammaModA M U) :
    gammaResA M h2 (gammaResA M h1 x) = gammaResA M (h2.trans h1) x := by
  simp only [gammaResA_apply]
  change (M.presheaf.map (homOfLE h2).op) ((M.presheaf.map (homOfLE h1).op) x)
     = (M.presheaf.map (homOfLE (h2.trans h1)).op) x
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  congr 1

/-- The `leftRes` leg `∏ᵢ Γ(M,Uᵢ) → ∏ᵢⱼ Γ(M, Uᵢ ⊓ Uⱼ)` (restrict the `i`-th factor),
as an `A`-linear map. Project-local: the first leg of the sheaf-condition equalizer in the
`A`-module presentation. -/
noncomputable def leftRes {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (∀ i, gammaModA M (U i)) →ₗ[groundRing X] (∀ p : ι × ι, gammaModA M (U p.1 ⊓ U p.2)) :=
  LinearMap.pi (fun p => (gammaResA M (inf_le_left)).comp (LinearMap.proj p.1))

/-- The `rightRes` leg `∏ᵢ Γ(M,Uᵢ) → ∏ᵢⱼ Γ(M, Uᵢ ⊓ Uⱼ)` (restrict the `j`-th factor),
as an `A`-linear map. -/
noncomputable def rightRes {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (∀ i, gammaModA M (U i)) →ₗ[groundRing X] (∀ p : ι × ι, gammaModA M (U p.1 ⊓ U p.2)) :=
  LinearMap.pi (fun p => (gammaResA M (inf_le_right)).comp (LinearMap.proj p.2))

/-- The `A`-linear map `Γ(M, ⊤) → ∏ᵢ Γ(M, Uᵢ)` restricting a global section to the cover. -/
noncomputable def toCover {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    gammaModA M (⊤ : X.Opens) →ₗ[groundRing X] (∀ i, gammaModA M (U i)) :=
  LinearMap.pi (fun _ => gammaResA M le_top)

/-- The restriction of a global section to a cover is a compatible family: it lands in the
`eqLocus` of the two restriction legs. Project-local: the equalizer-membership feeding the
global-sections `eqLocus` presentation. -/
theorem leftRes_toCover {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (s : gammaModA M (⊤ : X.Opens)) :
    leftRes M U (toCover M U s) = rightRes M U (toCover M U s) := by
  funext p
  simp only [leftRes, rightRes, toCover, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, gammaResA_comp]

/-- The global-sections-to-compatible-families map corestricted to the `eqLocus`. -/
noncomputable def toCoverEqLocus {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    gammaModA M (⊤ : X.Opens) →ₗ[groundRing X] LinearMap.eqLocus (leftRes M U) (rightRes M U) :=
  (toCover M U).codRestrict _ (leftRes_toCover M U)

/-- **Global sections as an `A`-module equalizer.** For `M : X.Modules` and an open cover
`U` of `X` (`⨆ i, U i = ⊤`), the global sections `Γ(X, M) = Γ(M, ⊤)`, regarded as a module
over the ground ring `A = Γ(X, ⊤)`, are `A`-linearly isomorphic to the `eqLocus` of the two
restriction legs `leftRes`, `rightRes : ∏ᵢ Γ(M, Uᵢ) → ∏ᵢⱼ Γ(M, Uᵢ ⊓ Uⱼ)`.

Project-local: this is the `LinearMap.eqLocus` presentation of global sections over the
ground ring `A` that `LinearMap.tensorEqLocusEquiv` (flat base change preserves finite
equalizers) consumes for the `H⁰` flat-base-change argument. Injectivity is the separatedness
of the sheaf of modules (`TopCat.Sheaf.eq_of_locally_eq'`) and surjectivity is the gluing
axiom (`TopCat.Sheaf.existsUnique_gluing'`), both on the underlying `Ab`-sheaf `M.presheaf`. -/
noncomputable def gammaTopEquivEqLocus {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    gammaModA M (⊤ : X.Opens) ≃ₗ[groundRing X] LinearMap.eqLocus (leftRes M U) (rightRes M U) :=
  LinearEquiv.ofBijective (toCoverEqLocus M U)
    ⟨by
      intro s t hst
      have h := Subtype.ext_iff.mp hst
      refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
        U ⊤ (fun _ => homOfLE le_top) hU.ge _ _ ?_
      intro i
      have hi := congrFun h i
      simp only [toCoverEqLocus, LinearMap.codRestrict_apply, toCover, LinearMap.pi_apply,
        gammaResA_apply] at hi ⊢
      exact hi,
     by
      rintro ⟨sf, hsf⟩
      have hcompat : TopCat.Presheaf.IsCompatible M.presheaf U sf := by
        intro i j
        have h := congrFun hsf (i, j)
        simp only [leftRes, rightRes, LinearMap.pi_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, gammaResA_apply] at h ⊢
        exact h
      obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
        (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) U ⊤ (fun _ => homOfLE le_top) hU.ge sf hcompat
      refine ⟨s, ?_⟩
      apply Subtype.ext
      funext i
      have h := hs i
      simp only [toCoverEqLocus, LinearMap.codRestrict_apply, toCover, LinearMap.pi_apply,
        gammaResA_apply] at h ⊢
      exact h⟩

/-- **Flat base change commutes with the `H⁰` equalizer.** For `M : X.Modules`, a cover `U`
of `X` (`⨆ i, U i = ⊤`), and a flat `A`-algebra `B` (`A = Γ(X, ⊤)`), base changing the global
sections `Γ(X, M)` along `A → B` is the `eqLocus` of the base-changed restriction legs:
\[ B ⊗_A Γ(X, M) ≅ \operatorname{eqLocus}(B ⊗ \mathrm{leftRes},\ B ⊗ \mathrm{rightRes}). \]

Project-local: the composite of the equalizer presentation
`gammaTopEquivEqLocus` with `LinearMap.tensorEqLocusEquiv` (flatness commutes with the finite
equalizer). This is the module-level core that the `H⁰` flat-base-change reduction consumes:
the right-hand side is, by the same presentation applied to the base-changed sheaf, the global
sections of the pulled-back module over `B`. -/
noncomputable def baseChangeGammaEquiv {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (B : Type u) [CommRing B] [Algebra (groundRing X) B]
    [Module.Flat (groundRing X) B] :
    TensorProduct (groundRing X) B (gammaModA M (⊤ : X.Opens)) ≃ₗ[B]
      LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor B B (leftRes M U))
        (TensorProduct.AlgebraTensorModule.lTensor B B (rightRes M U)) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (gammaTopEquivEqLocus M U hU)) ≪≫ₗ
    LinearMap.tensorEqLocusEquiv B B (leftRes M U) (rightRes M U)

open scoped TensorProduct

namespace Modules

/-- Canonical algebra map `B → Γ(X', O)` for the base-change pullback `X' = X ×_{Spec A} Spec B`,
from the projection `X' ⟶ Spec B`. -/
noncomputable def pullbackGroundRingAlg {X : Scheme.{u}} (B : Type u) [CommRing B]
    [Algebra (groundRing X) B] :
    B →+* groundRing (pullback X.toSpecΓ
      (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))) :=
  ((pullback.snd X.toSpecΓ
      (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).appTop).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

end Modules

end AlgebraicGeometry
