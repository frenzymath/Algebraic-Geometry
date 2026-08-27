/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import AlgebraicJacobian.Cohomology.CechHigherDirectImage

/-!
# Presheaf-level Čech section complex (P3b)

This file contains the section Čech complex and the free-Yoneda equivalences:
- `sectionCechComplex`        — cosimplicial `Ab`-valued section Čech complex
                                (`\lean{AlgebraicGeometry.sectionCechComplex}`)
- `freeYonedaHomEquiv`        — Hom-set equivalence out of the free presheaf
                                (`\lean{AlgebraicGeometry.freeYonedaHomEquiv}`)
- `freeYonedaHomAddEquiv`     — additive version of the above
                                (`\lean{AlgebraicGeometry.freeYonedaHomAddEquiv}`)
- `injective_toPresheafOfModules` — injectivity transport to presheaves of modules
                                (`\lean{AlgebraicGeometry.injective_toPresheafOfModules}`)

Related machinery that has moved to sibling files:
- `cechFreePresheafComplex` / `cechFreeComplex_quasiIso` → `FreePresheafComplex.lean`
- `cechComplex_hom_identification` / `injective_cech_acyclic` → `CechBridge.lean`
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-
Planner strategy (P3b presheaf-Čech bridge; see analogies/p3b-presheafcech.md +
blueprint §Presheaf-level Čech machinery):

The goal is to prove that injective `O_X`-modules have trivial positive-degree Čech
cohomology with respect to any open cover.  The strategy avoids `presheafModules_
enoughInjectives` and `cech_delta_functor_presheaves` (decisions 4–5 in the analogy
file are expensive Mathlib gaps and are NOT on the critical path).  The build order is:

─────────────────────────────────────────────────────────────────────────────────
Step 1 — `sectionCechComplex`
─────────────────────────────────────────────────────────────────────────────────
Type: given a scheme `X`, an open cover `𝒰 : X.OpenCover`, an open `U : Opens ↥X`,
and a presheaf of modules `F : X.PresheafOfModules`, produce the section Čech
cochain complex

    Č•(𝒰, F, U) : CochainComplex (ModuleCat (X.ringCatSheaf.val.obj (op U))) ℕ

whose degree-`p` term is the product `∏_{(i₀,…,iₚ) : Fin (p+1) → 𝒰.J}
  F.obj (op (𝒰.U i₀ ⊓ … ⊓ 𝒰.U iₚ ⊓ U))`, equipped with the alternating restriction
differential.

THIS OBJECT IS DISTINCT from `CechComplex` in `CechHigherDirectImage.lean`:
`CechComplex` lives in `S.Modules` (pushforward along `f`) and is a relative complex.
`sectionCechComplex` is a plain cochain complex of `R`-modules where `R = O_X(U)`.

Key Mathlib hooks:
- `PresheafOfModules` — the category `X.PresheafOfModules =
  PresheafOfModules X.ringCatSheaf.val`.
- `PresheafOfModules.evaluation R (op V) : PresheafOfModules R ⥤ ModuleCat (R.obj (op V))`
  — the exact "sections over `V`" functor; use it to extract `F.obj (op V)`.
- `CochainComplex.of` or `HomologicalComplex.mk` — assemble the complex from
  degree-`p` objects and differentials.

─────────────────────────────────────────────────────────────────────────────────
Step 2 — `cechFreePresheafComplex`
─────────────────────────────────────────────────────────────────────────────────
Type: given `X` and `𝒰`, produce the chain complex of presheaves of modules

    K(𝒰)_• : ChainComplex X.PresheafOfModules ℕ

whose degree-`p` term is the direct sum `⨁_{(i₀,…,iₚ) : Fin (p+1) → 𝒰.J}
  (PresheafOfModules.free _).obj (yoneda.obj (𝒰.U i₀ ⊓ … ⊓ 𝒰.U iₚ))`.

DO NOT introduce a bespoke extension-by-zero functor `j_!`.  The blueprint's
`(j_{i₀…iₚ})_! (O_X|_{U_{i₀…iₚ}})` is canonically identified with
`(PresheafOfModules.free _).obj (yoneda.obj U_…)`: on sections over `V`, this is
the free `R(V)`-module on `Hom(V, U_…)` — which is `R(V)` when `V ⊆ U_…` and `0`
otherwise, matching extension-by-zero of `O_X|_{U_…}` exactly.

The differentials are `(PresheafOfModules.free _).map` of the representable maps
`yoneda.obj (U_{i₀⊓…⊓U_{iₚ₊₁}}) → yoneda.obj (U_{i₀⊓…⊓̂ᵢⱼ⊓…⊓U_{iₚ₊₁}})` induced
by the inclusion of opens `𝒰.U i₀ ⊓ … ⊓ 𝒰.U iₚ₊₁ ≤ 𝒰.U i₀ ⊓ … ⊓̂ᵢⱼ ⊓ …`, with
the standard alternating sign.

Key Mathlib hooks:
- `PresheafOfModules.free R : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules R` — the free
  presheaf-of-modules functor.
- `PresheafOfModules.freeAdjunction R : free R ⊣ toPresheaf R ⋙ whiskeringRight … (forget Ab)`
  — the adjunction; `freeObjDesc` / `freeHomEquiv` give the universal property
  `Hom(free(P), F) ≅ NatTrans P (F ∘ forget)` used in step 3.
- `yoneda : Opens ↥X ⥤ (Opens ↥X)ᵒᵖ ⥤ Type u` — the Yoneda embedding.
- Use `Finset.univ`-indexed direct sums; `ChainComplex.of` or `HomologicalComplex.mk`
  to assemble.

─────────────────────────────────────────────────────────────────────────────────
Step 3 — `cechComplex_hom_identification`
─────────────────────────────────────────────────────────────────────────────────
Type: a natural isomorphism of cochain complexes of abelian groups (or
`O_X(U)`-modules):

    Hom_{X.PresheafOfModules}(K(𝒰)_•, F)  ≅  Č•(𝒰, F, U)

i.e., the complex of hom-sets out of `K(𝒰)_•` is the section Čech cochain complex.

Strategy:
- At degree `p`, term-by-term: use the adjunction iso
  `(PresheafOfModules.freeAdjunction _).homEquiv` to identify
  `Hom_{PMod}(free(yoneda(U_I)), F)  ≅  NatTrans (yoneda(U_I)) (toPresheaf F)`
  and then Yoneda (`yonedaEquiv`) to get `≅  (toPresheaf F).obj (op U_I) = F.obj (op U_I)`.
  The product over multi-indices matches the degree-`p` term of `Č•(𝒰, F, U)`.
- Check that the differential intertwines: the differential on `Hom(K_•, F)` induced
  by pre-composition with the alternating-sign `free.map` maps matches the alternating
  restriction differential of `Č•(𝒰, F, U)`.
- Build as a cochain-complex isomorphism using `HomologicalComplex.Hom.isoOfComponents`.

Key Mathlib hooks:
- `PresheafOfModules.freeAdjunction` — the core adjunction.
- `yonedaEquiv` — the Yoneda natural bijection.
- `PresheafOfModules.evaluation` — sections extraction.

─────────────────────────────────────────────────────────────────────────────────
Step 4 — `cechFreeComplex_quasiIso`
─────────────────────────────────────────────────────────────────────────────────
Type: the augmented complex `K(𝒰)_• → O_𝒰[0]` (augmentation = "sheaf restricted to
the cover") is a quasi-isomorphism, i.e., `K(𝒰)_•` is a free resolution of `O_𝒰`.

Strategy (Mathlib has no packaged Čech contractibility lemma; build it directly):
- Homology of presheaves of modules is computed objectwise
  (limits/colimits in `PresheafOfModules R` are objectwise; see `HasColimits`
  instance). So it suffices to show that for each open `V : Opens ↥X`,
  the complex `K(𝒰)_•(V)` of `R(V)`-modules is contractible.
- The sectionwise complex `K(𝒰)_•(V)` is:
  degree `p` = `⨁_{I : Fin(p+1)→J} R(V)` when `V ⊆ U_{I(0)} ⊓ … ⊓ U_{I(p)}`, else `0`.
- Fix any index `i_fix` such that `V ⊆ 𝒰.U i_fix` (if no such index, the complex is
  `0` and trivially exact). The contracting homotopy `h : K_p(V) → K_{p+1}(V)` is:
      `h(s)_{i₀,i₁,…,iₚ} = (i₀ = i_fix) · s_{i₁,…,iₚ}`
  (extend the multi-index by prepending `i_fix`). Check: `dh + hd = id` at each degree.
- Assemble using `Homotopy` / `HomotopyEquiv` from Mathlib (`HomologicalComplex.Homotopy`
  in `Mathlib.Algebra.Homology.Homotopy`). From the chain homotopy conclude
  `HomotopyEquiv` and hence quasi-isomorphism.
- Do NOT route through `ExtraDegeneracy` (it has a different index convention and is
  not directly applicable here).

Key Mathlib hooks:
- `HomologicalComplex.Homotopy` — chain homotopy type.
- `HomotopyEquiv.toQuasiIso` (or `Homotopy.toQuasiIso`) — chain homotopy ⟹ quasi-iso.

─────────────────────────────────────────────────────────────────────────────────
Step 5 — `injective_cech_acyclic`
─────────────────────────────────────────────────────────────────────────────────
Type: for an injective `I : X.Modules` and an open cover `𝒰 : X.OpenCover`, the
positive-degree Čech cohomology `Ȟ^p(𝒰, I) = 0` for all `p > 0`.

Strategy (two independent parts; does NOT need decisions 4–5):

Part (a) — Injective sheaf ⟹ injective presheaf:
- Apply `CategoryTheory.Injective.injective_of_adjoint` to the adjunction
  `PresheafOfModules.sheafificationAdjunction α` where `α = 𝟙` for the scheme `X`.
  This adjunction is `sheafification α ⊣ (forget R) ⋙ restrictScalars α`, i.e.
  sheafification is left adjoint to the inclusion `toPresheafOfModules`.
- The left adjoint `sheafification` is exact (it is exact as a colimit of
  sheafification-endofunctors over a Grothendieck topology), hence in particular
  `PreservesMonomorphisms`. So `Injective.injective_of_adjoint` gives:
  `I` injective in `X.Modules` ⟹ `Scheme.Modules.toPresheafOfModules.obj I`
  is injective in `X.PresheafOfModules`.
- Relevant Mathlib names:
  `PresheafOfModules.sheafificationAdjunction`,
  `CategoryTheory.Injective.injective_of_adjoint`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`,
  `Adjunction.map_injective`.

Part (b) — Vanishing of positive Čech cohomology:
- By step 4, `K(𝒰)_• → O_𝒰[0]` is an exact augmented complex (quasi-iso from step 4).
- Since `I_pshf := toPresheafOfModules.obj I` is injective in `X.PresheafOfModules`
  (by part (a)), the functor `Hom_{PMod}(-, I_pshf)` is exact.
- Applying `Hom_{PMod}(-, I_pshf)` to the exact augmented complex `K(𝒰)_• → O_𝒰` and
  using step 3 (`cechComplex_hom_identification`) to identify the resulting complex
  with `Č•(𝒰, I, U)`, conclude that `Č•(𝒰, I, U)` is exact in positive degrees, i.e.
  `Ȟ^p(𝒰, I) = 0` for `p > 0`.
- This is the Stacks-project proof of `lemma-injective-trivial-cech` (Stacks tag
  0BKP and surrounding; see `references/stacks-cohomology.md`).

─────────────────────────────────────────────────────────────────────────────────
Verified Mathlib API summary (LSP-checked in this project):
  PresheafOfModules
  PresheafOfModules.free
  PresheafOfModules.freeAdjunction
  PresheafOfModules.evaluation
  PresheafOfModules.sheafificationAdjunction
  CategoryTheory.Injective.injective_of_adjoint
  yoneda
─────────────────────────────────────────────────────────────────────────────────
-/

/-! ## Project-local Mathlib supplement — PresheafCech (injective transfer) -/

variable {X : Scheme.{u}}

/-- **An injective sheaf of `O_X`-modules is injective as a presheaf of modules.**

This is Part 1 of the {\v C}ech-acyclicity of injectives (blueprint
`lem:injective_cech_acyclic`, Stacks `lemma-injective-trivial-cech`): the inclusion
`Scheme.Modules.toPresheafOfModules X : X.Modules ⥤ X.PresheafOfModules` is the right
adjoint of the (exact) sheafification functor, so it carries injective objects to
injective objects.

Project-local because Mathlib has no packaged "injective sheaf of modules ⟹ injective
presheaf of modules" statement; it is obtained here by feeding
`PresheafOfModules.sheafificationAdjunction (𝟙 _)` (whose left adjoint
`sheafification` preserves monomorphisms) to `Injective.injective_of_adjoint`. The
right adjoint of that adjunction is *definitionally* `toPresheafOfModules X`
(`SheafOfModules.forget _ ⋙ restrictScalars (𝟙 _)`). -/
theorem injective_toPresheafOfModules (I : X.Modules) [Injective I] :
    Injective ((Scheme.Modules.toPresheafOfModules X).obj I) := by
  -- the left adjoint of `toPresheafOfModules X` is `sheafification (𝟙 _)`, which is
  -- exact and in particular preserves monomorphisms
  haveI : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).PreservesMonomorphisms :=
    inferInstance
  -- realign the ambient category instance so the `Injective` instance is found cheaply
  haveI : Injective (C := SheafOfModules X.ringCatSheaf) I := ‹Injective I›
  exact Injective.injective_of_adjoint
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)) I

/-- **Free–Yoneda representability (per-term bijection).**

For an open `V : Opens X` and a presheaf of `O_X`-modules `F`, the morphisms out of the
free presheaf of modules on the representable `yoneda V` are exactly the sections of
`F` over `V`:
```
  Hom_{PMod(O_X)}(free(yoneda V), F) ≃ F(V).
```
This is the free–forgetful adjunction (`PresheafOfModules.freeHomEquiv`) composed with
the Yoneda bijection (`yonedaEquiv`). It is the single-multi-index core of the
{\v C}ech complex hom-identification (blueprint `lem:cech_complex_hom_identification`,
Stacks `lemma-cech-map-into`): taking the product over multi-indices turns this into
`Hom(K(𝒰)_p, F) = Č^p(𝒰, F)`.

Project-local because Mathlib packages the two halves separately but not their
composite as the corepresentability of evaluation by `free(yoneda V)`. The target
`(F.presheaf ⋙ forget Ab).obj (op V)` is the underlying set of the section group
`F(V)`. -/
noncomputable def freeYonedaHomEquiv (V : TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) :
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⟶ F) ≃
      (F.presheaf ⋙ forget Ab).obj (Opposite.op V) :=
  PresheafOfModules.freeHomEquiv.trans yonedaEquiv

/-- **Generator formula for `freeYonedaHomEquiv`.** The bijection
`Hom(free(yoneda V), F) ≃ F(V)` is evaluation of the morphism's component at `V` on the
canonical free generator `freeMk (𝟙 V)`. Recorded project-locally because this concrete
description is what makes the bijection visibly additive (`freeYonedaHomAddEquiv`) and is
unavailable as a packaged Mathlib lemma. -/
lemma freeYonedaHomEquiv_apply (V : TopologicalSpace.Opens X) (F : X.PresheafOfModules)
    (ψ : (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⟶ F) :
    freeYonedaHomEquiv V F ψ
      = (ConcreteCategory.hom (ψ.app (Opposite.op V))) (ModuleCat.freeMk (𝟙 V)) := by
  simp only [freeYonedaHomEquiv]; rfl

/-- **Additive upgrade of `freeYonedaHomEquiv`.** The free–Yoneda hom bijection
`Hom_{PMod}(free(yoneda V), F) ≃ F(V)` is an isomorphism of abelian groups: the source is
the (preadditive) hom-group of presheaves of modules and the target is the section group
`F(V)`. This is the per-multi-index additive core of the {\v C}ech hom-identification
(blueprint `lem:cech_complex_hom_identification`); taking products over multi-indices and
intertwining with the differential upgrades it to the full complex isomorphism. Additivity
holds because, by `freeYonedaHomEquiv_apply`, the bijection is evaluation of the
component `ψ.app (op V)` (a module map, hence additive) on a fixed generator, and the
component of a sum of morphisms is the sum of components.

Project-local because Mathlib packages the underlying bijection (`freeHomEquiv` ∘
`yonedaEquiv`) only at the level of types, not as an `AddEquiv`. -/
noncomputable def freeYonedaHomAddEquiv (V : TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) :
    ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj V) ⟶ F) ≃+
      (F.presheaf.obj (Opposite.op V)) where
  toFun := freeYonedaHomEquiv V F
  invFun := (freeYonedaHomEquiv V F).symm
  left_inv := (freeYonedaHomEquiv V F).left_inv
  right_inv := (freeYonedaHomEquiv V F).right_inv
  map_add' f g := by
    rw [freeYonedaHomEquiv_apply, freeYonedaHomEquiv_apply, freeYonedaHomEquiv_apply,
      PresheafOfModules.add_app]
    change (ModuleCat.Hom.hom (f.app (Opposite.op V) + g.app (Opposite.op V))) _ = _
    rw [ModuleCat.hom_add]; rfl

/-! ## Project-local Mathlib supplement — section {\v C}ech complex -/

/-- **Cosimplicial abelian group underlying the section {\v C}ech complex.**

For a family of opens `U : ι → Opens X` (an open covering) and a presheaf of modules `F`,
the cosimplicial object in `Ab` whose value in cosimplicial degree `p` is the product
`∏_{σ : Fin (p+1) → ι} F(⨅ₖ U (σ k))` of sections over the `(p+1)`-fold intersections. A
cosimplicial map `f : [m] ⟶ [n]` acts at multi-index `σ : Fin (n+1) → ι` by projecting to
the coordinate `σ ∘ f` and then restricting along `⨅ₖ U (σ k) ≤ ⨅ₗ U (σ (f l))`. This is the
covariant ({\v C}ech) variance that the alternating-coface-map complex turns into a cochain
complex.

Project-local: Mathlib has no {\v C}ech complex of sections of a presheaf of modules. Built
as an honest `SimplexCategory ⥤ Ab` functor so that `alternatingCofaceMapComplex` supplies
`d² = 0` for free (no hand-rolled alternating-sum identity). -/
noncomputable def sectionCechCosimplicial {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) : CosimplicialObject Ab.{u} where
  obj n := ∏ᶜ (fun σ : Fin (n.len + 1) → ι => F.presheaf.obj (Opposite.op (⨅ k, U (σ k))))
  map {m n} f := Pi.lift (fun σ : Fin (n.len + 1) → ι =>
    Pi.π _ (σ ∘ f.toOrderHom) ≫
      F.presheaf.map (homOfLE (le_iInf (fun l => iInf_le _ (f.toOrderHom l)))).op)
  map_id n := by
    -- The map at `𝟙 n` projects to index `σ ∘ id = σ` and restricts along the thin
    -- (reflexive) `Opens` hom `homOfLE ⋯ : ⨅ U(σ k) ⟶ ⨅ U(σ k)`, which is the identity.
    ext1 σ
    simp only [Pi.lift_π]
    -- the restriction hom is an endomorphism in the thin `Opensᵒᵖ` category, hence `𝟙`
    rw [Subsingleton.elim (homOfLE _).op (𝟙 _)]
    -- `erw` is needed: the `Subsingleton.elim` rewrite leaves the term not type-correct
    -- under `instances` transparency, so plain `rw [Functor.map_id]` cannot match.
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp {l m n} f g := by
    apply Pi.hom_ext
    intro σ
    simp only [Pi.lift_π, Category.assoc, SimplexCategory.comp_toOrderHom]
    rw [← Category.assoc, Pi.lift_π, Category.assoc, ← Functor.map_comp]
    congr 1

/-- **Section {\v C}ech cochain complex of a presheaf of modules**
(blueprint `def:section_cech_complex`).

The cochain complex `Č•(𝒰, F)` of abelian groups with degree-`p` term
`∏_{σ : Fin (p+1) → ι} F(⨅ₖ U (σ k))` and the alternating-sum-of-restrictions differential,
obtained as the alternating-coface-map complex of `sectionCechCosimplicial`. This is the
section complex of the blueprint, kept distinct from the relative pushforward `CechComplex`;
it is the right-hand side of the {\v C}ech hom-identification
`Hom_{PMod}(K(𝒰)_•, F) ≅ Č•(𝒰, F)`.

Project-local: no {\v C}ech complex of sections of a presheaf of modules exists in Mathlib. -/
noncomputable def sectionCechComplex {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) : CochainComplex Ab.{u} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex Ab.{u}).obj (sectionCechCosimplicial U F)

end AlgebraicGeometry
