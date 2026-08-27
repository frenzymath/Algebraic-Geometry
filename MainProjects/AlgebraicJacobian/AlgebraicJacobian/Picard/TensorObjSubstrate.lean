/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate.StalkTensor
import AlgebraicJacobian.Picard.TensorObjSubstrate.Vestigial
import AlgebraicJacobian.Picard.TensorObjSubstrate.PresheafInternalHom
import AlgebraicJacobian.Picard.LineBundlePullback

/-!
# Tensor products in `Scheme.Modules`

The relative Picard group law sends two line bundles to their tensor product.
At the pinned Mathlib revision, tensor products are available for presheaves of
modules but not directly for `Scheme.Modules`. This file supplies the required
scheme-level operations:

1. a binary tensor-product operation
   `⊗ : Scheme.Modules X × Scheme.Modules X → Scheme.Modules X`;
2. the structure sheaf `O_X` as a designated unit object for `⊗`;
3. an inverse operation on the full subcategory of invertible objects, i.e.
   the dual `L⁻¹ = Hom(L, O_X)` of an invertible sheaf.

The construction sheafifies `PresheafOfModules.Monoidal.tensorObj` on the small
Zariski site. It develops functoriality, unitors, symmetry, associativity, duals,
evaluation, local triviality, and compatibility with pullback and restriction.
The tensor-inverse theorem is proved downstream in `TensorObjInverse.lean`.

The principal blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.Modules.tensorObj` (def) — the substrate binary
   operation `⊗ : Scheme.Modules X × Scheme.Modules X → Scheme.Modules X`,
   lifting `PresheafOfModules.Monoidal.tensorObj` on underlying presheaves
   composed with sheafification on the small Zariski site.
   Per blueprint `def:scheme_modules_tensorobj`.

2. `AlgebraicGeometry.Scheme.Modules.tensorObj_functoriality` (def) — the
   functorial action of `⊗` on morphisms: a pair `f : M ⟶ M'`, `g : N ⟶ N'`
   determines `f ⊗ g : tensorObj M N ⟶ tensorObj M' N'`.
   Per blueprint `lem:scheme_modules_tensorobj_functoriality`.

A full `MonoidalCategory (Scheme.Modules X)` instance is deliberately omitted;
the group law on isomorphism classes only needs the relevant coherence
isomorphisms. See blueprint `rem:scheme_modules_monoidal_off_path`.

## References

Blueprint: `blueprint/src/chapters/Picard_TensorObjSubstrate.tex`. Source:
[Kleiman], "The Picard scheme", §2 (FGA Explained, Chapter 9, §9.2), and
Stacks tags 01CR and 03DM. The underlying Mathlib construction is in
`Mathlib.CategoryTheory.Monoidal.PresheafOfModules`
(`PresheafOfModules.Monoidal.tensorObj`).

## Sub-module layout

Supporting constructions live under `AlgebraicJacobian/Picard/TensorObjSubstrate/`:

- `StalkTensor.lean` proves the stalk tensor comparison.
- `Vestigial.lean` contains auxiliary local-injectivity and stalk constructions.
- `PresheafInternalHom.lean` develops the presheaf algebra used here:
  `RestrictScalarsRingIsoTensor`, lax-monoidal `restrictScalars`, pushforward
  adjunction (H1), `StrongMonoidalRestrictScalars` (H2), `InternalHom`, `Dual`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-! ## §1. The substrate tensor-product operation -/

/-- **The substrate operation `⊗` on `Scheme.Modules X`.**

For a scheme `X` and `M, N : X.Modules`, the tensor product
`M ⊗_X N : X.Modules` is the sheafification of the presheaf-of-modules tensor
product `PresheafOfModules.Monoidal.tensorObj` of the underlying presheaves of
`M` and `N` (affine-locally `(M ⊗_X N)(Spec A) = M(Spec A) ⊗_A N(Spec A)`).

Per blueprint `def:scheme_modules_tensorobj`. The body lifts
`PresheafOfModules.Monoidal.tensorObj` through the sheafification functor on
the small Zariski site of `X`. -/
noncomputable def tensorObj {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val) :
    SheafOfModules X.ringCatSheaf)

/-- **Functoriality of `⊗_X`.**

A pair of morphisms `f : M ⟶ M'` and `g : N ⟶ N'` in `X.Modules` determines a
morphism `f ⊗ g : tensorObj M N ⟶ tensorObj M' N'`, compatible with identities
and composition; the assignment `(M, N) ↦ tensorObj M N` thereby extends to a
bifunctor `X.Modules × X.Modules ⥤ X.Modules` natural in both arguments.

Per blueprint `lem:scheme_modules_tensorobj_functoriality`. The body inherits
the morphism action from `PresheafOfModules.Monoidal.tensorObj` under
sheafification. -/
noncomputable def tensorObj_functoriality {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') : tensorObj M N ⟶ tensorObj M' N' :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
    (MonoidalCategory.tensorHom
      (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) f.val g.val)

/-- **`⊗`-invertibility of an `𝒪_X`-module.** (Blueprint
`def:scheme_modules_isinvertible`.) `M : X.Modules` is `⊗`-invertible when it
admits a tensor inverse: an object `N` with `M ⊗_X N ≅ 𝒪_X`, where
`𝒪_X = SheafOfModules.unit X.ringCatSheaf` is the designated unit. This is the
scheme-level analogue of Mathlib's `Module.Invertible`; the predicate carries its
inverse witness existentially, so the dual needed by the relative Picard group
law is definitional. -/
def IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ N : X.Modules, Nonempty (tensorObj M N ≅ SheafOfModules.unit X.ringCatSheaf)

/-- **The sheaf-level dual `M^∨ := ℋom_{𝒪_X}(M, 𝒪_X)`** of an `𝒪_X`-module.

For a scheme `X` and `M : X.Modules`, the dual `dual M : X.Modules` is the
sheafification of the presheaf-of-modules dual `PresheafOfModules.dual` of the
underlying presheaf of `M` (the internal hom into the structure presheaf,
`M^∨(U) = ℋom_{𝒪_X|_U}(M|_U, 𝒪_X|_U)`).

The construction is the dual analogue of `tensorObj`: apply
`PresheafOfModules.sheafification (𝟙 …)` on the small Zariski site to the presheaf dual
`PresheafOfModules.dual M.val`. The scheme's structure presheaf `X.presheaf` is
`CommRingCat`-valued over the single-universe topological site `Opens X`, hence is
exactly the base `R₀ : Dᵒᵖ ⥤ CommRingCat.{u}` that `PresheafOfModules.dual`
requires (the value `M^∨(U) = M|_U ⟶ R|_U` is an `R(U)`-module, needing
commutativity) — no CommRingCat/RingCat re-bridging is needed, since
`tensorObj` already takes `(R := X.presheaf)` over the same CommRingCat presheaf
and `X.ringCatSheaf.obj = X.presheaf ⋙ forget₂ CommRingCat RingCat` definitionally.

The sheafification functor already lands in `SheafOfModules`, so no manual
`Presheaf.IsSheaf` / sheaf-condition descent is needed (sheafifying an already-sheaf
gives an iso object; this is the file's convention, matching `tensorObj`).

Per blueprint `lem:internal_hom_isSheaf` (§`sec:tensorobj_dual_infra`); Stacks
tags 01CM (internal hom into a sheaf is a sheaf) / 01CR item 2. This is the
`⊗`-inverse candidate of an invertible sheaf, feeding `exists_tensorObj_inverse`. -/
noncomputable def dual {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.dual (R₀ := X.presheaf) M.val) :
    SheafOfModules X.ringCatSheaf)

/-- **The sheaf-level dual is contravariantly functorial in isomorphisms.** An isomorphism
`e : M ≅ M'` in `X.Modules` induces `dual M' ≅ dual M`, obtained by sheafifying the presheaf-level
dual iso `PresheafOfModules.dualIsoOfIso` of the underlying presheaf isomorphism. This is the
reusable "dual respects isos" ingredient (the dual analogue of `tensorObjIsoOfIso`) feeding the
assembly of `dual_isLocallyTrivial`: a trivialisation `L.restrict f ≅ 𝒪` yields, contravariantly,
`dual 𝒪 ≅ dual (L.restrict f)`. -/
noncomputable def dualIsoOfIso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M') :
    dual M' ≅ dual M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (PresheafOfModules.dualIsoOfIso (R₀ := X.presheaf)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e))

/-! ## §2. Why no full monoidal-category instance is needed

The full `MonoidalCategory (X.Modules)` instance is deliberately not built. Per
blueprint `rem:scheme_modules_monoidal_off_path`,
the relative Picard group law is a structure on *isomorphism classes* of line
bundles — every group axiom is a `Nonempty (… ≅ …)` proposition, so no monoidal
coherence and no `MonoidalClosed` structure is consumed. The group law is built
directly on the line-bundle subcategory from the coherence isomorphisms below,
mirroring Mathlib's `CommRing.Pic`. -/

/-! ## §3. The lift through `LineBundle.OnProduct`

The following helper lemmas record the lift of the substrate to the
locally-trivial subcategory used by the relative Picard consumer. -/

/-- **The substrate operation respects isomorphisms in both arguments.**

A pair of isomorphisms `e : M ≅ M'` and `e' : N ≅ N'` in `X.Modules` induces an
isomorphism `tensorObj M N ≅ tensorObj M' N'`, obtained by sheafifying the
tensor product (in the presheaf-of-modules monoidal category) of the underlying
presheaf isomorphisms `e.val`, `e'.val`. Its `hom` is
`tensorObj_functoriality e.hom e'.hom`. This is the reusable functor-of-isos
ingredient feeding `tensorObj_isLocallyTrivial`. -/
noncomputable def tensorObjIsoOfIso {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (e' : N ≅ N') : tensorObj M N ≅ tensorObj M' N' :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso
      (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e'))

/-- **The substrate tensor of the structure sheaf with itself is the structure
sheaf.**

`tensorObj 𝒪_X 𝒪_X ≅ 𝒪_X`, where `𝒪_X = SheafOfModules.unit X.ringCatSheaf` is the
designated unit object. Built from the presheaf-level left unitor
`λ_ (𝟙_)` (the unit of the `PresheafOfModules` monoidal category is exactly
`SheafOfModules.unit.val`) under sheafification, composed with the
sheafification-adjunction counit isomorphism on the (already-sheaf) unit. -/
noncomputable def tensorObj_unit_iso {X : Scheme.{u}} :
    tensorObj (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
      ≅ SheafOfModules.unit X.ringCatSheaf := by
  -- Use the explicit monoidal structure so the second tensor factor remains the literal
  -- structure-presheaf carrier; this avoids an unnecessary definitional equality between
  -- two presentations of the monoidal unit.
  exact
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
        ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).leftUnitor
          (SheafOfModules.unit X.ringCatSheaf).val) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app
        (SheafOfModules.unit X.ringCatSheaf)

/-- **Left unitor for `⊗_X`.** `𝒪_X ⊗_X M ≅ M`. (Blueprint
`lem:tensorobj_unit_iso`, left half, `AlgebraicGeometry.Scheme.Modules.tensorObj_left_unitor`.)
Sheafification of the presheaf-level left unitor `λ_ M.val`, composed with the
sheafification counit identifying `sheafification M.val` with the (already-sheaf)
`M`. The cheap `mapIso` pattern; uses no abstract pullback. -/
noncomputable def tensorObj_left_unitor {X : Scheme.{u}} (M : X.Modules) :
    tensorObj (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
      ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).leftUnitor M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- **Right unitor for `⊗_X`.** `M ⊗_X 𝒪_X ≅ M`. (Blueprint
`lem:tensorobj_unit_iso`, right half, `AlgebraicGeometry.Scheme.Modules.tensorObj_right_unitor`.)
Sheafification of the presheaf-level right unitor `ρ_ M.val`, composed with the
sheafification counit. -/
noncomputable def tensorObj_right_unitor {X : Scheme.{u}} (M : X.Modules) :
    tensorObj M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
      ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).rightUnitor M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- **Braiding for `⊗_X`.** `M ⊗_X N ≅ N ⊗_X M`. (Blueprint
`lem:tensorobj_comm_iso`, `AlgebraicGeometry.Scheme.Modules.tensorObj_braiding`.)
The presheaf-of-modules monoidal category is symmetric; its braiding `β_ M.val
N.val` sheafifies to the asserted isomorphism by the cheap `mapIso` pattern. -/
noncomputable def tensorObj_braiding {X : Scheme.{u}} (M N : X.Modules) :
    tensorObj M N ≅ tensorObj N M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).mapIso
    (BraidedCategory.braiding
      (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M.val N.val)

/-- **Associator for `⊗_X`.** (Blueprint
`lem:tensorobj_assoc_iso`, `AlgebraicGeometry.Scheme.Modules.tensorObj_assoc_iso`.)
For arbitrary `M, N, P : X.Modules` there is an isomorphism
`(M ⊗_X N) ⊗_X P ≅ M ⊗_X (N ⊗_X P)`. This is the objectwise existence-of-iso datum the
group law consumes (associativity as a `Nonempty (… ≅ …)`).

No flatness or local-triviality hypothesis is used. Instead, the proof uses stability of
the class inverted by sheafification under left and right whiskering.
Writing `a = PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)` and `η` the
sheafification-adjunction unit, the three-step composite is:
  1. `a(η_{M.val ⊗ᵖ N.val} ▷ P.val)` is iso, giving
     `(M ⊗ N) ⊗ P ≅ a((M.val⊗N.val) ⊗ P.val)`;
  2. `a.mapIso α : a((M.val⊗N.val)⊗P.val) ≅ a(M.val⊗(N.val⊗P.val))`, `α` the
     presheaf-of-modules associator;
  3. `a(M.val ◁ η_{N.val ⊗ᵖ P.val})` is iso, giving
     `a(M.val⊗(N.val⊗P.val)) ≅ M ⊗ (N ⊗ P)`.
Steps 1/3 invert the whiskered sheafification unit via the flatness-free
`PresheafOfModules.W_whisker{Right,Left}_of_W` (η = `toSheafify ∈ J.W`, and `J.W` is
stable under whiskering) together with `isIso_sheafification_map_of_W` (the sheafification
functor IS the localization at `J.W.inverseImage (toPresheaf _)`). The defeq carrier bridge
`X.ringCatSheaf.obj = X.presheaf ⋙ forget₂ CommRingCat RingCat` is handled by the leading
`letI instMS` below. -/
noncomputable def tensorObj_assoc_iso {X : Scheme.{u}} {M N P : X.Modules} :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) := by
  -- The whiskered sheafification units are inverted for arbitrary modules.
  -- Bridge the monoidal structure across the `rfl`-defeq carrier
  -- `X.ringCatSheaf.obj = X.presheaf ⋙ forget₂ CommRingCat RingCat`.
  letI instMS : MonoidalCategoryStruct (_root_.PresheafOfModules (X.ringCatSheaf.obj)) :=
    inferInstanceAs (MonoidalCategoryStruct
      (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
  set a := PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) with ha
  -- Underlying presheaf tensors and the sheafification unit `η = toSheafify`.
  set MN := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val with hMN
  set NP := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) N.val P.val with hNP
  set η := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit with hη
  -- The two whiskered-unit localizer facts (ROUTE (d), via `W_whisker{Right,Left}_of_W`).
  -- `η_A = toSheafify` lies in `J.W` (`W_toSheafify`).
  have hηMN : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app MN)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hηNP : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app NP)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hW1 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app MN ▷ P.val)) :=
    PresheafOfModules.W_whiskerRight_of_W (R := X.presheaf) P.val (η.app MN) hηMN
  have hW3 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ η.app NP)) :=
    PresheafOfModules.W_whiskerLeft_of_W (R := X.presheaf) M.val (η.app NP) hηNP
  -- Steps 1 and 3: the sheafification functor inverts the whiskered units.
  have hi1 : IsIso (a.map (η.app MN ▷ P.val)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.obj) _ hW1
  have hi3 : IsIso (a.map (M.val ◁ η.app NP)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.obj) _ hW3
  -- Step 2: the presheaf-of-modules associator, transported under `a`.
  have e2 := a.mapIso
    ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).associator M.val N.val P.val)
  exact (@asIso _ _ _ _ _ hi1).symm ≪≫ e2 ≪≫ (@asIso _ _ _ _ _ hi3)

/-- **Refining a trivialisation to a smaller open.** If `M` is trivialised on an
open `U` (`M.restrict U.ι ≅ 𝒪_U`), it is trivialised on every open `W ≤ U`.

The chart-chase is identical in spirit to `LineBundle.IsLocallyTrivial.pullback`:
factor `W.ι = (X.homOfLE hWU) ≫ U.ι`, transport through `restrictFunctorCongr`
and `restrictFunctorComp` to identify `M.restrict W.ι` with
`(M.restrict U.ι).restrict (X.homOfLE hWU)`, restrict the given trivialisation
`e` along that open immersion, and identify the restricted unit with the unit
via `restrictFunctorIsoPullback` + `pullbackObjUnitToUnit` (an isomorphism
because the open immersion's `Opens.map` is `Final`). -/
noncomputable def restrictIsoUnitOfLE {X : Scheme.{u}} {M : X.Modules} {U W : X.Opens}
    (hWU : W ≤ U)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    M.restrict W.ι ≅ SheafOfModules.unit (W : Scheme).ringCatSheaf := by
  have hWU' : W ≤ (𝟙 X) ⁻¹ᵁ U := hWU
  set j : (W : Scheme) ⟶ (U : Scheme) := Scheme.Hom.resLE (𝟙 X) U W hWU' with hj
  have hjι : j ≫ U.ι = W.ι := by rw [hj, Scheme.Hom.resLE_comp_ι, Category.comp_id]
  haveI : (TopologicalSpace.Opens.map j.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  -- M.restrict W.ι ≅ (pullback W.ι).obj M
  refine (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M ≪≫ ?_
  -- ≅ (pullback (j ≫ U.ι)).obj M
  refine (Scheme.Modules.pullbackCongr hjι.symm).app M ≪≫ ?_
  -- ≅ (pullback j).obj ((pullback U.ι).obj M)
  refine (Scheme.Modules.pullbackComp j U.ι).symm.app M ≪≫ ?_
  -- ≅ (pullback j).obj (M.restrict U.ι)
  refine (Scheme.Modules.pullback j).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M) ≪≫ ?_
  -- ≅ (pullback j).obj 𝒪_U
  refine (Scheme.Modules.pullback j).mapIso e ≪≫ ?_
  -- ≅ 𝒪_W
  haveI hI : IsIso (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ hI

/-- **Substrate tensor commutes with restriction along an open immersion.**

For an open immersion `f : Y ⟶ X` and `M N : X.Modules`,
`(tensorObj M N).restrict f ≅ tensorObj (M.restrict f) (N.restrict f)`.

The substrate tensor is a sheafification of the presheaf tensor, and it commutes
with restriction along an open immersion. The proof is the following composite:
  Step 1 (`restrictFunctorIsoPullback`): reduce `restrict` to the abstract pullback.
  Step 2 (`SheafOfModules.sheafificationCompPullback`): move the pullback inside the
    sheafification (sheafification commutes with pullback).
  Step 3: strip the outer sheafification (`.mapIso`), descending to the presheaf goal
    `(pullback φ).obj (M.val ⊗ₚ N.val) ≅ (M.restrict f).val ⊗ₚ (N.restrict f).val`.
  Step 4: close that presheaf goal by **H1 ∘ H2**:
    • H1: the presheaf-level iso
      `pushforward β ≅ pullback φ`, obtained from the de-sheafified presheaf
      `PresheafOfModules.pushforwardPushforwardAdj` (adjunction along the open-immersion
      pair `f.opensFunctor ⊣ Opens.map f.base`) against the existing
      `pullbackPushforwardAdjunction` via `Adjunction.leftAdjointUniq`. Here `β` is the
      restriction structure map, so `(M.restrict f).val = (pushforward β).obj M.val`
      definitionally.
    • H2 (strong-monoidal tensorator): `pushforward β = pushforward₀ ⋙ restrictScalars β`
      with `β` sectionwise the open-immersion ring isomorphism `f.appIso`, so
      `restrictScalars β` is strong monoidal (`restrictScalarsMonoidalOfBijective`); the
      composite
      `μIso` is the tensorator.
-/
noncomputable def tensorObj_restrict_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M N : X.Modules) :
    (tensorObj M N).restrict f ≅ tensorObj (M.restrict f) (N.restrict f) := by
  -- Step 1. Reduce `restrict` to `pullback` along the open immersion `f`
  -- (`restrictFunctorIsoPullback`, Mathlib).
  refine (Scheme.Modules.restrictFunctorIsoPullback f).app (tensorObj M N) ≪≫ ?_
  -- Step 2. **Sheafification commutes with pullback.** `tensorObj M N` is, by
  -- definition, `sheafification.obj (PresheafOfModules.Monoidal.tensorObj
  -- M.val N.val)`, so the genuine Mathlib lemma
  -- `SheafOfModules.sheafificationCompPullback`
  -- (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`,
  -- `sheafification ⋙ pullback φ ≅ PresheafOfModules.pullback φ.hom ⋙
  -- sheafification`) moves the pullback *inside* the sheafification. This
  -- discharges half (ii) of the original obstruction (sheafification commuting
  -- with pullback). After it the goal is the purely **presheaf-level** residual
  -- `sheafify ((PresheafOfModules.pullback φ.hom).obj (M.val ⊗ N.val))
  --    ≅ (M.restrict f).tensorObj (N.restrict f)`.
  refine (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) ≪≫ ?_
  -- Step 3. **Strip the outer sheafification.** Both sides are
  -- `PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)` applied to a
  -- presheaf-of-modules: the LHS to `(pullback φ.hom).obj (M.val ⊗ₚ N.val)`, and
  -- the RHS `(M.restrict f).tensorObj (N.restrict f)` *by definition* to
  -- `(M.restrict f).val ⊗ₚ (N.restrict f).val`. So it suffices to give the
  -- comparison at the PRESHEAF level and sheafify it. This is a genuine reduction
  -- step (verified: the goal below has no sheafification).
  refine (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).mapIso ?_
  -- Step 4. The remaining presheaf goal is
  --   `(PresheafOfModules.pullback φ).obj (M.val ⊗ₚ N.val)
  --      ≅ (M.restrict f).val ⊗ₚ (N.restrict f).val`
  -- where `φ = (Scheme.Hom.toRingCatSheafHom f).hom` and `⊗ₚ =
  -- PresheafOfModules.Monoidal.tensorObj`. We close it via:
  --  (H1, the linchpin) the presheaf-level iso `pushforward β ≅ pullback φ`, built from
  --      the presheaf `pushforwardPushforwardAdj` (above) against the existing
  --      `pullbackPushforwardAdjunction` via `leftAdjointUniq`. Here `β` is the
  --      open-immersion structure map of `restrictFunctor f`, so
  --      `(M.restrict f).val = (pushforward β).obj M.val` definitionally.
  --  (H2) the strong-monoidal comparison `(pushforward β).obj (A ⊗ₚ B) ≅
  --      (pushforward β).obj A ⊗ₚ (pushforward β).obj B`.
  -- `φR` (the scheme structure map) and `β` (the restrictFunctor structure map) are kept as
  -- `let`-bindings (zeta-transparent) so the unit/counit triangle goals below reduce; the
  -- open-immersion adjunction is INLINED for the same reason (a `have` would make `adj.unit`
  -- opaque and block the `congr` defeq, exactly as in Mathlib's sheaf-level `restrictAdjunction`).
  let φR := (Scheme.Hom.toRingCatSheafHom f).hom
  -- The restrictFunctor structure map `β` (so `(M.restrict f).val = (pushforward β).obj M.val`).
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv
      -- Supply inverse naturality explicitly in the form used by the open-immersion API.
      naturality := fun _ _ i => f.appIso_inv_naturality i }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  -- H1 via the presheaf pushforward-pushforward adjunction + `leftAdjointUniq`.
  have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  let H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  refine (H1.app (PresheafOfModules.Monoidal.tensorObj M.val N.val)).symm ≪≫ ?_
  -- H2: the strong-monoidal tensorator of `pushforward β = pushforward₀ ⋙ restrictScalars β`.
  -- `β` is sectionwise bijective (it is the `forget₂`-image of the open-immersion structure ring
  -- iso `f.appIso`), so `restrictScalars β` is strong monoidal
  -- (`restrictScalarsMonoidalOfBijective`), and `pushforward₀OfCommRingCat` is monoidal.
  -- The composite's `μIso` is the tensorator. It is built over the syntactic `_ ⋙ forget₂`
  -- base form, where the `MonoidalCategory` instance is
  -- found canonically); the result is DEFEQ to the goal — whose base `X.ringCatSheaf.obj` is only
  -- defeq, not syntactically, `X.presheaf ⋙ forget₂` — and `(pushforward β).obj M.val =
  -- (M.restrict f).val` definitionally, so `exact` closes it without any instance diamond.
  have hβ : ∀ U, Function.Bijective (β.app U).hom := by
    intro U
    haveI : IsIso (β.app U) :=
      inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
    exact ConcreteCategory.bijective_of_isIso (β.app U)
  let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
  haveI : (PresheafOfModules.restrictScalars β').Monoidal :=
    PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
  exact (Functor.Monoidal.μIso
    (PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf
      ⋙ PresheafOfModules.restrictScalars β')
    (M.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))).symm

/-- **Tensor product of locally-trivial modules is locally trivial.**

If `M, N : X.Modules` are locally trivial of rank one (line bundles), so is
their tensor product `tensorObj M N`. Per blueprint
`lem:tensorobj_preserves_locally_trivial`. The proof picks, for each point `x`,
a common affine open `W ∋ x` contained in trivialising opens `U` (for `M`) and
`U'` (for `N`), refines both trivialisations to `W` via `restrictIsoUnitOfLE`,
then transports through `tensorObj_restrict_iso`, the bifunctoriality
`tensorObjIsoOfIso`, and the unit isomorphism `tensorObj_unit_iso`:
`(M ⊗ N)|_W ≅ M|_W ⊗ N|_W ≅ 𝒪_W ⊗ 𝒪_W ≅ 𝒪_W`. -/
lemma tensorObj_isLocallyTrivial {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.IsLocallyTrivial M) (hN : LineBundle.IsLocallyTrivial N) :
    LineBundle.IsLocallyTrivial (tensorObj M N) := by
  intro x
  obtain ⟨U, hxU, hU_aff, ⟨eM⟩⟩ := hM x
  obtain ⟨U', hxU', hU'_aff, ⟨eN⟩⟩ := hN x
  obtain ⟨W, hW_aff, hxW, hWsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := U ⊓ U') ⟨hxU, hxU'⟩
  have hWU : W ≤ U := le_trans hWsub inf_le_left
  have hWU' : W ≤ U' := le_trans hWsub inf_le_right
  refine ⟨W, hxW, hW_aff, ⟨?_⟩⟩
  exact tensorObj_restrict_iso W.ι M N ≪≫
    tensorObjIsoOfIso (restrictIsoUnitOfLE hWU eM) (restrictIsoUnitOfLE hWU' eN) ≪≫
    tensorObj_unit_iso

/-! ## Project-local Mathlib supplement — the d.2-free descent re-route (B-connector)

The "locally-iso ⇒ iso" half of the descent assembly of `exists_tensorObj_inverse`:
a morphism of `𝒪_X`-modules that restricts to an isomorphism on an open
neighbourhood of every point is a global isomorphism. The route is the stalkwise
iso criterion `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` (for sheaves valued
in `Ab`, whose forgetful functor reflects isos and preserves limits / filtered
colimits) together with `Scheme.Modules.restrictStalkNatIso` (restriction along an
open immersion commutes with stalks). **No stalk-⊗ ("d.2") is invoked**: this is a
statement about a single module morphism, never about the tensor stalk. -/

/-- **B-connector: a morphism of `𝒪_X`-modules that restricts to an isomorphism on
an open cover is an isomorphism.** For `φ : M ⟶ N` in `X.Modules`, if every point
`x` lies in an open `U x` on which the restriction `(restrictFunctor (U x).ι).map φ`
is an isomorphism, then `φ` is an isomorphism. This is the B-bridge of the d.2-free
descent re-route assembling `exists_tensorObj_inverse`. -/
lemma isIso_of_isIso_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (U : X → X.Opens) (hxU : ∀ x, x ∈ U x)
    (h : ∀ x, IsIso ((Scheme.Modules.restrictFunctor (U x).ι).map φ)) :
    IsIso φ := by
  -- It suffices that each stalk map of the underlying `Ab`-sheaf morphism is iso.
  have hst : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((Scheme.Modules.toPresheaf X).map φ)) := by
    intro x
    obtain ⟨x', hx'⟩ : ∃ x', (U x).ι x' = x := by
      have hmem : x ∈ (U x).ι.opensRange := by
        rw [Scheme.Opens.opensRange_ι]; exact hxU x
      exact AlgebraicGeometry.Scheme.Hom.mem_opensRange.mp hmem
    haveI : IsIso ((Scheme.Modules.restrictFunctor (U x).ι).map φ) := h x
    -- `(restrictFunctor … ⋙ toPresheaf … ⋙ stalkFunctor x').map φ` is iso (functor of an iso).
    haveI hFφ : IsIso ((Scheme.Modules.restrictFunctor (U x).ι ⋙
        Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x').map φ) := by
      dsimp only [Functor.comp_map]; exact Functor.map_isIso _ _
    -- Transport the iso across `restrictStalkNatIso` to the stalk at `(U x).ι x' = x`.
    have hGφ : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} ((U x).ι x')).map
        ((Scheme.Modules.toPresheaf X).map φ)) :=
      (CategoryTheory.NatIso.isIso_map_iff
        (Scheme.Modules.restrictStalkNatIso (U x).ι x') φ).mp hFφ
    exact hx' ▸ hGφ
  -- Package as a morphism of `TopCat.Sheaf Ab X` and apply the stalkwise iso criterion.
  let MS : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let NS : TopCat.Sheaf Ab.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let fS : MS ⟶ NS := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  haveI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fS.hom) := hst
  haveI hSiso : IsIso fS := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fS
  have h1 : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    have := (TopCat.Sheaf.forget Ab.{u} X).map_isIso fS
    exact this
  exact (CategoryTheory.isIso_iff_of_reflects_iso φ (Scheme.Modules.toPresheaf X)).mp h1

/-- **A-bridge step (ii): promote an `𝒪_X`-linear `Ab`-presheaf morphism to a module
morphism.** Given a morphism `g : M.presheaf ⟶ N.presheaf` of the underlying
`Ab`-presheaves that is sectionwise `𝒪_X`-linear, package it as a morphism `M ⟶ N`
of `𝒪_X`-modules. This wraps `PresheafOfModules.homMk` at the `Scheme.Modules` level;
it is the "promote to `𝒪_X`-linear" half of the descent A-bridge `homOfLocalCompat`
(the ab-sheaf gluing produces the linear `g`; this lemma turns it into a module map).
Sectionwise linearity is a property the consumer checks on a separated presheaf. -/
noncomputable def homMk {X : Scheme.{u}} {M N : X.Modules}
    (g : M.val.presheaf ⟶ N.val.presheaf)
    (hg : ∀ (V : (TopologicalSpace.Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj V) (m : M.val.obj V),
      (g.app V).hom (r • m) = r • (g.app V).hom m) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk (M₁ := M.val) (M₂ := N.val) g hg⟩

/-- The underlying `Ab`-presheaf morphism of `homMk g hg` is `g` itself. -/
@[simp] lemma toPresheaf_map_homMk {X : Scheme.{u}} {M N : X.Modules}
    (g : M.val.presheaf ⟶ N.val.presheaf)
    (hg : ∀ (V : (TopologicalSpace.Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj V) (m : M.val.obj V),
      (g.app V).hom (r • m) = r • (g.app V).hom m) :
    (Scheme.Modules.toPresheaf X).map (homMk g hg) = g :=
  rfl

-- Tensor-inverse existence is proved downstream as `Modules.exists_tensorObj_inverse` in
-- `TensorObjInverse.lean`.

/-! ## §5. The invertibility-carrier Picard group `picCommGroup`

This is the by-hand commutative-group law on isomorphism classes of `⊗`-invertible
`𝒪_X`-modules (blueprint §`sec:tensorobj_pic_carrier`). Every group axiom is a single
existence-of-isomorphism `Nonempty (… ≅ …)` read as an equality of iso-classes; no
pentagon/triangle/hexagon coherence and no `MonoidalCategory` instance is invoked.
The inverse is carried by the membership witness of `IsInvertible` itself. -/

/-- **Step 1 — associator on `⊗`-invertible objects** (blueprint
`lem:tensorobj_assoc_iso_invertible`). An immediate specialisation of the now
*unconditional* `tensorObj_assoc_iso`; the invertibility hypotheses are not consumed
(they match the blueprint statement). -/
noncomputable def tensorObj_assoc_iso_invertible {X : Scheme.{u}} {M N P : X.Modules}
    (_hM : IsInvertible M) (_hN : IsInvertible N) (_hP : IsInvertible P) :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) :=
  tensorObj_assoc_iso

/-- **Middle-four interchange for `⊗_X`** (helper). For arbitrary `𝒪_X`-modules
`A, B, C, D`, there is an isomorphism `(A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D)`,
assembled from the unconditional associator and the braiding (no coherence consumed).
Used to reassociate the four factors in `IsInvertible.tensorObj`. -/
private noncomputable def tensorObj_middleFour {X : Scheme.{u}} (A B C D : X.Modules) :
    tensorObj (tensorObj A B) (tensorObj C D)
      ≅ tensorObj (tensorObj A C) (tensorObj B D) :=
  tensorObj_assoc_iso ≪≫
    tensorObjIsoOfIso (Iso.refl A)
      (tensorObj_assoc_iso.symm ≪≫
        tensorObjIsoOfIso (tensorObj_braiding B C) (Iso.refl D) ≪≫
        tensorObj_assoc_iso) ≪≫
    tensorObj_assoc_iso.symm

/-- **Step 3 — `⊗`-invertibility is closed under tensor product** (blueprint
`lem:isinvertible_tensor`). If `M, M'` are `⊗`-invertible with inverses `N, N'`,
then `N ⊗ N'` is a tensor inverse of `M ⊗ M'`. -/
theorem IsInvertible.tensorObj {X : Scheme.{u}} {M M' : X.Modules}
    (hM : IsInvertible M) (hM' : IsInvertible M') :
    IsInvertible (Scheme.Modules.tensorObj M M') := by
  obtain ⟨N, ⟨e⟩⟩ := hM
  obtain ⟨N', ⟨e'⟩⟩ := hM'
  exact ⟨Scheme.Modules.tensorObj N N',
    ⟨tensorObj_middleFour M M' N N' ≪≫ tensorObjIsoOfIso e e' ≪≫ tensorObj_unit_iso⟩⟩

/-- **Step 4 — the structure sheaf is `⊗`-invertible** (blueprint
`lem:isinvertible_unit`). Witness `𝒪_X`, iso `tensorObj_unit_iso`. -/
theorem isInvertible_unit {X : Scheme.{u}} :
    IsInvertible (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨SheafOfModules.unit X.ringCatSheaf, ⟨tensorObj_unit_iso⟩⟩

/-- **Step 5 — the tensor inverse is determined up to isomorphism** (blueprint
`lem:isinvertible_inverse_welldef`). If `M ⊗ N ≅ 𝒪_X` and `M ⊗ N' ≅ 𝒪_X` then
`N ≅ N'`, via the inverse-of-inverse chain. -/
theorem IsInvertible.inverse_unique {X : Scheme.{u}} {M N N' : X.Modules}
    (e : Scheme.Modules.tensorObj M N ≅ SheafOfModules.unit X.ringCatSheaf)
    (e' : Scheme.Modules.tensorObj M N' ≅ SheafOfModules.unit X.ringCatSheaf) :
    Nonempty (N ≅ N') :=
  ⟨(tensorObj_right_unitor N).symm ≪≫
    tensorObjIsoOfIso (Iso.refl N) e'.symm ≪≫
    tensorObj_assoc_iso.symm ≪≫
    tensorObjIsoOfIso (tensorObj_braiding N M ≪≫ e) (Iso.refl N') ≪≫
    tensorObj_left_unitor N'⟩

/-- The setoid of `⊗`-invertible `𝒪_X`-modules: `M ∼ M'` iff there exists an
isomorphism `M ≅ M'` (blueprint `def:pic_carrier`). -/
instance picSetoid (X : Scheme.{u}) : Setoid {M : X.Modules // IsInvertible M} where
  r M M' := Nonempty ((M : X.Modules) ≅ (M' : X.Modules))
  iseqv :=
    ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- **Step 2 — the invertibility-carrier Picard group** (blueprint
`def:pic_carrier`): the quotient of `⊗`-invertible `𝒪_X`-modules by isomorphism. -/
def PicGroup (X : Scheme.{u}) : Type _ := Quotient (picSetoid X)

/-- Multiplication on `PicGroup X`: `[M] · [M'] := [M ⊗_X M']`, well-defined on
iso-classes by bifunctoriality (`tensorObjIsoOfIso`), landing in `PicGroup` by
`IsInvertible.tensorObj`. -/
noncomputable def picMul {X : Scheme.{u}} : PicGroup X → PicGroup X → PicGroup X :=
  Quotient.lift₂
    (fun a b => Quotient.mk _ ⟨tensorObj a.1 b.1, a.2.tensorObj b.2⟩)
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨a', ha'⟩ ⟨b', hb'⟩ ⟨ea⟩ ⟨eb⟩
      exact Quotient.sound ⟨tensorObjIsoOfIso ea eb⟩)

/-- The inverse class on `PicGroup X`: `[M] ↦ [N]` for the membership witness `N`
of `IsInvertible M`, well-defined by `IsInvertible.inverse_unique`. -/
noncomputable def picInv {X : Scheme.{u}} : PicGroup X → PicGroup X :=
  Quotient.lift
    (fun a => Quotient.mk _
      ⟨Classical.choose a.2,
        a.1, ⟨tensorObj_braiding _ a.1 ≪≫ (Classical.choose_spec a.2).some⟩⟩)
    (by
      rintro ⟨a, ha⟩ ⟨a', ha'⟩ ⟨ea⟩
      refine Quotient.sound ?_
      -- both `Classical.choose ha` and `Classical.choose ha'` are tensor inverses of `a`
      have h1 : tensorObj a (Classical.choose ha) ≅ SheafOfModules.unit X.ringCatSheaf :=
        (Classical.choose_spec ha).some
      have h2 : tensorObj a (Classical.choose ha') ≅ SheafOfModules.unit X.ringCatSheaf :=
        tensorObjIsoOfIso ea (Iso.refl _) ≪≫ (Classical.choose_spec ha').some
      exact IsInvertible.inverse_unique h1 h2)

/-- **Step 6 — the invertibility-carrier Picard group is abelian** (blueprint
`thm:pic_commgroup`). `[M] · [M'] := [M ⊗_X M']`, `1 := [𝒪_X]`, and `[M]⁻¹` the
class of any membership witness of `IsInvertible M`. Each group axiom is a single
existence-of-isomorphism: unit laws ← unitors, associativity ← associator,
commutativity ← braiding, left inverse ← the witness iso. No monoidal coherence. -/
noncomputable instance picCommGroup (X : Scheme.{u}) : CommGroup (PicGroup X) where
  mul := picMul
  one := Quotient.mk _ ⟨SheafOfModules.unit X.ringCatSheaf, isInvertible_unit⟩
  inv := picInv
  mul_assoc := by
    rintro a b c
    induction a using Quotient.ind with | _ a => ?_
    induction b using Quotient.ind with | _ b => ?_
    induction c using Quotient.ind with | _ c => ?_
    exact Quotient.sound ⟨tensorObj_assoc_iso⟩
  one_mul := by
    rintro a
    induction a using Quotient.ind with | _ a => ?_
    exact Quotient.sound ⟨tensorObj_left_unitor a.1⟩
  mul_one := by
    rintro a
    induction a using Quotient.ind with | _ a => ?_
    exact Quotient.sound ⟨tensorObj_right_unitor a.1⟩
  inv_mul_cancel := by
    rintro a
    induction a using Quotient.ind with | _ a => ?_
    exact Quotient.sound
      ⟨tensorObj_braiding (Classical.choose a.2) a.1 ≪≫ (Classical.choose_spec a.2).some⟩
  mul_comm := by
    rintro a b
    induction a using Quotient.ind with | _ a => ?_
    induction b using Quotient.ind with | _ b => ?_
    exact Quotient.sound ⟨tensorObj_braiding a.1 b.1⟩

/-! ## §6. Pullback-monoidality substrate (A.1.c): `IsInvertible.pullback`

Project-local Mathlib supplement. The relative Picard consumer re-bases onto the
`IsInvertible` carrier and its structure maps are *pullback* maps for GENERAL scheme
morphisms (the projection `C ×_S T → T` and base-change maps are neither open
immersions nor flat). We need that pullback preserves `⊗`-invertibility. This requires
`pullbackTensorIso` (`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`) and `pullbackUnitIso`
(`f^*𝒪_X ≅ 𝒪_Y`). Blueprint §`sec:tensorobj_pullback_monoidality`. -/

/-- **Composition coherence of the unit→pushforward-unit comparison.**

For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X`, the canonical comparison
`unitToPushforwardObjUnit` of the composite `h ≫ f` factors through the comparisons
of `f` and `h` and the pushforward pseudofunctor coherence `pushforwardComp`. This is
the *pushforward-side* (right-adjoint) half of the composition coherence; it is
concrete (sectionwise it is just functoriality of the structure-sheaf ring maps,
hence `rfl` after the `ext`-chain) and is the pushforward-side input from which the
genuinely-needed *pullback-side* coherence of `pullbackObjUnitToUnit` is obtained by
adjunction-mate transport. Mathlib-absent at the pinned commit. -/
lemma unitToPushforwardObjUnit_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    SheafOfModules.unitToPushforwardObjUnit (h ≫ f).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp h f).hom.app (SheafOfModules.unit Z.ringCatSheaf) := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- **Composition coherence of the unit comparison `pullbackObjUnitToUnit`
(the genuinely-new ingredient for `pullbackUnitIso`).**

For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X`, the canonical comparison
`f^*𝒪 ⟶ 𝒪` of the composite `h ≫ f` factors through the comparisons of `f` and `h`
and the pullback pseudofunctor coherence `pullbackComp`:
`pullbackObjUnitToUnit (h≫f) = (pullbackComp h f).inv ≫ (pullback h).map (pbu f) ≫ pbu h`.

This is the pullback-side (left-adjoint) composition coherence — Mathlib-absent at the
pinned commit and NOT a sectionwise statement (the abstract left-adjoint pullback has no
sectionwise value). It is obtained by adjunction-mate transport from the pushforward-side
coherence `unitToPushforwardObjUnit_comp`: transposing both sides under
`pullbackPushforwardAdjunction (h≫f)`, the left side becomes `unitToPushforwardObjUnit (h≫f)`
and the right side is reassembled via the conjugate/mate identity
`conjugateEquiv_pullbackComp_inv` (relating `pullbackComp.inv` to `pushforwardComp.hom`),
`unit_conjugateEquiv`, and the composite-adjunction unit `Adjunction.comp_unit_app`.

Consumed by `pullbackUnitIso`: on an affine chart `V` the inclusion `V.ι ≫ f` factors as
`g ≫ U.ι` with `Opens.map g.base` `Final`, so two applications of this coherence (one for
each factorisation) express the restricted global comparison as a composite of isomorphisms
(`pbu` for an open immersion / a `Final`-chart morphism is an iso), whence
`pullbackObjUnitToUnit f` is an iso by `isIso_of_isIso_restrict`.

The proof uses `erw` for the associativity / functoriality steps because the `SheafOfModules`
category compositions appear in defeq-but-not-syntactic forms (`Scheme.Modules.pullback f`
vs `SheafOfModules.pullback f.toRingCatSheafHom`) on which plain `rw [Category.assoc]` /
`rw [Functor.map_comp]` fail to unify. -/
lemma pullbackObjUnitToUnit_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    SheafOfModules.pullbackObjUnitToUnit (h ≫ f).toRingCatSheafHom =
      (Scheme.Modules.pullbackComp h f).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pullback h).map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
      SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom := by
  have key := unitToPushforwardObjUnit_comp h f
  have conj := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction h))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f))
    (Scheme.Modules.pullbackComp h f).inv (SheafOfModules.unit X.ringCatSheaf)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at conj
  apply (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)).homEquiv _ _ |>.injective
  have hL : (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit (h ≫ f).toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit (h ≫ f).toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (h ≫ f).toRingCatSheafHom
  have hi : (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)).homEquiv _ _
      ((Scheme.Modules.pullbackComp h f).inv.app (SheafOfModules.unit X.ringCatSheaf))
    = ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pushforwardComp h f).hom.app
          ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).obj
            (SheafOfModules.unit X.ringCatSheaf)) := by
    rw [Adjunction.homEquiv_unit]; exact conj.symm
  have hLf : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  have hLh : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      h.toRingCatSheafHom
  have hinner : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
        ((Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward h).map
        ((Scheme.Modules.pullback h).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
    have e := Adjunction.homEquiv_unit (adj := Scheme.Modules.pullbackPushforwardAdjunction h)
      (X := (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf))
      (Y := SheafOfModules.unit Z.ringCatSheaf)
      (f := (Scheme.Modules.pullback h).map
          (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    have key2 : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          ((Scheme.Modules.pullback h).map
              (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
        = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
            SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
      rw [Adjunction.homEquiv_naturality_left]; exact congrArg _ hLh
    exact e.symm.trans key2
  have hcomp' : ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullback h).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) := by
    have ef := Adjunction.homEquiv_unit (adj := Scheme.Modules.pullbackPushforwardAdjunction f)
      (X := SheafOfModules.unit X.ringCatSheaf) (Y := SheafOfModules.unit Y.ringCatSheaf)
      (f := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    rw [Adjunction.comp_unit_app, Functor.comp_map]
    erw [Category.assoc, ← Functor.map_comp, hinner, Functor.map_comp]
    erw [← Category.assoc]
    rw [show (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pushforward f).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
        = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom from ef.symm.trans hLf]
    rfl
  rw [hL, key, Adjunction.homEquiv_naturality_right, hi]
  erw [Category.assoc, ← (Scheme.Modules.pushforwardComp h f).hom.naturality
      ((Scheme.Modules.pullback h).map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)]
  erw [← Category.assoc, hcomp']
  erw [Category.assoc]

/-! ### Pullback of the structure sheaf

The comparison `SheafOfModules.pullbackObjUnitToUnit f` is an isomorphism for every
scheme morphism. Indeed, preimage on opens is representably flat, hence the comparison
functor `Opens.map f.base` is final. The helper below isolates that finality instance so
the implicit adjunction data of `pullbackObjUnitToUnit` are synthesized canonically. -/

/-- **`IsIso (pullbackObjUnitToUnit g)` from a single `Final` hypothesis, at a clean site.**
Project-local: isolates the lone `(Opens.map g.base).Final` instance so that the Mathlib
`OfFinal` instance synthesises without colliding with other finality hypotheses. -/
private lemma isIso_pbu_of_final {X Y : Scheme.{u}} (g : Y ⟶ X)
    [(TopologicalSpace.Opens.map g.base).Final] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance

/-- **Bundled `Iso` form of the unit comparison `pullbackObjUnitToUnit g`** for a `Final`
comparison functor — the analogue of `CategoryTheory.Functor.Monoidal.μIso`. Project-local:
hands out the isomorphism (rather than a bare `IsIso` instance) so downstream coherence
reasoning stays at the `Iso` level and never re-triggers the `pbu` instance synthesis. -/
noncomputable def pullbackObjUnitToUnitIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    [(TopologicalSpace.Opens.map g.base).Final] :
    (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
    (isIso_pbu_of_final g)

@[simp] lemma pullbackObjUnitToUnitIso_hom {X Y : Scheme.{u}} (g : Y ⟶ X)
    [(TopologicalSpace.Opens.map g.base).Final] :
    (pullbackObjUnitToUnitIso g).hom =
      SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom := rfl

/-- **Pullback preserves the structure sheaf** (blueprint `lem:pullback_unit_iso`):
`f^*𝒪_X ≅ 𝒪_Y` for an arbitrary morphism of schemes `f : Y ⟶ X`, where
`𝒪_X = SheafOfModules.unit X.ringCatSheaf`. The comparison functor `Opens.map f.base` is
always `Final` (preimage on opens is representably flat), so the Mathlib unit comparison
`pullbackObjUnitToUnit f` is an isomorphism unconditionally. -/
noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  haveI : (TopologicalSpace.Opens.map f.base).Final := final_of_representablyFlat _
  pullbackObjUnitToUnitIso f

/-- **Sheafification reconciles the presheaf tensor with the tensor of the
sheafified factors.** For presheaves of modules `P, Q` on `X`, sheafifying the
presheaf tensor `P ⊗ Q` agrees with sheafifying the tensor of the underlying
presheaves of their sheafifications `(a P).val ⊗ (a Q).val`, where
`a = PresheafOfModules.sheafification (𝟙 𝒪_X)`. This is the "sheafification is
monoidal" reconciliation, built — exactly as in `tensorObj_assoc_iso` — by
whiskering the sheafification unit `η` (a `J.W`-morphism, hence locally bijective)
on each side and inverting under `a` via `isIso_sheafification_map_of_W` together
with the flatness-free `W_whisker{Right,Left}_of_W`. It is the bridge reconciling a
presheaf-level tensorator with the substrate `⊗_X` (whose `.val` carries an extra
sheafification on each factor), as needed by the pullback-monoidality comparison
`pullbackTensorIso`. -/
noncomputable def sheafifyTensorUnitIso {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) ≅
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          ((PresheafOfModules.sheafification
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P).val
          ((PresheafOfModules.sheafification
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj Q).val) := by
  letI instMS : MonoidalCategoryStruct (_root_.PresheafOfModules (X.ringCatSheaf.obj)) :=
    inferInstanceAs (MonoidalCategoryStruct
      (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
  set a := PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) with ha
  set η := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit with hη
  have hηP : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app P)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hηQ : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app Q)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hW1 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app P ▷ Q)) :=
    PresheafOfModules.W_whiskerRight_of_W (R := X.presheaf) Q (η.app P) hηP
  have hW2 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map ((a.obj P).val ◁ η.app Q)) :=
    PresheafOfModules.W_whiskerLeft_of_W (R := X.presheaf) (a.obj P).val (η.app Q) hηQ
  have hi1 : IsIso (a.map (η.app P ▷ Q)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.obj) _ hW1
  have hi2 : IsIso (a.map ((a.obj P).val ◁ η.app Q)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.obj) _ hW2
  exact (@asIso _ _ _ _ _ hi1) ≪≫ (@asIso _ _ _ _ _ hi2)

/-- **The presheaf-of-modules pushforward is lax monoidal** (the analogist-named `μ_G`,
Mathlib-absent at the pin). For a morphism `φ : S₀ ⋙ forget₂ ⟶ F.op ⋙ (R₀ ⋙ forget₂)`
of presheaves of *commutative* rings, `PresheafOfModules.pushforward φ` unfolds to
`pushforward₀OfCommRingCat F R₀ ⋙ restrictScalars φ`, the composite of the strong-monoidal
topological pushforward `pushforward₀OfCommRingCat` (Mathlib) and the lax-monoidal
`restrictScalars φ` (project `restrictScalarsLaxMonoidal`), hence lax monoidal by
`Functor.LaxMonoidal.comp`.

The hypothesis necessarily uses the *inner* `forget₂` association (`F.op ⋙ (R₀ ⋙ forget₂)`,
the form `PresheafOfModules.pushforward` expects), but the monoidal-category instance on the
middle presheaf is keyed on the *outer* association `(F.op ⋙ R₀) ⋙ forget₂` (the form
`pushforward₀OfCommRingCat`'s target carries). The two are defeq; bridging them with a local
`MonoidalCategory` instance triggers a kernel-rejected diamond, so instead `φ` is defeq-cast
to the outer form (`φ'`) for the `restrictScalars` factor, and the resulting composite — defeq
to `pushforward φ` — is transported back by `exact`. Its mate supplies the oplax
comparison `δ` on the abstract left-adjoint pullback below. -/
noncomputable instance presheafPushforwardLaxMonoidal
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforward φ).LaxMonoidal := by
  let φ' : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      (F.op ⋙ R₀) ⋙ forget₂ CommRingCat RingCat := φ
  have h : (PresheafOfModules.pushforward₀OfCommRingCat F R₀ ⋙
      PresheafOfModules.restrictScalars φ').LaxMonoidal := inferInstance
  exact h

/-- **The abstract presheaf-of-modules pullback is oplax monoidal**, with canonical
comparison map `δ_{A,B} : f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B`. This is the mate of the lax
tensorator of `pushforward φ` (`presheafPushforwardLaxMonoidal`) across the
pullback–pushforward adjunction, via Mathlib's doctrinal `leftAdjointOplaxMonoidal`. It
supplies the canonical comparison map for the abstract left adjoint without a sectionwise
model. No `MonoidalCategory (SheafOfModules)` instance is needed: the comparison lives in
the monoidal category of presheaves of modules. Its sheafification is proved invertible on
line bundles below by reducing to the unit case on a trivializing cover. -/
noncomputable instance presheafPullbackOplaxMonoidal
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    [(PresheafOfModules.pushforward φ).IsRightAdjoint] :
    (PresheafOfModules.pullback φ).OplaxMonoidal :=
  (PresheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal

/-! ### Pullback and tensor products

The abstract presheaf pullback is oplax monoidal, so it carries a canonical comparison
map `δ : f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`. For arbitrary modules this map need not be an
isomorphism. The relative Picard construction only needs the result for line bundles;
there it follows locally from the unit case and globally from local triviality. Thus the
proof below sheafifies `δ`, proves the unit comparison, and descends isomorphism along a
trivializing cover, without constructing a concrete strong-monoidal inverse-image functor. -/

/-- **Identifying the sheafified presheaf-pullback of `M.val` with the abstract pullback.**
For `f : Y ⟶ X` and `M : X.Modules`, sheafifying the presheaf-level pullback of the
underlying presheaf `M.val` recovers the abstract `𝒪`-module pullback `(pullback f).obj M`.
This is the per-object form of `SheafOfModules.sheafificationCompPullback` composed with the
sheafification counit on the (already-sheaf) `M`; it is the bridge used to reconcile the
right-hand side of the pullback–tensor comparison `pullbackTensorMap` with the substrate
`tensorObj` of the pullbacks. -/
noncomputable def pullbackValIso {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback (f.toRingCatSheafHom).hom).obj M.val)
      ≅ (Scheme.Modules.pullback f).obj M :=
  ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app M.val).symm ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit).app M)

/-- **The sheaf-level pullback–tensor comparison map `δ_sheaf`** (blueprint
`lem:pullback_tensor_map`). For a morphism of schemes `f : Y ⟶ X` and arbitrary
`M N : X.Modules`, the canonical comparison morphism
`f^*(M ⊗_X N) ⟶ f^*M ⊗_Y f^*N`. It is the sheaf-level transport of the presheaf-level
oplax comparison `δ` (`presheafPullbackOplaxMonoidal`) through sheafification, assembled
from the `sheafificationCompPullback` device, `sheafifyTensorUnitIso`, and `pullbackValIso`.
This is a *map only*: in general it is not asserted to be an isomorphism (the invertible
case is upgraded to an iso by local trivialisation in `IsInvertible.pullback`). -/
noncomputable def pullbackTensorMap {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ⟶
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  let φ := f.toRingCatSheafHom
  let φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := φ.hom
  let a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)
  refine ((SheafOfModules.sheafificationCompPullback φ).app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫ ?_
  refine a_Y.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val) ≫ ?_
  refine (sheafifyTensorUnitIso (X := Y)
      ((PresheafOfModules.pullback φ').obj M.val)
      ((PresheafOfModules.pullback φ').obj N.val)).hom ≫ ?_
  exact a_Y.map (MonoidalCategory.tensorHom
    (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
    ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
    ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom))

/-! ## Project-local Mathlib supplement — D1: the presheaf pullback Lan decomposition

These are general `PresheafOfModules` statements (any `F : C ⥤ D`, ring presheaves
`R, S`), not specific to schemes; they are project-local because Mathlib's pinned commit
exposes neither `extendScalars` nor `pullback₀` at the presheaf-of-modules level. Both are
realised as the left adjoint of an existing right adjoint: `pushforward₀ F R` is
definitionally `pushforward (𝟙 (F.op ⋙ R))` (because `restrictScalars (𝟙) = 𝟭` on the nose,
witnessed by Mathlib's `restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full`), and
`restrictScalars φ` is definitionally `pushforward (F := 𝟭) φ`; since `pushforward _` is
always a right adjoint, so are these two, and their left adjoints `pullback₀`/`extendScalars`
exist. The decomposition `pullback φ ≅ extendScalars φ ⋙ pullback₀` then follows from the
definitional factorisation `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ` by
uniqueness of left adjoints (`Adjunction.leftAdjointCompIso`).

Per blueprint `lem:pullback_lan_decomposition` (D1). The local-triviality argument below
does not use this decomposition, but it is retained as reusable presheaf infrastructure. -/

section PullbackLanDecomposition

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- `pushforward₀ F R` is a right adjoint: it is definitionally `pushforward (𝟙 (F.op ⋙ R))`
(since `restrictScalars (𝟙) = 𝟭` on the nose). Project-local; carries the existence of the
topological inverse image `pullback₀`. -/
private lemma pushforward₀IsRightAdjoint (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) :
    (PresheafOfModules.pushforward₀.{u} F R).IsRightAdjoint :=
  inferInstanceAs (PresheafOfModules.pushforward.{u} (𝟙 (F.op ⋙ R))).IsRightAdjoint

/-- `restrictScalars φ` is a right adjoint: it is definitionally `pushforward (F := 𝟭) φ`.
Project-local; carries the existence of the extension of scalars `extendScalars`. -/
private lemma restrictScalarsIsRightAdjoint (φ : S ⟶ F.op ⋙ R) :
    (PresheafOfModules.restrictScalars.{u} φ).IsRightAdjoint :=
  inferInstanceAs
    (PresheafOfModules.pushforward.{u} (F := 𝟭 C) (R := F.op ⋙ R) φ).IsRightAdjoint

/-- **The topological inverse image `pullback₀ := (pushforward₀ F R).leftAdjoint`**, the
left adjoint of the fixed-ring pushforward. On underlying presheaves it is the left Kan
extension along `F.op`. Project-local (no `PresheafOfModules` inverse-image functor at the
pin); the carrier of D3. -/
noncomputable def pullback0 (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) :
    _root_.PresheafOfModules.{u} (F.op ⋙ R) ⥤ _root_.PresheafOfModules.{u} R :=
  haveI := pushforward₀IsRightAdjoint F R
  (PresheafOfModules.pushforward₀ F R).leftAdjoint

/-- **Extension of scalars `extendScalars φ := (restrictScalars φ).leftAdjoint`**, the left
adjoint of restriction of scalars along a morphism of ring presheaves. Project-local; the
carrier of D2 (strong monoidal via `distribBaseChange`). -/
noncomputable def extendScalars (φ : S ⟶ F.op ⋙ R) :
    _root_.PresheafOfModules.{u} S ⥤ _root_.PresheafOfModules.{u} (F.op ⋙ R) :=
  haveI := restrictScalarsIsRightAdjoint φ
  (PresheafOfModules.restrictScalars φ).leftAdjoint

/-- The adjunction `pullback₀ ⊣ pushforward₀`. -/
noncomputable def pullback0Adjunction (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) :
    pullback0 F R ⊣ PresheafOfModules.pushforward₀ F R :=
  haveI := pushforward₀IsRightAdjoint F R
  Adjunction.ofIsRightAdjoint (PresheafOfModules.pushforward₀ F R)

/-- The adjunction `extendScalars φ ⊣ restrictScalars φ`. -/
noncomputable def extendScalarsAdjunction (φ : S ⟶ F.op ⋙ R) :
    extendScalars φ ⊣ PresheafOfModules.restrictScalars φ :=
  haveI := restrictScalarsIsRightAdjoint φ
  Adjunction.ofIsRightAdjoint (PresheafOfModules.restrictScalars φ)

/-- **D1 — the presheaf pullback Lan decomposition** (blueprint `lem:pullback_lan_decomposition`).
For `φ : S ⟶ F.op ⋙ R` presenting a pushforward of presheaves of modules, the presheaf
pullback factors as extension of scalars followed by the topological inverse image,
`pullback φ ≅ extendScalars φ ⋙ pullback₀`. This is the left-adjoint reversal of the
definitional factorisation `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ`, obtained
from `Adjunction.leftAdjointCompIso` (uniqueness of left adjoints). Project-local. -/
noncomputable def pullbackLanDecomposition (φ : S ⟶ F.op ⋙ R) :
    PresheafOfModules.pullback φ ≅ extendScalars φ ⋙ pullback0 F R :=
  (Adjunction.leftAdjointCompIso
    (extendScalarsAdjunction φ) (pullback0Adjunction F R)
    (PresheafOfModules.pullbackPushforwardAdjunction φ)
    (Iso.refl (PresheafOfModules.pushforward φ))).symm

end PullbackLanDecomposition

/-! ## Project-local Mathlib supplement — D1'–D4' loc-triv pullback–tensor comparison

The locally-trivial-restricted upgrade of the oplax comparison map
`pullbackTensorMap` (`f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`) to an isomorphism, blueprint
§`sec:tensorobj_pullback_monoidality`, sub-lemmas D1'–D4'. -/

section LocTrivPullbackTensor

/-- **The sheafified `⊗ₘ` of the two `pullbackValIso`s is an isomorphism.**
Factored out so the `tensorIso (C := _ ⋙ forget₂)` elaboration mirrors
`tensorObjIsoOfIso`; elaborating it inside a tactic block with `extract_lets` locals is
prohibitively expensive. This supports
`isIso_pullbackTensorMap_of_isIso_sheafifyDelta`. -/
private lemma isIso_sheafify_tensorHom_pullbackValIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (M N : X.Modules) :
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
      (MonoidalCategory.tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom))) :=
  ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso
      (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
      ((SheafOfModules.forget Y.ringCatSheaf).mapIso (pullbackValIso f M))
      ((SheafOfModules.forget Y.ringCatSheaf).mapIso (pullbackValIso f N)))).isIso_hom

/-- **Reduction of `pullbackTensorMap` iso-ness to the sheafified presheaf δ.**

`pullbackTensorMap f M N` is the four-fold composite
`(sheafificationCompPullback).hom ≫ a_Y.map δ ≫ (sheafifyTensorUnitIso).hom ≫
  a_Y.map (tensorHom …)`.
Three of the four factors (`sheafificationCompPullback`, `sheafifyTensorUnitIso`,
and the `tensorHom` of the two `pullbackValIso`s) are isomorphisms unconditionally;
the only conditional factor is the sheafification `a_Y.map δ` of the presheaf-level
oplax comparison `δ`. Hence `pullbackTensorMap f M N` is an iso whenever that
sheafified δ is an iso. This isolates the only remaining content, the sheafified `δ`,
for D2' (unit pair) and D4' (chart-chase). Project-local. -/
lemma isIso_pullbackTensorMap_of_isIso_sheafifyDelta {X Y : Scheme.{u}}
    (f : Y ⟶ X) (M N : X.Modules)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.obj)).map
          (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val))) :
    IsIso (pullbackTensorMap f M N) := by
  unfold pullbackTensorMap
  extract_lets φ φ' a_Y
  -- piece 2 (the sheafified δ) is the only conditional factor — supplied by `h`.
  haveI hδ : IsIso (a_Y.map
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val)) := h
  -- pieces 1 and 3 are `Iso.hom`s; piece 4 is `a_Y.map` of the (iso) `⊗ₘ` of the two
  -- `pullbackValIso`s, supplied by the factored top-level helper.
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hδ
    (IsIso.comp_isIso' inferInstance (isIso_sheafify_tensorHom_pullbackValIso f M N)))

/-- **Converse of `isIso_sheafification_map_of_W`.** A morphism of presheaves of modules whose
image under the associated-sheaf functor is an isomorphism lies (on underlying additive presheaves)
in the sheafification localizer `J.W`. This is the same morphism-property identity
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` (the sheafification
functor *is* the localization at `J.W.inverseImage (toPresheaf _)`) read backwards. Project-local:
needed to feed the flatness-free whiskering lemmas `W_whisker{Left,Right}_of_W` from a sheafified
iso (the D2' η-bridge route, below). -/
private lemma W_of_isIso_sheafification {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat} {Rsh : CategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ Rsh.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat] [CategoryTheory.HasWeakSheafify J AddCommGrpCat]
    {A B : _root_.PresheafOfModules.{u} R₀} (f : A ⟶ B)
    (hf : IsIso ((PresheafOfModules.sheafification α).map f)) :
    J.W ((PresheafOfModules.toPresheaf R₀).map f) := by
  have h := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (J := J) α
  have h2 : (CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules Rsh)).inverseImage
      (PresheafOfModules.sheafification α) f := hf
  rw [← h] at h2
  exact h2

/-- **D2' δ-wrapping — the sheafified cotensorator on the unit pair is an iso, given the η-bridge.**

The presheaf-level oplax unitality `Functor.OplaxMonoidal.left_unitality_hom` factors the
cotensorator `δ (pullback φ') 𝟙_ 𝟙_` of the abstract presheaf pullback through the unit comparison
`η (pullback φ')` (right-whiskered by `F.obj 𝟙_`) and the (iso) left unitor. Sheafifying, the
unitor factor and the `F.map (λ_ 𝟙_)` factor are isomorphisms unconditionally; the whiskered
`η`-factor `a_Y.map (η F ▷ F.obj 𝟙_)` is an iso whenever `a_Y.map (η F)` is — because a sheafified
iso lies in `J.W` (`W_of_isIso_sheafification`), `J.W` is stable under right-whiskering
(`W_whiskerRight_of_W`, flatness-free), and `J.W`-morphisms sheafify to isos
(`isIso_sheafification_map_of_W`). Hence the sheafified `δ` on the unit pair is an iso, which is
exactly the hypothesis the reduction brick `isIso_pullbackTensorMap_of_isIso_sheafifyDelta` consumes
on `M = N = 𝒪`. Project-local; the **δ-wrapping** half of D2' (`lem:pullback_tensor_iso_unit`),
self-contained modulo the η-bridge `IsIso (a_Y.map (η (pullback φ')))`. -/
lemma isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')))) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ')
        (SheafOfModules.unit X.ringCatSheaf).val (SheafOfModules.unit X.ringCatSheaf).val)) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj) with ha
  change IsIso (a_Y.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') (𝟙_ _) (𝟙_ _)))
  set F := PresheafOfModules.pullback φ' with hF
  have hWη : (Opens.grothendieckTopology (Y : TopCat)).W
      ((PresheafOfModules.toPresheaf _).map (Functor.OplaxMonoidal.η F)) :=
    W_of_isIso_sheafification (𝟙 Y.ringCatSheaf.obj) _ h
  have hWw : (Opens.grothendieckTopology (Y : TopCat)).W
      ((PresheafOfModules.toPresheaf _).map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _))) :=
    PresheafOfModules.W_whiskerRight_of_W (R := Y.presheaf) _ _ hWη
  haveI hIsoW : IsIso (a_Y.map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _))) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 Y.ringCatSheaf.obj) _ hWw
  haveI hIsoLam : IsIso (a_Y.map (λ_ (F.obj (𝟙_ _))).hom) := inferInstance
  have hBC : IsIso (a_Y.map
      (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _) ≫ (λ_ (F.obj (𝟙_ _))).hom)) := by
    rw [Functor.map_comp]; infer_instance
  haveI hD : IsIso (a_Y.map (F.map (λ_ (𝟙_ _)).hom)) := inferInstance
  have hlu := Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ _)
  have key : a_Y.map (Functor.OplaxMonoidal.δ F (𝟙_ _) (𝟙_ _)) ≫
      a_Y.map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _) ≫ (λ_ (F.obj (𝟙_ _))).hom)
      = a_Y.map (F.map (λ_ (𝟙_ _)).hom) := by
    rw [← Functor.map_comp]; exact congrArg _ hlu
  have heq : a_Y.map (Functor.OplaxMonoidal.δ F (𝟙_ _) (𝟙_ _))
      = a_Y.map (F.map (λ_ (𝟙_ _)).hom) ≫
        inv (a_Y.map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _) ≫ (λ_ (F.obj (𝟙_ _))).hom)) := by
    rw [← key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]; infer_instance

/-- **Right-unit δ-wrapping for an arbitrary first factor.** If the sheafified oplax unit
comparison of presheaf pullback is an isomorphism, then so is the sheafified cotensorator
`a_Y.map (δ F M.val 𝟙_)`. The proof is the right-handed oplax unitality identity: the unit
comparison is left-whiskered by `F.obj M.val`, which preserves the sheafification localizer, and
the remaining two right-unitor maps are isomorphisms. No flatness or local-freeness assumption on
`M` is used. -/
lemma isIso_sheafifyDelta_rightUnit_of_isIso_sheafifyEta {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.obj)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')))) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.obj)).map
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val
        (SheafOfModules.unit X.ringCatSheaf).val)) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf)
    (𝟙 Y.ringCatSheaf.obj) with ha
  set F := PresheafOfModules.pullback φ' with hF
  change IsIso (a_Y.map (Functor.OplaxMonoidal.δ F M.val (𝟙_ _)))
  let ρX := (PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).rightUnitor M.val
  let ρY := (PresheafOfModules.monoidalCategoryStruct
    (R := Y.presheaf)).rightUnitor (F.obj M.val)
  have hWη : (Opens.grothendieckTopology (Y : TopCat)).W
      ((PresheafOfModules.toPresheaf _).map (Functor.OplaxMonoidal.η F)) :=
    W_of_isIso_sheafification (𝟙 Y.ringCatSheaf.obj) _ h
  have hWw : (Opens.grothendieckTopology (Y : TopCat)).W
      ((PresheafOfModules.toPresheaf _).map
        (F.obj M.val ◁ Functor.OplaxMonoidal.η F)) :=
    PresheafOfModules.W_whiskerLeft_of_W (R := Y.presheaf)
      (F.obj M.val) (Functor.OplaxMonoidal.η F) hWη
  haveI hIsoW : IsIso (a_Y.map (F.obj M.val ◁ Functor.OplaxMonoidal.η F)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 Y.ringCatSheaf.obj) _ hWw
  haveI hIsoRho : IsIso (a_Y.map ρY.hom) := inferInstance
  haveI hIsoComp :
      IsIso (a_Y.map (F.obj M.val ◁ Functor.OplaxMonoidal.η F ≫ ρY.hom)) := by
    rw [Functor.map_comp]
    infer_instance
  haveI hFmap : IsIso (a_Y.map (F.map ρX.hom)) := inferInstance
  have hru := Functor.OplaxMonoidal.right_unitality_hom F M.val
  have key : a_Y.map (Functor.OplaxMonoidal.δ F M.val (𝟙_ _)) ≫
      a_Y.map (F.obj M.val ◁ Functor.OplaxMonoidal.η F ≫ ρY.hom)
      = a_Y.map (F.map ρX.hom) := by
    rw [← Functor.map_comp]
    exact congrArg _ hru
  have heq : a_Y.map (Functor.OplaxMonoidal.δ F M.val (𝟙_ _))
      = a_Y.map (F.map ρX.hom) ≫
        inv (a_Y.map (F.obj M.val ◁ Functor.OplaxMonoidal.η F ≫ ρY.hom)) := by
    rw [← key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- **D2' assembly — `pullbackTensorMap` on the unit pair is an iso, given the η-bridge.**
Chains the δ-wrapping `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta` into the reduction brick
`isIso_pullbackTensorMap_of_isIso_sheafifyDelta` (on `M = N = 𝒪`). This is the full statement of
D2' (`lem:pullback_tensor_iso_unit`) modulo the single remaining η-bridge hypothesis
`IsIso (a_Y.map (η (pullback φ')))` (the sheafification-mate identification of the sheafified
presheaf unit comparison with `pullbackUnitIso`, the unit-side analog of
`pullbackObjUnitToUnit_comp`). Project-local. -/
lemma isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')))) :
    IsIso (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) := by
  apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta
  exact isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta f h

/-! ### The unit comparison

The following lemmas identify the sheafified oplax unit with the sheaf-level structure
sheaf comparison. This proves that `pullbackTensorMap` is an isomorphism on the unit pair,
which is the local input for the line-bundle argument. -/

/-- **Codomain identification for the D2' η-bridge.** The sheafification counit identifies the
sheafified presheaf monoidal unit `a_Y.obj 𝟙_` with the sheaf-level structure module
`𝒪_Y = SheafOfModules.unit Y.ringCatSheaf` (`𝟙_ = (unit Y).val` definitionally, and `unit Y` is
already a sheaf, so the counit at it is an isomorphism). This is the right-hand vertical of the
η-bridge square `a_Y.map (η (pullback φ')) ≫ sheafifyUnitIso.hom
= (pullbackValIso f 𝒪_X).hom ≫ pullbackObjUnitToUnit φ`. -/
noncomputable def sheafifyUnitIso {Y : Scheme.{u}} :
    (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).obj
        (𝟙_ (_root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).counit).app (SheafOfModules.unit Y.ringCatSheaf)

/-- **Presheaf-side mate identity for the η-bridge** (`unit_app_unit_comp_map_η` instantiated).
For a scheme morphism `f : Y ⟶ X` with `φ' = f.toRingCatSheafHom.hom`, the presheaf-of-modules
adjunction unit at the monoidal unit, post-composed with the pushforward of the oplax unit
comparison `η (pullback φ')`, recovers the lax unit `ε (pushforward φ')`. This is the
presheaf-level driver of the D2' η-bridge: under sheafification (via `sheafificationCompPullback`)
it transports to the sheaf identity
`homEquiv (pullbackObjUnitToUnit φ) = unitToPushforwardObjUnit φ`.
Project-local: it certifies that the project's `presheafPushforwardLaxMonoidal` /
`presheafPullbackOplaxMonoidal` instances are `Adjunction.IsMonoidal`-compatible, so the Mathlib
mate identity fires for this concrete adjunction. -/
lemma presheafUnit_comp_map_eta {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    (PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) ≫
      (PresheafOfModules.pushforward φ').map
        (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))
      = Functor.LaxMonoidal.ε (PresheafOfModules.pushforward φ') := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  haveI : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
  exact Adjunction.unit_app_unit_comp_map_η (PresheafOfModules.pullbackPushforwardAdjunction φ')

/-- **D2' η-bridge: reduction to the unit comparison square.**
Given the commuting square identifying the sheafified presheaf unit comparison `a_Y.map (η F)`
with the sheaf-level `pullbackObjUnitToUnit φ` through the canonical isos `pullbackValIso` and
`sheafifyUnitIso`, the η-bridge `IsIso (a_Y.map (η (pullback φ')))` follows (the comparison
`pullbackObjUnitToUnit φ` is an iso since `Opens.map f.base` is always `Final`). This isolates the
only mathematical content of the η-bridge as the square hypothesis `hsq`, the unit-side
analogue of `pullbackObjUnitToUnit_comp`. -/
lemma isIso_sheafifyEta_of_unitSquare {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hsq : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
            (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')) ≫ sheafifyUnitIso.hom
          = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
      (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj) with ha
  set F := PresheafOfModules.pullback φ' with hF
  haveI hfin : (TopologicalSpace.Opens.map f.base).Final := final_of_representablyFlat _
  haveI hpbu : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    isIso_pbu_of_final f
  have key : a_Y.map (Functor.OplaxMonoidal.η F) ≫ sheafifyUnitIso.hom
      = (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom :=
    (Iso.inv_comp_eq _).mp hsq
  rw [(Iso.eq_comp_inv sheafifyUnitIso).mpr key]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' inferInstance hpbu) inferInstance

/-- **Composite-adjunction `homEquiv` factorisation** (blueprint
`lem:comp_homequiv_factor_sheafify_pullback`, ★ step 3). For composable adjunctions
`adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂`, the hom-set bijection of the composite adjunction
`A = adj₁.comp adj₂ : L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` factors as the composite of the two factor
bijections: a morphism `(L₁ ⋙ L₂).obj c ⟶ e` is transposed first across `adj₂` and then
across `adj₁`. This is the standard naturality of `homEquiv` under composition of adjunctions,
read off the `homEquiv = unit ≫ R.map` formula together with `Adjunction.comp_unit_app`.
Project-local. -/
lemma compHomEquivFactor {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {c : C₁} {e : C₃}
    (g : (L₁ ⋙ L₂).obj c ⟶ e) :
    (adj₁.comp adj₂).homEquiv c e g
      = adj₁.homEquiv c (R₂.obj e) (adj₂.homEquiv (L₁.obj c) e g) := by
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Functor.map_comp]
  exact Category.assoc _ _ _

/-- **The `sheafificationCompPullback` comparison is the canonical `leftAdjointUniq`** of the
two composite adjunctions of the unit square. With
`A = (sheafificationAdjunction 𝟙_X).comp (SheafOfModules.pullbackPushforwardAdjunction φ)` (left
adjoint `a_X ⋙ SheafOfModules.pullback φ`) and
`B = (PresheafOfModules.pullbackPushforwardAdjunction φ').comp (sheafificationAdjunction 𝟙_Y)`
(left adjoint `PresheafOfModules.pullback φ' ⋙ a_Y`), the Mathlib device
`SheafOfModules.sheafificationCompPullback φ` is, on the nose (`rfl`),
`Adjunction.leftAdjointUniq A B`. This is the definitional identification the blueprint asserts
(`lem:leftadjointuniq_app_unit_eta`): it is what makes the mate-calculus `homEquiv_leftAdjointUniq`
identities fire for the concrete unit-square adjunctions. Project-local linchpin. -/
lemma sheafificationCompPullback_eq_leftAdjointUniq {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
      = ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).comp
          (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)).leftAdjointUniq
        ((PresheafOfModules.pullbackPushforwardAdjunction φ').comp
          (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
            (𝟙 Y.ringCatSheaf.obj))) :=
  rfl

/-- **leftAdjointUniq transport of the composite unit** (blueprint
`lem:leftadjointuniq_app_unit_eta`, ★ step 4). For the two composite adjunctions `A`, `B` of the
unit square, applying `A.homEquiv` to the `𝟙_`-component of the comparison
`sheafificationCompPullback φ` recovers `B.unit.app 𝟙_`, which expands (by
`Adjunction.comp_unit_app` on `B`) into the presheaf pullback–pushforward unit followed by the
pushforward of the sheafification unit. This is the genuinely adjunction-theoretic head of step 4
of `lem:eta_bridge_unit_square`. Project-local. -/
lemma leftAdjointUniqUnitEta {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).comp
        (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)).homEquiv
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) _
        ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))
      = (PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) ≫
        (PresheafOfModules.pushforward φ').map
          ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
              (𝟙 Y.ringCatSheaf.obj)).unit.app
            ((PresheafOfModules.pullback φ').obj
              (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set A := (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)
    with hA
  set B := (PresheafOfModules.pullbackPushforwardAdjunction φ').comp
      (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj))
    with hB
  have hg : (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
      = (A.leftAdjointUniq B).hom.app
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) := rfl
  rw [hg]
  refine Eq.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app A B
    (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))) ?_
  rw [hB, Adjunction.comp_unit_app]
  rfl

/-- **Transport of the composite unit by `leftAdjointUniq`, at a general object.**
For the two composite adjunctions `A` and `B` of the unit square, applying
`A.homEquiv` to the `P`-component of `sheafificationCompPullback φ` recovers
`B.unit.app P`. Expanding by `Adjunction.comp_unit_app` identifies the comparison with
the composite-adjunction unit. This is the object-generic form of
`leftAdjointUniqUnitEta`, whose argument is the monoidal unit. -/
lemma leftAdjointUniqUnitEta_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).comp
        (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)).homEquiv P _
        ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app P)
      = (PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app P ≫
        (PresheafOfModules.pushforward φ').map
          ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
              (𝟙 Y.ringCatSheaf.obj)).unit.app
            ((PresheafOfModules.pullback φ').obj P)) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set A := (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)
    with hA
  set B := (PresheafOfModules.pullbackPushforwardAdjunction φ').comp
      (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj))
    with hB
  have hg : (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app P
      = (A.leftAdjointUniq B).hom.app P := rfl
  rw [hg]
  refine Eq.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app A B P) ?_
  rw [hB, Adjunction.comp_unit_app]
  rfl

/-- **`restrictScalars (𝟙 R)` is the identity on morphisms.**
The functor is definitionally the identity, but this propositional form lets proofs remove
its wrappers by a syntactic rewrite without normalizing a sheafification-laden composite. -/
lemma restrictScalarsId_map {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : _root_.PresheafOfModules R} (g : M ⟶ N) :
    (PresheafOfModules.restrictScalars (𝟙 R)).map g = g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Step 7 — the presheaf lax-unit `ε` of `pushforward φ'` is the underlying presheaf map of
the sheaf-level structure-unit comparison `unitToPushforwardObjUnit φ`** (blueprint
`lem:epsilon_presheaf_to_sheaf_unit`). Both act sectionwise as `φ.hom.app X`. This is the SOLE
genuinely-new ingredient of the D2′ `(∗∗)` close: after the abstract telescope and the Y-side
sheafification triangle fold the big `homEquiv` argument down to `ε (pushforward φ')`, this lemma
lands it on `(unitToPushforwardObjUnit φ).val` (defeq `R_X.map (unitToPushforwardObjUnit φ)`).
Proved sectionwise via the `Functor.LaxMonoidal.comp` ε-formula (`pushforward₀`'s `ε = 𝟙`),
`restrictScalarsLaxε`, `ModuleCat.restrictScalars_η`, and `unitToPushforwardObjUnit_val_app_apply`.
Project-local. -/
lemma epsilonPresheafToSheafUnit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    Functor.LaxMonoidal.ε (PresheafOfModules.pushforward φ')
      = (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val := by
  apply PresheafOfModules.hom_ext
  intro X₀
  apply ModuleCat.hom_ext
  ext
  -- Provide the `CommRing` instance on the scalar ring `S₀` in the `(restrictScalars f).obj 𝟙_`
  -- spelling that `ModuleCat.restrictScalars_η` synthesises against (synthInstance does not reduce
  -- `(restrictScalars f).obj 𝟙_` to the `forget₂`-carrier where the canonical instance is keyed).
  letI : CommRing ↑((ModuleCat.restrictScalars
      (RingCat.Hom.hom ((Hom.toRingCatSheafHom f).hom.app X₀))).obj (𝟙_ (ModuleCat
        ↑((((TopologicalSpace.Opens.map f.base).op ⋙ Y.presheaf) ⋙
            forget₂ CommRingCat RingCat).obj X₀)))) :=
    inferInstanceAs (CommRing ↑((((TopologicalSpace.Opens.map f.base).op ⋙ Y.presheaf) ⋙
      forget₂ CommRingCat RingCat).obj X₀))
  -- LHS: `ε (pushforward φ')` reduces (through the `pushforward₀ ⋙ restrictScalars` composite,
  -- `pushforward₀`'s `ε = 𝟙`) to `ε (restrictScalars φ'.app X₀)`, hence to `φ'.app X₀` by
  -- `restrictScalars_η`.  RHS: `unitToPushforwardObjUnit_val_app_apply` gives `φ.hom.app X₀`.
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply, ModuleCat.restrictScalars_η]
  rfl

-- The right-triangle and unit-naturality composites normalize the sheafification machinery,
-- including the definitionally equal carriers `𝟙_Yp` and `(unit Y).val`.
set_option maxHeartbeats 1600000 in
-- The sheafification right triangle forces normalization across the unit-presheaf carrier.
/-- **Y-side sheafification right-triangle for the oplax unit comparison** (substep (ii) of the D2′
`(∗∗)` close). For `f : Y ⟶ X` with `φ' = f.toRingCatSheafHom.hom` and `F = pullback φ'`, the
sheafification unit at `F.obj 𝟙ᵖ`, post-composed with the presheaf maps of
`a_Y.map (η F)`
and `sheafifyUnitIso.hom`, recovers the oplax unit comparison `η F`. This is exactly
`Equiv.apply_symm_apply` for the presheaf sheafification adjunction `homEquiv`: the second factor
`a_Y.map (η F) ≫ sheafifyUnitIso.hom` is `homEquiv.symm (η F)`: its second factor is
the adjunction counit at `𝒪_Y`. Hence applying `homEquiv` recovers `η F`.
The separate lemma keeps this normalization out of `pullbackEtaUnitSquare`. -/
lemma pullbackSheafifyUnitEtaTriangle {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    (PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
        ((PresheafOfModules.pullback φ').obj
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))
      ≫ (((PresheafOfModules.sheafification (𝟙 (Y.ringCatSheaf.obj))).map
            (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))).val ≫
          sheafifyUnitIso.hom.val)
      = Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ') := by
  letI : (PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction _).isRightAdjoint
  -- Fold sheafification-unit naturality at `η F`, then use the right triangle on `𝒪_Y`.
  rw [← Category.assoc]
  erw [← (PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.naturality,
    Category.assoc, Functor.id_map]
  -- Y-side right triangle on the SHEAF `𝒪_Y = unit Y`: `sheafifyUnitIso = (asIso counit).app 𝒪_Y`.
  have htri : (PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
        (𝟙_ (_root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≫ sheafifyUnitIso.hom.val = 𝟙 _ := by
    rw [sheafifyUnitIso]
    have h := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Y.ringCatSheaf.obj))).right_triangle_components (SheafOfModules.unit Y.ringCatSheaf)
    simp only [Iso.app_hom, asIso_hom] at h ⊢
    exact h
  -- `rw [htri]` cannot fire on the LHS (the codomain `𝟙_Yp` vs `(unit Y).val` are defeq only at
  -- non-reducible transparency).  Expand the RHS `η F` to `η F ≫ 𝟙` via `Category.comp_id` (its
  -- `η F` is read from the goal without resynthesizing `OplaxMonoidal`; `congr 1` then
  -- reduces the result to `htri`.
  refine Eq.trans ?_ (Category.comp_id _)
  congr 1

-- The mate-calculus telescope (steps 1–6) plus the substep-(i) `.val` reshaping and the syntactic
-- Removing `restrictScalars (𝟙)` across the sheafification-laden mate telescope exceeds the
-- default budget; 3,200,000 heartbeats is sufficient for the assembled proof.
set_option maxHeartbeats 3200000 in
-- The mate telescope normalizes six sheafification and restriction-scalar comparison steps.
/-- **The unit square** (blueprint `lem:eta_bridge_unit_square`, the assembly target). The
sheafified presheaf unit comparison `a_Y.map (η F)`, conjugated by the canonical isos
`pullbackValIso` and `sheafifyUnitIso`, equals the sheaf-level structure-unit comparison
`pullbackObjUnitToUnit φ`. The proof transposes the square across the *sheaf* pullback–pushforward
adjunction `pullbackPushforwardAdjunction φ` (`homEquiv.injective`); the right-hand side image is
`unitToPushforwardObjUnit φ` by `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`,
reducing the square to the concrete pushforward-side identity (∗∗), which telescopes through the
already-closed `compHomEquivFactor` (step 3), `leftAdjointUniqUnitEta` (step 4) and
`presheafUnit_comp_map_eta` (step 6). Project-local. -/
lemma pullbackEtaUnitSquare {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')) ≫ sheafifyUnitIso.hom
        = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set φ := f.toRingCatSheafHom with hφ
  -- Transpose across the sheaf pullback–pushforward adjunction.
  apply ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf)).injective
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  -- We keep the goal in `homEquiv` form (NOT unfolding via `homEquiv_unit`), driving the
  -- telescope through the closed mate-lemmas `compHomEquivFactor`, `leftAdjointUniqUnitEta`,
  -- `presheafUnit_comp_map_eta` and
  -- `sheafificationCompPullback_eq_leftAdjointUniq`.
  -- Step 1: decompose `pullbackValIso.inv` into `(pullback φ).map c⁻¹` followed by
  -- `(sheafificationCompPullback φ).hom`
  -- where `c = (asIso (sheafification-counit_X)).app 𝒪_X`.
  simp only [pullbackValIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  rw [Category.assoc]
  -- Step 2: pull the leading `(pullback φ).map c⁻¹` out of `homEquiv` (`homEquiv_naturality_left`),
  -- then peel off `rest = a_Y.map (η F) ≫ sheafifyUnitIso.hom` using
  -- `homEquiv_naturality_right`.
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  -- Steps 3+4: rewrite `sheafAdj.homEquiv (sheafificationCompPullback φ).hom.app 𝟙ᵖ` via the
  -- composite-adjunction factorisation `compHomEquivFactor` and then `leftAdjointUniqUnitEta`.
  have hkey :
      (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
            (SheafOfModules.unit X.ringCatSheaf).val).hom
        = ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
              (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
            (((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
                (𝟙 X.ringCatSheaf.obj)).comp
                (SheafOfModules.pullbackPushforwardAdjunction φ)).homEquiv _ _
              ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
                (SheafOfModules.unit X.ringCatSheaf).val).hom) := by
    rw [Equiv.eq_symm_apply, ← compHomEquivFactor]
  erw [hkey, leftAdjointUniqUnitEta f]
  -- Fold the trailing `(pushforward φ).map rest` into the X-side `homEquiv.symm`
  -- (`homEquiv_naturality_right_symm`): `symm(x) ≫ k = symm(x ≫ R_X.map k)`.
  erw [← Adjunction.homEquiv_naturality_right_symm]
  -- X-triangle (`right_triangle_components`): the sheafification unit/counit on the sheaf `𝒪_X`
  -- cancel, collapsing the `homEquiv` composite to
  -- `(unitToPushforwardObjUnit φ).val`.
  have hXtri : (PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.obj))).unit.app
        (SheafOfModules.unit X.ringCatSheaf).val ≫
      (PresheafOfModules.restrictScalars (𝟙 (X.ringCatSheaf.obj))).map
        ((SheafOfModules.forget X.ringCatSheaf).map
          ((asIso (PresheafOfModules.sheafificationAdjunction
              (𝟙 (X.ringCatSheaf.obj))).counit).app (SheafOfModules.unit X.ringCatSheaf)).hom)
      = 𝟙 _ := by
    have h := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.obj))).right_triangle_components (SheafOfModules.unit X.ringCatSheaf)
    simp only [Iso.app_hom, asIso_hom, Functor.comp_map] at h ⊢
    exact h
  have hrhs : ((PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.obj))).homEquiv
        (SheafOfModules.unit X.ringCatSheaf).val
        ((SheafOfModules.pushforward φ).obj (SheafOfModules.unit Y.ringCatSheaf)))
      (((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.obj))).counit).app
          (SheafOfModules.unit X.ringCatSheaf)).hom ≫ SheafOfModules.unitToPushforwardObjUnit φ)
      = (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 (X.ringCatSheaf.obj))).map
          (SheafOfModules.unitToPushforwardObjUnit φ) := by
    rw [Adjunction.homEquiv_unit]
    simp only [Functor.comp_map, Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans (hXtri ▸ Category.id_comp _)
  -- Move `c⁻¹` to the RHS (`Iso.inv_comp_eq`), transpose the X-side `homEquiv.symm`
  -- (`Equiv.symm_apply_eq`), and collapse via `hrhs`, reducing to a PRESHEAF-level equation
  -- whose RHS is `(unitToPushforwardObjUnit φ).val`.
  rw [Iso.inv_comp_eq, Equiv.symm_apply_eq]
  refine Eq.trans ?_ hrhs.symm
  -- For the pushforward-side identity, first split the underlying-presheaf map
  -- of `g = a_Y.map (η F) ≫ sheafifyUnitIso.hom` and reduce `R_X.map ((pushforward φ).map g)`.
  simp only [Functor.comp_map, SheafOfModules.forget_map, SheafOfModules.pushforward_map_val,
    SheafOfModules.comp_val]
  -- Strip the two `restrictScalars (𝟙)` wrappers SYNTACTICALLY via `restrictScalarsId_map`, landing
  -- the goal in the syntactic presheaf category (no `whnf` on `rs`-over-sheafification — that is
  -- catastrophic).  This succeeds and leaves the CLEAN presheaf goal
  --   `(u ≫ pf₁.map toSheafify_Y) ≫ pf₂.map ((a_Y.map (η F)).val ≫ sheafifyUnitIso.hom.val)
  --      = (unitToPushforwardObjUnit (Hom.toRingCatSheafHom f)).val`,
  -- where `pf₁ = pushforward (Hom.toRingCatSheafHom f).hom` and `pf₂ = pushforward φ.hom` are DEFEQ
  -- but spelled differently: `Hom.toRingCatSheafHom f` from `leftAdjointUniqUnitEta`
  -- versus the local `φ`. The remaining calculation merges the two pushforward images via
  -- `Functor.map_comp`,
  -- fold `toSheafify_Y ≫ (a_Y.map (η F)).val ≫ sheafifyUnitIso.hom.val = η F` by the (closed)
  -- `pullbackSheafifyUnitEtaTriangle f`, then `presheafUnit_comp_map_eta f` and (closed)
  -- `epsilonPresheafToSheafUnit f` collapse to `(unitToPushforwardObjUnit φ).val`.
  rw [restrictScalarsId_map, restrictScalarsId_map]
  -- Reassociate and merge the two `pushforward φ'` images. Definitional matching handles
  -- the two local spellings at the connecting object. Fold the argument to `η F`, then use
  -- `presheafUnit_comp_map_eta` and `epsilonPresheafToSheafUnit`.
  erw [Category.assoc, ← Functor.map_comp, pullbackSheafifyUnitEtaTriangle f,
    presheafUnit_comp_map_eta f, epsilonPresheafToSheafUnit f]

/-- **D2′ — the pullback–tensor comparison on the unit pair is an isomorphism** (blueprint
`lem:pullback_tensor_iso_unit`). Feeds the unit square `pullbackEtaUnitSquare` into the IsIso
plumbing `isIso_sheafifyEta_of_unitSquare` (yielding `IsIso (a_Y.map (η (pullback φ')))`), then into
`isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta`. -/
lemma pullbackTensorMap_unit_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsIso (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) :=
  isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta f
    (isIso_sheafifyEta_of_unitSquare f (pullbackEtaUnitSquare f))

/-- **The pullback–tensor comparison with a right unit is unconditional.** For every scheme
morphism `f` and every module `M`, the specific comparison map
`f^*(M ⊗ 𝒪_X) ⟶ f^*M ⊗ f^*𝒪_X` is an isomorphism. This is the arbitrary-`M`
right-unitality consequence of the same sheafified oplax unit square used for the unit pair. -/
lemma pullbackTensorMap_isIso_of_right_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) :
    IsIso (pullbackTensorMap f M (SheafOfModules.unit X.ringCatSheaf)) := by
  apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta
  exact isIso_sheafifyDelta_rightUnit_of_isIso_sheafifyEta f M
    (isIso_sheafifyEta_of_unitSquare f (pullbackEtaUnitSquare f))

/-- **Characterisation of `sheafifyTensorUnitIso.hom` on the `⋙ forget₂` carrier.** Strips the
`letI instMS` cast so the two `a.map` whisker factors are stated on the same presheaf carrier as
the rest of `pullbackTensorMap` — the bridge that lets `Functor.map_comp` merge them. -/
private lemma sheafifyTensorUnitIso_hom_eq {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (sheafifyTensorUnitIso P Q).hom
      = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
          (MonoidalCategory.whiskerRight
            (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app P) Q) ≫
        (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
          (MonoidalCategory.whiskerLeft
            (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
              (𝟙 X.ringCatSheaf.obj)).obj P).val
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app Q)) := by
  rfl

/-- **`sheafifyTensorUnitIso.hom` as `a.map` of a single `tensorHom`.** The
two whisker factors of `sheafifyTensorUnitIso_hom_eq` merge (`← Functor.map_comp`) into a single
`a.map` of `η_P ▷ Q ≫ (aP).val ◁ η_Q`, which is the `tensorHom` `η_P ⊗ η_Q` of the two
sheafification-unit components by `tensorHom_def`. The final `exact` absorbs the
definitionally equal `restrictScalars (𝟙)`
wrapper on `η`'s codomain that blocks a syntactic `← tensorHom_def`. Stating the comparison as one
`tensorHom` keeps every term in the single monoidal instance on the `⋙ forget₂` carrier, so the
naturality reduces to plain bifunctoriality (`← tensor_comp`) + the two single-component unit
squares — no `whisker_exchange`, no cross-instance crossing. -/
lemma sheafifyTensorUnitIso_hom_eq' {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (sheafifyTensorUnitIso P Q).hom
      = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
          (MonoidalCategory.tensorHom
            (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app P)
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app Q)) := by
  rw [sheafifyTensorUnitIso_hom_eq, ← Functor.map_comp]
  congr 1
  exact (MonoidalCategory.tensorHom_def
    (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _).symm

-- The `erw` defeq matching across the `SheafOfModules`/`Scheme.Modules` carrier and the
-- sheafification-laden composites is heartbeat-heavy; bump past the default.
set_option maxHeartbeats 1600000 in
-- Naturality crosses the abstract pullback and its sheafified presheaf carrier.
/-- **Naturality of `pullbackValIso` in the module argument.** For `u : M ⟶ M'` in `X.Modules`,
the identification `pullbackValIso f` (sheafified presheaf-pullback ≅ abstract pullback) is natural:
`a_Y.map (F.map u.val) ≫ (pullbackValIso f M').hom = (pullbackValIso f M).hom ≫ (pullback f).map u`,
where `F = PresheafOfModules.pullback φ'`. Both factors of `pullbackValIso`
(`sheafificationCompPullback` and the sheafification counit) are natural; this is their paste.
Helper for `pullbackTensorMap_natural` (D1′). -/
lemma pullbackValIso_hom_natural {X Y : Scheme.{u}} (f : Y ⟶ X) {M M' : X.Modules} (u : M ⟶ M') :
    (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map u.val) ≫
      (pullbackValIso f M').hom
      = (pullbackValIso f M).hom ≫ (Scheme.Modules.pullback f).map u := by
  simp only [pullbackValIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc]
  erw [(SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).inv.naturality u.val]
  rw [Functor.comp_map,
    show (SheafOfModules.pullback (Hom.toRingCatSheafHom f)).map
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map u.val)
        = (Scheme.Modules.pullback f).map
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.obj)).map u.val) from rfl]
  erw [Category.assoc]
  erw [← Functor.map_comp (Scheme.Modules.pullback f)
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map u.val)
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit).app M').hom,
    ← Functor.map_comp (Scheme.Modules.pullback f)
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit).app M).hom u]
  congr 1
  congr 1
  exact (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit.naturality u

-- Whiskered sheafification-unit naturality across the sheafification-laden composites is
-- heartbeat-heavy; bump past the default.
set_option maxHeartbeats 1600000 in
-- The proof pastes two whiskered sheafification-unit naturality squares.
/-- **Naturality of `sheafifyTensorUnitIso`.** For presheaf maps `p : P ⟶ P'`, `q : Q ⟶ Q'`,
the reconciliation `sheafifyTensorUnitIso` (relating `a(P⊗Q)` with `a((aP).val ⊗ (aQ).val)`) is
natural. It is the paste of the naturality of the sheafification unit `η` whiskered on each side.
Helper for `pullbackTensorMap_natural` (D1′). -/
lemma sheafifyTensorUnitIso_hom_natural {X : Scheme.{u}}
    {P P' Q Q' : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (p : P ⟶ P') (q : Q ⟶ Q') :
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (MonoidalCategory.tensorHom (C := _root_.PresheafOfModules
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)) p q) ≫
      (sheafifyTensorUnitIso P' Q').hom
      = (sheafifyTensorUnitIso P Q).hom ≫
        (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
          (MonoidalCategory.tensorHom (C := _root_.PresheafOfModules
            (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((SheafOfModules.forget X.ringCatSheaf).map
              ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
                (𝟙 X.ringCatSheaf.obj)).map p))
            ((SheafOfModules.forget X.ringCatSheaf).map
              ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
                (𝟙 X.ringCatSheaf.obj)).map q))) := by
  -- Pin both comparison factors as one `a.map (η ⊗ η)` using
  -- `sheafifyTensorUnitIso_hom_eq'`. Naturality then follows from `Functor.map_comp`,
  -- bifunctoriality, and a single monoidal instance on the `⋙ forget₂` carrier.
  rw [sheafifyTensorUnitIso_hom_eq', sheafifyTensorUnitIso_hom_eq']
  -- Merge both `a.map _ ≫ a.map _` (`erw`: the connecting tensor object is defeq-but-not-syntactic
  -- — `Monoidal.tensorObj` vs the `⋙ forget₂` instance, plus the `restrictScalars (𝟙)` wrapper on
  -- `η`'s codomain — but cheap: no `restrictScalars`-over-sheafification `whnf` at the boundary).
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  -- Presheaf goal: (p ⊗ q) ≫ (η_{P'} ⊗ η_{Q'}) = (η_P ⊗ η_Q) ≫ (a.map p ⊗ a.map q).
  -- Single-component unit-naturality squares (`restrictScalars (𝟙)` map-wrapper stripped).
  have hp : p ≫ (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.obj))).unit.app P'
      = (PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.obj))).unit.app P ≫
        (SheafOfModules.forget X.ringCatSheaf).map
          ((PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.obj))).map p) := by
    have h := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.obj))).unit.naturality p
    simp only [Functor.id_map, Functor.comp_map, restrictScalarsId_map] at h ⊢
    exact h
  have hq : q ≫ (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.obj))).unit.app Q'
      = (PresheafOfModules.sheafificationAdjunction (𝟙 (X.ringCatSheaf.obj))).unit.app Q ≫
        (SheafOfModules.forget X.ringCatSheaf).map
          ((PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.obj))).map q) := by
    have h := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.obj))).unit.naturality q
    simp only [Functor.id_map, Functor.comp_map, restrictScalarsId_map] at h ⊢
    exact h
  -- Split the left `tensorHom` composite using a definitionally matched term, because `rw`
  -- cannot bridge the noncanonical monoidal instance in the goal. Apply the two unit
  -- squares, then reassemble the right composite. `(C := …)` ensures that the
  -- `MonoidalCategory` instance resolves (the underscore form leaves it a stuck metavariable).
  refine (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).trans ?_
  rw [hp, hq]
  exact (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).symm

set_option maxHeartbeats 3200000 in
-- The four-square chase merges sheafification maps across pinned monoidal instances.
/-- **D1′ — naturality of the sheaf-level pullback–tensor comparison `pullbackTensorMap`**
(blueprint `lem:pullback_tensor_map_natural`). For `a : M ⟶ M'`, `b : N ⟶ N'` in `X.Modules`,
the comparison `δ_sheaf = pullbackTensorMap f` commutes with `f^*(a ⊗ b)` on the source and
`f^*a ⊗ f^*b` on the target. Project-local. -/
lemma pullbackTensorMap_natural {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (tensorObj_functoriality a b) ≫ pullbackTensorMap f M' N'
      = pullbackTensorMap f M N ≫
        tensorObj_functoriality ((Scheme.Modules.pullback f).map a)
          ((Scheme.Modules.pullback f).map b) := by
  -- `pullbackTensorMap f M N` is the four-fold composite
  --   S1 ≫ S2 ≫ S3 ≫ S4 with
  --   S1 = (sheafificationCompPullback φ).app (M.val ⊗ N.val) .hom,
  --   S2 = a_Y.map (δ (pullback φ') M.val N.val),
  --   S3 = (sheafifyTensorUnitIso (F M.val) (F N.val)).hom,
  --   S4 = a_Y.map (tensorHom (pullbackValIso f M).hom.val (pullbackValIso f N).hom.val).
  -- Naturality is the paste of four squares:
  --   • S1 : naturality of `sheafificationCompPullback φ` at `tensorHom a.val b.val` (NatTrans);
  --   • S2 : `Functor.OplaxMonoidal.δ_natural` for `pullback φ'`, under `a_Y.map`;
  --   • S3 : `sheafifyTensorUnitIso_hom_natural`;
  --   • S4 : `pullbackValIso_hom_natural` and bifunctoriality of `⊗`.
  -- The cleaner route (avoiding the sheaf-level carrier friction at S1) is to merge
  -- `a_Y.map δ ≫ S3 ≫ S4` into a single `a_Y.map Ψ` (Ψ presheaf-level), move S1 by its NatTrans
  -- naturality, and discharge the resulting PRESHEAF equation by `δ_natural` + the η-naturality of
  -- the two helpers — the same merge that `sheafifyTensorUnitIso_hom_natural` reduces to.
  simp only [pullbackTensorMap, tensorObj_functoriality]
  -- Square 1 is naturality of the `sheafificationCompPullback φ` natural isomorphism at
  -- `a.val ⊗ₘ b.val`.  After this the goal is
  --   S1 ≫ a_Y.map (Fp.map (a.val ⊗ b.val)) ≫ a_Y.map δ' ≫ S3' ≫ S4'
  --     = (S1 ≫ a_Y.map δ ≫ S3 ≫ S4) ≫ Q0,   Fp = PresheafOfModules.pullback φ'.
  erw [(SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).hom.naturality_assoc]
  rw [Functor.comp_map]
  -- Square 2 (S2): `Functor.comp_map` leaves both factors over the same directly spelled
  -- sheafification functor. Merge them, then commute `δ` past `Fp.map (a.val ⊗ b.val)` by
  -- `δ_natural` (reverse) and split.
  -- The two `a_Y.map` factors are right-associated, so use the reassociated form of
  -- `Functor.map_comp`. Definitional rewriting bridges the noncanonical monoidal instance:
  -- `a.map (Fp.map (a.val ⊗ b.val)) ≫ a.map (δ_{M',N'}) ≫ rest`
  -- into `a.map (Fp.map (a.val ⊗ b.val) ≫ δ_{M',N'}) ≫ rest`, where
  -- `Fp = PresheafOfModules.pullback φ'`.
  erw [← Functor.map_comp_assoc]
  -- For square 2, under the merged `a.map (…)`, the argument is
  --   `Fp.map (a.val ⊗ b.val) ≫ δ_{M'.val,N'.val}`,  Fp = PresheafOfModules.pullback φ',
  -- which by oplax naturality `Functor.OplaxMonoidal.δ_natural` equals
  --   `δ_{M.val,N.val} ≫ (Fp.map a.val ⊗ Fp.map b.val)`.
  -- Re-present `F`'s ring hom at the
  -- canonical `⋙ forget₂` spelling with a `show … from` ascription inside the
  -- `δ_natural` application,
  -- so the registered `MonoidalCategory` instance synthesizes.  `erw` (not `rw`): the ascription
  -- pretty-prints as `have this := …; this`, whose reducible-defeq match to the bare hom only `erw`
  -- bridges. `dsimp only []` then removes the reducible ascription.
  erw [← Functor.OplaxMonoidal.δ_natural
    (F := PresheafOfModules.pullback
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom f).hom))
    a.val b.val]
  dsimp only []
  -- Now: S1 ≫ a_Y.map (δ_{M,N} ≫ (Fp.map a.val ⊗ Fp.map b.val)) ≫ S3(M',N') ≫ S4(M',N')
  --    = (S1 ≫ a_Y.map δ_{M,N} ≫ S3(M,N) ≫ S4(M,N)) ≫ a_Y.map (a.val^* ⊗ b.val^*).
  -- Split `a_Y.map (δ ≫ φ)` and right-associate so S1 and `a_Y.map δ_{M,N}` are common prefixes.
  erw [Functor.map_comp]
  simp only [Category.assoc]
  -- Peel the common S1 (`.hom.app` vs `.app … .hom`, defeq) and `a_Y.map δ_{M,N}` via `rfl` legs.
  refine congr_arg₂ (· ≫ ·) rfl ?_
  refine congr_arg₂ (· ≫ ·) rfl ?_
  -- Residual (key): a_Y.map (Fp.map a.val ⊗ Fp.map b.val) ≫ S3(M',N') ≫ S4(M',N')
  --              = S3(M,N) ≫ S4(M,N) ≫ a_Y.map (a.val^* ⊗ b.val^*).
  -- Square 3: naturality of `sheafifyTensorUnitIso` (reassoc form, post-composed by S4(M',N')).
  erw [reassoc_of% (sheafifyTensorUnitIso_hom_natural
    ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map a.val)
    ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map b.val))]
  -- Now: S3(M,N) ≫ a_Y.map (forget(a_Y(Fp a.val)) ⊗ forget(a_Y(Fp b.val))) ≫ S4(M',N')
  --    = S3(M,N) ≫ a_Y.map (forget(pullbackValIso M).hom ⊗
  --        forget(pullbackValIso N).hom) ≫ a_Y.map (a^* ⊗ b^*).
  -- `erw [Category.assoc]` bridges the instance-level mismatch between the two presentations of
  -- the connecting object; plain `rw` cannot see the `(f ≫ g) ≫ h` pattern across it.
  erw [Category.assoc]
  -- Cancel the common `S3(M,N)` iso prefix, then merge each side's two `a_Y.map`s into a single
  -- `a_Y.map (_ ≫ _)` via definitionally matched forms of `Functor.map_comp`, so `refine`
  -- bridges the same inferred-instance gap that blocks `rw`).
  erw [Iso.cancel_iso_hom_left]
  refine ((Functor.map_comp _ _ _).symm.trans ?_).trans (Functor.map_comp _ _ _)
  congr 1
  -- Square 4 (presheaf-level): bifunctoriality of `⊗` + naturality of `pullbackValIso` per leg.
  --   (forget(a_Y(Fp a.val)) ⊗ forget(a_Y(Fp b.val))) ≫
  --     (forget(pullbackValIso M').hom ⊗ forget(pullbackValIso N').hom)
  -- = (forget(pullbackValIso M).hom ⊗ forget(pullbackValIso N).hom) ≫ (a^*.val ⊗ b^*.val).
  -- Per-leg naturality of `pullbackValIso` under `forget`: merge the two `forget.map`s,
  -- apply sheaf-level naturality, then split them again. `((pullback f).map u).val` is
  -- of `(pullback f).map u`, so the closing `rfl` discharges the `forget`/`.val` boundary.
  have hleg : ∀ {P P' : X.Modules} (u : P ⟶ P'),
      (SheafOfModules.forget Y.ringCatSheaf).map
          ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map u.val)) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f P').hom
        = (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f P).hom ≫
          ((Scheme.Modules.pullback f).map u).val := by
    intro P P' u
    rw [← Functor.map_comp]
    erw [pullbackValIso_hom_natural]
    rw [Functor.map_comp]
    rfl
  -- Split the left `tensorHom` composite by bifunctoriality, rewrite each leg by `hleg`,
  -- and reassemble the right composite. `(C := …)` pins the monoidal instance on the
  -- `⋙ forget₂` carrier;
  -- `erw` bridges the connecting object's inferred-instance gap that blocks `rw [hleg …]`.
  refine (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).trans ?_
  erw [hleg a, hleg b]
  exact (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).symm

/-- **Sq2 prerequisite — ring-map reconciliation.** For composable `h : Z ⟶ Y`, `f : Y ⟶ X`,
the structure ring-presheaf map of the composite factors through the whiskered ring maps of `f`
and `h`. This is the presheaf-level identity needed to feed `PresheafOfModules.pullbackComp` into
the oplax `comp_δ` decomposition (Sq2 of `pullbackTensorMap_restrict`). -/
private lemma toRingCatSheafHom_comp_hom_reconcile {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    (Hom.toRingCatSheafHom (h ≫ f)).hom =
      (Hom.toRingCatSheafHom f).hom ≫
        (TopologicalSpace.Opens.map f.base).op.whiskerLeft (Hom.toRingCatSheafHom h).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Sectionwise value of the presheaf `restrictScalars` lax tensorator.** The lax μ of
`PresheafOfModules.restrictScalars α`, evaluated at a section `W`, is by definition the `ModuleCat`
lax μ of `restrictScalars (α.app W).hom`. This `rfl` lemma keeps the ambient term from
being normalized: rewriting with it turns `(μ (restrictScalars α) M₁ M₂).app W` into a
`ModuleCat` μ on
which `ModuleCat.restrictScalars_μ_tmul` matches syntactically (a direct `erw` on the presheaf form
`whnf`-explodes). -/
private lemma restrictScalars_μ_app
    {C : Type u} [Category.{u} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : (R ⋙ forget₂ CommRingCat RingCat) ⟶ (S ⋙ forget₂ CommRingCat RingCat))
    (M₁ M₂ : _root_.PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ) :
    (Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars α) M₁ M₂).app W
      = Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app W).hom)
          (M₁.obj W) (M₂.obj W) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Pure-tensor value of the `ModuleCat` `restrictScalars` lax tensorator, in `ModuleCat.Hom.hom`
application form, with `forget₂`-carrier rings.** Bridges `ModuleCat.restrictScalars_μ_tmul` (stated
with the bundled coercion) to the `ModuleCat.Hom.hom`-applied form goals carry after
`ModuleCat.hom_comp`/`LinearMap.comp_apply`.  The source/target rings are `forget₂`-carriers of
presheaves of *commutative* rings (`Rc.obj W'`, `Sc.obj W'`), so the `CommRing` instances the goal's
`⊗ₜ` carries (coming from `CommRingCat`) are exactly the ones the statement uses — a generic
`Type`-level form fails to synthesise `CommRing` on a bare `RingCat` carrier.  Applied in context to
the goal's heavy objects as explicit arguments and discharged by `erw` (matching only the residual
defeq instance differences, no `whnf` of the heavy `pushforward₀` sections, which would explode). -/
private lemma forget₂_restrictScalars_μ_hom_tmul
    {C : Type u} [Category.{u} C] {Rc Sc : Cᵒᵖ ⥤ CommRingCat.{u}} {W' : Cᵒᵖ}
    (f : (Rc ⋙ forget₂ CommRingCat RingCat).obj W' ⟶ (Sc ⋙ forget₂ CommRingCat RingCat).obj W')
    (M₁ M₂ : ModuleCat.{u} ((Sc ⋙ forget₂ CommRingCat RingCat).obj W'))
    (m : M₁) (n : M₂) :
    ModuleCat.Hom.hom (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars f.hom) M₁ M₂)
        (m ⊗ₜ[(Rc ⋙ forget₂ CommRingCat RingCat).obj W'] n) = m ⊗ₜ n :=
  ModuleCat.restrictScalars_μ_tmul f.hom M₁ M₂ m n

set_option backward.isDefEq.respectTransparency false in
/-- **Pure-tensor value of the presheaf `restrictScalars` lax tensorator (full collapse).**
On a pure tensor, `(μ (restrictScalars α) M₁ M₂).app W` is the identity.  Combines
`restrictScalars_μ_app` (rfl, exposes the `ModuleCat` μ) with `ModuleCat.restrictScalars_μ_tmul`.
Stated with `M₁ M₂` as *atoms*, so the proof never `whnf`s heavy ambient objects; in context it is
`rw`-applied with `R`, `S` pinned (the `forget₂`-association the goal carries), so keyed matching
succeeds without `whnf`. -/
private lemma restrictScalars_μ_app_tmul
    {C : Type u} [Category.{u} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : (R ⋙ forget₂ CommRingCat RingCat) ⟶ (S ⋙ forget₂ CommRingCat RingCat))
    (M₁ M₂ : _root_.PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ)
    (m : (M₁.obj W)) (n : (M₂.obj W)) :
    ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars α) M₁ M₂).app W)
        (m ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj W] n) = m ⊗ₜ n := by
  rw [restrictScalars_μ_app]
  exact ModuleCat.restrictScalars_μ_tmul (α.app W).hom (M₁.obj W) (M₂.obj W) m n

set_option backward.isDefEq.respectTransparency false in
/-- **Pure-tensor value of the `pushforward`-mapped `restrictScalars` lax tensorator.**  The "outer
leg" of `pushforwardComp_lax_μ`: `((pushforward φ).map (μ (restrictScalars ψ) N₁ N₂)).app W` applied
to a pure tensor is the identity.  Reindexes through `pushforward_map_app_apply` (`pushforward φ` is
`pushforward₀ ⋙ restrictScalars φ`, so the section map at `W` is the `μ` at `F.op.obj W`), then
collapses by `restrictScalars_μ_app_tmul`.  `N₁ N₂` are *atoms*; in context the lemma is applied to
the goal's heavy objects as explicit arguments and discharged by `erw` (which matches the residual
defeq instance differences without `whnf`-ing the heavy objects). -/
private lemma pushforward_map_restrictScalars_μ_app_tmul
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {T₀ : Eᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (ψ : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      G.op ⋙ (T₀ ⋙ forget₂ CommRingCat RingCat))
    (N₁ N₂ : _root_.PresheafOfModules ((G.op ⋙ T₀) ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ)
    (m : (N₁.obj (F.op.obj W))) (n : (N₂.obj (F.op.obj W))) :
    ModuleCat.Hom.hom
        (((PresheafOfModules.pushforward φ).map
          (Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars
            (show (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
              ((G.op ⋙ T₀) ⋙ forget₂ CommRingCat RingCat) from ψ)) N₁ N₂)).app W)
        (m ⊗ₜ[(R₀ ⋙ forget₂ CommRingCat RingCat).obj (F.op.obj W)] n) = m ⊗ₜ n := by
  erw [PresheafOfModules.pushforward_map_app_apply]
  exact restrictScalars_μ_app_tmul _ N₁ N₂ (F.op.obj W) m n

/-- **Reduction of the `pushforward` lax tensorator to the `restrictScalars` μ (morphism level).**
The lax μ of a single `PresheafOfModules.pushforward φ` equals the lax μ of the change-of-rings
`restrictScalars φ'` on the (strongly-monoidal, `μIso = refl`) reindexed objects
`pushforward₀OfCommRingCat F R₀`. This unfolds the opaque `presheafPushforwardLaxMonoidal` μ (the
`Functor.LaxMonoidal.comp` of `pushforward₀`'s μ = identity and `restrictScalars`'s μ) to the
directly-computable `restrictScalars` μ — staying at the `PresheafOfModules` morphism level so the
`(presheaf-tensor).obj W` vs `ModuleCat`-tensor mismatch never surfaces. Mirrors the ε-twin
`epsilonPresheafToSheafUnit`. -/
private lemma pushforward_μ_eq
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (A B : _root_.PresheafOfModules (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    letI φ' : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
        (F.op ⋙ R₀) ⋙ forget₂ CommRingCat RingCat := φ
    Functor.LaxMonoidal.μ (PresheafOfModules.pushforward φ) A B
      = Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars φ')
          ((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj A)
          ((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj B) := by
  rfl

/-- **Lax tensorator coherence for composition of presheaf pushforwards.**
Since `PresheafOfModules.pushforwardComp φ ψ = Iso.refl`, the tensorator of the
composite `pushforward ψ ⋙ pushforward φ` agrees with that of the single pushforward
along `φ ≫ F.op ◁ ψ`.

This is not definitional: it contains the change-of-rings map
`ModuleCat.restrictScalars_μ_tmul`. The proof works sectionwise and on pure tensors,
uses `Functor.LaxMonoidal.comp_μ` and `pushforward_μ_eq`, and reduces the inner and
outer restriction-of-scalars maps with the two pure-tensor helper lemmas. -/
private lemma pushforwardComp_lax_μ
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {T₀ : Eᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (ψ : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      G.op ⋙ (T₀ ⋙ forget₂ CommRingCat RingCat))
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (X Y : _root_.PresheafOfModules (T₀ ⋙ forget₂ CommRingCat RingCat)) :
    Functor.LaxMonoidal.μ
        (PresheafOfModules.pushforward ψ ⋙ PresheafOfModules.pushforward φ) X Y =
      Functor.LaxMonoidal.μ
        (PresheafOfModules.pushforward (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)) X Y := by
  -- Check the equality sectionwise and on pure tensors. `Functor.LaxMonoidal.comp_μ`
  -- unfolds the composite tensorator to
  --   `μ (pushforward φ) (..) (..)  ≫  (pushforward φ).map (μ (pushforward ψ) X Y)`,
  -- and `pushforward_μ_eq` (×2) reduces each `μ (pushforward _)` to the lighter
  -- `μ (restrictScalars _)` on the strong-monoidal `pushforward₀` objects.  On a pure tensor every
  -- `restrictScalars` μ is the identity (`ModuleCat.restrictScalars_μ_tmul`): the inner leg is
  -- collapsed by `forget₂_restrictScalars_μ_hom_tmul` (`hinner`) and the `(pushforward φ).map …`
  -- leg by `pushforward_map_restrictScalars_μ_app_tmul`; this reindexes the section map to
  -- `F.op.obj W` via `pushforward_map_app_apply` and collapses there).  After both legs the LHS is
  -- `m ⊗ₜ n`, which is defeq to the RHS single-pushforward μ on the same pure tensor — so the final
  -- `erw [houter]` closes the goal by its trailing `rfl`.  The heavy `pushforward₀` sections never
  -- get `whnf`-ed: all collapse lemmas are stated with atomic objects and applied to the goal's
  -- concrete objects as explicit arguments, then matched by `erw` up to the residual defeq
  -- `forget₂`-association / instance differences only.
  refine PresheafOfModules.hom_ext (fun W => ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_)
  rw [Functor.LaxMonoidal.comp_μ]
  rw [pushforward_μ_eq, pushforward_μ_eq]
  rw [PresheafOfModules.comp_app]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [restrictScalars_μ_app (R := S₀) (S := F.op ⋙ R₀)]
  have hinner := forget₂_restrictScalars_μ_hom_tmul (Rc := S₀) (Sc := F.op ⋙ R₀) (φ.app W)
    (((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj
      ((PresheafOfModules.pushforward ψ).obj X)).obj W)
    (((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj
      ((PresheafOfModules.pushforward ψ).obj Y)).obj W)
    m n
  erw [hinner]
  have houter := pushforward_map_restrictScalars_μ_app_tmul φ ψ
    ((PresheafOfModules.pushforward₀OfCommRingCat G T₀).obj X)
    ((PresheafOfModules.pushforward₀OfCommRingCat G T₀).obj Y) W m n
  erw [houter]

/-- **Sq2b — monoidality of `PresheafOfModules.pullbackComp` (the δ-transport across the
left-adjoint composition iso).** The presheaf-level core of D3′: the canonical oplax comparison
`δ` of the pullback for a composite ring map `φ ≫ F.op ◁ ψ` transports, through the pullback
pseudofunctor coherence `pullbackComp φ ψ`, into the `Functor.OplaxMonoidal.comp` comparison of
the composite `pullback φ ⋙ pullback ψ`.

This is the η→δ analogue of `pullbackObjUnitToUnit_comp`, proved at the `PresheafOfModules` level
(dissolving the `forget₂`-instance / associativity / reconcile frictions of working at the
`Scheme`/`forget₂` level). The proof is the adjunction-mate calculus: transpose under
`pullbackPushforwardAdjunction (φ ≫ F.op ◁ ψ)`, rewrite the oplax δ as the mate of the lax μ
(`Adjunction.unit_app_tensor_comp_map_δ`), and use the conjugate identity
`conjugateEquiv_leftAdjointCompIso_inv` (here `pushforwardComp = Iso.refl`, so the mate of
`pullbackComp.inv` is the identity). The sole residual is the lax-μ composition coherence of
`PresheafOfModules.pushforward` across `pushforwardComp` (`pushforwardComp_lax_μ`). -/
private lemma pullbackComp_δ
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {T₀ : Eᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (ψ : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      G.op ⋙ (T₀ ⋙ forget₂ CommRingCat RingCat))
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (M N : _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat)) :
    Functor.OplaxMonoidal.δ
        (PresheafOfModules.pullback (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)) M N =
      (PresheafOfModules.pullbackComp φ ψ).inv.app (M ⊗ N) ≫
        Functor.OplaxMonoidal.δ
          (PresheafOfModules.pullback φ ⋙ PresheafOfModules.pullback ψ) M N ≫
        ((PresheafOfModules.pullbackComp φ ψ).hom.app M ⊗ₘ
          (PresheafOfModules.pullbackComp φ ψ).hom.app N) := by
  -- Transpose both sides under the adjunction for the composite ring map.
  apply (PresheafOfModules.pullbackPushforwardAdjunction
    (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat)
    (φ ≫ F.op.whiskerLeft ψ)).homEquiv _ _ |>.injective
  -- Both sides become `aχ.unit (M⊗N) ≫ (pushforward χ).map (…)`:
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  -- The reduction uses the mate of `pullbackComp.inv`, the monoidality of the composite
  -- adjunction, naturality of the tensorator, and the triangle identity:
  --
  --   LHS = aχ.unit(M⊗N) ≫ (pushforward χ).map (δ (pullback χ) M N)
  --       = (aχ.unit M ⊗ₘ aχ.unit N) ≫ μ(pushforward χ) (pullback χ M) (pullback χ N)
  --                                          [Adjunction.unit_app_tensor_comp_map_δ (adj := aχ)]
  --
  --   RHS = aχ.unit(M⊗N) ≫ (pushforward χ).map (c.inv(M⊗N) ≫ comp_δ ≫ (c.hom M ⊗ₘ c.hom N))
  --       where c := pullbackComp φ ψ.  Expand `map_comp`, then:
  --   (MATE)   aχ.unit(M⊗N) ≫ (pushforward χ).map (c.inv(M⊗N)) = aC.unit(M⊗N)
  --                              [the mate of c.inv is the identity; aC := aφ.comp aψ]
  --   (U-C)    aC.unit(M⊗N) ≫ (pushforward ψ ⋙ pushforward φ).map (comp_δ) =
  --              (aC.unit M ⊗ₘ aC.unit N) ≫ μ(pushforward ψ ⋙ pushforward φ) (LM) (LN)
  --                              [unit_app_tensor_comp_map_δ for the composite adjunction]
  --   (μ-NAT)  μ(pushforward χ) (LM)(LN) ≫ (pushforward χ).map (c.hom M ⊗ₘ c.hom N) =
  --              ((pushforward χ).map (c.hom M) ⊗ₘ (pushforward χ).map (c.hom N)) ≫
  --                μ(pushforward χ) (pullback χ M) (pullback χ N)   [Functor.LaxMonoidal.μ_natural]
  --   (TRI)    aC.unit P ≫ (pushforward χ).map (c.hom P) = aχ.unit P   [(MATE) + c.inv ≫ c.hom = 𝟙]
  --   tensorHom_comp_tensorHom merges the three ⊗ₘ legs; with (TRI) the RHS becomes
  --              (aχ.unit M ⊗ₘ aχ.unit N) ≫
  --                μ(pushforward ψ ⋙ pushforward φ) (pullback χ M) (pullback χ N).
  --
  -- LHS = RHS then holds IFF
  --   μ(pushforward ψ ⋙ pushforward φ) X Y = μ(pushforward χ) X Y   (= `pushforwardComp_lax_μ`).
  -- The final equality of tensorators is `pushforwardComp_lax_μ` above; it contains the
  -- genuine `ModuleCat` change-of-rings coherence absent from the unit comparison.
  erw [Adjunction.unit_app_tensor_comp_map_δ
    (adj := PresheafOfModules.pullbackPushforwardAdjunction
      (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ))]
  -- (MATE): the conjugate/mate of `pullbackComp.inv` is `pushforwardComp.hom = 𝟙`.
  -- (MATE) — the conjugate of `pullbackComp.inv` is `pushforwardComp.hom = 𝟙`:
  have hconj : conjugateEquiv
        ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
          (PresheafOfModules.pullbackPushforwardAdjunction ψ))
        (PresheafOfModules.pullbackPushforwardAdjunction
          (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ))
        (PresheafOfModules.pullbackComp φ ψ).inv = 𝟙 _ := by
    simp only [PresheafOfModules.pullbackComp, Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      PresheafOfModules.pushforwardComp, Iso.refl_hom]
  have hmate : ∀ (P : _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat)),
      (PresheafOfModules.pullbackPushforwardAdjunction
          (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat)
          (φ ≫ F.op.whiskerLeft ψ)).unit.app P ≫
        (PresheafOfModules.pushforward (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)).map
          ((PresheafOfModules.pullbackComp φ ψ).inv.app P) =
      ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
        (PresheafOfModules.pullbackPushforwardAdjunction ψ)).unit.app P := by
    intro P
    have hu := unit_conjugateEquiv
      ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
        (PresheafOfModules.pullbackPushforwardAdjunction ψ))
      (PresheafOfModules.pullbackPushforwardAdjunction
        (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ))
      (PresheafOfModules.pullbackComp φ ψ).inv P
    rw [hconj] at hu
    simp only [NatTrans.id_app] at hu
    exact hu.symm
  -- Expand the RHS `map` of the composite and apply (MATE):
  rw [Functor.map_comp, Functor.map_comp]
  erw [reassoc_of% (hmate (M ⊗ N))]
  -- (U-C): rewrite `aC.unit(M⊗N) ≫ map(comp_δ)` via the mate of the composite adjunction `aC`:
  erw [reassoc_of% (Adjunction.unit_app_tensor_comp_map_δ
    (adj := (PresheafOfModules.pullbackPushforwardAdjunction φ).comp
      (PresheafOfModules.pullbackPushforwardAdjunction ψ)) M N)]
  -- (μ-COH): replace the composite-pushforward μ by the χ-pushforward μ (the genuine residual):
  rw [pushforwardComp_lax_μ φ ψ]
  -- (TRI): for any `P`, `aC.unit P ≫ (pushforward χ).map (c.hom P) = aχ.unit P`.
  have htri : ∀ (P : _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat)),
      ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
          (PresheafOfModules.pullbackPushforwardAdjunction ψ)).unit.app P ≫
        (PresheafOfModules.pushforward (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)).map
          ((PresheafOfModules.pullbackComp φ ψ).hom.app P) =
      (PresheafOfModules.pullbackPushforwardAdjunction
        (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat)
        (φ ≫ F.op.whiskerLeft ψ)).unit.app P := by
    intro P
    erw [← reassoc_of% (hmate P)]
    erw [← Functor.map_comp]
    erw [(PresheafOfModules.pullbackComp φ ψ).inv_hom_id_app P, CategoryTheory.Functor.map_id,
      Category.comp_id]
  -- (μ-NAT): slide μ past `map (c.hom ⊗ c.hom)`, merge the legs, then apply (TRI):
  erw [← Functor.LaxMonoidal.μ_natural]
  conv_lhs => rw [← htri M, ← htri N]
  erw [← MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat))]
  exact Category.assoc _ _ _

/-- **Compatibility of `homEquiv` with mates.**
For adjunctions `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂`, and `α : L₂ ⟶ L₁`,
transposing `α.app c ≫ f` under `adj₂` is the transpose of `f` under `adj₁`,
followed by `conjugateEquiv adj₁ adj₂ α`. This peels the leading `pullbackComp`
factor while leaving the isomorphism opaque. The proof uses `unit_conjugateEquiv` and
naturality of the conjugate transformation. -/
private lemma homEquiv_conjugateEquiv_app' {𝒞 𝒟 : Type*} [CategoryTheory.Category 𝒞]
    [CategoryTheory.Category 𝒟] {L₁ L₂ : 𝒞 ⥤ 𝒟} {R₁ R₂ : 𝒟 ⥤ 𝒞}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : 𝒞} {d : 𝒟}
    (f : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ f)
      = adj₁.homEquiv c d f ≫ (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d := by
  have h1 := CategoryTheory.unit_conjugateEquiv adj₁ adj₂ α c
  have huA : adj₂.homEquiv c d (α.app c ≫ f)
      = adj₂.unit.app c ≫ R₂.map (α.app c ≫ f) :=
    Adjunction.homEquiv_unit adj₂ c d (α.app c ≫ f)
  have huB : adj₁.homEquiv c d f = adj₁.unit.app c ≫ R₁.map f :=
    Adjunction.homEquiv_unit adj₁ c d f
  have e1 : adj₂.homEquiv c d (α.app c ≫ f)
      = (adj₂.unit.app c ≫ R₂.map (α.app c)) ≫ R₂.map f :=
    huA.trans <| (CategoryTheory.whisker_eq (adj₂.unit.app c) (R₂.map_comp (α.app c) f)).trans
      (Category.assoc _ _ _).symm
  have e2 : adj₁.homEquiv c d f ≫ (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d
      = (adj₁.unit.app c ≫ (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app (L₁.obj c))
          ≫ R₂.map f :=
    (CategoryTheory.eq_whisker huB
        ((CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d)).trans <|
      (Category.assoc _ _ _).trans <|
        (CategoryTheory.whisker_eq (adj₁.unit.app c)
          ((CategoryTheory.conjugateEquiv adj₁ adj₂ α).naturality f)).trans
          (Category.assoc _ _ _).symm
  exact e1.trans ((CategoryTheory.eq_whisker h1.symm (R₂.map f)).trans e2.symm)

/-- **Sheaf-level conjugate/mate of `pullbackComp.inv` (the R0-peel building block for Sq1).**
For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and any `Q : X.Modules`, the unit of the
composite-pullback adjunction `pullbackPushforwardAdjunction (h ≫ f)`, post-composed with the
pushforward of `pullbackComp.inv`, equals the unit of the composite adjunctions for `f`
and `h`, post-composed with `pushforwardComp.hom`. This follows from
`unit_conjugateEquiv` and `conjugateEquiv_pullbackComp_inv`, since the mate of
`pullbackComp.inv` is `pushforwardComp.hom`. It supplies the sheafification-free first
step of the Sq1 mate calculation. -/
private lemma sheaf_unit_comp_pushforward_pullbackComp_inv {X Y Z : Scheme.{u}}
    (h : Z ⟶ Y) (f : Y ⟶ X) (Q : X.Modules) :
    (SheafOfModules.pullbackPushforwardAdjunction
      (Scheme.Hom.toRingCatSheafHom (h ≫ f))).unit.app Q ≫
        (SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom (h ≫ f))).map
          ((Scheme.Modules.pullbackComp h f).inv.app Q) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app Q ≫
        (Scheme.Modules.pushforwardComp h f).hom.app
          ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).obj Q) := by
  have conj := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction h))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f))
    (Scheme.Modules.pullbackComp h f).inv Q
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at conj
  exact conj.symm

/-- **STEP-1 bridge (presheaf↔sheaf pushforward compatibility, the binding obligation of the D3′
Sq1 tail).** The forgetful functor `SheafOfModules.forget` intertwines the sheaf-level
`SheafOfModules.pushforward φ` with the presheaf-level `PresheafOfModules.pushforward φ.hom`:
for any morphism `g` of sheaves of modules over `R`,
`forget.map ((pushforward φ).map g) = (PresheafOfModules.pushforward φ.hom).map (forget.map g)`.

This is the compatibility named in the blueprint's `lem:pullback_tensor_map_basechange` Sq1-tail
binding-obligation paragraph: it is what lets the recovered sheaf-level `B_f`/`B_h` unit factors
(which live under `SheafOfModules.pushforward`) be slid across into the presheaf-level
`PresheafOfModules.pushforward` of the unit identity. This is definitional:
`SheafOfModules.pushforward` is built sectionwise from `PresheafOfModules.pushforward`, and
`forget` is the
`.val` projection (`forget_map`), so the two sides are equal by `rfl`. -/
private lemma forget_map_pushforward_map
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {A B : SheafOfModules.{u} R} (g : A ⟶ B) :
    (SheafOfModules.forget S).map ((SheafOfModules.pushforward φ).map g) =
      (PresheafOfModules.pushforward φ.hom).map ((SheafOfModules.forget R).map g) := by
  rfl

-- The mate-calculus telescope (transpose under the composite adjunction `A_{h≫f}`, the R0-kill via
-- `homEquiv_conjugateEquiv_app'`, the adj₁ split, and the R1-peel `hnatL`) elaborates the heavy
-- sheafification-laden `homEquiv` composites, exceeding the default 200000 heartbeat budget.
-- The transparency-respecting path repeatedly unfolds the opaque `Lan`-built left adjoint
-- when comparing the Scheme and sheaf pullback spellings. Disabling that path matches the
-- setting used by Mathlib's pullback-cocycle lemmas.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
-- The mate calculation compares nested and composite pullbacks through two opaque left adjoints.
/-- **Sq1 — composition coherence of `SheafOfModules.sheafificationCompPullback` (the S1 paste
square of D3′).** For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and any presheaf of
modules `P` over `X`, the sheafification–pullback comparison of the composite `h ≫ f` factors
through the comparisons of `f` and `h`, conjugated by the sheaf-level pullback pseudofunctor iso
`Scheme.Modules.pullbackComp h f` on the left and the presheaf-level pullback pseudofunctor iso
`PresheafOfModules.pullbackComp φ'_f φ'_h` (sheafified) on the right. Mathlib-absent at the pin;
the S1-foundational composition coherence consumed by `pullbackTensorMap_restrict`. It is the
`sheafificationCompPullback` twin of `pullbackObjUnitToUnit_comp`: both `sheafificationCompPullback`
isos are `leftAdjointUniq` comparisons of composite adjunctions
(`sheafificationCompPullback_eq_leftAdjointUniq`),
so the coherence is proved by the adjunction-mate calculus, transposing under the composite
`A_{h≫f} = (sheafAdj_X).comp (pullbackPushforwardAdjunction (h≫f))`. -/
lemma sheafificationCompPullback_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app P).hom =
      (Scheme.Modules.pullbackComp h f).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) ≫
        (Scheme.Modules.pullback h).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).hom ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).hom ≫
        (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app P) := by
  -- Work at the natural-transformation level so the middle adjunction absorbs the
  -- sheafification adjunction over `Y`. The local identity instances below provide both
  -- local injectivity and surjectivity needed for the final sheafification whisker.
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥Z) (𝟙 (Z.ringCatSheaf.obj)) :=
    Presheaf.instIsLocallyInjectiveOfIsIsoFunctorOpposite _ _
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥Z) (𝟙 (Z.ringCatSheaf.obj)) :=
    Presheaf.isLocallySurjective_of_iso (Opens.grothendieckTopology ↥Z) (𝟙 (Z.ringCatSheaf.obj))
  have key : (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).hom
      = Functor.whiskerLeft (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
            (Scheme.Modules.pullbackComp h f).inv ≫
          Functor.whiskerRight
            (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).hom
            (Scheme.Modules.pullback h) ≫
          Functor.whiskerLeft (PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom)
            (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom ≫
          Functor.whiskerRight
            (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
              (Hom.toRingCatSheafHom h).hom).hom
            (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)) := by
    -- Express the mate cocycle through three instances of
    -- `Adjunction.leftAdjointCompNatTrans_assoc`. The first uses the sheaf pullback leg.
    let adj01 := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)
    let adj12 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom f)
    let adj23 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom h)
    let adj02 := (PresheafOfModules.pullbackPushforwardAdjunction
        (Hom.toRingCatSheafHom f).hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
        (𝟙 Y.ringCatSheaf.obj))
    let adj13 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom (h ≫ f))
    let adj03 := (PresheafOfModules.pullbackPushforwardAdjunction
        (Hom.toRingCatSheafHom (h ≫ f)).hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
        (𝟙 Z.ringCatSheaf.obj))
    let τ012 :
        ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ⟶
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f) ⋙
            (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.obj))) := 𝟙 _
    let τ123 :
        SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)) ⟶
          SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
            SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f) :=
      (SheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f)
        (Hom.toRingCatSheafHom h)).inv
    let τ013 :
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)) ⋙
            (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.obj))) := 𝟙 _
    let τ023 :
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
            ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.obj)) ⋙
              PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom)) :=
      Functor.whiskerLeft (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj))
        (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).inv
    have hτ :
        τ023 ≫ Functor.whiskerLeft
            (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h)) τ012 =
          τ013 ≫ Functor.whiskerRight τ123
              (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.obj)) ≫
            (CategoryTheory.Functor.associator _ _ _).hom := by
      ext A
      rfl
    have E1 := Adjunction.leftAdjointCompNatTrans_assoc
      adj01 adj12 adj23 adj02 adj13 adj03 τ012 τ123 τ013 τ023 hτ
    -- The second instance: the same outer (02,23,03)-triangle, but resolved through the
    -- PRESHEAF pullback leg `adj01' = PrPbPushAdj φ'_f` instead of the sheaf leg.
    let adj01' := PresheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom f).hom
    let adj12' := PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.obj)
    let adj13' := (PresheafOfModules.pullbackPushforwardAdjunction
        (Hom.toRingCatSheafHom h).hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
        (𝟙 Z.ringCatSheaf.obj))
    let τ012' :
        ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ⟶
          ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) := 𝟙 _
    let τ123' :
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) ⟶
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
            (SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.obj))) := 𝟙 _
    let τ013' :
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
          (((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) :=
      Functor.whiskerLeft (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj))
        (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).inv
    have hτ' :
        τ023 ≫ Functor.whiskerLeft
            (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h)) τ012' =
          τ013' ≫ Functor.whiskerRight τ123'
              (PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ≫
            (CategoryTheory.Functor.associator _ _ _).hom := by
      ext A
      rfl
    have E2 := Adjunction.leftAdjointCompNatTrans_assoc
      adj01' adj12' adj23 adj02 adj13' adj03 τ012' τ123' τ013' τ023 hτ'
    -- Identify the four generic comparison transformations with the named project isos.
    have I1 : Adjunction.leftAdjointCompNatTrans adj12 adj23 adj13 τ123
        = (Scheme.Modules.pullbackComp h f).hom := rfl
    have I2 : Adjunction.leftAdjointCompNatTrans adj01 adj13 adj03 τ013
        = (SheafOfModules.sheafificationCompPullback
            (Hom.toRingCatSheafHom (h ≫ f))).hom := rfl
    have I3 : Adjunction.leftAdjointCompNatTrans adj01 adj12 adj02 τ012
        = (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).hom := rfl
    have I4 : Adjunction.leftAdjointCompNatTrans adj12' adj23 adj13' τ123'
        = (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom := rfl
    have I5 : Adjunction.leftAdjointCompNatTrans adj01' adj12' adj02 τ012' = 𝟙 _ :=
      conjugateEquiv_symm_id _
    -- ★3 via a THIRD assoc instance — the (f,h)-presheaf pair against the composite presheaf
    -- pullback adjunction.  Both outer comparison transformations trivialize
    -- (`conjugateEquiv_symm_id`), so the instance identifies the mixed `(01',13',03)`-comparison
    -- with the sheafified presheaf-`pullbackComp` coherence with NO conjugate manipulation.
    let adjh' := PresheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom h).hom
    let adjZ' := PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
      (𝟙 Z.ringCatSheaf.obj)
    let adjhf' := PresheafOfModules.pullbackPushforwardAdjunction
      (Hom.toRingCatSheafHom (h ≫ f)).hom
    let τ012'' :
        PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom ⟶
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom :=
      (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
        (Hom.toRingCatSheafHom h).hom).inv
    let τ123'' :
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) ⟶
          ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) := 𝟙 _
    let τ023'' :
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
          ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) := 𝟙 _
    have hτ'' :
        τ023'' ≫ Functor.whiskerLeft
            (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.obj)) τ012'' =
          τ013' ≫ Functor.whiskerRight τ123''
              (PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ≫
            (CategoryTheory.Functor.associator _ _ _).hom := by
      ext A
      rfl
    have E3 := Adjunction.leftAdjointCompNatTrans_assoc
      adj01' adjh' adjZ' adjhf' adj13' adj03 τ012'' τ123'' τ013' τ023'' hτ''
    have J1 : Adjunction.leftAdjointCompNatTrans adjh' adjZ' adj13' τ123'' = 𝟙 _ :=
      conjugateEquiv_symm_id _
    have J2 : Adjunction.leftAdjointCompNatTrans adjhf' adjZ' adj03 τ023'' = 𝟙 _ :=
      conjugateEquiv_symm_id _
    have J3 : Adjunction.leftAdjointCompNatTrans adj01' adjh' adjhf' τ012''
        = (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom := rfl
    rw [I1, I2, I3] at E1
    simp only [I4, I5] at E2
    simp only [J1, J2, J3] at E3
    -- Evaluate the pasted identities at `P`, eliminate the mixed comparison, and peel the
    -- invertible `pullbackComp` whisker.
    apply NatTrans.ext
    funext P
    have e1 := congr_app E1 P
    have e2 := congr_app E2 P
    have e3 := congr_app E3 P
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, NatTrans.id_app] at e1 e2 e3 ⊢
    -- Normalize the definitionally equal object spellings before removing identity factors.
    try dsimp only [Functor.comp_obj] at e1 e2 e3 ⊢
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at e1 e2 e3
    -- Remove the leading identities with definitional matching, eliminate the mixed
    -- comparison between `e1` and `e2`, then resolve it with `e3`.
    erw [Category.id_comp] at e2
    erw [Category.id_comp] at e3
    rw [← e2] at e1
    rw [e3] at e1
    -- Peel the invertible `pullbackComp`-component; `exact` closes the remaining
    -- `Scheme.Modules` vs `SheafOfModules` spelling differences by defeq.
    exact (Iso.eq_inv_comp ((Scheme.Modules.pullbackComp h f).app
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).obj P))).mpr e1
  -- Evaluate `key` at `P`; the local transparency setting controls the comparison between
  -- the Scheme and sheaf pullback spellings.
  have happ := NatTrans.congr_app key P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at happ ⊢
  exact happ

/-- **Brick 1 (Sq-cancellation).**
For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and any presheaf `T` over `X`, the
sheafification functor sends the `hom ≫ inv` round trip of
`PresheafOfModules.pullbackComp` to the identity. This supplies the middle cancellation in
`pullbackTensorMap_restrict`. -/
private lemma sheafifyMap_pullbackComp_hom_inv_id {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (T : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.obj)).map
        ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).hom.app T) ≫
      (PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.obj)).map
        ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).inv.app T) = 𝟙 _ := by
  rw [← Functor.map_comp]
  erw [Iso.hom_inv_id_app]
  exact
    (PresheafOfModules.sheafification
      (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.obj)).map_id _

/-- Cancel a middle inverse pair in a fourfold categorical composite.

The abstract formulation gives all compositions the same `Category` instance. It can therefore be
applied by definitional equality to composites whose concrete `SheafOfModules` presentations differ.
-/
private lemma comp_cancel_mid {C : Type*} [Category C] {A₀ B₀ C₀ D₀ E₀ F₀ : C}
    (r0 : A₀ ⟶ B₀) (r1 : B₀ ⟶ C₀) (r5 : C₀ ⟶ D₀) (d : D₀ ⟶ E₀) (e : E₀ ⟶ D₀)
    (rest : D₀ ⟶ F₀) (hde : d ≫ e = 𝟙 D₀) :
    (r0 ≫ r1 ≫ r5 ≫ d) ≫ e ≫ rest = r0 ≫ r1 ≫ r5 ≫ rest := by
  simp only [Category.assoc]
  rw [← Category.assoc d e rest, hde, Category.id_comp]

/-- Substitute a buried pair in a nested categorical composite.

The conclusion deliberately preserves the nesting used by `pullbackTensorMap_restrict`, allowing
definitional unification across alternate presentations of `SheafOfModules` composition. -/
private lemma comp_slide_nested {C : Type*} [Category C] {a b c d e k m n g d' : C}
    (r0 : a ⟶ b) (r1 : b ⟶ c) (r5 : c ⟶ d) (p : d ⟶ e) (q : e ⟶ k) (rtc : k ⟶ m)
    (s3 : m ⟶ n) (s4 : n ⟶ g) (u : c ⟶ d') (v : d' ⟶ e) (rhs : a ⟶ g)
    (hsl : r5 ≫ p = u ≫ v)
    (hrest : (r0 ≫ r1 ≫ (u ≫ v) ≫ q ≫ rtc) ≫ s3 ≫ s4 = rhs) :
    (r0 ≫ r1 ≫ r5 ≫ (p ≫ q) ≫ rtc) ≫ s3 ≫ s4 = rhs := by
  have hassoc : r5 ≫ (p ≫ q) ≫ rtc = (r5 ≫ p) ≫ q ≫ rtc := by
    simp only [Category.assoc]
  rw [hassoc, hsl]; exact hrest

/-- Cancel three equal prefix factors before comparing the remaining categorical composites.

The explicit prefix equalities accommodate the definitionally equal `SheafOfModules` and
`Scheme.Modules` presentations used by the caller. -/
private lemma comp_cancel_three_lr {C : Type*} [Category C]
    {a b cc c' e kk mm nn g c4 c5 c6 c7 c8 c9 : C}
    (r0 : a ⟶ b) (r1 : b ⟶ cc) (u : cc ⟶ c') (v : c' ⟶ e) (q : e ⟶ kk) (rtc : kk ⟶ mm)
    (s3 : mm ⟶ nn) (s4 : nn ⟶ g)
    (r0' : a ⟶ b) (m1 : b ⟶ cc) (m2 : cc ⟶ c') (m3 : c' ⟶ c4) (m4 : c4 ⟶ c5) (vv : c5 ⟶ c6)
    (dh : c6 ⟶ c7) (sh3 : c7 ⟶ c8) (sh4 : c8 ⟶ c9) (tf : c9 ⟶ g)
    (hr0 : r0 = r0') (hr1 : r1 = m1) (hu : u = m2)
    (hcore : v ≫ q ≫ rtc ≫ s3 ≫ s4 = m3 ≫ m4 ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf) :
    (r0 ≫ r1 ≫ (u ≫ v) ≫ q ≫ rtc) ≫ s3 ≫ s4
      = r0' ≫ (m1 ≫ m2 ≫ m3 ≫ m4) ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf := by
  subst hr0 hr1 hu
  simp only [Category.assoc]
  rw [hcore]

/-- Replace a threefold prefix by a slid pair, then compare the residual composites.

This is the categorical skeleton of the merged Sq3/Sq4 argument in
`pullbackTensorMap_restrict`. -/
private lemma comp_slide_three {C : Type*} [Category C]
    {a b b3 c1 c2 c3 d1 d2 d3 d4 d5 g : C}
    (v : a ⟶ b) (q : b ⟶ c1) (rtc : c1 ⟶ c2) (s3 : c2 ⟶ c3) (s4 : c3 ⟶ g)
    (m3 : a ⟶ d1) (m4 : d1 ⟶ d2) (vv : d2 ⟶ b3) (dh : b3 ⟶ d3) (sh3 : d3 ⟶ d4)
    (sh4 : d4 ⟶ d5) (tf : d5 ⟶ g) (vtail : b ⟶ b3)
    (hcomb : m3 ≫ m4 ≫ vv = v ≫ vtail)
    (hcore2 : q ≫ rtc ≫ s3 ≫ s4 = vtail ≫ dh ≫ sh3 ≫ sh4 ≫ tf) :
    v ≫ q ≫ rtc ≫ s3 ≫ s4 = m3 ≫ m4 ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf := by
  rw [hcore2, ← Category.assoc v vtail, ← hcomb]
  simp only [Category.assoc]

/-- Merge two mapped morphisms and finish with a supplied naturality equation. -/
private lemma map_comp_slide {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {x y z : C} {w : D} (s3f : x ⟶ y) (s4f : y ⟶ z) (gmap : x ⟶ z)
    (vv : G.obj z ⟶ w) (rhs : G.obj x ⟶ w)
    (hg : gmap = s3f ≫ s4f) (hnat : G.map gmap ≫ vv = rhs) :
    G.map s3f ≫ G.map s4f ≫ vv = rhs := by
  have e : G.map s3f ≫ G.map s4f = G.map gmap := by rw [hg, Functor.map_comp]
  calc G.map s3f ≫ G.map s4f ≫ vv
        = (G.map s3f ≫ G.map s4f) ≫ vv := by rw [Category.assoc]
    _ = G.map gmap ≫ vv := by rw [e]
    _ = rhs := hnat

/-- Lift an equality between fourfold and fivefold composites through a functor. -/
private lemma map_comp4_eq_comp5 {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x₀ x₁ x₂ x₃ x₄ : C} (a₁ : x₀ ⟶ x₁) (a₂ : x₁ ⟶ x₂) (a₃ : x₂ ⟶ x₃) (a₄ : x₃ ⟶ x₄)
    {z₁ z₂ z₃ z₄ : C} (b₁ : x₀ ⟶ z₁) (b₂ : z₁ ⟶ z₂) (b₃ : z₂ ⟶ z₃) (b₄ : z₃ ⟶ z₄) (b₅ : z₄ ⟶ x₄)
    (hcore : a₁ ≫ a₂ ≫ a₃ ≫ a₄ = b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅) :
    F.map a₁ ≫ F.map a₂ ≫ F.map a₃ ≫ F.map a₄
      = F.map b₁ ≫ F.map b₂ ≫ F.map b₃ ≫ F.map b₄ ≫ F.map b₅ := by
  simp only [← Functor.map_comp]
  rw [hcore]

/-- Compare threefold and fourfold `tensorHom` chains from equal composites on both legs. -/
private lemma tensorHom_collapse_3_4 {C : Type*} [Category C] [MonoidalCategory C]
    {xM₀ xM₁ xM₂ xM₃ xN₀ xN₁ xN₂ xN₃ : C}
    (p₁ : xM₀ ⟶ xM₁) (p₂ : xM₁ ⟶ xM₂) (p₃ : xM₂ ⟶ xM₃)
    (q₁ : xN₀ ⟶ xN₁) (q₂ : xN₁ ⟶ xN₂) (q₃ : xN₂ ⟶ xN₃)
    {yM₁ yM₂ yM₃ yN₁ yN₂ yN₃ : C}
    (r₁ : xM₀ ⟶ yM₁) (r₂ : yM₁ ⟶ yM₂) (r₃ : yM₂ ⟶ yM₃) (r₄ : yM₃ ⟶ xM₃)
    (s₁ : xN₀ ⟶ yN₁) (s₂ : yN₁ ⟶ yN₂) (s₃ : yN₂ ⟶ yN₃) (s₄ : yN₃ ⟶ xN₃)
    (hM : p₁ ≫ p₂ ≫ p₃ = r₁ ≫ r₂ ≫ r₃ ≫ r₄)
    (hN : q₁ ≫ q₂ ≫ q₃ = s₁ ≫ s₂ ≫ s₃ ≫ s₄) :
    MonoidalCategory.tensorHom p₁ q₁ ≫ MonoidalCategory.tensorHom p₂ q₂ ≫
        MonoidalCategory.tensorHom p₃ q₃
      = MonoidalCategory.tensorHom r₁ s₁ ≫ MonoidalCategory.tensorHom r₂ s₂ ≫
          MonoidalCategory.tensorHom r₃ s₃ ≫ MonoidalCategory.tensorHom r₄ s₄ := by
  simp only [MonoidalCategory.tensorHom_comp_tensorHom, hM, hN]

/-- The adjunction triangle in the form `L.map (η ≫ R.map k) ≫ ε = k`.

For sheafification this reassembles the counit factor in `pullbackValIso_comp_leg`. -/
private lemma adj_unit_map_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (P : C) (M : D) (k : L.obj P ⟶ M) :
    L.map (adj.unit.app P ≫ R.map k) ≫ adj.counit.app M = k :=
  (adj.homEquiv P M).left_inv k

/-- Map a cocycle equality through a functor and prefix both sides by the same morphism. -/
private lemma comp_forget_cocycle {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c a' d' : C} {Wd : D} (η : Wd ⟶ F.obj a) (x : a ⟶ b) (y : b ⟶ c)
    (x' : a ⟶ a') (y' : a' ⟶ d') (z' : d' ⟶ c) (h : x ≫ y = x' ≫ y' ≫ z') :
    η ≫ F.map x ≫ F.map y = η ≫ F.map x' ≫ F.map y' ≫ F.map z' := by
  rw [← Functor.map_comp, h, Functor.map_comp, Functor.map_comp]

/-- Collapse a palindromic composite when its three nested pairs are inverse. -/
private lemma inv_telescope {C : Type*} [Category C] {w x y z t : C}
    (A : w ⟶ x) (A' : x ⟶ w) (B : x ⟶ y) (B' : y ⟶ x) (Cc : y ⟶ z) (C' : z ⟶ y) (g : w ⟶ t)
    (hA : A ≫ A' = 𝟙 w) (hB : B ≫ B' = 𝟙 x) (hC : Cc ≫ C' = 𝟙 y) :
    g = (A ≫ B ≫ Cc) ≫ C' ≫ B' ≫ A' ≫ g := by
  simp only [Category.assoc]
  rw [← Category.assoc Cc C', hC, Category.id_comp, ← Category.assoc B B', hB, Category.id_comp,
    ← Category.assoc A A', hA, Category.id_comp]

/-- Assemble the two naturality paths and their shared adjunction triangle into one cocycle. -/
private lemma cocycle_assemble {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {dA dB dC dD dQ : D} {cP cQ cR cS : C}
    (p : dA ⟶ dB) (sf : dB ⟶ dC) (m1 : dC ⟶ dD)
    (sh : dA ⟶ F.obj cP) (x1 : cP ⟶ cQ) (pa : F.obj cQ ⟶ dC) (x2 : cQ ⟶ cR) (pw : F.obj cR ⟶ dD)
    (q : dA ⟶ dQ) (sQ : dQ ⟶ F.obj cS) (x3 : cP ⟶ cS) (x4 : cS ⟶ cR)
    (h1 : p ≫ sf = sh ≫ F.map x1 ≫ pa) (h2 : pa ≫ m1 = F.map x2 ≫ pw)
    (h3 : q ≫ sQ = sh ≫ F.map x3) (h4 : x3 ≫ x4 = x1 ≫ x2) :
    p ≫ sf ≫ m1 = q ≫ (sQ ≫ F.map x4) ≫ pw := by
  rw [reassoc_of% h1, h2, Category.assoc sQ, reassoc_of% h3, ← Category.assoc (F.map x1),
    ← Functor.map_comp, ← Category.assoc (F.map x3), ← Functor.map_comp, h4]

set_option maxHeartbeats 1600000 in
-- Expanding `comp_δ` retains the full sheafification and monoidal-instance telescope.
/-- Split the oplax tensorator of a composite presheaf pullback after sheafification.

The explicit ring-map ascriptions keep the monoidal instances aligned with those in
`pullbackTensorMap_restrict`. -/
private lemma sheafifyMap_δcomp_split {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M N : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map
        (Functor.OplaxMonoidal.δ
          (PresheafOfModules.pullback
              (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map f.base).op ⋙
                    (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom f).hom) ⋙
            PresheafOfModules.pullback
              (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map h.base).op ⋙
                    (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom h).hom))
          M.val N.val) =
      (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map
          ((PresheafOfModules.pullback
              (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map h.base).op ⋙
                    (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom h).hom)).map
            (Functor.OplaxMonoidal.δ
              (PresheafOfModules.pullback
                (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                    (TopologicalSpace.Opens.map f.base).op ⋙
                      (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                  from (Hom.toRingCatSheafHom f).hom))
              M.val N.val)) ≫
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map
          (Functor.OplaxMonoidal.δ
            (PresheafOfModules.pullback
              (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map h.base).op ⋙
                    (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom h).hom))
            ((PresheafOfModules.pullback
              (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map f.base).op ⋙
                    (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom f).hom)).obj M.val)
            ((PresheafOfModules.pullback
              (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map f.base).op ⋙
                    (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom f).hom)).obj N.val)) := by
  -- The composite oplax structure defines `δ (F ⋙ G)` as `G.map (δ F) ≫ δ G`.
  rw [← Functor.map_comp]
  congr 1

/-- Inverse form of `sheafificationCompPullback_comp`.

Cancelling its three inverse pairs gives the reassembly used by `pullbackValIso_comp_leg`. -/
private lemma sheafificationCompPullback_comp_inv {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app P) ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app P).inv
      = ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).inv ≫
          (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
            ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).inv ≫
          (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).hom.app
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  have hA : ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).inv ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  have hB : (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).inv ≫
        (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback
            (Hom.toRingCatSheafHom f)).app P).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hC :
      (SheafOfModules.pullbackComp
        (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).hom.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) ≫
        (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  rw [Iso.comp_inv_eq, sheafificationCompPullback_comp h f P]
  exact inv_telescope _ _ _ _ _ _ _ hA hB hC

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- Closing unification reconciles the composite ring-map and nested pullback spellings.
/-- Per-leg composition coherence for `pullbackValIso`.

The sheafification unit followed by the underlying map of `pullbackValIso` composes
pseudofunctorially. The inverse comparison factors reassemble by
`sheafificationCompPullback_comp`, while the counit factors reassemble by naturality. -/
lemma pullbackValIso_comp_leg {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (W : X.Modules) :
    (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).hom.app W.val ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (Z.ringCatSheaf.obj))).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom (h ≫ f)).hom).obj W.val) ≫
          (SheafOfModules.forget Z.ringCatSheaf).map (pullbackValIso (h ≫ f) W).hom
      = (PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
              (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 (Z.ringCatSheaf.obj))).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
                ((pullback f).obj W).val) ≫
            (SheafOfModules.forget Z.ringCatSheaf).map (pullbackValIso h ((pullback f).obj W)).hom ≫
              (SheafOfModules.forget Z.ringCatSheaf).map ((pullbackComp h f).app W).hom := by
  -- Move both leading units by naturality, then prove the remaining sheaf-level cocycle.
  have hUZ1 :
      (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app W.val ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 (Z.ringCatSheaf.obj))).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom (h ≫ f)).hom).obj W.val)
        = (PresheafOfModules.sheafificationAdjunction (𝟙 (Z.ringCatSheaf.obj))).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val)) ≫
            (SheafOfModules.forget Z.ringCatSheaf).map
              ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
                ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
                  (Hom.toRingCatSheafHom h).hom).hom.app W.val)) := by
    -- Normalize the functor composition before unifying the two object presentations.
    have hnat := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Z.ringCatSheaf.obj))).unit.naturality
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app W.val)
    simp only [Functor.id_map, Functor.comp_map, restrictScalarsId_map] at hnat
    exact hnat
  have hUZ2 :
      (PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
              (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 (Z.ringCatSheaf.obj))).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
              ((pullback f).obj W).val)
        = (PresheafOfModules.sheafificationAdjunction (𝟙 (Z.ringCatSheaf.obj))).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val)) ≫
            (SheafOfModules.forget Z.ringCatSheaf).map
              ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
                  ((PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
                      ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
                    (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom))) := by
    have hnat := (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Z.ringCatSheaf.obj))).unit.naturality
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
              (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom))
    simp only [Functor.id_map, Functor.comp_map, restrictScalarsId_map] at hnat
    exact hnat
  -- The sheaf-level cocycle (H): the genuine content, in `SheafOfModules Z`.
  have hH :
      (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
            ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
              (Hom.toRingCatSheafHom h).hom).hom.app W.val) ≫
          (pullbackValIso (h ≫ f) W).hom
        = (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
                ((PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
                    ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
                  (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom)) ≫
            (pullbackValIso h ((pullback f).obj W)).hom ≫ ((pullbackComp h f).app W).hom := by
    set b := (PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj))).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom with hb
    -- Unfold pVI on the (h≫f)- and h-legs (the f-leg is hidden inside the opaque `b`).
    simp only [pullbackValIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    have h1 := sheafificationCompPullback_comp_inv h f W.val
    have h2 := ((Scheme.Modules.pullbackComp h f).hom.naturality
      (((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit).app W).hom)).symm
    have h3 :=
      (SheafOfModules.sheafificationCompPullback
        (Hom.toRingCatSheafHom h)).inv.naturality b
    -- (T): the adjunction triangle for the sheafification adjunction on `Y`.
    have h4 : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map b ≫
          (((asIso (PresheafOfModules.sheafificationAdjunction
            (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).counit).app ((pullback f).obj W)).hom)
        = (pullbackValIso f W).hom :=
      adj_unit_map_counit
        (PresheafOfModules.sheafificationAdjunction (𝟙 (Y.ringCatSheaf.obj)))
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val)
        ((pullback f).obj W) (pullbackValIso f W).hom
    exact cocycle_assemble (Scheme.Modules.pullback h) _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4
  -- Reduction: rewrite each side as `η^Z_{phh(phf W.val)} ≫ forget Z (·)` and close by `hH`.
  slice_lhs 1 2 => rw [hUZ1]
  slice_rhs 1 2 => rw [hUZ2]
  exact comp_forget_cocycle (SheafOfModules.forget Z.ringCatSheaf) _ _ _ _ _ _ hH


set_option maxHeartbeats 3200000 in
-- The tensorator coherence interleaves four sheafified comparison squares.
/-- Composition coherence of the sheaf-level pullback tensorator.

For composable scheme morphisms, `pullbackTensorMap` for the composite factors through the
comparisons for the two morphisms and the pullback pseudofunctor coherence. Specializing this
identity to the two factorizations of a base-change square gives the blueprint's restricted
comparison. -/
lemma pullbackTensorMap_restrict {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M N : X.Modules) :
    pullbackTensorMap (h ≫ f) M N =
      (Scheme.Modules.pullbackComp h f).inv.app (tensorObj M N) ≫
      (Scheme.Modules.pullback h).map (pullbackTensorMap f M N) ≫
      pullbackTensorMap h ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) ≫
      (tensorObjIsoOfIso ((Scheme.Modules.pullbackComp h f).app M)
        ((Scheme.Modules.pullbackComp h f).app N)).hom := by
  -- Expand each tensorator comparison into its four defining factors. The proof then pastes:
  -- sheafification-pullback coherence, the composite oplax tensorator, the tensor-unit
  -- comparison, and `pullbackValIso` coherence. The latter two squares must be interleaved because
  -- their arguments use different presentations of the pulled-back underlying presheaves.
  simp only [pullbackTensorMap, tensorObjIsoOfIso]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  -- Keep the first comparison folded while assembling the adjacent inverse pair.
  have h1 := sheafificationCompPullback_comp h f (PresheafOfModules.Monoidal.tensorObj M.val N.val)
  letI instMSX :
      MonoidalCategoryStruct
        (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
    inferInstance
  letI instMSZ :
      MonoidalCategoryStruct
        (_root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
    inferInstance
  -- Explicit functor spellings keep the cancellation factors syntactically aligned.
  let φfh := (Hom.toRingCatSheafHom (h ≫ f)).hom
  let φf := (Hom.toRingCatSheafHom f).hom
  let φh := (Hom.toRingCatSheafHom h).hom
  let pb := PresheafOfModules.pullbackComp φf φh
  let δfh := Functor.OplaxMonoidal.δ
    (F := PresheafOfModules.pullback
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map (h ≫ f).base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom (h ≫ f)).hom))
    M.val N.val
  let δcomp := Functor.OplaxMonoidal.δ
    (F := PresheafOfModules.pullback
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom f).hom) ⋙
      PresheafOfModules.pullback
        (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
            (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
          from (Hom.toRingCatSheafHom h).hom))
    M.val N.val
  let tcomp :=
    MonoidalCategory.tensorHom
      (C := _root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat))
      (pb.hom.app M.val) (pb.hom.app N.val)
  have hδ :
      (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map δfh =
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map
            ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
              (Hom.toRingCatSheafHom h).hom).inv.app
              (PresheafOfModules.Monoidal.tensorObj M.val N.val)) ≫
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map δcomp ≫
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map tcomp := by
    -- Apply `pullbackComp_δ` under sheafification, folding mapped composites first.
    have hd := pullbackComp_δ
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom f).hom)
      (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom h).hom) M.val N.val
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map hd
  -- Combine the first comparison and the composite tensorator in one canonical category instance.
  have hmain :
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app
          (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map δfh =
      (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)) ≫
        (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj
            (PresheafOfModules.Monoidal.tensorObj M.val N.val))).hom ≫
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map δcomp ≫
        (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map tcomp := by
    -- Restate the coherence so its concrete category instance matches this local composite.
    have h1' :
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom =
          (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
              ((PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.obj))).obj
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)) ≫
            (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
              ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫
            ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj
                (PresheafOfModules.Monoidal.tensorObj M.val N.val))).hom ≫
            (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map
              ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
                (Hom.toRingCatSheafHom h).hom).hom.app
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)) := h1
    -- Expose the inverse pair and cancel it through the abstract categorical helper.
    rw [h1']
    erw [hδ]
    exact comp_cancel_mid _ _ _ _ _ _
      (sheafifyMap_pullbackComp_hom_inv_id h f (PresheafOfModules.Monoidal.tensorObj M.val N.val))
  -- Splice the cancelled prefix into the main composite.
  erw [reassoc_of% hmain]
  -- Split the composite oplax tensorator into the two pullback tensorators.
  erw [sheafifyMap_δcomp_split h f M N]
  -- Slide the second sheafification comparison past the first pullback tensorator by naturality.
  have hslide :
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj
              (PresheafOfModules.Monoidal.tensorObj M.val N.val))).hom ≫
          (PresheafOfModules.sheafification (𝟙 (Z.ringCatSheaf.obj))).map
            ((PresheafOfModules.pullback
                (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                    (TopologicalSpace.Opens.map h.base).op ⋙
                      (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                  from (Hom.toRingCatSheafHom h).hom)).map
              (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback
                (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                    (TopologicalSpace.Opens.map f.base).op ⋙
                      (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                  from (Hom.toRingCatSheafHom f).hom)) M.val N.val))
        = (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
              ((PresheafOfModules.sheafification (𝟙 (Y.ringCatSheaf.obj))).map
                (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback
                  (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                      (TopologicalSpace.Opens.map f.base).op ⋙
                        (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                    from (Hom.toRingCatSheafHom f).hom)) M.val N.val)) ≫
            ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
              (PresheafOfModules.Monoidal.tensorObj
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val))).hom :=
    ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom.naturality
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback
        (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
            (TopologicalSpace.Opens.map f.base).op ⋙
              (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
          from (Hom.toRingCatSheafHom f).hom)) M.val N.val)).symm
  -- The explicit ring-map ascriptions make this equation definitionally match the nested slide.
  refine comp_slide_nested _ _ _ _ _ _ _ _ _ _ _ hslide ?_
  -- Cancel the common prefix, using definitional equality for its two presentations.
  refine comp_cancel_three_lr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl ?_
  -- Package the tensor-unit and `pullbackValIso` legs over `Y` as one presheaf morphism.
  set gg :
      PresheafOfModules.Monoidal.tensorObj
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val) ⟶
        PresheafOfModules.Monoidal.tensorObj ((pullback f).obj M).val ((pullback f).obj N).val :=
    MonoidalCategory.tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
        ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val))
        ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val)) ≫
      MonoidalCategory.tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)
    with hgg
  -- `a_Y.map gg = S3_f ≫ S4_f` (first factor by `sheafifyTensorUnitIso_hom_eq'`, second is `S4_f`).
  have hg :
      (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map gg
        = (sheafifyTensorUnitIso
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val)).hom ≫
          (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
            (MonoidalCategory.tensorHom
              (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
              ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
              ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)) := by
    -- Split `a_Y.map (A ≫ B)` as a defeq `exact` (the `≫` in `gg` lives in the `forget₂`-carrier
    -- monoidal instance, defeq-but-not-syntactic to `a_Y`'s domain — bridged by `exact`, not `rw`).
    have hsplit :
        (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map gg
          = (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
              (MonoidalCategory.tensorHom
                (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
                ((PresheafOfModules.sheafificationAdjunction
                  (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
                  ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val))
                ((PresheafOfModules.sheafificationAdjunction
                  (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
                  ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val))) ≫
            (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map
              (MonoidalCategory.tensorHom
                (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
                ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
                ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)) := by
      rw [hgg]
      exact (PresheafOfModules.sheafification
        (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map_comp _ _
    rw [hsplit]
    congr 1
    exact (sheafifyTensorUnitIso_hom_eq' _ _).symm
  -- Splice the slide: `m3 ≫ m4 ≫ vv = v ≫ a_Z.map (Fp_h.map gg)` from `hg` + naturality of
  -- `sheafificationCompPullback h` at `gg`.
  refine comp_slide_three _ _ _ _ _ _ _ _ _ _ _ _
    ((PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.obj)).map
      ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map gg)) ?_ ?_
  · -- Merge the mapped factors, then use naturality at `gg`.
    exact map_comp_slide (Scheme.Modules.pullback h) _ _
      ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).map gg)
      _ _ hg
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom.naturality gg)
  · -- Fold the remaining Sq3/Sq4 comparison into a presheaf equality over `Z`.
    rw [sheafifyTensorUnitIso_hom_eq', sheafifyTensorUnitIso_hom_eq']
    simp only [Functor.mapIso_hom, MonoidalCategory.tensorIso_hom]
    refine map_comp4_eq_comp5 _ _ _ _ _ _ _ _ _ _ ?_
    -- Expose `gg` as a tensor of its two legs before applying tensorator naturality.
    have hgg2 : gg =
        MonoidalCategory.tensorHom
          (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
          ((PresheafOfModules.sheafificationAdjunction
              (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
            (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
          ((PresheafOfModules.sheafificationAdjunction
              (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val) ≫
            (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom) := by
      rw [hgg]
      exact MonoidalCategory.tensorHom_comp_tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _
    rw [hgg2]
    -- Pin the pullback functor so tensorator naturality uses the intended monoidal instance.
    have hδnat := Functor.OplaxMonoidal.δ_natural
      (F := PresheafOfModules.pullback
        (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
            (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
          from (Hom.toRingCatSheafHom h).hom))
      ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
      ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)
    erw [← reassoc_of% hδnat]
    -- Cancel the common tensorator and reduce the remaining tensor morphisms to their two legs.
    rw [show tcomp = MonoidalCategory.tensorHom
      (C := _root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat))
      (pb.hom.app M.val) (pb.hom.app N.val) from rfl]
    congr 1
    refine tensorHom_collapse_3_4
      (C := _root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · -- per-leg M (the `pullbackValIso` composition coherence, Sq4): the canonical "unit into the
      -- pullback's underlying presheaf" composes pseudofunctorially across `h ≫ f`.
      exact pullbackValIso_comp_leg h f M
    · exact pullbackValIso_comp_leg h f N


/-! ## Pure-tensor calculations for pushforward coherence -/

set_option backward.isDefEq.respectTransparency false in
/-- Pure-tensor value of the oplax tensorator for a strong `restrictScalars` functor.

For sectionwise-bijective `α`, the oplax tensorator is inverse to the lax tensorator and therefore
sends the relabelled pure tensor over `S` to the corresponding pure tensor over `R`. -/
private lemma restrictScalars_δ_app_tmul
    {C : Type u} [Category.{u} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : (R ⋙ forget₂ CommRingCat RingCat) ⟶ (S ⋙ forget₂ CommRingCat RingCat))
    (hα : ∀ U, Function.Bijective (α.app U).hom)
    (M₁ M₂ : _root_.PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ)
    (m : (M₁.obj W)) (n : (M₂.obj W)) :
    letI := PresheafOfModules.restrictScalarsMonoidalOfBijective α hα
    ModuleCat.Hom.hom ((Functor.OplaxMonoidal.δ (PresheafOfModules.restrictScalars α) M₁ M₂).app W)
        (m ⊗ₜ[(S ⋙ forget₂ CommRingCat RingCat).obj W] n)
      = (m ⊗ₜ n : ↑(((PresheafOfModules.restrictScalars α).obj M₁ ⊗
          (PresheafOfModules.restrictScalars α).obj M₂).obj W)) := by
  letI := PresheafOfModules.restrictScalarsMonoidalOfBijective α hα
  have hμ : ModuleCat.Hom.hom
      ((Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars α) M₁ M₂).app W)
        (m ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj W] n) = m ⊗ₜ n :=
    restrictScalars_μ_app_tmul α M₁ M₂ W m n
  rw [← hμ, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← PresheafOfModules.comp_app,
    Functor.Monoidal.μ_δ]
  rfl


private lemma isIso_of_isIso_comp4_mid {C : Type*} [Category C] {W₀ X₀ Y₀ Z₀ T₀ : C}
    {a : W₀ ⟶ X₀} {b : X₀ ⟶ Y₀} {c : Y₀ ⟶ Z₀} {d : Z₀ ⟶ T₀}
    (h : IsIso (a ≫ b ≫ c ≫ d)) (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b := by
  haveI := h; haveI := ha; haveI := hc; haveI := hd
  haveI : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a (b ≫ c ≫ d)
  exact IsIso.of_isIso_comp_right b (c ≫ d)

/-- **Helper (trivial-base reduction): `pullbackTensorMap` is an iso when both base modules
are trivial.** For `f : Y ⟶ X` and `P Q : X.Modules` each isomorphic to the unit `𝒪_X`, the
comparison `pullbackTensorMap f P Q` is an isomorphism. Proof: conjugate the unit-pair iso
`pullbackTensorMap_unit_isIso` by the trivialisations `eP, eQ` through the naturality square
`pullbackTensorMap_natural`. Both flanking factors of that square are isos (functor-images and
`tensorObjIsoOfIso` of isos), so the unit-pair iso transports to `pullbackTensorMap f P Q`. -/
lemma pullbackTensorMap_isIso_of_base_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P Q : X.Modules} (eP : P ≅ SheafOfModules.unit X.ringCatSheaf)
    (eQ : Q ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (pullbackTensorMap f P Q) := by
  have hnat := pullbackTensorMap_natural f eP.hom eQ.hom
  -- the `tensorObj_functoriality` of two isos is the `.hom` of `tensorObjIsoOfIso`, hence iso.
  haveI : IsIso (tensorObj_functoriality eP.hom eQ.hom) :=
    (tensorObjIsoOfIso eP eQ).isIso_hom
  haveI : IsIso (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) := pullbackTensorMap_unit_isIso f
  haveI : IsIso ((Scheme.Modules.pullback f).map (tensorObj_functoriality eP.hom eQ.hom)) :=
    Functor.map_isIso _ _
  haveI hG : IsIso (tensorObj_functoriality ((Scheme.Modules.pullback f).map eP.hom)
      ((Scheme.Modules.pullback f).map eQ.hom)) :=
    (tensorObjIsoOfIso ((Scheme.Modules.pullback f).mapIso eP)
      ((Scheme.Modules.pullback f).mapIso eQ)).isIso_hom
  haveI hL : IsIso ((Scheme.Modules.pullback f).map (tensorObj_functoriality eP.hom eQ.hom) ≫
      pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf)) := inferInstance
  rw [hnat] at hL
  exact IsIso.of_isIso_comp_right (pullbackTensorMap f P Q)
    (tensorObj_functoriality ((Scheme.Modules.pullback f).map eP.hom)
      ((Scheme.Modules.pullback f).map eQ.hom))

/-- **Sectionwise value of the presheaf-level `pushforwardPushforwardAdj` unit.** The unit of
`pushforwardPushforwardAdj adj φ ψ H₁ H₂ : pushforward φ ⊣ pushforward ψ` is the four-fold composite
`(pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫ (pushforwardCongr _).hom ≫
(pushforwardComp _ _).inv`.  Both `pushforwardId` and `pushforwardComp` are `Iso.refl` (identity on
carriers), and `pushforwardNatTrans`/`pushforwardCongr` act on carriers by the presheaf restriction
map of `M` along `adj.counit` (the `restrictScalars` base change is the identity on the underlying
abelian group).  Hence on a section at `U`, the unit is just `M.map (adj.counit.app U.unop).op`.
This is the presheaf-level value lemma the K1 η-bridge needs (no sheaf-level twin exists). -/
private lemma pushforwardPushforwardAdj_unit_app_app_apply
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
    (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)
    (M : _root_.PresheafOfModules R) (U : Dᵒᵖ) (x : M.obj U) :
    (((PresheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app U).hom x
      = (M.map (adj.counit.app U.unop).op).hom x := by
  rfl

/-- **Sectionwise value of the presheaf-level `pushforwardPushforwardAdj` counit** (dual of
`pushforwardPushforwardAdj_unit_app_app_apply`). The counit of
`pushforwardPushforwardAdj adj φ ψ H₁ H₂ : pushforward φ ⊣ pushforward ψ` is the four-fold composite
`(pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫ (pushforwardCongr _).hom ≫
(pushforwardId _).hom`.  Both `pushforwardId` and `pushforwardComp` are `Iso.refl` (identity on
carriers), and `pushforwardNatTrans`/`pushforwardCongr` act on carriers by the presheaf restriction
map of `N` along `adj.unit` (the `restrictScalars` base change is the identity on the underlying
abelian group).  Hence on a section at `U`, the counit is just `N.map (adj.unit.app U.unop).op`.
This is the presheaf-level value lemma the K1 μ/`lhs_tmul` counit-pair leg needs (mirrors Mathlib's
`pushforwardPushforwardAdj_counit_app_val_app`, but at the presheaf level). -/
private lemma pushforwardPushforwardAdj_counit_app_app_apply
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
    (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)
    (N : _root_.PresheafOfModules S) (U : Cᵒᵖ)
    (y : ((PresheafOfModules.pushforward ψ ⋙ PresheafOfModules.pushforward φ).obj N).obj U) :
    (((PresheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app N).app U).hom y
      = (N.map (adj.unit.app U.unop).op).hom y := by
  rfl

/-- **Sectionwise unit-preservation of the strong-monoidal `restrictScalars` oplax unit.**
For a sectionwise-bijective ground-ring map `α`, the oplax monoidal unit `η (restrictScalars α)`
sends the section ring unit `1` to `1`.  The unit element is typed through the genuine ring
`(S ⋙ forget₂ …).obj W` (so `OfNat`/`One` synthesises), transported along `𝟙_ = unit`.  This is
the LHS twin of the K1 η-collapse residual: lax `ε` sends `1 ↦ 1`
(`ModuleCat.restrictScalars_η` + `RingHom.map_one`) and `ε ≫ η = 𝟙` (`Functor.Monoidal.ε_η`). -/
lemma restrictScalars_oplaxMonoidal_η_app_one {C : Type u} [Category.{u} C]
    {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ S ⋙ forget₂ CommRingCat RingCat)
    (hα : ∀ U, Function.Bijective (α.app U).hom) (W : Cᵒᵖ) :
    letI := PresheafOfModules.restrictScalarsMonoidalOfBijective α hα
    ((Functor.OplaxMonoidal.η (PresheafOfModules.restrictScalars α)).app W).hom
        (1 : (S ⋙ forget₂ CommRingCat RingCat).obj W)
      = (1 : (R ⋙ forget₂ CommRingCat RingCat).obj W) := by
  letI := PresheafOfModules.restrictScalarsMonoidalOfBijective α hα
  have hε : ((Functor.LaxMonoidal.ε (PresheafOfModules.restrictScalars α)).app W).hom
      (1 : (R ⋙ forget₂ CommRingCat RingCat).obj W)
      = (1 : (S ⋙ forget₂ CommRingCat RingCat).obj W) := by
    erw [ModuleCat.restrictScalars_η]; exact RingHom.map_one _
  rw [← hε, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← PresheafOfModules.comp_app,
      show Functor.LaxMonoidal.ε (PresheafOfModules.restrictScalars α)
          ≫ Functor.OplaxMonoidal.η (PresheafOfModules.restrictScalars α) = 𝟙 _
        from Functor.Monoidal.ε_η _]
  rfl

/-- **K1 η-side collapse: `H1` respects the unit comparison.** In the K1 setting (open immersion
`f : Y ⟶ X`, presheaf structure map `φ'`, structure-ring iso `β`/`β'`, strong-monoidal restriction
functor `Gβ = pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙ restrictScalars β'`, and the
`leftAdjointUniq` iso `H1 : Gβ ≅ pullback φ'`), the strong unit comparison `η Gβ` agrees, under
`H1`, with the oplax unit comparison `η (pullback φ')`. This is the unit-side counterpart of
`presheafUnit_comp_map_eta`; sectionwise it is the `f.appIso` identity on the unit module. -/
private lemma pushforward_eta_appIso_collapse {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    haveI hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
      (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
      PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
        (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
        (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
    have hβ : ∀ U, Function.Bijective (β.app U).hom := by
      intro U
      haveI : IsIso (β.app U) :=
        inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
      exact ConcreteCategory.bijective_of_isIso (β.app U)
    let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
    letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
      PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
    letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
      PresheafOfModules.restrictScalars β'
    let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
    Functor.OplaxMonoidal.η Gβ
      = (hadj'.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φ')).hom.app (𝟙_ _)
        ≫ Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ') := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  haveI hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv
      naturality := fun _ _ i => f.appIso_inv_naturality i }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  -- `hadj` is a `let` (not `have`): the statement's signature `let`s zeta-reduce the `H1` term in
  -- the goal to its fully-unfolded `pushforwardPushforwardAdj …` form, so a transparent `let` is
  -- needed for the mate lemmas (`unit_leftAdjointUniq_hom_app`) to key-match it via `erw`.
  let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  have hβ : ∀ U, Function.Bijective (β.app U).hom := by
    intro U
    haveI : IsIso (β.app U) :=
      inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
    exact ConcreteCategory.bijective_of_isIso (β.app U)
  let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
  letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
    PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
  letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
    PresheafOfModules.restrictScalars β'
  let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
  -- Transpose across `hadj'`; the uniqueness comparison contracts the units, and
  -- `presheafUnit_comp_map_eta` identifies the resulting right-adjoint unit comparison.
  apply (hadj'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  erw [reassoc_of% (Adjunction.unit_leftAdjointUniq_hom_app hadj'
    (PresheafOfModules.pullbackPushforwardAdjunction φ') (𝟙_ _))]
  erw [presheafUnit_comp_map_eta f]
  -- Identify the right-adjoint unit comparison and verify it sectionwise on the ring generator `1`.
  erw [epsilonPresheafToSheafUnit f]
  refine PresheafOfModules.hom_ext (fun U => ?_)
  apply ModuleCat.hom_ext
  ext
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  -- Split the composite unit and reindex the section through the pushforward.
  rw [PresheafOfModules.comp_app]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [Functor.OplaxMonoidal.comp_η,
      show Functor.OplaxMonoidal.η
        (PresheafOfModules.pushforward₀OfCommRingCat
          (Hom.opensFunctor f) X.presheaf) = 𝟙 _ from rfl]
  erw [PresheafOfModules.pushforward_map_app_apply]
  -- The preceding pushforward value lemma has exposed the unit-module restriction map; it preserves
  -- the ring unit.
  erw [PresheafOfModules.unit_map_one]
  -- Both remaining maps preserve the ring unit.
  erw [restrictScalars_oplaxMonoidal_η_app_one β' hβ (Opposite.op (f ⁻¹ᵁ Opposite.unop U)),
    map_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pure-tensor value of the directly defined pushforward composition tensorator.

After reindexing by `pushforward₀OfCommRingCat`, `pushforward_μ_eq` identifies this tensorator with
the tensorator of `restrictScalars`, whose pure-tensor value is
`restrictScalars_μ_app_tmul`. -/
lemma pushforward_lax_mu_comparison_rhs_tmul
    {C : Type u} [Category.{u} C] {S₀ T₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ' : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶ (T₀ ⋙ forget₂ CommRingCat RingCat))
    (M₁ M₂ : _root_.PresheafOfModules (T₀ ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ)
    (m : (M₁.obj W)) (n : (M₂.obj W)) :
    ((Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars φ') M₁ M₂).app W).hom
        (m ⊗ₜ[(S₀ ⋙ forget₂ CommRingCat RingCat).obj W] n) = m ⊗ₜ n :=
  -- The abstract parameters keep the section-module instances canonical.
  restrictScalars_μ_app_tmul φ' M₁ M₂ W m n

set_option maxHeartbeats 1600000 in
-- The mate tensorator expands through the sectionwise unit, tensorator, and counit legs.
set_option backward.isDefEq.respectTransparency false in
/-- Sectionwise equality of the transported and directly defined pushforward tensorators.

On pure tensors, unfold the adjunction mate and compute its unit, tensorator, and counit legs. The
directly defined side is handled by `pushforward_lax_mu_comparison_rhs_tmul`. -/
lemma pushforward_lax_mu_comparison_lhs_tmul {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f]
    (A B : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (W : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    haveI _hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
      (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
      PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
        (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
        (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
    have hβ : ∀ U, Function.Bijective (β.app U).hom := by
      intro U
      haveI : IsIso (β.app U) :=
        inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
      exact ConcreteCategory.bijective_of_isIso (β.app U)
    let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
    letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
      PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
    letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
      PresheafOfModules.restrictScalars β'
    let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
    (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (PresheafOfModules.pushforward φ')
        (Adjunction.rightAdjointLaxMonoidal hadj') (Gβ.obj A) (Gβ.obj B)).app W
      = (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (PresheafOfModules.pushforward φ')
        (presheafPushforwardLaxMonoidal φ') (Gβ.obj A) (Gβ.obj B)).app W := by
  intro α β hadj hβ β' hadj'
  -- Work on pure tensors in the section module at `W`.
  refine ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_)
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
  rw [PresheafOfModules.comp_app]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- Evaluate the adjunction unit through a polymorphic local statement to preserve its instance.
  have hU : ∀ (M : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
      (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) (x : (M.obj U)),
      ((hadj'.unit.app M).app U).hom x
        = (M.map (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U.unop).op).hom x :=
    fun M U x => pushforwardPushforwardAdj_unit_app_app_apply _ _ _ _ _ M U x
  erw [hU]
  -- Split the mapped tensorator-counit composite and evaluate it on the section.
  rw [Functor.map_comp, PresheafOfModules.comp_app]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- Evaluate the tensor-presheaf restriction on a pure tensor over an abstract ring functor.
  have h1 : ∀ {R : (TopologicalSpace.Opens ↑X)ᵒᵖ ⥤ CommRingCat.{u}}
      (P Q : _root_.PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
      {V : (TopologicalSpace.Opens ↑X)ᵒᵖ} (g : W ⟶ V) (p : P.obj W) (q : Q.obj W),
      ((P ⊗ Q).map g).hom (p ⊗ₜ q) = (P.map g).hom p ⊗ₜ (Q.map g).hom q := by
    intro R P Q V g p q; exact PresheafOfModules.Monoidal.tensorObj_map_tmul g p q
  have h1c := h1 ((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).obj
      ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
        PresheafOfModules.restrictScalars β').obj A))
    ((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).obj
      ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
        PresheafOfModules.restrictScalars β').obj B))
    (f.isOpenEmbedding.isOpenMap.adjunction.counit.app W.unop).op m n
  erw [h1c]
  -- Reindex the outer counit pair through the pushforward.
  rw [PresheafOfModules.pushforward_map_app_apply]
  -- Reindex the inner tensorator and collapse its value on the pure tensor.
  erw [PresheafOfModules.pushforward_map_app_apply,
    restrictScalars_δ_app_tmul β' hβ
      ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf).obj
        ((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).obj
          ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
            PresheafOfModules.restrictScalars β').obj A)))
      ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf).obj
        ((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).obj
          ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
            PresheafOfModules.restrictScalars β').obj B)))
      (Opposite.op ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W)))]
  -- Split the counit tensor morphism into its two sectionwise legs.
  erw [PresheafOfModules.Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]
  -- Express each adjunction counit leg as restriction along the topological unit.
  have hC : ∀ (N : _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
      (U : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
      (y : (((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom ⋙
          (PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
            PresheafOfModules.restrictScalars β')).obj N).obj U)),
      ConcreteCategory.hom ((hadj'.counit.app N).app U) y =
        ConcreteCategory.hom
          (N.map (f.isOpenEmbedding.isOpenMap.adjunction.unit.app U.unop).op) y :=
    fun N U y => pushforwardPushforwardAdj_counit_app_app_apply _ _ _ _ _ N U y
  -- Pin the presheaf, open, and section element when applying the counit formula to each leg.
  erw [hC ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
        PresheafOfModules.restrictScalars β').obj A)
      (Opposite.op ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W)))
      ((ModuleCat.Hom.hom (((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).obj
            ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
              PresheafOfModules.restrictScalars β').obj A)).map
          (f.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op)) m)]
  erw [hC ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
        PresheafOfModules.restrictScalars β').obj B)
      (Opposite.op ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W)))
      ((ModuleCat.Hom.hom (((PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).obj
            ((PresheafOfModules.pushforward₀OfCommRingCat (Hom.opensFunctor f) X.presheaf ⋙
              PresheafOfModules.restrictScalars β').obj B)).map
          (f.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op)) n)]
  -- The directly defined tensorator also sends the pure tensor to itself.
  erw [pushforward_lax_mu_comparison_rhs_tmul]
  -- The two restrictions compose to the identity because the category of opens is thin.
  have hfac : ∀ (P : _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
      (z : ↑(P.obj (Opposite.op ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W))))),
      ConcreteCategory.hom
          (P.map (f.isOpenEmbedding.isOpenMap.adjunction.unit.app
            ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W))).op)
        (ConcreteCategory.hom
          (P.map
            ((TopologicalSpace.Opens.map f.base).map
              (f.isOpenEmbedding.isOpenMap.adjunction.counit.app
                (Opposite.unop W)).op.unop).op) z) = z := by
    intro P z
    -- Use `P.map_comp` to retain the definitionally equal intermediate open.
    have step : ConcreteCategory.hom (P.map
          (((TopologicalSpace.Opens.map f.base).map
              (f.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op.unop).op ≫
            (f.isOpenEmbedding.isOpenMap.adjunction.unit.app
              ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W))).op)) z = z := by
      conv_lhs => rw [show ((TopologicalSpace.Opens.map f.base).map
              (f.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op.unop).op ≫
            (f.isOpenEmbedding.isOpenMap.adjunction.unit.app
              ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W))).op
          = 𝟙 _ from Subsingleton.elim _ _]
      exact (ConcreteCategory.congr_hom (P.map_id _) z).trans (CategoryTheory.id_apply z)
    exact (ConcreteCategory.congr_hom
      (P.map_comp
        ((TopologicalSpace.Opens.map f.base).map
          (f.isOpenEmbedding.isOpenMap.adjunction.counit.app (Opposite.unop W)).op.unop).op
        (f.isOpenEmbedding.isOpenMap.adjunction.unit.app
          ((TopologicalSpace.Opens.map f.base).obj (Opposite.unop W))).op) z).symm.trans step
  congr 1
  · simp only [PresheafOfModules.pushforward_obj_map_apply]; exact hfac _ m
  · simp only [PresheafOfModules.pushforward_obj_map_apply]; exact hfac _ n

/- The transported and directly defined pushforward tensorators agree sectionwise by the preceding
pure-tensor calculation. -/
lemma pushforward_lax_mu_comparison {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (A B : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    haveI _hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
      (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
      PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
        (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
        (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
    have hβ : ∀ U, Function.Bijective (β.app U).hom := by
      intro U
      haveI : IsIso (β.app U) :=
        inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
      exact ConcreteCategory.bijective_of_isIso (β.app U)
    let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
    letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
      PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
    letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
      PresheafOfModules.restrictScalars β'
    let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (PresheafOfModules.pushforward φ')
        (Adjunction.rightAdjointLaxMonoidal hadj') (Gβ.obj A) (Gβ.obj B)
      = @Functor.LaxMonoidal.μ _ _ _ _ _ _ (PresheafOfModules.pushforward φ')
        (presheafPushforwardLaxMonoidal φ') (Gβ.obj A) (Gβ.obj B) := by
  intro α β hadj hβ β' hadj'
  -- Reduce the morphism equality to the sectionwise comparison.
  exact PresheafOfModules.hom_ext (fun W => pushforward_lax_mu_comparison_lhs_tmul f A B W)

/-- Mate conjugation for two oplax tensorators sharing a right adjoint.

If the transported right-adjoint tensorator agrees with the ambient lax tensorator on `F₁ A` and
`F₁ B`, then `δ F₁` is the `leftAdjointUniq` conjugate of `δ F₂`. The proof transposes through
`adj₁`, contracts the uniqueness comparisons, and applies the supplied tensorator equality. -/
lemma deltaConjOfMuComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F₁ F₂ : C ⥤ D} {G : D ⥤ C} (adj₁ : F₁ ⊣ G) (adj₂ : F₂ ⊣ G)
    [F₁.OplaxMonoidal] [F₂.OplaxMonoidal] [G.LaxMonoidal] [adj₂.IsMonoidal] (A B : C)
    (hμ : @Functor.LaxMonoidal.μ _ _ _ _ _ _ G (Adjunction.rightAdjointLaxMonoidal adj₁)
          (F₁.obj A) (F₁.obj B)
        = Functor.LaxMonoidal.μ G (F₁.obj A) (F₁.obj B)) :
    Functor.OplaxMonoidal.δ F₁ A B
      = (adj₁.leftAdjointUniq adj₂).hom.app (A ⊗ B) ≫ Functor.OplaxMonoidal.δ F₂ A B
        ≫ ((adj₁.leftAdjointUniq adj₂).inv.app A ⊗ₘ (adj₁.leftAdjointUniq adj₂).inv.app B) := by
  -- The inverse uniqueness comparison carries the `adj₂` unit to the `adj₁` unit.
  have htri' : ∀ P, adj₂.unit.app P ≫ G.map ((adj₁.leftAdjointUniq adj₂).inv.app P)
      = adj₁.unit.app P := by
    intro P
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.unit_leftAdjointUniq_hom_app adj₂ adj₁ P
  -- (LHS mate): `δ F₁` transposes to `μ (rightAdjointLaxMonoidal adj₁)` (instance forced).
  have hLHS : adj₁.unit.app (A ⊗ B) ≫ G.map (Functor.OplaxMonoidal.δ F₁ A B)
      = (adj₁.unit.app A ⊗ₘ adj₁.unit.app B) ≫
        @Functor.LaxMonoidal.μ _ _ _ _ _ _ G (Adjunction.rightAdjointLaxMonoidal adj₁)
          (F₁.obj A) (F₁.obj B) := by
    letI := Adjunction.rightAdjointLaxMonoidal adj₁
    letI : adj₁.IsMonoidal := inferInstance
    exact adj₁.unit_app_tensor_comp_map_δ A B
  -- μ-naturality (tensorHom form) on the `H1.inv` legs; the `_left`/`_right` `@[simp]` variants are
  -- whiskering-based and do not fire on the `⊗ₘ` form, so we feed the combined `μ_natural` by hand.
  have hnat := Functor.LaxMonoidal.μ_natural G ((adj₁.leftAdjointUniq adj₂).inv.app A)
    ((adj₁.leftAdjointUniq adj₂).inv.app B)
  -- Transpose across `adj₁` and replace the left tensorator by its right-adjoint mate.
  apply (adj₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  -- Restate the goal with the monoidal instance used by `hLHS`.
  change adj₁.unit.app (A ⊗ B) ≫ G.map (Functor.OplaxMonoidal.δ F₁ A B) =
    adj₁.unit.app (A ⊗ B) ≫ G.map ((adj₁.leftAdjointUniq adj₂).hom.app (A ⊗ B) ≫
      Functor.OplaxMonoidal.δ F₂ A B ≫
        ((adj₁.leftAdjointUniq adj₂).inv.app A ⊗ₘ (adj₁.leftAdjointUniq adj₂).inv.app B))
  rw [hLHS]
  -- Contract the two mates on the right, then slide `μ` past the inverse comparison legs.
  conv_rhs =>
    rw [Functor.map_comp, Functor.map_comp]
    -- the unit's source object prints as `(𝟭 C).obj (A ⊗ B)` (not `A ⊗ B`), so the `reassoc_of%`
    -- pattern is matched up to defeq with `erw`, not `rw`.
    erw [reassoc_of% (Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ (A ⊗ B)),
      reassoc_of% (adj₂.unit_app_tensor_comp_map_δ A B)]
    erw [← hnat, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  exact congr_arg₂ (· ≫ ·)
    (congr_arg₂ MonoidalCategory.tensorHom (htri' A).symm (htri' B).symm) hμ

/-- **K1 μ/δ-side collapse: `H1` respects the tensorator.** In the K1 setting, for all presheaves
of modules `A B`, the strong tensorator `δ Gβ A B` of the restriction functor agrees with the
`H1`-conjugate of the oplax tensorator `δ (pullback φ') A B`. This is the genuine geometric content
of K1 (the μ/δ-side twin of `presheafUnit_comp_map_eta`, the open-immersion analogue of
`pushforwardComp_lax_μ`). It is the abstract mate-conjugation `deltaConjOfMuComparison` fed the bare
tensorator comparison `pushforward_lax_mu_comparison` (the genuine, NON-circular geometric input;
routing through `hadj'.IsMonoidal` would be circular, since that instance consumes this lemma). -/
lemma pushforward_mu_appIso_collapse {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (A B : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    haveI hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
      (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
      PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
        (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
        (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
    have hβ : ∀ U, Function.Bijective (β.app U).hom := by
      intro U
      haveI : IsIso (β.app U) :=
        inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
      exact ConcreteCategory.bijective_of_isIso (β.app U)
    let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
    letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
      PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
    letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
      PresheafOfModules.restrictScalars β'
    let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
    Functor.OplaxMonoidal.δ Gβ A B
      = (hadj'.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φ')).hom.app (A ⊗ B)
        ≫ Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') A B
        ≫ ((hadj'.leftAdjointUniq
              (PresheafOfModules.pullbackPushforwardAdjunction φ')).inv.app A
            ⊗ₘ (hadj'.leftAdjointUniq
              (PresheafOfModules.pullbackPushforwardAdjunction φ')).inv.app B) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  haveI hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv
      naturality := fun _ _ i => f.appIso_inv_naturality i }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  -- `hadj` is a `let` (not `have`): keeps the goal's `H1 = hadj'.leftAdjointUniq` term in its
  -- fully-unfolded `pushforwardPushforwardAdj …` form key-matchable via `erw` (cf. the η-side).
  let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  have hβ : ∀ U, Function.Bijective (β.app U).hom := by
    intro U
    haveI : IsIso (β.app U) :=
      inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
    exact ConcreteCategory.bijective_of_isIso (β.app U)
  let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
  letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
    PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
  letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
    PresheafOfModules.restrictScalars β'
  let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
  -- Apply mate conjugation to the sectionwise tensorator comparison.
  exact deltaConjOfMuComparison hadj' (PresheafOfModules.pullbackPushforwardAdjunction φ') A B
    (pushforward_lax_mu_comparison f A B)

/-- **Abstract iso-sandwich: an oplax tensorator conjugate to a strong one is an iso.**
If `F₁` is strong monoidal (so its oplax `δ` is invertible), `F₂` is oplax monoidal, `e : F₁ ≅ F₂`
is any natural iso, and the `δ`'s are conjugate via `e`
(`δ F₁ A B = e.hom.app (A⊗B) ≫ δ F₂ A B ≫ (e.inv.app A ⊗ₘ e.inv.app B)`, the conclusion of
`pushforward_mu_appIso_collapse`), then `δ F₂ A B` is itself an iso: it equals the all-iso
composite `inv (e.hom.app (A⊗B)) ≫ δ F₁ A B ≫ inv (e.inv.app A ⊗ₘ e.inv.app B)`. -/
lemma isIso_oplaxδ_of_conj {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] {F₁ F₂ : C ⥤ D}
    [F₁.Monoidal] [F₂.OplaxMonoidal] (e : F₁ ≅ F₂) (A B : C)
    (hconj : Functor.OplaxMonoidal.δ F₁ A B
      = e.hom.app (A ⊗ B) ≫ Functor.OplaxMonoidal.δ F₂ A B
        ≫ (e.inv.app A ⊗ₘ e.inv.app B)) :
    IsIso (Functor.OplaxMonoidal.δ F₂ A B) := by
  have h2 : Functor.OplaxMonoidal.δ F₂ A B
      = inv (e.hom.app (A ⊗ B)) ≫ Functor.OplaxMonoidal.δ F₁ A B
        ≫ inv (e.inv.app A ⊗ₘ e.inv.app B) := by
    rw [hconj]; simp
  rw [h2]; infer_instance


end LocTrivPullbackTensor

end Modules

end Scheme

end AlgebraicGeometry
