/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate
import AlgebraicJacobian.Picard.TensorObjSubstrate.PresheafInternalHom

/-!
# Duals of locally trivial modules

This file develops the sectionwise comparison needed to commute duals with restriction along an
open immersion. It proves `dual_restrict_iso` and `dual_isLocallyTrivial`, and also supplies
`homOfLocalCompat`, the gluing construction for compatible local module morphisms.

The main construction is `sliceDualTransport`. It reindexes a dual section across the open-map
functor and transports its scalar action through the structure-ring isomorphism. The resulting
sectionwise isomorphisms assemble into the presheaf comparison used by `dual_restrict_iso`.

Blueprint chapter: `blueprint/src/chapters/Picard_TensorObjSubstrate.tex`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

/-! ## §0. Presheaf-level: the dual of the monoidal unit is the unit

Project-local supplement to `PresheafInternalHom.lean`: `PresheafOfModules.dual 𝟙_ ≅ 𝟙_`
(the evaluation-at-`1` isomorphism `ℋom(𝟙_, 𝟙_) ≅ 𝟙_`), built over a general single-universe
base category.  It feeds `Scheme.Modules.dual_unit_iso` (below) at `R₀ := Y.presheaf`. -/

namespace PresheafOfModules

open InternalHom Opposite

variable {D : Type u} [Category.{u, u} D] {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- **Section equivalence for the dual of the unit.** At an object `X`, endomorphisms of the
(restricted) unit `restr X 𝟙_ ⟶ restr X 𝟙_` are identified `R₀(X)`-linearly with `R₀(X)` itself,
via evaluation at `1`; the inverse is multiplication by a global scalar (`globalSMul`). The
substantive content is `left_inv`: every endomorphism of the unit is multiplication by its value
at `1` (proved from `φ`-naturality toward the terminal object of the slice). -/
noncomputable def unitDualSectionEquiv (X : Dᵒᵖ) :
    letI := internalHomObjModule X.unop
      (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
      (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    (restr X.unop (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))) ⟶
        restr X.unop (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))))
      ≃ₗ[(R₀.obj (op X.unop) : Type u)] (R₀.obj (op X.unop) : Type u) := by
  letI := internalHomObjModule X.unop
    (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
    (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
  exact
    { toFun := fun φ =>
        evalLin (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))) X φ
          (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X : Type u))
      map_add' := fun φ φ' => rfl
      map_smul' := fun c φ => by
        exact DFunLike.congr_fun (evalLin_smul _ X c φ)
          (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X : Type u))
      invFun := fun r =>
        globalSMul Over.mkIdTerminal
          (restr X.unop (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))) r
      left_inv := fun φ => by
        ext Y
        dsimp only
        erw [globalSMul_hom_apply]
        have hnat := PresheafOfModules.naturality_apply φ (Over.mkIdTerminal.from Y.unop).op
          (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X : Type u))
        erw [PresheafOfModules.unit_map_one] at hnat
        erw [hnat, smul_eq_mul, mul_one]
        rfl
      right_inv := fun r => by
        change ((globalSMul Over.mkIdTerminal
            (restr X.unop
              (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))) r).app
            (op (Over.mk (𝟙 X.unop)))).hom
            (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X : Type u)) = r
        rw [globalSMul_hom_apply, termRingMap_terminal]
        exact mul_one r }

/-- **The presheaf dual of the monoidal unit is the unit**, `PresheafOfModules.dual 𝟙_ ≅ 𝟙_`,
assembled sectionwise from `unitDualSectionEquiv` with the evaluation-at-`1` naturality (mirroring
`InternalHom.internalHomEval`'s naturality at `M = 𝟙_`). -/
noncomputable def dualUnitIsoGen :
    PresheafOfModules.dual (R₀ := R₀)
        (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))
      ≅ 𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.isoMk (fun X => (unitDualSectionEquiv X).toModuleIso)
    (fun {X Y} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
      change evalLin (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))) Y
            ((PresheafOfModules.dual
              (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).map f φ)
            (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj Y : Type u))
          = ((𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))).map f).hom
              (evalLin (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))) X φ
                (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X : Type u)))
      have key := PresheafOfModules.naturality_apply
        (φ : restr X.unop (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))) ⟶
          restr X.unop (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))))
        (Over.homMk f.unop (Category.comp_id _) : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op
        (1 : ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X : Type u))
      have hrm : (restr X.unop
            (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).map
          (Over.homMk f.unop (Category.comp_id _) : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op
          = (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))).map f := rfl
      rw [hrm] at key
      erw [PresheafOfModules.unit_map_one] at key
      have hAB : (op (Over.mk (𝟙 Y.unop ≫ f.unop)) : (Over X.unop)ᵒᵖ) = op (Over.mk f.unop) :=
        congrArg op (congrArg Over.mk (Category.id_comp f.unop))
      have homAppHEq : ∀ {A B : (Over X.unop)ᵒᵖ} (_ : A = B), HEq (φ.app A) (φ.app B) := by
        intro A B h; subst h; rfl
      have hdt : evalLin (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat))) Y
          ((PresheafOfModules.dual
            (𝟙_ (_root_.PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)))).map f φ)
          = (φ.app (op (Over.mk f.unop))).hom :=
        congrArg ModuleCat.Hom.hom (eq_of_heq (homAppHEq hAB))
      exact (DFunLike.congr_fun hdt _).trans key)

end PresheafOfModules

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-! ## §A. The C-bridge: restriction commutes with the sheaf-level dual -/

open Opposite in
/-- **Leg-B atomic claim: the lax-monoidal unit `ε` of `restrictScalars` along the open-immersion
structure ring iso `(f.appIso W').inv` is an isomorphism.**  Its underlying map is the (bijective)
ring map `(f.appIso W').inv.hom`, so `ε` is an iso by `restrictScalars_isIso_ε_of_bijective`
(`PresheafInternalHom.lean`) fed the bijectivity from `ConcreteCategory.bijective_of_isIso`.  This
is the single load-bearing fact powering `dualUnitRingSwap` (the codomain unit ring swap of leg-B),
phrased at the `CommRingCat` carrier so `CommRing` is native. -/
lemma isIso_ε_restrictScalars_appIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y) :
    IsIso (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').inv.hom)) :=
  restrictScalars_isIso_ε_of_bijective (Scheme.Hom.appIso f W').inv.hom
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso f W').inv)

/-- **Element action of `inv ε` for a `restrictScalars` along a bijective ring hom.**  The
lax-monoidal unit `ε (restrictScalars g)` has underlying map `g` (`ModuleCat.restrictScalars_η`);
since `g` is bijective `ε` is invertible (`restrictScalars_isIso_ε_of_bijective`) and the underlying
map of `inv ε` is `g⁻¹` (`(RingEquiv.ofBijective g hg).symm`).  This is the reusable element-level
ingredient that powers the ε-swap cancellations in the `sliceDualTransport` round-trips and
naturality (`dualUnitRingSwap`/`dualUnitRingSwapHom`/`unitRelabelSwap` are all `inv ε`s). -/
lemma εInv_apply {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (hg : Function.Bijective g) (s : S) :
    haveI := restrictScalars_isIso_ε_of_bijective g hg
    (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.inv (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars g)))) s
      = (RingEquiv.ofBijective g hg).symm s := by
  haveI := restrictScalars_isIso_ε_of_bijective g hg
  have key : (CategoryTheory.ConcreteCategory.hom
        (CategoryTheory.inv (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars g))))
        ((CategoryTheory.ConcreteCategory.hom (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars g)))
          ((RingEquiv.ofBijective g hg).symm s)) = (RingEquiv.ofBijective g hg).symm s := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply, IsIso.hom_inv_id]; rfl
  rw [ModuleCat.restrictScalars_η] at key
  rw [show g ((RingEquiv.ofBijective g hg).symm s) = s from
    (RingEquiv.ofBijective g hg).apply_symm_apply s] at key
  exact key

open Opposite in
/-- **Two ε-swap cancellation on the unit carrier.**  The reverse transport `sliceDualTransportInv`
applies `inv ε (.hom-direction)` after the forward transport's `inv ε (.inv-direction)`; on the
shared section ring `𝒪_X(f''ᵁP)` the two `inv ε` (= `(RingEquiv.ofBijective (appIso).hom).symm` and
`(RingEquiv.ofBijective (appIso).inv).symm`) cancel, because `(appIso f P).hom` and
`(appIso f P).inv` are mutually-inverse ring maps (`Iso.hom_inv_id`). Stated at the plain
`↑(X.presheaf.obj _)` carrier
(not the `restr`/`𝟙_` spelling) so the `RingEquiv`/`Mul` instance synthesis is native; the caller
bridges the unit-object spelling with `erw`. -/
lemma appIso_swap_cancel {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (P : TopologicalSpace.Opens ↥Y)
    (hh : Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appIso f P).hom))
    (hi : Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appIso f P).inv))
    (u : ↑(X.presheaf.obj (Opposite.op ((Scheme.Hom.opensFunctor f).obj P)))) :
    (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.Hom.appIso f P).hom) hh).symm
        ((RingEquiv.ofBijective
          (CommRingCat.Hom.hom (Scheme.Hom.appIso f P).inv) hi).symm u) = u := by
  have h1 : (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.Hom.appIso f P).inv) hi).symm u
      = (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.Hom.appIso f P).hom) hh) u := by
    rw [RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply, RingEquiv.ofBijective_apply]
    have hki := congrArg CommRingCat.Hom.hom (Scheme.Hom.appIso f P).hom_inv_id
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id] at hki
    exact (RingHom.congr_fun hki u).symm
  rw [h1, RingEquiv.symm_apply_apply]

open Opposite in
/-- **`inv ε`-relabel as the reverse section restriction map.**  For an `eqToHom`-induced section
relabel `X.presheaf.map (eqToHom e)` (`e : a = b` of section opens), the inverse `RingEquiv`
(produced by `εInv_apply` at the unit-relabel swap `unitRelabelSwap`) is just the reverse relabel
`X.presheaf.map (eqToHom e.symm)`.  Lets the `unitRelabelSwap` `inv ε` in the `sliceDualTransport`
round-trips collapse to a plain presheaf restriction, exposing `φ.naturality`. -/
lemma presheafMap_ofBijective_symm {X : Scheme.{u}}
    {a b : (TopologicalSpace.Opens ↥X)ᵒᵖ} (e : a = b)
    (hb : Function.Bijective (CommRingCat.Hom.hom (X.presheaf.map (eqToHom e))))
    (s : ↑(X.presheaf.obj b)) :
    (RingEquiv.ofBijective (CommRingCat.Hom.hom (X.presheaf.map (eqToHom e))) hb).symm s
      = (CommRingCat.Hom.hom (X.presheaf.map (eqToHom e.symm))) s := by
  rw [RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp, eqToHom_trans, eqToHom_refl, X.presheaf.map_id, ConcreteCategory.id_apply]

open Opposite in
/-- **Leg-B: the codomain unit ring-iso swap** `restrictScalars (f.appIso W').inv (𝟙_X(fW')) ⟶
𝟙_Y(W')`.  It is the inverse of the lax-monoidal unit `ε (restrictScalars (f.appIso W').inv.hom)`,
an isomorphism by `isIso_ε_restrictScalars_appIso`.  The endpoints are written at the canonical
`CommRingCat` section carriers `↑(X.presheaf.obj _)` / `↑(Y.presheaf.obj _)` (the
`forget₂`-composite carrier breaks `MonoidalCategoryStruct` synthesis); they reconcile by
`rfl`/defeq with the `restr`/`𝟙_`-section spellings of `sliceDualTransport`'s `codomainMap` hole. -/
noncomputable def dualUnitRingSwap {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y) :
    (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').inv.hom).obj
        (𝟙_ (ModuleCat ↑(X.presheaf.obj (op ((Scheme.Hom.opensFunctor f).obj W'))))) ⟶
      𝟙_ (ModuleCat ↑(Y.presheaf.obj (op W'))) :=
  haveI := isIso_ε_restrictScalars_appIso f W'
  CategoryTheory.inv (Functor.LaxMonoidal.ε
    (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').inv.hom))

open Opposite in
/-- **Leg-B (inverse direction): the unit codomain ring-iso swap for `invFun`** `𝟙_Y(W') ⟶
restrictScalars (f.appIso W').inv (𝟙_X(fW'))`.  This is the lax-monoidal unit
`ε (restrictScalars (f.appIso W').inv.hom)` ITSELF (not its inverse), the reverse of
`dualUnitRingSwap`.  By `isIso_ε_restrictScalars_appIso` it is an isomorphism and is the inverse of
`dualUnitRingSwap f W'` (they cancel by `IsIso.inv_hom_id`/`hom_inv_id`). -/
noncomputable def dualUnitRingSwapInv {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y) :
    (𝟙_ (ModuleCat ↑(Y.presheaf.obj (op W')))) ⟶
      (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').inv.hom).obj
        (𝟙_ (ModuleCat ↑(X.presheaf.obj (op ((Scheme.Hom.opensFunctor f).obj W'))))) :=
  Functor.LaxMonoidal.ε (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').inv.hom)

open Opposite in
/-- `dualUnitRingSwapInv` is a section of `dualUnitRingSwap` (`ε ≫ inv ε = 𝟙`). -/
@[simp] lemma dualUnitRingSwapInv_comp_dualUnitRingSwap {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (W' : TopologicalSpace.Opens ↥Y) :
    dualUnitRingSwapInv f W' ≫ dualUnitRingSwap f W' = 𝟙 _ := by
  haveI := isIso_ε_restrictScalars_appIso f W'
  simp [dualUnitRingSwapInv, dualUnitRingSwap]

open Opposite in
/-- `dualUnitRingSwap` is a section of `dualUnitRingSwapInv` (`inv ε ≫ ε = 𝟙`). -/
@[simp] lemma dualUnitRingSwap_comp_dualUnitRingSwapInv {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (W' : TopologicalSpace.Opens ↥Y) :
    dualUnitRingSwap f W' ≫ dualUnitRingSwapInv f W' = 𝟙 _ := by
  haveI := isIso_ε_restrictScalars_appIso f W'
  simp [dualUnitRingSwapInv, dualUnitRingSwap]

open Opposite in
/-- **`invFun` codomain ε is an iso (`.hom` direction).**  The lax-monoidal unit `ε` of
`restrictScalars` along `(f.appIso W').hom` (the `.hom`, not `.inv`, of the structure ring iso) is
an isomorphism, since `(f.appIso W').hom` is a bijective ring map.  This powers the `invFun`
codomain swap (which reindexes the `Over V` section back across `f.opensFunctor` using the
`.hom` direction, the mirror of `dualUnitRingSwap`'s `.inv`). -/
lemma isIso_ε_restrictScalars_appIso_hom {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y) :
    IsIso (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').hom.hom)) :=
  restrictScalars_isIso_ε_of_bijective (Scheme.Hom.appIso f W').hom.hom
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso f W').hom)

open Opposite in
/-- **`invFun` codomain unit ring-iso swap** `restrictScalars (f.appIso W').hom (𝟙_Y(W')) ⟶
𝟙_X(fW')`.  It is the inverse of the lax-monoidal unit `ε (restrictScalars (f.appIso W').hom)`,
an isomorphism by `isIso_ε_restrictScalars_appIso_hom`.  This is the codomain swap of the reverse
transport `invFun` (mirror of `dualUnitRingSwap`, using the `.hom` direction). -/
noncomputable def dualUnitRingSwapHom {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y) :
    (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').hom.hom).obj
        (𝟙_ (ModuleCat ↑(Y.presheaf.obj (op W')))) ⟶
      𝟙_ (ModuleCat ↑(X.presheaf.obj (op ((Scheme.Hom.opensFunctor f).obj W')))) :=
  haveI := isIso_ε_restrictScalars_appIso_hom f W'
  CategoryTheory.inv (Functor.LaxMonoidal.ε
    (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').hom.hom))

open Opposite in
/-- **ε is an iso for the section-ring relabel** `X.presheaf.map (eqToHom e)` (an `eqToHom`-induced,
hence bijective, ring map between section rings `𝒪_X(b) → 𝒪_X(a)` for `a = b`).  Phrased at the
`X.presheaf` (`CommRingCat`) carrier so `CommRing` is native. -/
lemma isIso_ε_restrictScalars_presheafMap {X : Scheme.{u}}
    {a b : (TopologicalSpace.Opens ↥X)ᵒᵖ} (e : a = b) :
    IsIso (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (X.presheaf.map (eqToHom e)).hom)) :=
  restrictScalars_isIso_ε_of_bijective (X.presheaf.map (eqToHom e)).hom
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom e)))

open Opposite in
/-- **Unit-section relabel swap** `restrictScalars (X.presheaf.map (eqToHom e)) (𝟙_X(b)) ⟶ 𝟙_X(a)`
for `a = b` (section opens of `X`).  It is `inv ε` of the relabel ring map, an isomorphism by
`isIso_ε_restrictScalars_presheafMap`.  This is the `?unit` codomain transport of
`sliceDualTransportInv`'s reverse component (mirror of `dualUnitRingSwap` for the `he`-relabel). -/
noncomputable def unitRelabelSwap {X : Scheme.{u}}
    {a b : (TopologicalSpace.Opens ↥X)ᵒᵖ} (e : a = b) :
    (ModuleCat.restrictScalars (X.presheaf.map (eqToHom e)).hom).obj
        (𝟙_ (ModuleCat ↑(X.presheaf.obj b))) ⟶
      𝟙_ (ModuleCat ↑(X.presheaf.obj a)) :=
  haveI := isIso_ε_restrictScalars_presheafMap e
  CategoryTheory.inv (Functor.LaxMonoidal.ε
    (ModuleCat.restrictScalars (X.presheaf.map (eqToHom e)).hom))

open Opposite in
/-- **Pointwise naturality of the `.hom` direction of the structure ring iso**: `(f.appIso _).hom`
intertwines the `X`- and `Y`-restriction maps. -/
lemma appIso_hom_naturality_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {U V : TopologicalSpace.Opens ↥Y} (i : op U ⟶ op V)
    (w : (X.presheaf.obj (op ((Hom.opensFunctor f).obj U)) : Type u)) :
    (Scheme.Hom.appIso f V).hom.hom ((X.presheaf.map ((Hom.opensFunctor f).op.map i)).hom w)
      = (Y.presheaf.map i).hom ((Scheme.Hom.appIso f U).hom.hom w) := by
  have hinj : Function.Injective (Scheme.Hom.appIso f V).inv.hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso f V).inv).1
  apply hinj
  have hVcancel : (Scheme.Hom.appIso f V).inv.hom ((Scheme.Hom.appIso f V).hom.hom
      ((X.presheaf.map ((Hom.opensFunctor f).op.map i)).hom w))
      = (X.presheaf.map ((Hom.opensFunctor f).op.map i)).hom w :=
    ConcreteCategory.congr_hom (Scheme.Hom.appIso f V).hom_inv_id _
  rw [hVcancel]
  have hUw : (Scheme.Hom.appIso f U).inv.hom ((Scheme.Hom.appIso f U).hom.hom w) = w :=
    ConcreteCategory.congr_hom (Scheme.Hom.appIso f U).hom_inv_id w
  have h1 := ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_naturality f i)
    ((Scheme.Hom.appIso f U).hom.hom w)
  change (Scheme.Hom.appIso f V).inv.hom
      ((Y.presheaf.map i).hom ((Scheme.Hom.appIso f U).hom.hom w))
      = (X.presheaf.map ((Hom.opensFunctor f).op.map i)).hom
        ((Scheme.Hom.appIso f U).inv.hom ((Scheme.Hom.appIso f U).hom.hom w)) at h1
  rw [hUw] at h1
  exact h1.symm

set_option backward.isDefEq.respectTransparency false in
open Opposite in
/-- The underlying map of `dualUnitRingSwap` is the `.hom` direction of the open-immersion
structure-ring isomorphism. -/
lemma dualUnitRingSwap_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y)
    (x : (X.presheaf.obj (op ((Scheme.Hom.opensFunctor f).obj W')) : Type u)) :
    (dualUnitRingSwap f W').hom x = (Scheme.Hom.appIso f W').hom.hom x := by
  have h := congrArg ModuleCat.Hom.hom (dualUnitRingSwap_comp_dualUnitRingSwapInv f W')
  have hx := DFunLike.congr_fun h x
  change (dualUnitRingSwapInv f W').hom ((dualUnitRingSwap f W').hom x) = x at hx
  dsimp [dualUnitRingSwapInv] at hx
  have hx' : (Scheme.Hom.appIso f W').inv.hom ((dualUnitRingSwap f W').hom x) = x := by
    simpa only [ModuleCat.restrictScalars_η] using hx
  have hinj : Function.Injective (Scheme.Hom.appIso f W').inv.hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso f W').inv).1
  apply hinj
  rw [hx']
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appIso f W').hom_inv_id x).symm

-- (v4.31.0: the `simpa [restrictScalars_η]` relies on `(restrictScalars _).obj (𝟙_ _)` being defeq
-- to `Γ(Y, _)`; the stricter v4.31.0 defeq rejects it, so restore the leniency knob.)
set_option backward.isDefEq.respectTransparency false in
open Opposite in
/-- The underlying map of `dualUnitRingSwapHom` is the `.inv` direction of the open-immersion
structure-ring isomorphism. -/
lemma dualUnitRingSwapHom_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W' : TopologicalSpace.Opens ↥Y)
    (x : (Y.presheaf.obj (op W') : Type u)) :
    (dualUnitRingSwapHom f W').hom x = (Scheme.Hom.appIso f W').inv.hom x := by
  haveI := isIso_ε_restrictScalars_appIso_hom f W'
  have h := congrArg ModuleCat.Hom.hom
    (IsIso.inv_hom_id (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').hom.hom)))
  have hx := DFunLike.congr_fun h x
  change (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (Scheme.Hom.appIso f W').hom.hom)).hom
      ((dualUnitRingSwapHom f W').hom x) = x at hx
  have hx' : (Scheme.Hom.appIso f W').hom.hom ((dualUnitRingSwapHom f W').hom x) = x := by
    simpa only [ModuleCat.restrictScalars_η] using hx
  have hinj : Function.Injective (Scheme.Hom.appIso f W').hom.hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso f W').hom).1
  apply hinj
  rw [hx']
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appIso f W').inv_hom_id x).symm

set_option backward.isDefEq.respectTransparency false in
open Opposite in
/-- The underlying map of `unitRelabelSwap` is the reverse relabel
`X.presheaf.map (eqToHom e.symm)`. -/
lemma unitRelabelSwap_apply {X : Scheme.{u}}
    {a b : (TopologicalSpace.Opens ↥X)ᵒᵖ} (e : a = b)
    (x : (X.presheaf.obj b : Type u)) :
    (unitRelabelSwap e).hom x = (X.presheaf.map (eqToHom e.symm)).hom x := by
  haveI := isIso_ε_restrictScalars_presheafMap e
  have h := congrArg ModuleCat.Hom.hom
    (IsIso.inv_hom_id (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (X.presheaf.map (eqToHom e)).hom)))
  have hx := DFunLike.congr_fun h x
  change (Functor.LaxMonoidal.ε
      (ModuleCat.restrictScalars (X.presheaf.map (eqToHom e)).hom)).hom
      ((unitRelabelSwap e).hom x) = x at hx
  have hx' : (X.presheaf.map (eqToHom e)).hom ((unitRelabelSwap e).hom x) = x := by
    simpa only [ModuleCat.restrictScalars_η] using hx
  have hinj : Function.Injective (X.presheaf.map (eqToHom e)).hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom e))).1
  apply hinj
  rw [hx']
  have hcomp : X.presheaf.map (eqToHom e.symm) ≫ X.presheaf.map (eqToHom e) = 𝟙 _ := by
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    exact X.presheaf.map_id b
  exact (ConcreteCategory.congr_hom hcomp x).symm

open PresheafOfModules InternalHom Opposite in
/-- **Pointwise naturality square of the forward slice-transport family** (the `toFun` of
`sliceDualTransport`). -/
lemma sliceDualTransport_naturality_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (φ : restr ((Hom.opensFunctor f).obj (unop V)) M.val ⟶
        restr ((Hom.opensFunctor f).obj (unop V))
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))
    {X₁ Y₁ : (Over (unop V))ᵒᵖ} (f₁ : X₁ ⟶ Y₁)
    (z : (M.val.obj (op ((Hom.opensFunctor f).obj (unop X₁).left)) : Type u)) :
    (dualUnitRingSwap f (unop Y₁).left).hom
        ((φ.app (op (Over.mk ((Hom.opensFunctor f).map (unop Y₁).hom)))).hom
          ((M.val.map ((Hom.opensFunctor f).map ((Over.forget (unop V)).map f₁.unop)).op).hom z))
      = (Y.presheaf.map ((Over.forget (unop V)).map f₁.unop).op).hom
          ((dualUnitRingSwap f (unop X₁).left).hom
            ((φ.app (op (Over.mk ((Hom.opensFunctor f).map (unop X₁).hom)))).hom z)) := by
  have hκw : (Hom.opensFunctor f).map f₁.unop.left ≫
      (Over.mk ((Hom.opensFunctor f).map (unop X₁).hom)).hom
      = (Over.mk ((Hom.opensFunctor f).map (unop Y₁).hom)).hom := Subsingleton.elim _ _
  have hnat := PresheafOfModules.naturality_apply φ
    ((Over.homMk ((Hom.opensFunctor f).map f₁.unop.left) hκw :
        Over.mk ((Hom.opensFunctor f).map (unop Y₁).hom) ⟶
          Over.mk ((Hom.opensFunctor f).map (unop X₁).hom)).op) z
  refine (dualUnitRingSwap_apply f (unop Y₁).left _).trans ?_
  refine Eq.trans ?_ (congrArg (Y.presheaf.map ((Over.forget (unop V)).map f₁.unop).op).hom
    (dualUnitRingSwap_apply f (unop X₁).left _).symm)
  refine Eq.trans (congrArg (Scheme.Hom.appIso f (unop Y₁).left).hom.hom hnat) ?_
  exact appIso_hom_naturality_apply f (((Over.forget (unop V)).map f₁.unop).op)
    ((φ.app (op (Over.mk ((Hom.opensFunctor f).map (unop X₁).hom)))).hom z)

open PresheafOfModules InternalHom Opposite in
/-- **Pointwise naturality square of the reverse slice-transport family** (the `app` of
`sliceDualTransportInv`), extracted standalone. -/
lemma sliceDualTransportInv_naturality_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (β : Y.ringCatSheaf.obj ⟶ (Hom.opensFunctor f).op ⋙ X.ringCatSheaf.obj)
    (_hβ : ∀ (P : TopologicalSpace.Opens ↥Y),
        ((β.app (op P)).hom).comp ((Scheme.Hom.appIso f P).hom.hom) = RingHom.id _)
    (ψ : (((PresheafOfModules.pushforward β).obj M.val).dual.obj V : Type u))
    {X₁ Y₁ : (Over ((Hom.opensFunctor f).obj (unop V)))ᵒᵖ} (f₁ : X₁ ⟶ Y₁)
    (z : (M.val.obj (op (unop X₁).left) : Type u))
    (hPVX : f ⁻¹ᵁ (unop X₁).left ≤ unop V)
    (heX : f ''ᵁ (f ⁻¹ᵁ (unop X₁).left) = (unop X₁).left)
    (hPVY : f ⁻¹ᵁ (unop Y₁).left ≤ unop V)
    (heY : f ''ᵁ (f ⁻¹ᵁ (unop Y₁).left) = (unop Y₁).left) :
    (unitRelabelSwap (congrArg op heY.symm)).hom
        ((dualUnitRingSwapHom f (f ⁻¹ᵁ (unop Y₁).left)).hom
          ((ψ.app (op (Over.mk (homOfLE hPVY)))).hom
            ((M.val.map (eqToHom (congrArg op heY.symm))).hom
              (((restr ((Hom.opensFunctor f).obj (unop V)) M.val).map f₁).hom z))))
      = ((restr ((Hom.opensFunctor f).obj (unop V))
            (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).map f₁).hom
          ((unitRelabelSwap (congrArg op heX.symm)).hom
            ((dualUnitRingSwapHom f (f ⁻¹ᵁ (unop X₁).left)).hom
              ((ψ.app (op (Over.mk (homOfLE hPVX)))).hom
                ((M.val.map (eqToHom (congrArg op heX.symm))).hom z)))) := by
  rw [unitRelabelSwap_apply, unitRelabelSwap_apply, dualUnitRingSwapHom_apply,
    dualUnitRingSwapHom_apply]
  have hba : (unop Y₁).left ≤ (unop X₁).left := ((Over.forget _).map f₁.unop).le
  have hPYX : f ⁻¹ᵁ (unop Y₁).left ≤ f ⁻¹ᵁ (unop X₁).left :=
    (TopologicalSpace.Opens.map f.base).monotone hba
  have hψ := PresheafOfModules.naturality_apply ψ
    (Over.homMk (homOfLE hPYX) (Subsingleton.elim _ _) :
      (Over.mk (homOfLE hPVY) : Over (unop V)) ⟶ Over.mk (homOfLE hPVX)).op
    ((M.val.map (eqToHom (congrArg op heX.symm))).hom z)
  have hM : (M.val.map (eqToHom (congrArg op heY.symm))).hom
        (((restr (f ''ᵁ unop V) M.val).map f₁).hom z)
      = (ConcreteCategory.hom
          ((restr (unop V) ((PresheafOfModules.pushforward β).obj M.val)).map
            (Over.homMk (homOfLE hPYX) (Subsingleton.elim _ _) :
              (Over.mk (homOfLE hPVY) : Over (unop V)) ⟶ Over.mk (homOfLE hPVX)).op))
          ((M.val.map (eqToHom (congrArg op heX.symm))).hom z) := by
    rw [show ((restr (f ''ᵁ unop V) M.val).map f₁).hom z
          = (M.val.map ((Over.forget (f ''ᵁ unop V)).map f₁.unop).op).hom z from rfl,
        show (ConcreteCategory.hom
              ((restr (unop V) ((PresheafOfModules.pushforward β).obj M.val)).map
                (Over.homMk (homOfLE hPYX) (Subsingleton.elim _ _) :
                  (Over.mk (homOfLE hPVY) : Over (unop V)) ⟶ Over.mk (homOfLE hPVX)).op))
              ((M.val.map (eqToHom (congrArg op heX.symm))).hom z)
          = (M.val.map ((Hom.opensFunctor f).map
                ((Over.forget (unop V)).map (Over.homMk (homOfLE hPYX) (Subsingleton.elim _ _) :
                  (Over.mk (homOfLE hPVY) : Over (unop V)) ⟶ Over.mk (homOfLE hPVX)))).op).hom
              ((M.val.map (eqToHom (congrArg op heX.symm))).hom z) from rfl]
    have fuse : ∀ {U₁ U₂ U₃ : (TopologicalSpace.Opens ↥X)ᵒᵖ} (p : U₁ ⟶ U₂) (q : U₂ ⟶ U₃)
        (w : (M.val.obj U₁ : Type u)),
        (M.val.map q).hom ((M.val.map p).hom w) = (M.val.map (p ≫ q)).hom w := by
      intro U₁ U₂ U₃ p q w; rw [M.val.map_comp]; rfl
    erw [fuse, fuse]
    congr 1
  rw [hM, hψ]
  have hAI := ConcreteCategory.congr_hom
    (Scheme.Hom.appIso_inv_naturality f (homOfLE hPYX).op)
    ((ConcreteCategory.hom (ψ.app (op (Over.mk (homOfLE hPVX)))))
      ((M.val.map (eqToHom (congrArg op heX.symm))).hom z))
  simp only [ConcreteCategory.comp_apply] at hAI
  erw [hAI]
  have hU : ∀ (w : (X.presheaf.obj (op (unop X₁).left) : Type u)),
      (ModuleCat.Hom.hom ((restr (f ''ᵁ unop V)
            (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))).map f₁)) w
        = (X.presheaf.map ((Over.forget (f ''ᵁ unop V)).map f₁.unop).op).hom w := fun w => rfl
  rw [hU]
  have hring :
      ((Hom.appIso f (f ⁻¹ᵁ (unop X₁).left)).inv ≫
          X.presheaf.map ((Hom.opensFunctor f).op.map (homOfLE hPYX).op)) ≫
        X.presheaf.map (eqToHom (congrArg op heY))
      = (Hom.appIso f (f ⁻¹ᵁ (unop X₁).left)).inv ≫
          X.presheaf.map (eqToHom (congrArg op heX)) ≫
          X.presheaf.map ((Over.forget (f ''ᵁ unop V)).map f₁.unop).op := by
    rw [Category.assoc, ← X.presheaf.map_comp, ← X.presheaf.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hring _

open PresheafOfModules InternalHom Opposite in
/-- **Reverse slice transport (the `invFun` of `sliceDualTransport`), extracted top-level.**

Given a dual section `ψ : restr V ((pushforward β).obj M.val) ⟶ restr V 𝟙_Y` over `Over V`,
this produces the X-slice dual section `restr fV M.val ⟶ restr fV 𝟙_X` over `Over fV`
(`fV = f.opensFunctor.obj V.unop`), the mirror of `sliceDualTransport`'s forward `toFun`.

For `W'' : (Over fV)ᵒᵖ`, set `P := f⁻¹ᵁ W''.left` (so `f.opensFunctor.obj P = W''.left` only
propositionally, via `image_preimage_of_le` since `fV ⊆ range f`).  The component at `W''` is the
X-slice mirror of the forward component, conjugated by the `eqToHom`s from `image_preimage_of_le`
(mirror of `homLocalSection`):
`eqToHom … ≫ (restrictScalars (f.appIso P).hom.hom).map (ψ.app (op (Over.mk (homOfLE hPV)))) ≫
  dualUnitRingSwapHom f P`,
the codomain swap being `dualUnitRingSwapHom = inv (ε (restrictScalars (f.appIso P).hom.hom))`
(the `.hom`-direction `inv ε`). -/
noncomputable def sliceDualTransportInv {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (β : Y.ringCatSheaf.obj ⟶ (Hom.opensFunctor f).op ⋙ X.ringCatSheaf.obj)
    -- This identifies the two successive scalar restrictions in the reverse component.
    (hβ : ∀ (P : TopologicalSpace.Opens ↥Y),
        ((β.app (op P)).hom).comp ((Scheme.Hom.appIso f P).hom.hom) = RingHom.id _)
    (ψ : (((PresheafOfModules.pushforward β).obj M.val).dual.obj V : Type u)) :
    (((PresheafOfModules.pushforward β).obj M.val.dual).obj V : Type u) := by
  refine { app := fun W'' => ?_, naturality := ?_ }
  · -- For `W' ≤ fV`, transport through `P = f⁻¹ᵁ W'` and its image equality.
    set W' := (unop W'').left with hW'
    have hW'fV : W' ≤ f ''ᵁ (unop V) := (unop W'').hom.le
    have hPV : f ⁻¹ᵁ W' ≤ unop V :=
      le_trans ((TopologicalSpace.Opens.map f.base).monotone hW'fV)
        (le_of_eq (f.preimage_image_eq (unop V)))
    have he : f ''ᵁ (f ⁻¹ᵁ W') = W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr (hW'fV.trans (f.image_le_opensRange (unop V)))
    -- First reindex `ψ` and transport the unit through the structure-ring isomorphism.
    have core := (ModuleCat.restrictScalars (Scheme.Hom.appIso f (f ⁻¹ᵁ W')).hom.hom).map
        (ψ.app (op (Over.mk (homOfLE hPV)))) ≫ dualUnitRingSwapHom f (f ⁻¹ᵁ W')
    -- The relabel is semilinear, so map the in-fiber composite through `restrictScalars`.
    refine M.val.map (eqToHom (congrArg op he.symm)) ≫
      (ModuleCat.restrictScalars ((X.ringCatSheaf.obj.map (eqToHom (congrArg op he.symm))).hom)).map
        (?collapse ≫ core) ≫ ?unit
    case collapse =>
      -- Collapse the two scalar restrictions using `hβ`.
      exact (ModuleCat.restrictScalarsId'App _ (hβ (f ⁻¹ᵁ W'))
            (M.val.obj (op (f ''ᵁ f ⁻¹ᵁ W')))).inv ≫
        (ModuleCat.restrictScalarsComp'App ((Scheme.Hom.appIso f (f ⁻¹ᵁ W')).hom.hom)
            ((β.app (op (f ⁻¹ᵁ W'))).hom) _ rfl (M.val.obj (op (f ''ᵁ f ⁻¹ᵁ W')))).hom
    case unit =>
      -- Transport the unit back across the section-ring relabel.
      exact unitRelabelSwap (congrArg op he.symm)
  · -- Naturality is the extracted pointwise square for the same four transports.
    intro X₁ Y₁ f₁
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => ?_
    exact sliceDualTransportInv_naturality_apply f M V β hβ ψ f₁ z
      (le_trans ((TopologicalSpace.Opens.map f.base).monotone (unop X₁).hom.le)
        (le_of_eq (f.preimage_image_eq (unop V))))
      (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
          exact inf_eq_right.mpr ((unop X₁).hom.le.trans (f.image_le_opensRange (unop V))))
      (le_trans ((TopologicalSpace.Opens.map f.base).monotone (unop Y₁).hom.le)
        (le_of_eq (f.preimage_image_eq (unop V))))
      (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
          exact inf_eq_right.mpr ((unop Y₁).hom.le.trans (f.image_le_opensRange (unop V))))

open PresheafOfModules InternalHom Opposite in
/-- **Clean pointwise form of the reverse-transport component.**  The `app` component of
`sliceDualTransportInv` at `W''`, evaluated at `z`, is the four-leg composite of the def reduced by
`rfl`. -/
lemma sliceDualTransportInv_app_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (β : Y.ringCatSheaf.obj ⟶ (Hom.opensFunctor f).op ⋙ X.ringCatSheaf.obj)
    (hβ : ∀ (P : TopologicalSpace.Opens ↥Y),
        ((β.app (op P)).hom).comp ((Scheme.Hom.appIso f P).hom.hom) = RingHom.id _)
    (ψ : (((PresheafOfModules.pushforward β).obj M.val).dual.obj V : Type u))
    (W'' : (Over ((Hom.opensFunctor f).obj (unop V)))ᵒᵖ)
    (hPV : f ⁻¹ᵁ (unop W'').left ≤ unop V)
    (he : f ''ᵁ (f ⁻¹ᵁ (unop W'').left) = (unop W'').left)
    (z : (M.val.obj (op (unop W'').left) : Type u)) :
    (ModuleCat.Hom.hom ((sliceDualTransportInv f M V β hβ ψ).app W'')) z
      = (unitRelabelSwap (congrArg op he.symm)).hom
          ((dualUnitRingSwapHom f (f ⁻¹ᵁ (unop W'').left)).hom
            ((ψ.app (op (Over.mk (homOfLE hPV)))).hom
              ((M.val.map (eqToHom (congrArg op he.symm))).hom z))) := rfl

set_option maxHeartbeats 800000 in
-- Constructing the carrier equivalence and reducing scalar restriction in its naturality field
-- exceed the default heartbeat budget for this declaration.
open PresheafOfModules InternalHom Opposite in
/-- **Leg (A)∘(B): the sectionwise slice transport of the dual along an open immersion.**

For an open immersion `f : Y ⟶ X`, `M : X.Modules`, and an open `V` of `Y` (as `(Opens Y)ᵒᵖ`),
this is the `𝒪_Y(V)`-linear isomorphism between the two sectionwise values of the Step-4 residual
of `dual_restrict_iso`:
```
  ((pushforward β).obj (dual M.val)).obj V  ≅  (dual ((pushforward β).obj M.val)).obj V
```
where `β` is the open-immersion structure ring morphism `Y.ringCatSheaf ⟶ f.opensFunctor.op ⋙
X.ringCatSheaf` (`β.app U = (forget₂ _ _).map (f.appIso U).inv`).

The construction mirrors `homLocalSection` (the thin-poset `eqToHom`-conjugation slice transport)
composed with `restrictScalarsRingIsoDualEquiv` (the `𝒪_Y(V)`-linear codomain-unit ring swap of leg
(B)): a dual section `φ : restr fV M.val ⟶ restr fV 𝟙_X` over `Over (fV)` is reindexed across
`f.opensFunctor` to a dual section over `Over V`, conjugating each component by the structure ring
iso `f.appIso`; naturality on the thin poset `Opens Y` is `Subsingleton.elim`. -/
noncomputable def sliceDualTransport {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ) :
    letI α : Y.presheaf ⟶ (Hom.opensFunctor f).op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    letI β : Y.ringCatSheaf.obj ⟶ (Hom.opensFunctor f).op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    (((PresheafOfModules.pushforward β).obj (PresheafOfModules.dual M.val)).obj V) ≅
      ((PresheafOfModules.dual ((PresheafOfModules.pushforward β).obj M.val)).obj V) := by
  -- Pin the two module structures before constructing the sectionwise linear equivalence.
  set β : Y.ringCatSheaf.obj ⟶ (Hom.opensFunctor f).op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight
      ({ app := fun U ↦ (Hom.appIso f (Opposite.unop U)).inv
         naturality := fun _ _ i => f.appIso_inv_naturality i } :
        Y.presheaf ⟶ (Hom.opensFunctor f).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat) with hβ
  letI lhsMod : Module (Y.ringCatSheaf.obj.obj V : Type u)
      (((PresheafOfModules.pushforward β).obj (PresheafOfModules.dual M.val)).obj V : Type u) :=
    inferInstance
  letI rhsMod : Module (Y.ringCatSheaf.obj.obj V : Type u)
      ((PresheafOfModules.dual ((PresheafOfModules.pushforward β).obj M.val)).obj V : Type u) :=
    InternalHom.internalHomObjModule (R := Y.presheaf) V.unop
      ((PresheafOfModules.pushforward β).obj M.val) (𝟙_ _)
  refine LinearEquiv.toModuleIso (m₁ := lhsMod) (m₂ := rhsMod) ?_
  refine
    { toFun := fun φ =>
        { app := fun W =>
            -- Reindex the source component across the opens functor.
            (ModuleCat.restrictScalars (β.app (Opposite.op W.unop.left)).hom).map
                (φ.app (Opposite.op (Over.mk (Hom.opensFunctor f |>.map W.unop.hom)))) ≫
              -- Transport the unit through the structure-ring isomorphism.
              dualUnitRingSwap f W.unop.left
          naturality := ?_ }
      invFun := ?_
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · -- Use the extracted pointwise naturality square.
    intro X₁ Y₁ f₁
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => ?_
    exact sliceDualTransport_naturality_apply f M V φ f₁ z
  · -- Additivity follows from the additive scalar-restriction functor.
    intro x y
    apply PresheafOfModules.hom_ext
    intro W
    change (ModuleCat.restrictScalars _).map ((x + y).app _) ≫ _ = _
    rw [show (x + y).app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom)))
          = x.app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom)))
            + y.app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom))) from rfl,
        Functor.map_add, Preadditive.add_comp]
    rfl
  -- Scalar compatibility follows from naturality of `f.appIso.inv` and linearity of the unit swap.
  · intro m x
    apply PresheafOfModules.hom_ext
    intro W
    change (ModuleCat.restrictScalars _).map ((m • x).app _) ≫ _
        = _ ≫ (globalSMul Over.mkIdTerminal
            (restr (unop V)
              (𝟙_ (_root_.PresheafOfModules
                (Y.presheaf ⋙ forget₂ CommRingCat RingCat))))
            ((RingHom.id _) m)).app W
    erw [PresheafOfModules.comp_app]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, globalSMul_hom_apply,
      ModuleCat.restrictScalars.map_apply]
    -- Abbreviations: `W' = (unop W).left`, `A = op (Over.mk (opensFunctor.map W.hom))`,
    -- `u = (x.app A).hom z`, `d = dualUnitRingSwap f W'`.  After the `simp only` the goal is
    --   `d.hom (s • u) = c • (g ≫ d).hom z`
    -- with `s = (termRingMap A) ((β.app V) m)`, `c = (termRingMap W) m`,
    -- `g = (restrictScalars (β.app (op W')).hom).map (x.app A)`.
    -- Step 1. Reduce the RHS value `(g ≫ d).hom z` to `d.hom u` (defeq; `conv`+`change` see
    -- through the `ModuleCat`/`restrictScalars` instance projections that block `rw`).
    conv_rhs =>
      arg 2
      change (ModuleCat.Hom.hom (dualUnitRingSwap f (unop W).left))
        ((ModuleCat.Hom.hom
          (x.app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom))))) z)
    -- Step 2. `d.hom` is `𝒪_Y(W')`-linear: `d.hom (s • u) = d.hom (c •[restr] u) = c • d.hom u`,
    -- reducing to the scalar identity `s • u = c •[restr] u` (term-mode to tolerate the
    -- defeq-not-syntactic ring carrier of the codomain scalar `c`).
    refine (congrArg (ModuleCat.Hom.hom (dualUnitRingSwap f (unop W).left))
      (?_ : _ = _)).trans ((dualUnitRingSwap f (unop W).left).hom.map_smul _ _)
    -- Step 3. The scalar identity `s • u = c •[restr] u` reduces (`congr 1`) to the pure ring
    -- identity `(termRingMap A) (β.app V m) = (f.appIso W').inv ((termRingMap W) m)` — the
    -- naturality of `f.appIso.inv` against restriction along `f.opensFunctor`.
    congr 1
    simp only [termRingMap, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
      Over.forget_map, Over.mkIdTerminal_from_left, RingHom.id_apply]
    exact (ConcreteCategory.congr_hom
      (Scheme.Hom.appIso_inv_naturality f (((unop W).hom).op)) m).symm
  -- The inverse is the reverse sectionwise transport defined above.
  · refine fun ψ => sliceDualTransportInv f M V β ?_ ψ
    -- Discharge the β-compatibility hypothesis for the specific `β = whiskerRight (f.appIso).inv`:
    -- `(β.app (op P)).hom = (f.appIso P).inv.hom`, so the composite with `(f.appIso P).hom` is the
    -- identity by `Iso.hom_inv_id` of the structure ring iso.
    intro P
    rw [hβ]
    have h := congrArg CommRingCat.Hom.hom (Scheme.Hom.appIso f P).hom_inv_id
    simp only [Functor.whiskerRight_app, CommRingCat.hom_comp, CommRingCat.hom_id] at h ⊢
    exact h
  -- The left inverse reduces componentwise to the two unit swaps and a down-set relabel.
  · intro φ
    apply PresheafOfModules.hom_ext
    intro W''
    -- Expose the pointwise transport and use naturality across the image-preimage equality.
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => ?_
    have hPV : f ⁻¹ᵁ (unop W'').left ≤ unop V :=
      le_trans ((TopologicalSpace.Opens.map f.base).monotone (unop W'').hom.le)
        (le_of_eq (f.preimage_image_eq (unop V)))
    have he : f ''ᵁ (f ⁻¹ᵁ (unop W'').left) = (unop W'').left := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr ((unop W'').hom.le.trans (f.image_le_opensRange (unop V)))
    rw [sliceDualTransportInv_app_apply f M V β _ _ W'' hPV he z]
    simp only [CategoryTheory.ConcreteCategory.comp_apply, dualUnitRingSwapHom_apply,
      unitRelabelSwap_apply]
    erw [dualUnitRingSwap_apply, CategoryTheory.Iso.hom_inv_id_apply]
    have hφ := PresheafOfModules.naturality_apply φ
      (Over.homMk (eqToHom he) (Subsingleton.elim _ _) :
        (Over.mk ((Hom.opensFunctor f).map (homOfLE hPV)) : Over (f ''ᵁ unop V)) ⟶ unop W'').op z
    rw [show ((restr (unop ((Hom.opensFunctor f).op.obj V)) M.val).map
          (Over.homMk (eqToHom he) (Subsingleton.elim _ _) :
            (Over.mk ((Hom.opensFunctor f).map (homOfLE hPV)) : Over (f ''ᵁ unop V)) ⟶
              unop W'').op).hom z
        = (M.val.map (eqToHom he).op).hom z from rfl, eqToHom_op] at hφ
    erw [hφ]
    change (X.presheaf.map (eqToHom (congrArg op he))).hom
        ((X.presheaf.map (eqToHom he).op).hom ((φ.app W'').hom z))
      = (φ.app W'').hom z
    rw [eqToHom_op]
    have hmaps : X.presheaf.map (eqToHom (congr_arg op he.symm)) ≫
        X.presheaf.map (eqToHom (congrArg op he)) = 𝟙 _ := by
      rw [← X.presheaf.map_comp, eqToHom_trans]
      exact X.presheaf.map_id _
    exact ConcreteCategory.congr_hom hmaps ((φ.app W'').hom z)
  -- The right inverse is the same cancellation in the opposite direction.
  · intro ψ
    apply PresheafOfModules.hom_ext
    intro W
    -- Reduce to elements, collapse the structure-ring transports, and apply `ψ.naturality`.
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun z => ?_
    -- β-compatibility, re-derived inline (matches the discharge in `invFun`, proof-irrelevant).
    have hβc : ∀ (P : TopologicalSpace.Opens ↥Y),
        ((β.app (op P)).hom).comp ((Scheme.Hom.appIso f P).hom.hom) = RingHom.id _ := by
      intro P
      rw [hβ]
      have h := congrArg CommRingCat.Hom.hom (Scheme.Hom.appIso f P).hom_inv_id
      simp only [Functor.whiskerRight_app, CommRingCat.hom_comp, CommRingCat.hom_id] at h ⊢
      exact h
    set W'' : (Over ((Hom.opensFunctor f).obj (unop V)))ᵒᵖ :=
      op (Over.mk ((Hom.opensFunctor f).map (unop W).hom)) with hW''
    have hPV : f ⁻¹ᵁ (unop W'').left ≤ unop V :=
      le_trans ((TopologicalSpace.Opens.map f.base).monotone (unop W'').hom.le)
        (le_of_eq (f.preimage_image_eq (unop V)))
    have he : f ''ᵁ (f ⁻¹ᵁ (unop W'').left) = (unop W'').left := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr ((unop W'').hom.le.trans (f.image_le_opensRange (unop V)))
    change (dualUnitRingSwap f (unop W).left).hom
        ((ModuleCat.Hom.hom ((sliceDualTransportInv f M V β hβc ψ).app W'')) z)
      = (ModuleCat.Hom.hom (ψ.app W)) z
    rw [sliceDualTransportInv_app_apply f M V β hβc ψ W'' hPV he z]
    simp only [dualUnitRingSwapHom_apply, unitRelabelSwap_apply]
    erw [dualUnitRingSwap_apply]
    -- Step (1): collapse the three structure-ring legs into a single `Y.presheaf` relabel.
    have hPA : f ⁻¹ᵁ (unop W'').left = (unop W).left := f.preimage_image_eq (unop W).left
    have hcomp :
        (Scheme.Hom.appIso f (f ⁻¹ᵁ (unop W'').left)).inv ≫
            X.presheaf.map (eqToHom (congrArg op he)) ≫ (Scheme.Hom.appIso f (unop W).left).hom
          = Y.presheaf.map (eqToHom (congrArg op hPA)) := by
      have hnat := Scheme.Hom.appIso_inv_naturality f
        (eqToHom (congrArg op hPA) :
          (op (f ⁻¹ᵁ (unop W'').left) : (TopologicalSpace.Opens ↥Y)ᵒᵖ) ⟶ op (unop W).left)
      rw [eqToHom_map (Hom.opensFunctor f).op (congrArg op hPA)] at hnat
      rw [← Category.assoc,
        show (Scheme.Hom.appIso f (f ⁻¹ᵁ (unop W'').left)).inv ≫
              X.presheaf.map (eqToHom (congrArg op he))
            = Y.presheaf.map (eqToHom (congrArg op hPA)) ≫
                (Scheme.Hom.appIso f (unop W).left).inv from hnat.symm]
      exact (Category.assoc _ _ _).trans
        ((congrArg (Y.presheaf.map (eqToHom (congrArg op hPA)) ≫ ·)
            (Scheme.Hom.appIso f (unop W).left).inv_hom_id).trans (Category.comp_id _))
    have step1 := ConcreteCategory.congr_hom hcomp
      ((ψ.app (op (Over.mk (homOfLE hPV)))).hom
        ((M.val.map (eqToHom (congrArg op he.symm))).hom z))
    simp only [ConcreteCategory.comp_apply] at step1
    erw [step1]
    -- Step (2): ψ-naturality at the slice morphism `Over.mk (homOfLE hPV) ⟶ unop W`.
    have hψ := PresheafOfModules.naturality_apply ψ
      (Over.homMk (eqToHom hPA) (Subsingleton.elim _ _) :
        (Over.mk (homOfLE hPV) : Over (unop V)) ⟶ unop W).op z
    rw [show ((restr (unop V) ((PresheafOfModules.pushforward β).obj M.val)).map
          (Over.homMk (eqToHom hPA) (Subsingleton.elim _ _) :
            (Over.mk (homOfLE hPV) : Over (unop V)) ⟶ unop W).op).hom z
        = (M.val.map (eqToHom (congrArg op he.symm))).hom z from rfl] at hψ
    erw [hψ]
    -- Step (3): the two `Y.presheaf` relabels collapse to `𝟙` over the thin poset.
    change (Y.presheaf.map (eqToHom (congrArg op hPA))).hom
        ((Y.presheaf.map (eqToHom hPA).op).hom ((ψ.app W).hom z))
      = (ψ.app W).hom z
    rw [eqToHom_op]
    have hmaps : Y.presheaf.map (eqToHom (congrArg op hPA.symm)) ≫
        Y.presheaf.map (eqToHom (congrArg op hPA)) = 𝟙 _ := by
      rw [← Y.presheaf.map_comp, eqToHom_trans]
      exact Y.presheaf.map_id _
    exact ConcreteCategory.congr_hom hmaps ((ψ.app W).hom z)

/-- **Restriction along an open immersion commutes with the sheaf-level dual (C-bridge).**

The proof first rewrites restriction as pullback and moves pullback through sheafification. It then
identifies the resulting presheaves sectionwise using `sliceDualTransport`; naturality follows
from the thin-poset structure of opens. This is blueprint `lem:dual_restrict_iso`. -/
noncomputable def dual_restrict_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) :
    (dual M).restrict f ≅ dual (M.restrict f) := by
  -- Step 1. Reduce `restrict` to `pullback` along the open immersion `f`.
  refine (Scheme.Modules.restrictFunctorIsoPullback f).app (dual M) ≪≫ ?_
  -- Step 2. Sheafification commutes with pullback.
  refine (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app
      (PresheafOfModules.dual (R₀ := X.presheaf) M.val) ≪≫ ?_
  -- Step 3. Strip the outer sheafification, descending to the presheaf residual.
  refine (PresheafOfModules.sheafification (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.obj)).mapIso ?_
  -- Reduce to the presheaf-level comparison.
  --   `(pullback φ).obj (dual M.val) ≅ dual ((M.restrict f).val)`.
  -- H1: replace `pullback φ` with `pushforward β` (β the open-immersion structure ring iso).
  let φR := (Scheme.Hom.toRingCatSheafHom f).hom
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv, naturality := fun _ _ i => f.appIso_inv_naturality i }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  let H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  refine (H1.app (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).symm ≪≫ ?_
  -- Residual: `(pushforward β).obj (dual M.val) ≅ dual ((pushforward β).obj M.val)`.
  -- Assemble sectionwise from `sliceDualTransport`.  The `isoMk` naturality square is the
  -- thin-poset `Opens Y` coherence of the `sliceDualTransport` family: the connecting Hom-space in
  -- the thin poset `Opens Y` is a subsingleton, so the square commutes definitionally.
  refine PresheafOfModules.isoMk (fun V => sliceDualTransport f M V) ?_
  intro V W g
  subsingleton

/-! ## §B. Local triviality of the dual -/

/-- **Presheaf-level: the dual of the monoidal unit is the unit.**
`PresheafOfModules.dual 𝟙_ = ℋom(𝟙_, 𝟙_) ≅ 𝟙_`, the evaluation-at-`1` isomorphism.
Local supplement (the `PresheafOfModules`-level ingredient of `dual_unit_iso`). -/
noncomputable def presheafDualUnitIso {Y : Scheme.{u}} :
    PresheafOfModules.dual (R₀ := Y.presheaf)
        (𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≅ 𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.dualUnitIsoGen (R₀ := Y.presheaf)

/-- **The dual of the structure sheaf is the structure sheaf.** `dual 𝒪_Y ≅ 𝒪_Y`.
The presheaf-level dual of the monoidal unit `𝟙_` is the unit (evaluation at `1`),
sheafified and identified with the (already-sheaf) unit by the sheafification counit.
Mirrors `tensorObj_unit_iso` with the presheaf left unitor replaced by
`presheafDualUnitIso`. The third leg of the `dual_isLocallyTrivial` chain. -/
noncomputable def dual_unit_iso {Y : Scheme.{u}} :
    dual (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).mapIso
      (presheafDualUnitIso (Y := Y)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit Y.ringCatSheaf)

/-- **The dual of a locally-trivial `𝒪_X`-module is locally trivial.**

On each affine chart trivializing `L`, compose `dual_restrict_iso`, the contravariant image of the
local trivialization, and `dual_unit_iso`. This is blueprint `lem:dual_isLocallyTrivial`. -/
lemma dual_isLocallyTrivial {X : Scheme.{u}} {L : X.Modules}
    (hL : LineBundle.IsLocallyTrivial L) :
    LineBundle.IsLocallyTrivial (dual L) := by
  -- Mirrors `tensorObj_isLocallyTrivial`: trivialise the dual on each affine open `U`
  -- where `L` is trivial, via the three-step chain
  --   `(dual L)|_U ≅ dual (L|_U) ≅ dual 𝒪_U ≅ 𝒪_U`.
  intro x
  obtain ⟨U, hxU, hU_aff, ⟨eL⟩⟩ := hL x
  refine ⟨U, hxU, hU_aff, ⟨?_⟩⟩
  exact dual_restrict_iso U.ι L ≪≫ (dualIsoOfIso eL).symm ≪≫ dual_unit_iso

/-! ## §C. The A-bridge: compatible local morphisms glue to a global morphism -/

open Opposite TopologicalSpace in
/-- **The local section of the hom-sheaf manufactured from `f i`** (the load-bearing piece
of `homOfLocalCompat`, blueprint `localSection`).  Working with the underlying `Ab`-presheaves
`F = M.val.presheaf`, `G = N.val.presheaf`, the presheaf of types
`presheafHom F G` (`Mathlib.CategoryTheory.Sites.SheafHom`) sends an open `W` to the morphisms of
the restrictions of `F`, `G` to the slice `Over W`.  Its value at `U i` is built from the
components of `f i`, conjugated by `eqToHom` along the down-set identity
`(U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V) = V` (valid for `V ≤ U i`).  The naturality field — the genuine
coherence risk — is automatic on the thin poset `Opens X` once the `eqToHom`-conjugation is
peeled, via `Subsingleton.elim` on the hom-sets. -/
noncomputable def homLocalSection {X : Scheme.{u}} {M N : X.Modules} {ι : Type*}
    (U : ι → X.Opens) (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι) (i : ι) :
    (CategoryTheory.presheafHom M.val.presheaf N.val.presheaf).obj (op (U i)) where
  app W :=
    haveI hle : W.unop.left ≤ U i := W.unop.hom.le
    haveI himg : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W.unop.left) = W.unop.left := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hle
    M.val.presheaf.map (eqToHom (congrArg op himg.symm)) ≫
      ((PresheafOfModules.toPresheaf _).map (f i).val).app (op ((U i).ι ⁻¹ᵁ W.unop.left)) ≫
      N.val.presheaf.map (eqToHom (congrArg op himg))
  naturality := by
    intro A B φ
    have hBA : (unop B).left ≤ (unop A).left := ((Over.forget (U i)).map φ.unop).le
    let κ : (U i).ι ⁻¹ᵁ (unop B).left ⟶ (U i).ι ⁻¹ᵁ (unop A).left :=
      (Opens.map (U i).ι.base).map (homOfLE hBA)
    have himgA : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ (unop A).left) = (unop A).left := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (unop A).hom.le
    have himgB : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ (unop B).left) = (unop B).left := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (unop B).hom.le
    -- naturality of the underlying ab-presheaf morphism of `f i`
    have hm := ((PresheafOfModules.toPresheaf _).map (f i).val).naturality κ.op
    -- the two thin-poset square edges agree (`Opens X` is a thin poset)
    have hsubM : ((Over.forget (U i)).op.map φ) ≫ eqToHom (congrArg op himgB.symm)
        = eqToHom (congrArg op himgA.symm) ≫ ((U i).ι.opensFunctor.map κ).op :=
      Subsingleton.elim _ _
    have hsubN : ((U i).ι.opensFunctor.map κ).op ≫ eqToHom (congrArg op himgB)
        = eqToHom (congrArg op himgA) ≫ ((Over.forget (U i)).op.map φ) :=
      Subsingleton.elim _ _
    -- M-side: the φ-restriction followed by the `eqToHom` is the `eqToHom` followed by `κ`
    have hML : M.val.presheaf.map ((Over.forget (U i)).op.map φ) ≫
          M.val.presheaf.map (eqToHom (congrArg op himgB.symm))
        = M.val.presheaf.map (eqToHom (congrArg op himgA.symm)) ≫
          (M.restrict (U i).ι).val.presheaf.map κ.op := by
      rw [(M.val.presheaf.map_comp _ _).symm, hsubM]
      exact M.val.presheaf.map_comp _ _
    -- N-side analogue
    have hNR : N.val.presheaf.map ((U i).ι.opensFunctor.map κ).op ≫
          N.val.presheaf.map (eqToHom (congrArg op himgB))
        = N.val.presheaf.map (eqToHom (congrArg op himgA)) ≫
          N.val.presheaf.map ((Over.forget (U i)).op.map φ) := by
      rw [(N.val.presheaf.map_comp _ _).symm, hsubN]
      exact N.val.presheaf.map_comp _ _
    dsimp only [Functor.comp_map, Functor.op_map, Functor.op_obj, Functor.comp_obj]
    -- `erw` accepts the definitional equality between the two spellings of the op-map.
    erw [reassoc_of% hML]
    erw [Category.assoc, reassoc_of% hm, hNR]
    simp only [Category.assoc]
    rfl

open Opposite TopologicalSpace in
/-- **Convert a section of `presheafHom F G` over the terminal open `⊤` into a global
morphism `F ⟶ G`.**  Since `⊤` is terminal in `Opens X`, the value of `presheafHom F G`
at `op ⊤` already determines a full compatible family of sections (each open's value is the
restriction of the top section), which `presheafHomSectionsEquiv` identifies with a morphism
`F ⟶ G`.  This is sub-step (b) of `homOfLocalCompat`. -/
noncomputable def topSectionToHom {X : TopCat.{u}}
    {F G : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u}}
    (s : (CategoryTheory.presheafHom F G).obj (op ⊤)) : F ⟶ G :=
  CategoryTheory.presheafHomSectionsEquiv F G
    ⟨fun W => (CategoryTheory.presheafHom F G).map (homOfLE le_top).op s, by
      intro W W' e
      dsimp only
      rw [← Functor.map_comp_apply]
      congr 1⟩

open Opposite TopologicalSpace in
/-- **Sectionwise value of `topSectionToHom`.**  At an open `W`, the recovered morphism
evaluates to the `Over.mk (homOfLE le_top)`-component of the top section `s`. -/
lemma topSectionToHom_app {X : TopCat.{u}}
    {F G : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u}}
    (s : (CategoryTheory.presheafHom F G).obj (op ⊤)) (W : (TopologicalSpace.Opens X)ᵒᵖ) :
    (topSectionToHom s).app W = s.app (op (Over.mk (homOfLE (le_top) : W.unop ⟶ ⊤))) := by
  obtain ⟨W⟩ := W
  exact CategoryTheory.presheafHom_map_app_op_mk_id (homOfLE le_top) s

open Opposite TopologicalSpace in
/-- **Down-set image identity.**  For `V ≤ W` (opens of a scheme `X`), the image under the
open immersion `W.ι` of the preimage of `V` is `V` again: `W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V`.  This is
the equality powering the `eqToHom`-conjugations in `homLocalSection`. -/
lemma image_preimage_of_le {X : Scheme.{u}} (W : X.Opens) {V : X.Opens} (hV : V ≤ W) :
    W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hV

set_option backward.isDefEq.respectTransparency false in
open Opposite TopologicalSpace in
/-- **A-bridge: compatible local `𝒪_X`-module morphisms glue to a global morphism.**

The hypothesis compares the local maps sectionwise on every overlap after conjugating by the
canonical image-preimage equalities. The proof glues the corresponding sections of the hom-sheaf,
then promotes the resulting morphism to an `𝒪_X`-linear map using local linearity and separatedness.
This is blueprint `lem:sheafofmodules_hom_of_local_compat`. -/
noncomputable def homOfLocalCompat {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
        M.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U i) hVi).symm)) ≫
          ((PresheafOfModules.toPresheaf _).map (f i).val).app (op ((U i).ι ⁻¹ᵁ V)) ≫
            N.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U i) hVi)))
          = M.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U j) hVj).symm)) ≫
              ((PresheafOfModules.toPresheaf _).map (f j).val).app (op ((U j).ι ⁻¹ᵁ V)) ≫
                N.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U j) hVj)))) :
    M ⟶ N := by
  -- Step (i): glue the underlying ab-sheaf morphism.  The morphisms-presheaf
  -- `presheafHom M.val.presheaf N.val.presheaf` (`Mathlib.CategoryTheory.Sites.SheafHom`) is a
  -- sheaf of types because `N` is a sheaf (`Presheaf.IsSheaf.hom`, consuming `N.isSheaf`).
  let H : TopCat.Sheaf (Type u) (X : TopCat) :=
    ⟨CategoryTheory.presheafHom M.val.presheaf N.val.presheaf,
      Presheaf.IsSheaf.hom M.val.presheaf N.val.presheaf N.isSheaf⟩
  -- The cover `{U i}` exhausts `X`, so `iSup U = ⊤`.
  have hsup : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  -- The compatible family `homLocalSection U f` (its naturality is the load-bearing field,
  -- proved axiom-clean above) glues via `existsUnique_gluing` to a unique global section of `H`
  -- over `iSup U = ⊤`.  `hglue` records the unique-gluing engine fed with these local sections;
  -- it still requires the `IsCompatible` datum, which is exactly the assumed overlap agreement
  -- `hf` after the image-preimage conjugations.
  have hglue := H.existsUnique_gluing U (fun i => homLocalSection U f i)
  -- (a) The cocycle / `IsCompatible` condition: the two restrictions of `homLocalSection i`
  -- and `homLocalSection j` to the overlap `U i ⊓ U j` agree as sections of `H`.
  have hcompat : TopCat.Presheaf.IsCompatible
      (CategoryTheory.presheafHom M.val.presheaf N.val.presheaf) U
      (fun i => homLocalSection U f i) := by
    intro i j
    refine NatTrans.ext (funext fun Z => ?_)
    obtain ⟨W⟩ := Z
    erw [presheafHom_map_app W.hom (TopologicalSpace.Opens.infLELeft (U i) (U j)) _ rfl,
        presheafHom_map_app W.hom (TopologicalSpace.Opens.infLERight (U i) (U j)) _ rfl]
    -- Unfold `homLocalSection` so the goal becomes the explicit sectionwise core equation:
    -- at the overlap open `V := W.left ≤ U i ⊓ U j`,
    --   LHS = `M.map (eqToHom ..) ≫ (f i).val.app (op ((U i).ι ⁻¹ᵁ V)) ≫ N.map (eqToHom ..)`
    --   RHS = `M.map (eqToHom ..) ≫ (f j).val.app (op ((U j).ι ⁻¹ᵁ V)) ≫ N.map (eqToHom ..)`,
    -- both in the FIXED `Ab` hom-type `M.val(V) ⟶ N.val(V)`.  With the sectionwise `hf` this is
    -- exactly `hf i j W.left _ _` (the `eqToHom`-conjugations match by definitional proof
    -- irrelevance; `(Over.mk (W.hom ≫ infLE_))​.left ≡ W.left` defeq).
    simp only [homLocalSection]
    exact hf i j W.left (W.hom.le.trans inf_le_left) (W.hom.le.trans inf_le_right)
  -- (b) Glue and convert the amalgamated `op ⊤`-section to an ab-presheaf morphism `g`.
  -- `∃!` is a `Prop`, so the glued section is extracted as a term via `.choose`; `hsup`
  -- transports it from `op (iSup U)` to the terminal `op ⊤` that `topSectionToHom` consumes.
  refine homMk (topSectionToHom (hsup ▸ (hglue hcompat).choose)) ?_
  -- (c) sectionwise `𝒪_X`-linearity of `g = topSectionToHom (glued section)`.  On each `U i`
  -- the glued section restricts to `homLocalSection U f i` (the `IsGluing` datum `_hs`), whose
  -- components come from the module morphism `f i`, so `g` is `𝒪_X`-linear on opens `≤ U i`;
  -- since `{U i}` covers `X` and `N.val.presheaf` is separated (`section_ext`), linearity
  -- propagates to every section. The proof below connects the glued section to each local map and
  -- bridges its native scalar action with restriction of scalars along the identity.
  have _hs := (hglue hcompat).choose_spec.1
  intro V r m
  -- Abbreviate the glued ab-presheaf morphism `g`.
  set g : M.val.presheaf ⟶ N.val.presheaf :=
    topSectionToHom (hsup ▸ (hglue hcompat).choose) with hg
  -- **Connection lemma.**  On every open `W' ≤ U i`, the glued morphism `g` agrees with the
  -- local section `homLocalSection U f i` manufactured from `f i` — this is the content of the
  -- `IsGluing` datum `_hs`, transported through the `iSup U = ⊤` identification and the
  -- `presheafHom`-restriction calculus.
  have hconn : ∀ (i : ι) (W' : X.Opens) (hWi : W' ≤ U i),
      g.app (op W') = (homLocalSection U f i).app (op (Over.mk (homOfLE hWi))) := by
    intro i W' hWi
    have htr : ∀ {a : X.Opens} (h : a = ⊤) (y : H.obj.obj (op a)),
        (h ▸ y : H.obj.obj (op ⊤)) = H.obj.map (eqToHom (congrArg op h)) y := by
      intro a h y; subst h; simp
    rw [hg, topSectionToHom_app, htr hsup]
    have hop : eqToHom (congrArg op hsup) = (eqToHom hsup.symm).op := Subsingleton.elim _ _
    have hgl : TopCat.Presheaf.IsGluing H.obj U (fun i => homLocalSection U f i)
        (hglue hcompat).choose := _hs
    have hsi : (ConcreteCategory.hom (H.obj.map (Opens.leSupr U i).op)) (hglue hcompat).choose
        = homLocalSection U f i := hgl i
    rw [hop, presheafHom_map_app (homOfLE le_top) (eqToHom hsup.symm)
        (homOfLE le_top ≫ eqToHom hsup.symm) rfl, ← hsi,
      presheafHom_map_app (homOfLE hWi) (Opens.leSupr U i)
        (homOfLE hWi ≫ Opens.leSupr U i) rfl]
    rw [show (homOfLE le_top ≫ eqToHom hsup.symm : W' ⟶ iSup U)
        = (homOfLE hWi ≫ Opens.leSupr U i) from Subsingleton.elim _ _]
  -- It suffices, by separatedness of the sheaf `N`, to check the linearity equation on a
  -- neighbourhood of each point; we use the cover member `U i` through the point.
  refine N.isSheaf.section_ext ?_
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  refine ⟨V.unop ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  -- Reduce both sides via naturality of `g` (so the outer `N`-restriction is absorbed into
  -- `g.app (op W)`) and the semilinearity of the `M`, `N` restriction maps (`map_smul`) to
  -- local linearity of `g` at `W := V.unop ⊓ U i ≤ U i`.
  set W : X.Opens := V.unop ⊓ U i with hWdef
  have hWV : W ≤ V.unop := inf_le_left
  erw [← NatTrans.naturality_apply g (homOfLE hWV).op (r • m),
      PresheafOfModules.map_smul M.val (homOfLE hWV).op r m,
      PresheafOfModules.map_smul N.val (homOfLE hWV).op r ((g.app V).hom m),
      ← NatTrans.naturality_apply g (homOfLE hWV).op m]
  -- `g` agrees on `W ≤ U i` with the local section manufactured from the module morphism `f i`;
  -- it remains to prove the `homLocalSection`-component is `X.ringCatSheaf(W)`-linear.
  rw [hconn i W inf_le_right]
  -- The component is a triple composite through `(f i).val.app P`, where
  -- `P = (U i).ι ⁻¹ᵁ W`. Decompose it into the three legs.
  simp only [homLocalSection]
  -- The `homLocalSection`-component at `W` is the triple composite
  --   `Φ = M.val.map (eqToHom e₁) ≫ (f i).val.app P ≫ N.val.map (eqToHom e₂)`,
  -- an `Ab`-morphism `M(W) ⟶ N(W)`.  We must show `Φ (r' • m') = r' • Φ m'` for the structure
  -- scalar `r' = X.ringCatSheaf.map (homOfLE hWV).op r`. Expose the three legs.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
       ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
       PresheafOfModules.toPresheaf_map_app_apply,
       PresheafOfModules.toPresheaf_map_app_apply]
  -- Push the scalar through the three legs.  We use the *Γ-level* `Scheme.Modules.map_smul`
  -- (which keeps the native `Γ(M, ·)`-module structure) rather than `PresheafOfModules.map_smul`
  -- (whose semilinear codomain introduces a `restrictScalars`-along-`eqToHom` module that does not
  -- match the `f`-leg's `restrictScalars 𝟙` action — `(U i).ι.appIso = Iso.refl`).
  -- (a) Push the scalar through the `M` restriction map.
  erw [Scheme.Modules.map_smul M]
  -- (b) `f`-leg `(U i)`-linearity is available as the term `hfl`: `(f i).val.app P` is
  -- `(U i).ringCatSheaf(P)`-linear.  Since `(U i).ι.appIso = Iso.refl`
  -- (`AlgebraicGeometry.Scheme.Opens.ι_appIso`), `(U i).ringCatSheaf(P) = Γ(X, image)` and the
  -- `(U i)`-action on `M.restrict (U i).ι` is `ModuleCat.restrictScalars 𝟙` of the native action.
  have hfl := ((f i).val.app (op ((U i).ι ⁻¹ᵁ
    (Over.mk (homOfLE (inf_le_right : W ≤ U i))).left))).hom.map_smul
  -- **Native↔`restrictScalars 𝟙` smul bridge** for any `K : X.Modules`.  The `(U i)`-action
  -- on `K.restrict (U i).ι` is `ModuleCat.restrictScalars` of the native `Γ(X, image)`-action
  -- along the structure-ring map `(forget₂ …).map ((U i).ι.appIso _).inv`, which is the identity
  -- because `(U i).ι.appIso = Iso.refl` (`AlgebraicGeometry.Scheme.Opens.ι_appIso`).
  have hbridge : ∀ (K : X.Modules) (c : Γ(X, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))
      (y : Γ(K, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W)),
      (c • y : Γ(K, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))
        = (c • (show ↑((K.restrict (U i).ι).val.obj (op ((U i).ι ⁻¹ᵁ W))) from y)) := by
    intro K c y
    erw [ModuleCat.restrictScalars.smul_def']
    simp [AlgebraicGeometry.Scheme.Opens.ι_appIso]
    rfl
  -- **Native `Γ(X, image)`-linearity of the `f`-leg**, bridged from `hfl` via `hbridge`.
  have hfl_native : ∀ (c : Γ(X, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))
      (y : Γ(M, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W)),
      (ConcreteCategory.hom ((f i).val.app (op ((U i).ι ⁻¹ᵁ W)))) (c • y)
        = c • (ConcreteCategory.hom ((f i).val.app (op ((U i).ι ⁻¹ᵁ W)))) y := by
    intro c y
    rw [hbridge M c y]
    erw [hfl]
    rfl
  -- (c) `N`-leg semilinearity (native), pulling the structure scalar back out.
  erw [hfl_native, Scheme.Modules.map_smul N]
  -- (d) reconcile the `eqToHom`-transported scalars: the two down-set comparison maps `e₁, e₂`
  -- compose (through the identity `(U i).ι.appIso`) to `𝟙` on `Γ(X, image)`, since
  -- `(U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W) = W`; on the thin poset `Opens X` this is `Subsingleton.elim`.
  congr 1
  simp only [homOfLE_leOfHom, Over.forget_obj, ObjectProperty.ι_obj, op_unop,
    Opens.ι_appIso, Iso.refl_inv, Functor.whiskerRight_app, CommRingCat.forgetToRingCat_map_hom,
    RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
    ZeroHom.coe_mk]
  rw [← X.presheaf.map_id (op ((U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  refine (ConcreteCategory.congr_hom (congrArg X.presheaf.map
    (Subsingleton.elim _ (𝟙 (op W)))) _).trans ?_
  rw [X.presheaf.map_id]
  rfl

open PresheafOfModules InternalHom Opposite in
/-- **Clean pointwise form of the forward-transport component.** The `app` component of
`sliceDualTransport f M V` evaluated at a dual section `φ` equals the reindexed component
`φ.app` at the `f`-image of `W` followed by the codomain unit ring-swap `dualUnitRingSwap`.
Holds by `rfl`; the structure-ring naturality field is explicit in the section type. -/
lemma sliceDualTransport_app_apply {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Y)ᵒᵖ)
    (φ : letI α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
           { app := fun U => (f.appIso U.unop).inv,
             naturality := fun _ _ i => f.appIso_inv_naturality i }
         letI β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
           Functor.whiskerRight α (forget₂ CommRingCat RingCat)
         (((PresheafOfModules.pushforward β).obj
            (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).obj V))
    (W : (Over (unop V))ᵒᵖ)
    (z : (M.val.obj (op ((Hom.opensFunctor f).obj (unop W).left)) : Type u)) :
    (ModuleCat.Hom.hom
        (((ModuleCat.Hom.hom (sliceDualTransport f M V).hom) φ).app W)) z
      = (dualUnitRingSwap f (unop W).left).hom
          ((φ.app (op (Over.mk ((Hom.opensFunctor f).map (unop W).hom)))).hom z) := rfl


set_option maxHeartbeats 1600000 in
-- Expanding the slice transport and normalizing the appIso cocycle exceeds the default budget.
open PresheafOfModules InternalHom Opposite in
/-- **Sectionwise split of the composite slice dual transport via the `appIso` cocycle.**
The `app` component of `sliceDualTransport (h ≫ f) M V` evaluated at `φ`, `W`, `z` factors the
composite structure-ring swap `dualUnitRingSwap (h ≫ f)` into the two single-immersion swaps
`dualUnitRingSwap f (h ''ᵁ W')` and `dualUnitRingSwap h W'` (`W' = W.left`), reindexed by the
direct-image composition `Scheme.Hom.comp_image`.  This is the structure-ring half of the
pseudofunctoriality law; project-local because it factors the open-immersion `comp_appIso` cocycle
through the slice-transport `app_apply` form. -/
lemma sliceDualTransport_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (h : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion h]
    (M : X.Modules) (V : (TopologicalSpace.Opens ↥Z)ᵒᵖ)
    (φ : letI α : Z.presheaf ⟶ (Hom.opensFunctor (h ≫ f)).op ⋙ X.presheaf :=
           { app := fun U => ((h ≫ f).appIso U.unop).inv,
             naturality := fun _ _ i => (h ≫ f).appIso_inv_naturality i }
         letI β : Z.ringCatSheaf.obj ⟶ (Hom.opensFunctor (h ≫ f)).op ⋙ X.ringCatSheaf.obj :=
           Functor.whiskerRight α (forget₂ CommRingCat RingCat)
         (((PresheafOfModules.pushforward β).obj
            (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).obj V))
    (W : (Over (unop V))ᵒᵖ)
    (z : (M.val.obj (op ((Hom.opensFunctor (h ≫ f)).obj (unop W).left)) : Type u)) :
    (ModuleCat.Hom.hom
        (((ModuleCat.Hom.hom (sliceDualTransport (h ≫ f) M V).hom) φ).app W)) z
      = (dualUnitRingSwap h (unop W).left).hom
          ((dualUnitRingSwap f ((Hom.opensFunctor h).obj (unop W).left)).hom
            ((X.presheaf.map (eqToHom (Scheme.Hom.comp_image h f (unop W).left).symm).op).hom
              ((φ.app (op (Over.mk ((Hom.opensFunctor (h ≫ f)).map (unop W).hom)))).hom z))) := by
  rw [sliceDualTransport_app_apply (h ≫ f) M V φ W z, dualUnitRingSwap_apply,
    Scheme.Hom.comp_appIso h f (unop W).left, dualUnitRingSwap_apply, dualUnitRingSwap_apply]
  simp only [Iso.trans_hom, CommRingCat.hom_comp, RingHom.comp_apply, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, eqToHom_op]

end Modules

end Scheme

end AlgebraicGeometry
