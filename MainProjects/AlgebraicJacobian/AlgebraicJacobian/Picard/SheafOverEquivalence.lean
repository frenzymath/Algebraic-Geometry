/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Restrict
import AlgebraicJacobian.Picard.TensorObjSubstrate.Vestigial

/-!
# Sheaf-of-modules over-equivalence (shared slice root)

This file constructs the modules-level lift of the site equivalence
`TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U` to an equivalence of
sheaf-of-modules categories

```
overEquivalence U :
  SheafOfModules (↑U : Scheme).ringCatSheaf ≌ SheafOfModules (X.ringCatSheaf.over U)
```

together with two consumer isomorphisms and the corollary `chartOverIso`, which transports a
scheme-level trivialisation of a module to a trivialisation of its slice avatar.

The construction assembles three existing Mathlib primitives; the only genuine content is the
ring morphism `φ` identifying the two structure sheaves along the open immersion `U.ι`.

## Main results

* `Scheme.Modules.overEquivalence`: the equivalence of sheaf-of-modules categories above.
* `Scheme.Modules.restrictOverIso`: `(overEquivalence U).functor.obj (M.restrict U.ι) ≅ M.over U`.
* `Scheme.Modules.unitOverIso`: the equivalence matches the two unit modules.
* `Scheme.Modules.chartOverIso`: from `M.restrict U.ι ≅ 𝒪_{↥U}` obtain
  `M.over U ≅ 𝒪_X|_U`; the composite of the three isomorphisms above.

The last two are consumed by `LineBundleCoherence.chartOverIso` and, on the dual side, by
`dual_restrict_iso` / `sliceDualTransport` in `TensorObjSubstrate/DualInverse.lean`.

## References

Blueprint: `blueprint/src/chapters/Picard_SheafOverEquivalence.tex`,
sections `sec:soe_equivalence`, `sec:soe_consumers`, `sec:soe_chart`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-! ## §1. The equivalence (`def:sheafofmodules_over_equivalence`) -/

/- Shape of the construction.

   Write `e := TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U`, and equip
   `Over U` with `J := (Opens.grothendieckTopology X).over U` and `Opens ↥U` with
   `K := Opens.grothendieckTopology ↥U`.  The ring sheaves are `(↑U).ringCatSheaf` on the
   second site and `X.ringCatSheaf.over U` on the first, so the equivalence is oriented
   `SheafOfModules (↑U).ringCatSheaf ⥤ SheafOfModules (X.ringCatSheaf.over U)`.

   Continuity of both legs comes for free: the project's dense-subsite instance for
   `e.inverse` (`Vestigial.lean`) gives `e.inverse.IsDenseSubsite K J`, a dense subsite is
   continuous, and for an equivalence density of the inverse propagates to the functor.

   The mathematical content is the ring morphism
   `φ : X.ringCatSheaf.over U ⟶
      (e.functor.sheafPushforwardContinuous RingCat J K).obj (↑U : Scheme).ringCatSheaf`,
   which sectionwise at `V : Over U` is the structure-sheaf comparison
   `𝒪_X(V.left) ⟶ 𝒪_{↥U}(e V)` of the open immersion `U.ι` — the same datum
   `α U := (f.appIso U.unop).inv` that `Scheme.Modules.restrictFunctor` uses inline; `ψ` is
   the symmetric inverse.  The two coherences say that `φ` and `ψ` are mutually inverse, and
   are proved sectionwise from the `appIso` round-trips (they are genuine hom equalities:
   thinness of `Opens` does not make them automatic).  The equivalence is then
   `SheafOfModules.pushforwardPushforwardEquivalence e φ ψ`, whose underlying functor is
   `SheafOfModules.pushforward φ`. -/
/- Continuity of both legs of `Opens.overEquivalence U`.

   The site of `(↑U : Scheme).ringCatSheaf` is `Opens.grothendieckTopology ↥(↑U : Scheme)`,
   where `↥(↑U : Scheme)` is the carrier of the open subscheme reached via the
   `Scheme → TopCat → Type` coercion. This is *definitionally* the subtype `↥U`, but it
   keys differently in the instance discrimination tree, so typeclass search does not find
   the project's dense-subsite instance `overEquivInverseIsDenseSubsite` (stated for the
   bare topological space `↥U`). We therefore state the two continuity instances on the
   scheme-carrier form and discharge them by converting to the subtype form, where
   `overEquivInverseIsDenseSubsite` + the priority-900 `IsDenseSubsite → IsContinuous` and
   the equivalence's functor-density propagation resolve them. -/

/-- Continuity of the inverse leg of `overEquivalence U`. -/
instance overEquivInverseIsContinuous :
    (TopologicalSpace.Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥(↑U : Scheme)) ((Opens.grothendieckTopology ↥X).over U) := by
  change (TopologicalSpace.Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology ↥X).over U)
  infer_instance

/-- Continuity of the functor leg of `overEquivalence U`. -/
instance overEquivFunctorIsContinuous :
    (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology ↥X).over U) (Opens.grothendieckTopology ↥(↑U : Scheme)) := by
  change (TopologicalSpace.Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology ↥X).over U) (Opens.grothendieckTopology ↥U)
  infer_instance

/-- The open-immersion image of the reindexed open `e.functor V = ι⁻¹(V.left)` is `V.left`
itself, since `V.left ≤ U`. This is the equality that identifies the two structure-sheaf
presheaves underlying the over-equivalence's ring morphism `φ`. -/
private lemma image_overEquiv_functor_obj (V : Over U) :
    U.ι ''ᵁ ((TopologicalSpace.Opens.overEquivalence U).functor.obj V) = V.left := by
  apply TopologicalSpace.Opens.ext
  ext y
  simp only [Scheme.Hom.coe_image, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy
    exact ⟨⟨y, leOfHom V.hom hy⟩, hy, rfl⟩

/-- The structure-sheaf ring morphism underlying the over-equivalence: at `V : Over U` it
is the identification `𝒪_X(V.left) ≅ 𝒪_{↥U}(ι⁻¹ V.left)` of the structure sheaves, which on
the nose is `X.ringCatSheaf.val.map` of the open equality `image_overEquiv_functor_obj`
(the two presheaves agree definitionally via `toScheme_presheaf_obj`). -/
private noncomputable def phiOver :
    X.ringCatSheaf.over U ⟶
    ((TopologicalSpace.Opens.overEquivalence U).functor.sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology ↥X).over U)
        (Opens.grothendieckTopology ↥(↑U : Scheme))).obj (↑U : Scheme).ringCatSheaf :=
  ⟨{ app := fun V => X.ringCatSheaf.obj.map (eqToHom (image_overEquiv_functor_obj U V.unop)).op
     naturality := by
       intro a b f
       simp only [Functor.sheafPushforwardContinuous_obj_obj_map]
       erw [← Functor.map_comp, ← Functor.map_comp]
       congr 1 }⟩

/-- The left component of the inverse reindexing `e.inverse W` (i.e. the image of `W` in
`X` under the open immersion) is `U.ι ''ᵁ W`. Symmetric counterpart of
`image_overEquiv_functor_obj`. -/
private lemma left_overEquiv_inverse_obj (W : TopologicalSpace.Opens ↥(↑U : Scheme)) :
    ((TopologicalSpace.Opens.overEquivalence U).inverse.obj W).left = U.ι ''ᵁ W := by
  apply TopologicalSpace.Opens.ext
  ext y
  simp only [Scheme.Hom.coe_image, SetLike.mem_coe]
  rfl

/-- The inverse ring morphism `ψ`, symmetric to `phiOver`. -/
private noncomputable def psiOver :
    (↑U : Scheme).ringCatSheaf ⟶
    ((TopologicalSpace.Opens.overEquivalence U).inverse.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology ↥(↑U : Scheme))
        ((Opens.grothendieckTopology ↥X).over U)).obj (X.ringCatSheaf.over U) :=
  ⟨{ app := fun W => X.ringCatSheaf.obj.map (eqToHom (left_overEquiv_inverse_obj U W.unop)).op
     naturality := by
       intro a b f
       simp only [Functor.sheafPushforwardContinuous_obj_obj_map]
       rw [show (↑U : Scheme).ringCatSheaf.obj.map f
             = X.ringCatSheaf.obj.map (U.ι.opensFunctor.op.map f) from rfl]
       change (forget₂ CommRingCat RingCat).map _ ≫ (forget₂ CommRingCat RingCat).map _
           = (forget₂ CommRingCat RingCat).map _ ≫ (forget₂ CommRingCat RingCat).map _
       rw [← (forget₂ CommRingCat RingCat).map_comp, ← (forget₂ CommRingCat RingCat).map_comp]
       congr 1
       exact (Functor.map_comp _ _ _).symm.trans
         ((congrArg _ (Subsingleton.elim _ _)).trans (Functor.map_comp _ _ _)) }⟩

noncomputable def overEquivalence :
    SheafOfModules ((↑U : Scheme).ringCatSheaf) ≌ SheafOfModules (X.ringCatSheaf.over U) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence
    (TopologicalSpace.Opens.overEquivalence U) (phiOver U) (psiOver U) ?H₁ ?H₂
  · ext W : 2
    simp only [Functor.whiskerRight_app, NatTrans.op_app, NatTrans.comp_app,
      Functor.whiskerLeft_app, phiOver, psiOver]
    change X.ringCatSheaf.obj.map (U.ι.opensFunctor.op.map
            ((TopologicalSpace.Opens.overEquivalence U).counit.app W.unop).op) = _
    change (forget₂ CommRingCat RingCat).map _
        = (forget₂ CommRingCat RingCat).map _ ≫ (forget₂ CommRingCat RingCat).map _
    rw [← (forget₂ CommRingCat RingCat).map_comp]
    congr 1
    exact (congrArg _ (Subsingleton.elim _ _)).trans (Functor.map_comp _ _ _)
  · ext W : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.op_app, phiOver, psiOver, NatTrans.id_app,
      Functor.sheafPushforwardContinuous_obj_obj_map]
    rw [show (𝟙 ((Sheaf.over X.ringCatSheaf U).obj.obj W))
          = X.ringCatSheaf.obj.map (𝟙 (Opposite.op W.unop.left))
          from (X.ringCatSheaf.obj.map_id _).symm]
    change (forget₂ CommRingCat RingCat).map _ ≫ (forget₂ CommRingCat RingCat).map _
        ≫ (forget₂ CommRingCat RingCat).map _ = (forget₂ CommRingCat RingCat).map _
    rw [← (forget₂ CommRingCat RingCat).map_comp, ← (forget₂ CommRingCat RingCat).map_comp]
    congr 1
    exact ((Functor.map_comp _ _ _).trans
      (congrArg _ (Functor.map_comp _ _ _))).symm.trans (congrArg _ (Subsingleton.elim _ _))

/-! ## §2. Consumer isomorphisms
(`lem:sheafofmodules_restrict_over_iso`, `lem:sheafofmodules_unit_over_iso`) -/

/- Construction of `restrictOverIso : (overEquivalence U).functor.obj (M.restrict U.ι) ≅ M.over U`.

   `M.restrict U.ι = (restrictFunctor U.ι).obj M` is itself a `SheafOfModules.pushforward`,
   along the open-immersion functor `U.ι.opensFunctor : Opens ↥U ⥤ Opens X`: by construction
   `restrictFunctor f = SheafOfModules.pushforward ⟨α⟩` with `α U := (f.appIso U.unop).inv`.

   The functor underlying `(overEquivalence U).functor` is `SheafOfModules.pushforward φ`, so
   the composite is a pushforward along `U.ι.opensFunctor ⋙ e.functor`, identified by
   `SheafOfModules.pushforwardComp`; the φ round-trip cancels, so the composite ring morphism
   is the identity.  Then `SheafOfModules.pushforwardNatIso`, applied to the `eqToIso` of the
   equality of the two index functors `Over U ⥤ Opens X` (both send `V ↦ V.left`), transports
   the composite to `M.over U`.

   This mirrors `Scheme.Modules.restrictFunctorAdjCounitIso`. -/
/-- The ring morphism along `U.ι.opensFunctor` underlying `Scheme.Modules.restrictFunctor U.ι`;
reconstructed so that `restrictFunctor U.ι = SheafOfModules.pushforward (psiRestrict U)` holds
definitionally (verbatim from `restrictFunctor`'s internals). -/
private noncomputable def psiRestrict :
    (↑U : Scheme).ringCatSheaf ⟶
    (U.ι.opensFunctor.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology ↥(↑U : Scheme)) (Opens.grothendieckTopology ↥X)).obj
        X.ringCatSheaf :=
  letI α : (↑U : Scheme).presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app := fun W => (U.ι.appIso W.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

private lemma restrictFunctor_eq_pushforward_psiRestrict :
    Scheme.Modules.restrictFunctor U.ι = SheafOfModules.pushforward (psiRestrict U) := rfl

/-- The index `eqToIso` natural isomorphism `Over.forget U ≅ e.functor ⋙ U.ι.opensFunctor`
(both functors send `V ↦ V.left`), used to reconcile the two pushforward index functors. -/
private noncomputable def overForgetNatIso :
    Over.forget U ≅
    (TopologicalSpace.Opens.overEquivalence U).functor ⋙ U.ι.opensFunctor :=
  NatIso.ofComponents (fun V => eqToIso (image_overEquiv_functor_obj U V).symm)
    (fun _ => Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
noncomputable def restrictOverIso (M : X.Modules) :
    (overEquivalence U).functor.obj (M.restrict U.ι) ≅ M.over U := by
  -- Continuity of both index legs, and of their composite, supplied explicitly: nested typeclass
  -- search for these in the slice site cannot match Mathlib's instances (discrim-tree transparency
  -- on the `↥(↑U : Scheme)` carrier), so we pass them by `@`.
  haveI hF1 : ((TopologicalSpace.Opens.overEquivalence U).functor).IsContinuous
      ((Opens.grothendieckTopology ↥X).over U) (Opens.grothendieckTopology ↥(↑U : Scheme)) :=
    inferInstance
  haveI hF2 : (U.ι.opensFunctor).IsContinuous (Opens.grothendieckTopology ↥(↑U : Scheme))
      (Opens.grothendieckTopology ↥X) := inferInstance
  letI hcomp : ((TopologicalSpace.Opens.overEquivalence U).functor ⋙ U.ι.opensFunctor).IsContinuous
      ((Opens.grothendieckTopology ↥X).over U) (Opens.grothendieckTopology ↥X) :=
    @Functor.isContinuous_comp _ _ _ _ _ _ (TopologicalSpace.Opens.overEquivalence U).functor
      U.ι.opensFunctor ((Opens.grothendieckTopology ↥X).over U)
      (Opens.grothendieckTopology ↥(↑U : Scheme)) (Opens.grothendieckTopology ↥X) hF1 hF2
  refine (SheafOfModules.pushforwardComp (phiOver U) (psiRestrict U)).app M ≪≫ ?_
  refine (SheafOfModules.pushforwardNatIso _ (overForgetNatIso U)).app M ≪≫ ?_
  refine (SheafOfModules.pushforwardCongr ?heq).app M
  ext V x
  -- Sectionwise the composite ring map is `𝒪_X(V.left) → 𝒪_X(ι ''ᵁ (e.functor V)) → 𝒪_X(V.left)`
  -- via two mutually inverse `eqToHom` images (the open equality `ι ''ᵁ (e.functor V) = V.left`),
  -- hence the identity. The `psiRestrict` `appIso` round-trip collapses the middle to `𝟙`.
  simp only [phiOver, eqToHom_op, psiRestrict, Opposite.op_unop, Opens.ι_appIso, Iso.refl_inv,
    overForgetNatIso, Over.forget_obj, Category.assoc,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    ObjectProperty.ι_obj, NatTrans.comp_app, Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.whiskerRight_app, NatTrans.op_app, NatIso.ofComponents_hom_app, eqToIso.hom,
    RingCat.hom_comp, CommRingCat.forgetToRingCat_map_hom, RingHom.coe_comp, Function.comp_apply,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, RingCat.hom_id, RingHom.id_apply]
  erw [ConcreteCategory.id_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  erw [ConcreteCategory.id_apply]

/- Construction of `unitOverIso`:
   `(overEquivalence U).functor.obj (SheafOfModules.unit (↑U : Scheme).ringCatSheaf)
    ≅ SheafOfModules.unit (X.ringCatSheaf.over U)`.

   The functor underlying `(overEquivalence U).functor` is `SheafOfModules.pushforward φ`.
   The pushforward of a unit module along a morphism φ of ringed sites is the unit module
   of the codomain ring sheaf: `pushforward φ (unit R) ≅ unit S`, because φ is exactly the
   open-immersion identification of the two structure ring sheaves, so `pushforward φ` sends
   the `𝒪_U`-unit to the `𝒪_{X,over U}`-unit. φ being an isomorphism makes this a genuine
   iso (cf. the project's `pullbackObjUnitToUnitIso` pattern in `DualInverse.lean`). -/
noncomputable def unitOverIso :
    (overEquivalence U).functor.obj (SheafOfModules.unit (↑U : Scheme).ringCatSheaf) ≅
    SheafOfModules.unit (X.ringCatSheaf.over U) := by
  -- The over-equivalence functor is `SheafOfModules.pushforward (phiOver U)`, so this iso is the
  -- inverse of the canonical unit-comparison `unitToPushforwardObjUnit (phiOver U)`.
  -- That comparison is sectionwise `(phiOver U).hom.app`
  -- (`unitToPushforwardObjUnit_val_app_apply`),
  -- which is an isomorphism because `phiOver U` is one (its presheaf components are
  -- `X.ringCatSheaf.obj.map (eqToHom …).op`, images of `eqToHom` under a functor). Hence the
  -- comparison is a `SheafOfModules` isomorphism (sectionwise-iso reflection).
  haveI hφ : IsIso (phiOver U) := by
    have hmap : IsIso ((sheafToPresheaf ((Opens.grothendieckTopology ↥X).over U) RingCat).map
        (phiOver U)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro W
      exact inferInstanceAs
        (IsIso (X.ringCatSheaf.obj.map (eqToHom (image_overEquiv_functor_obj U W.unop)).op))
    exact isIso_of_reflects_iso (phiOver U) (sheafToPresheaf _ RingCat)
  haveI : IsIso (SheafOfModules.unitToPushforwardObjUnit (phiOver U)) := by
    -- Reflect iso-ness through `SheafOfModules.forget` then `PresheafOfModules.toPresheaf`
    -- down to the sectionwise additive maps. By `unitToPushforwardObjUnit_val_app_apply` the
    -- section at `W` is `(phiOver U).hom.app W`, which is an isomorphism since `phiOver U` is
    -- (`hφ`). The remaining leaf is exactly `IsIso` of (the additive map underlying) that
    -- sectionwise ring isomorphism.
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _),
        ← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _),
        NatTrans.isIso_iff_isIso_app]
    intro W
    -- The underlying ring-presheaf morphism `(phiOver U).hom` is sectionwise an iso (its
    -- components are `X.ringCatSheaf.obj.map (eqToHom …).op`, images of `eqToHom`), so each
    -- `(phiOver U).hom.app W` is a ring isomorphism.
    haveI hval : IsIso ((phiOver U).hom) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      exact inferInstanceAs
        (IsIso (X.ringCatSheaf.obj.map (eqToHom (image_overEquiv_functor_obj U V.unop)).op))
    haveI happ : IsIso ((phiOver U).hom.app W) := inferInstance
    -- The sectionwise map underlying `unitToPushforwardObjUnit (phiOver U)` at `W` is, up to
    -- definitional unfolding, the additive-group map `forget₂.map ((phiOver U).hom.app W)`
    -- (cf. `unitToPushforwardObjUnit_val_app_apply`), an iso since `(phiOver U).hom.app W` is.
    change IsIso ((forget₂ RingCat AddCommGrpCat).map ((phiOver U).hom.app W))
    infer_instance
  exact (asIso (SheafOfModules.unitToPushforwardObjUnit (phiOver U))).symm

/-! ## §3. Engine corollary (`lem:chart_over_iso`) -/

/- `chartOverIso` is the three-step composite:
   1. `(restrictOverIso U M).symm`
         : M.over U ≅ (overEquivalence U).functor.obj (M.restrict U.ι)
   2. `(overEquivalence U).functor.mapIso e`
         : ... ≅ (overEquivalence U).functor.obj (SheafOfModules.unit (↑U : Scheme).ringCatSheaf)
   3. `unitOverIso U`
         : ... ≅ SheafOfModules.unit (X.ringCatSheaf.over U)

   Each factor is an isomorphism; the composite has the required type.  This is the general
   form consumed by `LineBundleCoherence.chartOverIso` and, on the dual side, by
   `sliceDualTransport` / `dual_restrict_iso` in `TensorObjSubstrate/DualInverse.lean`. -/
noncomputable def chartOverIso (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (↑U : Scheme).ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (restrictOverIso U M).symm ≪≫ (overEquivalence U).functor.mapIso e ≪≫ unitOverIso U

end Modules

end Scheme

end AlgebraicGeometry
