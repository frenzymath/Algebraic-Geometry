/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.TensorObjSubstrate

/-!
# K1: pullbackTensorMap is an iso for open immersions

Leaf module split out of `TensorObjInverse.lean` to isolate the 6.4M-HB elaboration of K1
(`pullbackTensorMap_isIso_of_isOpenImmersion`) for OOM-safe filling.  Imports only
`TensorObjSubstrate` (monster-free — does NOT import `PresheafDualPullback`).
-/

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- K1: `pullbackTensorMap` is an isomorphism for any open immersion. -/
lemma pullbackTensorMap_isIso_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M N : X.Modules) : IsIso (pullbackTensorMap f M N) := by
  apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  haveI hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
  haveI hδ : IsIso (Functor.OplaxMonoidal.δ
      (PresheafOfModules.pullback φ') M.val N.val) := by
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv
        naturality := fun _ _ i => f.appIso_inv_naturality i }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    have hβ : ∀ U, Function.Bijective (β.app U).hom := by
      intro U
      haveI : IsIso (β.app U) :=
        inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
      exact ConcreteCategory.bijective_of_isIso (β.app U)
    let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
    letI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
      PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
    let hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
      PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
        (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
        (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
    letI Gβ := PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf ⋙
      PresheafOfModules.restrictScalars β'
    let hadj' : Gβ ⊣ PresheafOfModules.pushforward φ' := hadj
    exact isIso_oplaxδ_of_conj
      (hadj'.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φ')) M.val N.val
      (pushforward_mu_appIso_collapse f M.val N.val)
  exact Functor.map_isIso _ (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val)

end Modules

end Scheme

end AlgebraicGeometry
