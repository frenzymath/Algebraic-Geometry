/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Algebra.PushoutKernel
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Pullback ideals on affine morphisms

On the inverse image of an affine open under an affine morphism, pullback of an ideal
sheaf is computed by extension of its affine ideal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme.IdealSheafData

/-- Pullback of an ideal sheaf along an affine morphism is extension of the affine ideal. -/
lemma ideal_comap_of_isAffineHom (I : Y.IdealSheafData) (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ =
      (I.ideal U).map (f.app U).hom := by
  rw [comap, Scheme.Hom.ker_apply]
  have hpre :
      (pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U.1) =
        (pullback.fst f I.subschemeι) ⁻¹ᵁ (f ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition,
      Scheme.Hom.comp_preimage]
  have hUY :
      (pullback.fst f I.subschemeι) ⁻¹ᵁ (f ⁻¹ᵁ U.1) =
        (pullback.fst f I.subschemeι) ⁻¹ᵁ (f ⁻¹ᵁ U.1) ⊓
          (pullback.snd f I.subschemeι) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U.1) := by
    rw [hpre, inf_idem]
  have hp := (isIso_pushoutSection_iff
      (IsPullback.of_hasPullback f I.subschemeι)
      (le_refl (I.subschemeι ⁻¹ᵁ U.1))
      (le_refl (f ⁻¹ᵁ U.1)) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen
      (IsPullback.of_hasPullback f I.subschemeι)
      (le_refl (I.subschemeι ⁻¹ᵁ U.1))
      (le_refl (f ⁻¹ᵁ U.1)) hUY U.2
      (U.2.preimage I.subschemeι) (U.2.preimage f))
  have hk := CommRingCat.ker_inr_eq_map_ker_of_isPushout
    _ _ _ _ hp.flip (by
      simpa only [Scheme.Hom.appLE_eq_app] using I.subschemeι_app_surjective U)
  simpa only [Scheme.Hom.appLE_eq_app, I.ker_subschemeι_app U] using hk

end Scheme.IdealSheafData

end AlgebraicGeometry
