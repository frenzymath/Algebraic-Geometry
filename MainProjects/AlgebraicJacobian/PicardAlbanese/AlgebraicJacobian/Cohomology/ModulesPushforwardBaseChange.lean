/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Canonical pushforward base change for scheme modules

For a cartesian square of schemes, `canonicalBaseChangeMap` is the Beck--Chevalley mate

```text
g^* f_* M --> f'_* (g')^* M.
```

The two coherence theorems identify its pullback followed by the counit with the pullback of
the original counit.  Invertibility is deliberately not asserted here: it is a property of the
module and square, not part of the construction of the canonical map.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The canonical Beck--Chevalley mate for pushforward along a cartesian square. -/
noncomputable def canonicalBaseChangeMap
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' :=
  CategoryTheory.mateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f')
    (((Scheme.Modules.pullbackComp f' g) ≪≫
      Scheme.Modules.pullbackCongr sq.w.symm ≪≫
      (Scheme.Modules.pullbackComp g' f).symm).hom)

/-- Pulling back the canonical mate and evaluating recovers its defining pullback telescope. -/
theorem canonicalBaseChangeMap_pullback_counit
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (M : X.Modules) :
    (Scheme.Modules.pullback f').map ((canonicalBaseChangeMap sq).app M) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
          ((Scheme.Modules.pullback g').obj M) =
      ((((Scheme.Modules.pullbackComp f' g) ≪≫
        Scheme.Modules.pullbackCongr sq.w.symm ≪≫
        (Scheme.Modules.pullbackComp g' f).symm).hom).app
          ((Scheme.Modules.pushforward f).obj M)) ≫
        (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  rw [canonicalBaseChangeMap]
  exact CategoryTheory.mateEquiv_counit _ _ _ M

/-- After cancelling the pullback telescope, the base-changed counit is the pulled-back
original counit. -/
theorem canonicalBaseChangeMap_counit_cancel
    {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (M : X.Modules) :
    ((((Scheme.Modules.pullbackComp f' g) ≪≫
      Scheme.Modules.pullbackCongr sq.w.symm ≪≫
      (Scheme.Modules.pullbackComp g' f).symm).inv).app
        ((Scheme.Modules.pushforward f).obj M)) ≫
      ((Scheme.Modules.pullback f').map ((canonicalBaseChangeMap sq).app M) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
          ((Scheme.Modules.pullback g').obj M)) =
      (Scheme.Modules.pullback g').map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  erw [canonicalBaseChangeMap_pullback_counit]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

end AlgebraicGeometry
