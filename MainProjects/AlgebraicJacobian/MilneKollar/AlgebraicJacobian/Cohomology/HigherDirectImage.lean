/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Higher direct images `Rⁱ f_*` of quasi-coherent sheaves (`i ≥ 1`)

This file treats the higher derived direct images `Rⁱ f_* F` for `i ≥ 1`,
complementing the `i = 0` (direct-image) case of `Cohomology/FlatBaseChange.lean`.

Throughout, `f : X ⟶ S` is a morphism of schemes and `F : X.Modules` a sheaf of
modules on `X`. The `i`-th higher direct image `Rⁱ f_* F` is the `i`-th right
derived functor of the pushforward functor `f_*` applied to `F`.

This file supplies the single declaration needed downstream by the Čech
computation of higher direct images:

* `AlgebraicGeometry.higherDirectImage` — the higher direct image `Rⁱ f_* F`,
  the derived-functor object that `cech_computes_higherDirectImage` compares the
  Čech complex against.

See `blueprint/src/chapters/Cohomology_HigherDirectImage.tex`.

Source: Stacks Project, Cohomology of Schemes, Definition of `Rⁱ f_*`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {S X : Scheme.{u}}

/-- The `i`-th higher direct image `Rⁱ f_* F` of a sheaf of modules `F` on `X`
along a morphism `f : X ⟶ S`, defined as the `i`-th right derived functor of the
pushforward functor `f_*` applied to `F`.

For `i = 0` this recovers the ordinary pushforward `R⁰ f_* F = f_* F`.

Source: Stacks Project, Cohomology of Schemes, Definition of `Rⁱ f_*`. -/
noncomputable def higherDirectImage [HasInjectiveResolutions X.Modules]
    (f : X ⟶ S) (i : ℕ) (F : X.Modules) : S.Modules :=
  ((pushforward f).rightDerived i).obj F

end AlgebraicGeometry
