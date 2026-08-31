/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# DJ-0: quasi-compactness from a compact-space source via a surjection

The smallest, ungated brick of the DAT-J worksheet (`informal/w4-datj-worksheet.md`
§2.4): the abstract topological shape that `JacobianData.quasiCompact` consumes to get
quasi-compactness of the Jacobian structure morphism from the Abel image of `Div^g`-lite.

The mathematics is entirely mathlib's: the continuous surjective image of a compact space
is compact (`Function.Surjective.compactSpace`). This file packages that for scheme
morphisms and adds the quasi-compactness corollary over an affine base, so DAT-J's qc
field is a one-line instantiation. It is deliberately **Challenge-free** (mathlib-only, no
curve/Challenge imports) — the DAT-J producer cone must not cycle through `Challenge.lean`
(worksheet §0.5 / risk 1).

## Main results

* `AlgebraicGeometry.compactSpace_of_surjective`: if `f : X ⟶ Y` is a surjection of
  schemes out of a compact-space source `X`, then `Y` is a compact space.
* `AlgebraicGeometry.quasiCompact_of_surjective`: a structure morphism `g : Y ⟶ Z` to an
  affine base is quasi-compact as soon as `Y` receives such a surjection. This is the
  shape DAT-J's DJ-1 consumes with `X := Div^g` (`compactSpace_divScheme`), `f := abel`
  the Abel morphism, `g := J.hom`, `Z := Spec k`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- **DJ-0, compact-image half.** If `f : X ⟶ Y` is a surjection of schemes out of a
compact-space source, then the target is a compact space: the underlying map of `f` is a
continuous surjection (`Scheme.Hom.continuous`), and the continuous surjective image of a
compact space is compact (`Function.Surjective.compactSpace`). -/
theorem compactSpace_of_surjective (f : X ⟶ Y) [CompactSpace X]
    (hf : Function.Surjective f.base) : CompactSpace Y :=
  hf.compactSpace f.continuous

/-- **DJ-0, quasi-compactness corollary.** A structure morphism `g : Y ⟶ Z` to an affine
base is quasi-compact as soon as `Y` receives a surjection `f : X ⟶ Y` from a
compact-space source `X`. Over an affine base, `QuasiCompact g` is exactly `CompactSpace Y`
(`HasAffineProperty.iff_of_isAffine`, the `DivSchemeQProj` pattern), which the
compact-image half supplies.

This is the abstract shape `JacobianData.quasiCompact` consumes: instantiate
`X := Div^g` (compact via `compactSpace_divScheme`), `f := abel` the Abel morphism
(surjective on points, DJ-1), `g := J.hom`, `Z := Spec k`. -/
theorem quasiCompact_of_surjective (f : X ⟶ Y) (g : Y ⟶ Z) [IsAffine Z]
    [CompactSpace X] (hf : Function.Surjective f.base) : QuasiCompact g :=
  haveI : CompactSpace Y := compactSpace_of_surjective f hf
  HasAffineProperty.iff_of_isAffine.mpr ‹_›

end AlgebraicGeometry
