/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib

/-!
# Curve substrate: basic consequences of the standing hypotheses

The Jacobian challenge (`AlgebraicJacobian.Challenge`) works with a bundle
`C : Over (Spec (.of k))` together with the instances `[IsProper C.hom]`,
`[SmoothOfRelativeDimension 1 C.hom]` and `[GeometricallyIrreducible C.hom]`.
This file records the *topological and scheme-theoretic substrate* every later wave consumes,
as instances keyed on the `Over`-bundle:

* `AlgebraicGeometry.irreducibleSpace_left_of_geometricallyIrreducible`:
  a scheme geometrically irreducible over a field is irreducible (in particular nonempty).
* `AlgebraicGeometry.compactSpace_left_of_quasiCompact` and
  `AlgebraicGeometry.quasiSeparatedSpace_left_of_quasiSeparated`:
  a scheme quasi-compact (resp. quasi-separated) over `Spec k` is a quasi-compact
  (resp. quasi-separated) topological space; both hypotheses hold for proper morphisms.
* `AlgebraicGeometry.isIntegral_left_of_geometricallyReduced`:
  a scheme geometrically reduced and geometrically irreducible over a field is integral.
  In particular Mathlib's function-field API (`Scheme.functionField`) applies to `C.left`.

Geometric reducedness is taken as a *hypothesis* here: the implication
"smooth ⟹ geometrically reduced" is proved elsewhere in this project
(`AlgebraicJacobian.Curve.GeometricallyReduced`), never in this file.

Statements are given for an arbitrary `X : Over (Spec (.of k))` with the minimal hypotheses,
so that they also apply to the Jacobian bundle itself in later waves.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

section OverField

variable (X : Over (Spec (CommRingCat.of k)))

/-- A scheme geometrically irreducible over a field is irreducible.
In particular it is nonempty (`IrreducibleSpace.toNonempty`). -/
instance irreducibleSpace_left_of_geometricallyIrreducible
    [GeometricallyIrreducible X.hom] : IrreducibleSpace X.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom

/-- A scheme quasi-compact over `Spec k` (e.g. proper) is a quasi-compact topological space. -/
instance compactSpace_left_of_quasiCompact [QuasiCompact X.hom] : CompactSpace X.left :=
  QuasiCompact.compactSpace_of_compactSpace X.hom

/-- A scheme quasi-separated over `Spec k` (e.g. proper) is a quasi-separated topological
space. -/
instance quasiSeparatedSpace_left_of_quasiSeparated [QuasiSeparated X.hom] :
    QuasiSeparatedSpace X.left :=
  quasiSeparatedSpace_of_quasiSeparated X.hom

/-- A scheme geometrically reduced and geometrically irreducible over a field is integral.

Geometric reducedness is a hypothesis here; for the curve bundle of the challenge it is
supplied by "smooth ⟹ geometrically reduced", proved elsewhere in this project. -/
instance isIntegral_left_of_geometricallyReduced
    [GeometricallyIrreducible X.hom] [GeometricallyReduced X.hom] : IsIntegral X.left :=
  have : GeometricallyIntegral X.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible X.hom
  GeometricallyIntegral.isIntegral_of_subsingleton X.hom

end OverField

/-!
## Regression checks

The remaining standing consequences of the hypothesis bundle are already provided by Mathlib
instances; the `example`s below pin them down so a Mathlib bump cannot silently lose them.
They are stated for the exact curve bundle of `AlgebraicJacobian.Challenge`.
-/

section RegressionChecks

variable {C : Over (Spec (CommRingCat.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

-- `IsProper` unfolds into separatedness, universal closedness and finite type,
-- and quasi-compactness/quasi-separatedness follow.
example : IsSeparated C.hom := inferInstance
example : UniversallyClosed C.hom := inferInstance
example : LocallyOfFiniteType C.hom := inferInstance
example : QuasiCompact C.hom := inferInstance
example : QuasiSeparated C.hom := inferInstance

-- Geometric irreducibility makes the structure morphism surjective and the total space
-- an irreducible, nonempty, quasi-compact, quasi-separated topological space.
example : Surjective C.hom := inferInstance
example : IrreducibleSpace C.left := inferInstance
example : Nonempty C.left := inferInstance
example : CompactSpace C.left := inferInstance
example : QuasiSeparatedSpace C.left := inferInstance

-- With geometric reducedness (supplied by smoothness elsewhere in this project), the curve is
-- integral and Mathlib's function field 𝒪_{C,η} carries its field structure and algebra maps.
example [GeometricallyReduced C.hom] : IsIntegral C.left := inferInstance
noncomputable example [GeometricallyReduced C.hom] : Field C.left.functionField := inferInstance
noncomputable example [GeometricallyReduced C.hom] (x : C.left) :
    Algebra (C.left.presheaf.stalk x) C.left.functionField := inferInstance

end RegressionChecks

end AlgebraicGeometry
