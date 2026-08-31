/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteGaloisRepresentable
import AlgebraicJacobian.Picard.Pic0FiniteStageStableOrbitAffine

/-!
# Stable affine covers from the finite-stage Picard glue

This module consumes the stable-package orbit producers in the stable-cover engine and in the
finite-Galois Picard representability theorem.  Every wrapper is indexed by the exact selected
presentation; projectivity entry points remain compatibility wrappers around immersion.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

noncomputable section

variable {K k F : Type u} [Field K] [Field k] [Field F]
variable [Algebra F k] [Algebra.IsAlgebraic F k]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable (Ck : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 Ck.hom] [IsProper Ck.hom]
  [GeometricallyIrreducible Ck.hom] [IsSepClosed k]
variable (P : Pic0FiniteStageStableGluePackage Ck F)
variable [Algebra K P.context.triple.N.1]
  [FiniteDimensional K P.context.triple.N.1] [IsGalois K P.context.triple.N.1]

/-- On an algebraically closed finite-stage field, the represented group structure and
irreducibility produce the stable affine cover directly, without an immersion binder. -/
@[implicit_reducible]
noncomputable def
    pic0FiniteStageHasStableAffineCover_of_isAlgClosed_of_irreducible
    [IsAlgClosed P.context.triple.N.1]
    [LocallyOfFiniteType P.presentation.map]
    [IrreducibleSpace P.presentation.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    HasStableAffineCover K P.context.triple.N.1
      (pic0SemilinearGalActionOfRepresentableBy C rep) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isAlgClosed_of_irreducible C Ck P rep
  infer_instance

/-- Over an algebraically closed finite-stage field, connectedness of the represented group
produces the stable affine cover directly. -/
@[implicit_reducible]
noncomputable def
    pic0FiniteStageHasStableAffineCover_of_isAlgClosed_of_connected
    [IsAlgClosed P.context.triple.N.1]
    [LocallyOfFiniteType P.presentation.map]
    [ConnectedSpace P.presentation.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    HasStableAffineCover K P.context.triple.N.1
      (pic0SemilinearGalActionOfRepresentableBy C rep) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isAlgClosed_of_connected C Ck P rep
  infer_instance

/-- A finite-dimensional projective-space immersion produces the stable affine cover used by
the finite-Galois quotient construction. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageHasStableAffineCover_of_isImmersion
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over)
    {n : Type u} [Finite n]
    (i : P.presentation.glueData.glued ⟶
      ℙ(n; Spec (.of P.context.triple.N.1)))
    (hi : IsImmersion i) :
    HasStableAffineCover K P.context.triple.N.1
      (pic0SemilinearGalActionOfRepresentableBy C rep) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isImmersion C Ck P rep i hi
  infer_instance

/-- Compatibility wrapper producing the stable affine cover from projectivity of the
finite-stage glued morphism. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageHasStableAffineCover_of_isProjective
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over)
    (hproj : P.presentation.map.IsProjective) :
    HasStableAffineCover K P.context.triple.N.1
      (pic0SemilinearGalActionOfRepresentableBy C rep) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isProjective C Ck P rep hproj
  infer_instance

/-- Consume the finite-stage immersion producer in the finite-Galois Picard descent theorem.
The resulting quotient represents Picard zero over the original field. -/
noncomputable def pic0RepresentableBy_finiteStageGaloisDescent_of_isImmersion
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over)
    {n : Type u} [Finite n]
    (i : P.presentation.glueData.glued ⟶
      ℙ(n; Spec (.of P.context.triple.N.1)))
    (hi : IsImmersion i) :
    (pic0TypeFunctor C).RepresentableBy
      (StableAffineOpen.gluedQuotientOver
        (pic0SemilinearGalActionOfRepresentableBy C rep)) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isImmersion C Ck P rep i hi
  exact pic0RepresentableBy_finiteGaloisDescent C rep

/-- Consume the algebraically-closed irreducible group producer in finite-Galois Picard
descent.  The arbitrary-field analogue awaits the corresponding algebraic-group
`FiniteInAffine` theorem. -/
noncomputable def
    pic0RepresentableBy_finiteStageGaloisDescent_of_isAlgClosed_of_irreducible
    [IsAlgClosed P.context.triple.N.1]
    [LocallyOfFiniteType P.presentation.map]
    [IrreducibleSpace P.presentation.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    (pic0TypeFunctor C).RepresentableBy
      (StableAffineOpen.gluedQuotientOver
        (pic0SemilinearGalActionOfRepresentableBy C rep)) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isAlgClosed_of_irreducible C Ck P rep
  exact pic0RepresentableBy_finiteGaloisDescent C rep

/-- Consume the algebraically-closed connected group producer in finite-Galois Picard
descent.  This remains conditional on connectedness at the finite-stage carrier and does not
assert an arbitrary-field analogue. -/
noncomputable def
    pic0RepresentableBy_finiteStageGaloisDescent_of_isAlgClosed_of_connected
    [IsAlgClosed P.context.triple.N.1]
    [LocallyOfFiniteType P.presentation.map]
    [ConnectedSpace P.presentation.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    (pic0TypeFunctor C).RepresentableBy
      (StableAffineOpen.gluedQuotientOver
        (pic0SemilinearGalActionOfRepresentableBy C rep)) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isAlgClosed_of_connected C Ck P rep
  exact pic0RepresentableBy_finiteGaloisDescent C rep

/-- Compatibility wrapper consuming projectivity in the finite-Galois Picard descent theorem. -/
noncomputable def pic0RepresentableBy_finiteStageGaloisDescent_of_isProjective
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over)
    (hproj : P.presentation.map.IsProjective) :
    (pic0TypeFunctor C).RepresentableBy
      (StableAffineOpen.gluedQuotientOver
        (pic0SemilinearGalActionOfRepresentableBy C rep)) := by
  letI : (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
    pic0FiniteStageStableOrbitsInAffineOpen_of_isProjective C Ck P rep hproj
  exact pic0RepresentableBy_finiteGaloisDescent C rep

end

end AlgebraicGeometry
