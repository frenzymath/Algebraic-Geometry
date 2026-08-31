/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.GroupAffineOpen
import AlgebraicJacobian.Descent.QuasiProjectiveFiniteInAffine
import AlgebraicJacobian.Picard.Pic0FiniteStageStableGluePackage
import AlgebraicJacobian.Picard.Pic0GaloisAction

/-!
# Orbit affineness for a stable finite-stage Picard glue

These producers use the carrier and structure map selected by a
`Pic0FiniteStageStableGluePackage`.  In particular, this module does not reconstruct or import
the legacy finite-stage glue package.
-/

set_option autoImplicit false

universe u

open CategoryTheory
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

/-- The group object transported to the carrier selected by a stable glue presentation. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageStableGrpObjOfRepresentableBy
    (P : Pic0FiniteStageStableGluePackage Ck F)
    [Algebra K P.context.triple.N.1]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    GrpObj P.presentation.over :=
  GrpObj.ofRepresentableBy P.presentation.over
    (pic0Functor ((baseChange K P.context.triple.N.1).obj C) ⋙
      forget₂ CommGrpCat GrpCat) rep

/-- Stable-package form of the irreducible algebraic-group orbit producer.

Local finite type is explicit because a stable package deliberately permits an arbitrary
selected affine presentation; that geometric property is not encoded in the package itself. -/
@[implicit_reducible]
noncomputable def
    pic0FiniteStageStableOrbitsInAffineOpen_of_isAlgClosed_of_irreducible
    (P : Pic0FiniteStageStableGluePackage Ck F)
    [Algebra K P.context.triple.N.1]
    [FiniteDimensional K P.context.triple.N.1] [IsGalois K P.context.triple.N.1]
    [IsAlgClosed P.context.triple.N.1]
    [LocallyOfFiniteType P.presentation.map]
    [IrreducibleSpace P.presentation.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen := by
  letI : GrpObj P.presentation.over :=
    pic0FiniteStageStableGrpObjOfRepresentableBy C Ck P rep
  letI : LocallyOfFiniteType P.presentation.over.hom := by
    change LocallyOfFiniteType P.presentation.map
    infer_instance
  letI : IrreducibleSpace P.presentation.over.left := by
    change IrreducibleSpace P.presentation.glueData.glued
    infer_instance
  exact Scheme.orbitsInAffineOpen_of_finiteInAffine _
    (GroupScheme.finiteInAffine_of_isAlgClosed_of_irreducible P.presentation.over)

/-- Stable-package form of the connected algebraic-group orbit producer. -/
@[implicit_reducible]
noncomputable def
    pic0FiniteStageStableOrbitsInAffineOpen_of_isAlgClosed_of_connected
    (P : Pic0FiniteStageStableGluePackage Ck F)
    [Algebra K P.context.triple.N.1]
    [FiniteDimensional K P.context.triple.N.1] [IsGalois K P.context.triple.N.1]
    [IsAlgClosed P.context.triple.N.1]
    [LocallyOfFiniteType P.presentation.map]
    [ConnectedSpace P.presentation.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen := by
  letI : GrpObj P.presentation.over :=
    pic0FiniteStageStableGrpObjOfRepresentableBy C Ck P rep
  letI : LocallyOfFiniteType P.presentation.over.hom := by
    change LocallyOfFiniteType P.presentation.map
    infer_instance
  letI : ConnectedSpace P.presentation.over.left := by
    change ConnectedSpace P.presentation.glueData.glued
    infer_instance
  exact Scheme.orbitsInAffineOpen_of_finiteInAffine _
    (GroupScheme.finiteInAffine_of_isAlgClosed_of_connected P.presentation.over)

/-- An immersion into finite relative projective space makes the carrier of a selected
stable presentation `FiniteInAffine`. -/
theorem pic0FiniteStageStableFiniteInAffine_of_isImmersion
    (P : Pic0FiniteStageStableGluePackage Ck F)
    {n : Type u} [Finite n]
    (i : P.presentation.glueData.glued ⟶
      ℙ(n; Spec (.of P.context.triple.N.1)))
    (hi : IsImmersion i) :
    Scheme.FiniteInAffine P.presentation.glueData.glued := by
  letI : IsImmersion i := hi
  exact Scheme.finiteInAffine_of_isImmersion i
    (Scheme.finiteInAffine_projectiveSpace n
      (Spec (.of P.context.triple.N.1)))

/-- An immersion of the selected stable presentation supplies orbit affineness without
reconstructing the legacy glue package. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageStableOrbitsInAffineOpen_of_isImmersion
    (P : Pic0FiniteStageStableGluePackage Ck F)
    [Algebra K P.context.triple.N.1]
    [FiniteDimensional K P.context.triple.N.1] [IsGalois K P.context.triple.N.1]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over)
    {n : Type u} [Finite n]
    (i : P.presentation.glueData.glued ⟶
      ℙ(n; Spec (.of P.context.triple.N.1)))
    (hi : IsImmersion i) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen := by
  exact Scheme.orbitsInAffineOpen_of_finiteInAffine _
    (pic0FiniteStageStableFiniteInAffine_of_isImmersion Ck P i hi)

/-- Projectivity wrapper for the selected stable presentation. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageStableOrbitsInAffineOpen_of_isProjective
    (P : Pic0FiniteStageStableGluePackage Ck F)
    [Algebra K P.context.triple.N.1]
    [FiniteDimensional K P.context.triple.N.1] [IsGalois K P.context.triple.N.1]
    (rep : (pic0TypeFunctor ((baseChange K P.context.triple.N.1).obj C)).RepresentableBy
      P.presentation.over)
    (hproj : P.presentation.map.IsProjective) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen := by
  obtain ⟨n, hn, i, hi, -⟩ := hproj
  letI : Finite n := hn
  letI : IsClosedImmersion i := hi
  exact pic0FiniteStageStableOrbitsInAffineOpen_of_isImmersion C Ck P rep i
    (inferInstance : IsImmersion i)

end

end AlgebraicGeometry
