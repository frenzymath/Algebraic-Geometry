/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Descent.GroupAffineOpen
import AlgebraicJacobian.Descent.QuasiProjectiveFiniteInAffine
import AlgebraicJacobian.Picard.Pic0FiniteStageGeometry
import AlgebraicJacobian.Picard.Pic0FiniteStageGluePackage
import AlgebraicJacobian.Picard.Pic0GaloisAction

/-!
# Orbit affineness for the finite-stage Picard glue

An immersion of the finite-stage glued representative into finite relative projective space
gives the finite-in-affine property, so every orbit of its canonical finite-Galois action lies
in an affine open.  This file records the legacy producers at the exact carrier `P.gluedOver`
used by finite-stage descent.  The projectivity entry point remains as a compatibility wrapper.
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

/-- The group object on the finite-stage glue canonically transported from a
representation of Picard zero. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageGrpObjOfRepresentableBy
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver) :
    GrpObj P.gluedOver :=
  GrpObj.ofRepresentableBy P.gluedOver
    (pic0Functor ((baseChange K P.N.1).obj C) ⋙ forget₂ CommGrpCat GrpCat) rep

/-- Over an algebraically closed finite-stage field, irreducibility and the represented
group law make the glued Picard-zero carrier `FiniteInAffine`.

This is the exact finite-stage specialization of the algebraic-group translation theorem;
the arbitrary-field descent of that theorem is a separate geometric input. -/
theorem pic0FiniteStageFiniteInAffine_of_isAlgClosed_of_irreducible
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1] [IsAlgClosed P.N.1]
    [IrreducibleSpace P.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver) :
    Scheme.FiniteInAffine P.glueData.glued := by
  letI : GrpObj P.gluedOver :=
    pic0FiniteStageGrpObjOfRepresentableBy C Ck P rep
  letI : LocallyOfFiniteType P.gluedOver.hom := by
    change LocallyOfFiniteType P.gluedMap
    infer_instance
  letI : IrreducibleSpace P.gluedOver.left := by
    change IrreducibleSpace P.glueData.glued
    infer_instance
  exact GroupScheme.finiteInAffine_of_isAlgClosed_of_irreducible P.gluedOver

/-- The represented group law produces orbit affineness on the exact finite-stage carrier
over an algebraically closed field, with no projective-space immersion hypothesis. -/
@[implicit_reducible]
noncomputable def
    pic0FiniteStageOrbitsInAffineOpen_of_isAlgClosed_of_irreducible
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1] [FiniteDimensional K P.N.1] [IsGalois K P.N.1]
    [IsAlgClosed P.N.1] [IrreducibleSpace P.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
  Scheme.orbitsInAffineOpen_of_finiteInAffine _
    (pic0FiniteStageFiniteInAffine_of_isAlgClosed_of_irreducible C Ck P rep)

/-- Over an algebraically closed finite-stage field, connectedness and the represented
group law make the exact glued Picard-zero carrier `FiniteInAffine`. -/
theorem pic0FiniteStageFiniteInAffine_of_isAlgClosed_of_connected
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1] [IsAlgClosed P.N.1]
    [ConnectedSpace P.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver) :
    Scheme.FiniteInAffine P.glueData.glued := by
  letI : GrpObj P.gluedOver :=
    pic0FiniteStageGrpObjOfRepresentableBy C Ck P rep
  letI : LocallyOfFiniteType P.gluedOver.hom := by
    change LocallyOfFiniteType P.gluedMap
    infer_instance
  letI : ConnectedSpace P.gluedOver.left := by
    change ConnectedSpace P.glueData.glued
    infer_instance
  exact GroupScheme.finiteInAffine_of_isAlgClosed_of_connected P.gluedOver

/-- Connectedness of the represented finite-stage group supplies orbit affineness over an
algebraically closed field.  No arbitrary-field closure is asserted here. -/
@[implicit_reducible]
noncomputable def
    pic0FiniteStageOrbitsInAffineOpen_of_isAlgClosed_of_connected
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1] [FiniteDimensional K P.N.1] [IsGalois K P.N.1]
    [IsAlgClosed P.N.1] [ConnectedSpace P.glueData.glued]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
  Scheme.orbitsInAffineOpen_of_finiteInAffine _
    (pic0FiniteStageFiniteInAffine_of_isAlgClosed_of_connected C Ck P rep)

/-- A finite-dimensional projective-space immersion makes the finite-stage glue
`FiniteInAffine`. -/
theorem pic0FiniteStageFiniteInAffine_of_isImmersion
    (P : Pic0FiniteStageGluePackage Ck F)
    {n : Type u} [Finite n]
    (i : P.glueData.glued ⟶ ℙ(n; Spec (.of P.N.1)))
    (hi : IsImmersion i) :
    Scheme.FiniteInAffine P.glueData.glued := by
  letI : IsImmersion i := hi
  exact Scheme.finiteInAffine_of_isImmersion i
    (Scheme.finiteInAffine_projectiveSpace n (Spec (.of P.N.1)))

/-- A finite-dimensional projective-space immersion supplies orbit affineness for the
canonical action attached to a representation of Picard zero by the finite-stage glue. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageOrbitsInAffineOpen_of_isImmersion
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1] [FiniteDimensional K P.N.1] [IsGalois K P.N.1]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver)
    {n : Type u} [Finite n]
    (i : P.glueData.glued ⟶ ℙ(n; Spec (.of P.N.1)))
    (hi : IsImmersion i) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen :=
  Scheme.orbitsInAffineOpen_of_finiteInAffine _
    (pic0FiniteStageFiniteInAffine_of_isImmersion Ck P i hi)

/-- Compatibility wrapper deriving the immersion input from projectivity of the finite-stage
glued morphism. -/
@[implicit_reducible]
noncomputable def pic0FiniteStageOrbitsInAffineOpen_of_isProjective
    (P : Pic0FiniteStageGluePackage Ck F)
    [Algebra K P.N.1] [FiniteDimensional K P.N.1] [IsGalois K P.N.1]
    (rep : (pic0TypeFunctor ((baseChange K P.N.1).obj C)).RepresentableBy P.gluedOver)
    (hproj : P.gluedMap.IsProjective) :
    (pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen := by
  obtain ⟨n, hn, i, hi, -⟩ := hproj
  letI : Finite n := hn
  letI : IsClosedImmersion i := hi
  exact pic0FiniteStageOrbitsInAffineOpen_of_isImmersion C Ck P rep i
    (inferInstance : IsImmersion i)

end

end AlgebraicGeometry
