/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0FiniteStageGluedComparison
import AlgebraicJacobian.Picard.Pic0RepresentableByTransport

/-!
# The finite-stage comparison in the slice category

The global glued comparison is compatible with the structure maps, so it is an
isomorphism in `Over (Spec k)`.  Consequently the scalar extension of the
finite-stage glued object represents Picard-zero over the separably closed field.

This is deliberately a post-base-change statement.  It does not assert that
the finite-stage object already represents Picard-zero over its field of definition;
that requires descent of the universal class and its Yoneda equivalence.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom] [IsSepClosed k]

namespace Pic0FiniteStageGluePackage

variable {F : Type u} [Field F] [Algebra F k] [Algebra.IsAlgebraic F k]

/-- The finite-stage glued comparison, promoted to the slice over the
separably closed base field. -/
noncomputable def finiteStageBaseChangeOverIso
    (P : Pic0FiniteStageGluePackage C F) :
    (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).obj P.gluedOver ≅
      (pic0_sepClosed_representableBy (C := C)).1 := by
  refine Over.isoMk (finiteStageBaseChangeIso C P) ?_
  change (finiteStageBaseChangeIso C P).hom ≫
      (pic0_sepClosed_representableBy (C := C)).1.hom =
    pullback.snd P.gluedMap
      (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))
  exact finiteStageBaseChangeIso_hom_structureMap C P

/-- After scalar extension to the separably closed field, the finite-stage
glued object represents Picard-zero. -/
noncomputable def pic0RepresentableBy_finiteStageBaseChange
    (P : Pic0FiniteStageGluePackage C F) :
    (pic0TypeFunctor C).RepresentableBy
      ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap P.N.1 k)))).obj P.gluedOver) :=
  CategoryTheory.Functor.RepresentableBy.ofObjectIso
    (pic0_sepClosed_representableBy (C := C)).2
    (finiteStageBaseChangeOverIso C P).symm

end Pic0FiniteStageGluePackage

end

end AlgebraicGeometry
