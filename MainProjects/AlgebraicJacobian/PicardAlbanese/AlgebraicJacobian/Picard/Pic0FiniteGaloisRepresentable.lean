/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0GaloisInvariantMatch

/-!
# Conditional finite-Galois representability for Picard zero

This is a conditional producer: it descends a finite-level representative only
under the explicitly supplied orbit-in-an-affine-open instance.  It is not the
arbitrary-field representability endpoint.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicJacobian.GaloisDescent

namespace AlgebraicGeometry

noncomputable section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Conditional finite-Galois descent of a finite-level Picard-zero representative.

The orbit-in-an-affine-open instance is the sole extra descent hypothesis here;
this theorem does not claim arbitrary-field representability.
-/
noncomputable def pic0RepresentableBy_finiteGaloisDescent
    (C : Over (Spec (CommRingCat.of K)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    [FiniteDimensional K L] [IsGalois K L]
    {J : Over (Spec (CommRingCat.of L))}
    (rep : (pic0TypeFunctor ((baseChange K L).obj C)).RepresentableBy J)
    [((pic0SemilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen)] :
    (pic0TypeFunctor C).RepresentableBy
      (AlgebraicJacobian.GaloisDescent.StableAffineOpen.gluedQuotientOver
        (pic0SemilinearGalActionOfRepresentableBy C rep)) where
  homEquiv {T} :=
    ((StableAffineOpen.gluedQuotientOverHomEquiv
      (pic0SemilinearGalActionOfRepresentableBy C rep) T).trans
      (pic0GaloisInvariantEquivGaloisEquivariantOver C rep T).symm).trans
      (pic0GaloisInvariantEquiv (L := L) C T).symm
  homEquiv_comp {T T'} f v := by
    apply (pic0GaloisInvariantEquiv (L := L) C T).injective
    apply (pic0GaloisInvariantEquivGaloisEquivariantOver C rep T).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [StableAffineOpen.gluedQuotientOverHomEquiv_precomp]
    rw [pic0GaloisInvariantEquiv_precomp]
    rw [pic0GaloisInvariantEquivGaloisEquivariantOver_precomp]
    simp only [Equiv.apply_symm_apply]

end

end AlgebraicGeometry
