/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.GaloisQuotientOverlap
import AlgebraicJacobian.Picard.PicEtDescentNecessity

/-!
# Consuming the finite Galois quotient in Picard descent

This file connects the global quotient producer to the first representability
clause.  The explicit quotient and kernel-pair-cover hypotheses of
`seamClauseOne_of_isGaloisQuotient_lftFree` are discharged respectively by
`HasGaloisQuotient.exists_quotient` and the Galois graph cover.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PicScheme

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- Clause (1) of Picard representability after consuming the global finite
Galois quotient and its kernel-pair cover.  Compared with
`seamClauseOne_of_isGaloisQuotient_lftFree`, the explicit `hq` and `hcov`
arguments are gone. -/
theorem seamClauseOne_of_hasGaloisQuotient_lftFree
    [FiniteDimensional k k'] [IsGalois k k']
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    [(semilinearGalActionOfRepresentableBy C rep).OrbitsInAffineOpen]
    (hX' : LocallyOfFiniteType X'.hom) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom := by
  obtain ⟨Y, g, hq⟩ :=
    (inferInstance : AlgebraicJacobian.GaloisDescent.HasGaloisQuotient
      (semilinearGalActionOfRepresentableBy C rep)).exists_quotient
  exact seamClauseOne_of_isGaloisQuotient_lftFree
    (Y := Over.mk g) rep hq
    (AlgebraicJacobian.GaloisDescent.coverSelfSection_generate_mem_etaleTopology
      (k := k) (k' := k')) hX'

end AlgebraicGeometry.Scheme.PicScheme
