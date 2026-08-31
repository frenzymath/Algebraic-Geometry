/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DegreeZeroBaseField
import AlgebraicJacobian.Picard.Pic0Functor

/-!
# Degree at field-valued points after scalar extension

The degree of a relative Picard class at a field-valued point is unchanged after extending
that field-valued point along an arbitrary extension of the base field.  The zero-degree
corollary is the form needed when descending the fibrewise degree-zero condition.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-- Degree at a field-valued point is invariant under extension of that point's field. -/
theorem degAt_overSpecMap {T : Over (Spec (.of k))}
    (lam : picEt C T) {K L : Type u} [Field K] [Field L]
    [Algebra k K] [Algebra k L] (phi : K →ₐ[k] L)
    (t : overSpec k K ⟶ T) :
    degAt lam (Over.overSpecMap phi ≫ t) = degAt lam t := by
  rw [← degAt_picEtMap (C := C) t lam (Over.overSpecMap phi)]
  change PicEtAff.degAff L
      (picEtAffineEquiv C L
        (picEtMap C (Over.overSpecMap phi) (picEtMap C t lam))) =
    PicEtAff.degAff K (picEtAffineEquiv C K (picEtMap C t lam))
  rw [picEtAffineEquiv_naturality]
  letI : Algebra K L := phi.toRingHom.toAlgebra
  haveI : IsScalarTower k K L :=
    .of_algebraMap_eq fun x => (phi.commutes x).symm
  have hmap :
      PicEtAff.mapAlg C phi (picEtAffineEquiv C K (picEtMap C t lam)) =
        PicEtAff.map C L (picEtAffineEquiv C K (picEtMap C t lam)) := by
    unfold PicEtAff.mapAlg
    rfl
  rw [hmap, PicEtAff.degAff_map]

/-- The degree-zero condition can be checked after extending a field-valued point. -/
theorem degAt_overSpecMap_eq_zero_iff {T : Over (Spec (.of k))}
    (lam : picEt C T) {K L : Type u} [Field K] [Field L]
    [Algebra k K] [Algebra k L] (phi : K →ₐ[k] L)
    (t : overSpec k K ⟶ T) :
    degAt lam (Over.overSpecMap phi ≫ t) = 0 ↔ degAt lam t = 0 := by
  rw [degAt_overSpecMap]

end

end AlgebraicGeometry
