/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneSplitMembership
import AlgebraicJacobian.Picard.Pic0ChartLocusIsoInvariance

/-!
# Isomorphic field base change preserves the rank-one locus

The public rank-one locus over a field is characterized by `IsSplitWitness`.  The latter is
invariant under an isomorphism of field extensions, so the locus membership itself is invariant
under the induced slice isomorphism.  This is a small consumer theorem for the translated-cover
and descent lanes; it does not assert invariance for arbitrary (non-invertible) field maps.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

theorem mem_picRankOneOpen_overSpecMap_iff
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {K K' : Type u} [Field K] [Algebra k K] [Field K'] [Algebra k K']
    (e : K ≃ₐ[k] K')
    (lam : picDegLayer C (genus C : ℤ) (overSpec k K)) :
    (picDegLayerFunctor C (genus C : ℤ)).map
        (Over.overSpecMap e.toAlgHom).op lam ∈
        (PicRankOneOpen pi).obj (op (overSpec k K')) ↔
      lam ∈ (PicRankOneOpen pi).obj (op (overSpec k K)) := by
  constructor
  · intro h
    have hs := isSplitWitness_of_mem_picRankOneOpen_field pi h
    change IsSplitWitness C (picEtMap C (Over.overSpecMap e.toAlgHom) lam.1) at hs
    have hsl : IsSplitWitness C lam.1 :=
      (isSplitWitness_map_overSpecMap_iff C e lam.1).mp hs
    exact mem_picRankOneOpen_of_isSplitWitness pi hpi lam hsl
  · intro h
    have hs0 : IsSplitWitness C lam.1 :=
      isSplitWitness_of_mem_picRankOneOpen_field pi h
    have hs : IsSplitWitness C
        (picEtMap C (Over.overSpecMap e.toAlgHom) lam.1) :=
      isSplitWitness_map_overSpecMap C e lam.1 hs0
    exact mem_picRankOneOpen_of_isSplitWitness pi hpi _ hs

end

end AlgebraicGeometry
