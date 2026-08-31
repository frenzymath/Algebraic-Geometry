/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationSplit
import AlgebraicJacobian.Picard.Pic0RankOneSplitOfPresentation

/-!
# The fibrewise split-witness characterization of the public rank-one locus

Two consumer packagings of the landed rank-one openness bricks.

* `AlgebraicGeometry.mem_picRankOneOpen_iff_isSplitWitness` — the **fibrewise
  characterization at a field**: for a field base `K/k`, membership of a genus-degree class in
  the public rank-one locus `PicRankOneOpen` is equivalent to the class being a split witness.
  This simply pairs the two landed directions
  `mem_picRankOneOpen_of_isSplitWitness` (from `Pic0RankOneNativePresentationSplit`) and
  `isSplitWitness_of_mem_picRankOneOpen_field` (from `Pic0RankOneSplitOfPresentation`).

* `AlgebraicGeometry.isSplitWitness_testPoint_of_mem` — the **pointwise consequence at an
  arbitrary test**: a class living in the rank-one locus over any test `T` has a split-witness
  fibre at every point `t : T.left`.  The membership is pulled back along the affine field
  point `Over.testPoint t` by `picRankOneOpen_map_mem`, landing at the field
  `Over.testPointField t`, and the field converse then applies.  The underlying picard class
  of the pulled-back layer element is `picEtMap C (Over.testPoint t) lam.1` by definition of
  `picDegLayerFunctor`'s `map`.
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

/-- **The fibrewise split-witness characterization of `PicRankOneOpen` at a field.**

For a field base `K/k`, a genus-degree Picard class `lam` over `overSpec k K` belongs to the
public rank-one locus if and only if it is a split witness.  This is the conjunction of the two
landed directions: `isSplitWitness_of_mem_picRankOneOpen_field` (membership tested with the
identity produces a presentation, hence a split witness) and
`mem_picRankOneOpen_of_isSplitWitness` (a split field class receives the required native
presentation on every affine pullback, using `hpi`). -/
theorem mem_picRankOneOpen_iff_isSplitWitness
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    {K : Type u} [Field K] [Algebra k K]
    (lam : picDegLayer C (genus C : ℤ) (overSpec k K)) :
    lam ∈ (PicRankOneOpen pi).obj (op (overSpec k K)) ↔ IsSplitWitness C lam.1 :=
  ⟨fun h => isSplitWitness_of_mem_picRankOneOpen_field pi h,
   fun hsplit => mem_picRankOneOpen_of_isSplitWitness pi hpi lam hsplit⟩

/-- **Every point of a rank-one-open class has a split-witness fibre.**

For an arbitrary test `T` and a class `lam` of the degree-`genus C` layer that lies in the public
rank-one locus over `T`, the fibre of `lam` at any point `t : T.left` — read at the residue field
`Over.testPointField t` through the affine field point `Over.testPoint t` — is a split witness.

The membership is stable under pullback (`picRankOneOpen_map_mem`) along `(Over.testPoint t).op`,
which lands at the field base `overSpec k (Over.testPointField t)`; the field converse
`isSplitWitness_of_mem_picRankOneOpen_field` then applies.  The underlying picard class of the
pulled-back layer element is `picEtMap C (Over.testPoint t) lam.1` by definition of
`picDegLayerFunctor`'s `map`, so no explicit rewrite is needed. -/
theorem isSplitWitness_testPoint_of_mem
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    {T : Over (Spec (.of k))}
    {lam : (picDegLayerFunctor C (genus C : ℤ)).obj (op T)}
    (h : lam ∈ (PicRankOneOpen pi).obj (op T))
    (t : T.left) :
    IsSplitWitness C (picEtMap C (Over.testPoint t) lam.1) :=
  isSplitWitness_of_mem_picRankOneOpen_field pi
    (picRankOneOpen_map_mem pi (Over.testPoint t).op h)

end

end AlgebraicGeometry
