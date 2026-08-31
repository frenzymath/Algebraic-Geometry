/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCoaction
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaTripleProductBaseChange

/-!
# Coassociativity of intrinsic theta descent

The product comparison on triple intersections detects the two base-changed Cech faces.
For a triple `(i,j,l)`, the left face is read through the reversed overlap `(l,i)` and
the right face through `(l,j)`.  Restriction composition identifies those descriptions
with the existing pairwise comparison, while the three intrinsic restriction triangles
give the cocycle equality.

Everything here is attached to an already certified widened affine adaptation; no chart
containment or representability hypothesis is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsProper C.hom]
variable {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}

namespace AffAdaptation

attribute [local instance] thetaPieceSectionsModule thetaOverlapSectionsModule
  thetaTripleSectionsModule thetaPieceQuotientModule thetaOverlapQuotientModule
  thetaTripleQuotientModule thetaOverlapQuotientLeftModule
  thetaOverlapQuotientLeftTower thetaOverlapQuotientRightModule
  thetaOverlapQuotientRightTower productOverlapRightAlgebra
  productOverlapRightTower thetaPieceQuotientGluedModule
  thetaOverlapQuotientGluedModule chartProdPieceAlgebra
  chartProdOverlapAlgebra thetaPieceProdADModule thetaPieceProdCPModule
  thetaPieceProdTower thetaOverlapProdOvlModule thetaOverlapQuotientCPModule
  thetaOverlapProdCPModule thetaOverlapProdADModule thetaOverlapProdTower
  pieceThirdToTripleAlgebra thetaTripleQuotientPieceThirdModule
  chartProdPieceTripleThetaTower thetaTripleQuotientCPModule
  thetaTripleInnerCPModule thetaTripleProdCPModule

noncomputable section

variable (A : AffAdaptation D d) (a : ℕ)

omit [IsProper C.hom] in
/-- The triple intersection lies in the reversed pair consisting of its third and first
pieces. -/
theorem thetaTripleOpen_le_pair31 (i j l : D.index) :
    A.thetaTripleOpen i j l ≤ D.pieces l ⊓ D.pieces i := by
  intro x hx
  exact ⟨hx.2, hx.1.1⟩

omit [IsProper C.hom] in
/-- The triple intersection lies in the reversed pair consisting of its third and second
pieces. -/
theorem thetaTripleOpen_le_pair32 (i j l : D.index) :
    A.thetaTripleOpen i j l ≤ D.pieces l ⊓ D.pieces j := by
  intro x hx
  exact ⟨hx.2, hx.1.2⟩

/-- Restricting a third-piece coefficient through `(l,i)` agrees with direct restriction
to `(i,j,l)`. -/
theorem ovlToTriple_toOvlLeft_pair31 (i j l : D.index) (c : A.colength l) :
    A.ovlToTriple l i i j l (A.thetaTripleOpen_le_pair31 i j l)
        (A.toOvlLeft l i c) =
      A.pieceToTripleThird i j l c := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [A.toOvlLeft_mk, A.ovlToTriple_mk, A.pieceToTripleThird_mk]
  congr 1
  exact Scheme.resHom_resHom _ _ r

/-- Restricting a third-piece coefficient through `(l,j)` agrees with direct restriction
to `(i,j,l)`. -/
theorem ovlToTriple_toOvlLeft_pair32 (i j l : D.index) (c : A.colength l) :
    A.ovlToTriple l j i j l (A.thetaTripleOpen_le_pair32 i j l)
        (A.toOvlLeft l j c) =
      A.pieceToTripleThird i j l c := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [A.toOvlLeft_mk, A.ovlToTriple_mk, A.pieceToTripleThird_mk]
  congr 1
  exact Scheme.resHom_resHom _ _ r

/-- Pair-to-triple theta restriction is semilinear for the induced map on intrinsic
divisor quotient rings. -/
theorem thetaOverlapToTriple_smulColength
    (p q i j l : D.index)
    (h : A.thetaTripleOpen i j l ≤ D.pieces p ⊓ D.pieces q)
    (c : A.ovlColength p q)
    (x : A.ThetaOverlapQuotient (π := π) a p q) :
    A.thetaOverlapToTriple (π := π) a p q i j l h (c • x) =
      A.ovlToTriple p q i j l h c •
        A.thetaOverlapToTriple (π := π) a p q i j l h x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  change A.thetaOverlapToTriple (π := π) a p q i j l h (r • x) =
    relResAlgHom C R h r •
      A.thetaOverlapToTriple (π := π) a p q i j l h x
  exact (A.thetaOverlapToTriple (π := π) a p q i j l h).map_smulₛₗ r x

/-- A section of the first piece has the same triple restriction through `(i,j)` and
the reversed adjacent pair `(l,i)`. -/
theorem thetaToTriple_from_first_reversed (i j l : D.index)
    (x : A.ThetaPieceQuotient (π := π) a i) :
    A.thetaOverlapToTriple (π := π) a i j i j l
        (A.thetaTripleOpen_le_pair12 i j l)
        (A.thetaToOverlapLeft (π := π) a i j x) =
      A.thetaOverlapToTriple (π := π) a l i i j l
        (A.thetaTripleOpen_le_pair31 i j l)
        (A.thetaToOverlapRight (π := π) a l i x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapLeft_mk, A.thetaToOverlapRight_mk,
        A.thetaOverlapToTriple_mk, A.thetaOverlapToTriple_mk,
        secRes_secRes, secRes_secRes]

/-- A section of the second piece has the same triple restriction through `(i,j)` and
the reversed adjacent pair `(l,j)`. -/
theorem thetaToTriple_from_second_reversed (i j l : D.index)
    (x : A.ThetaPieceQuotient (π := π) a j) :
    A.thetaOverlapToTriple (π := π) a i j i j l
        (A.thetaTripleOpen_le_pair12 i j l)
        (A.thetaToOverlapRight (π := π) a i j x) =
      A.thetaOverlapToTriple (π := π) a l j i j l
        (A.thetaTripleOpen_le_pair32 i j l)
        (A.thetaToOverlapRight (π := π) a l j x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapRight_mk, A.thetaToOverlapRight_mk,
        A.thetaOverlapToTriple_mk, A.thetaOverlapToTriple_mk,
        secRes_secRes, secRes_secRes]

/-- A section of the third piece has the same triple restriction through the two reversed
adjacent pairs `(l,i)` and `(l,j)`. -/
theorem thetaToTriple_from_third_reversed (i j l : D.index)
    (x : A.ThetaPieceQuotient (π := π) a l) :
    A.thetaOverlapToTriple (π := π) a l i i j l
        (A.thetaTripleOpen_le_pair31 i j l)
        (A.thetaToOverlapLeft (π := π) a l i x) =
      A.thetaOverlapToTriple (π := π) a l j i j l
        (A.thetaTripleOpen_le_pair32 i j l)
        (A.thetaToOverlapLeft (π := π) a l j x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      rw [A.thetaToOverlapLeft_mk, A.thetaToOverlapLeft_mk,
        A.thetaOverlapToTriple_mk, A.thetaOverlapToTriple_mk,
        secRes_secRes, secRes_secRes]

set_option maxHeartbeats 1000000 in
-- Both finite-product comparisons are expanded on pure tensors in this detector formula.
set_option synthInstance.maxHeartbeats 500000 in
-- The chart, overlap, and triple quotient module towers are all dependent on the indices.
/-- After the triple-product comparison, the base-changed left face is restriction of the
pairwise comparison through the reversed overlap `(l,i)`. -/
theorem IsCertified.thetaTriple_leftFace_apply {n : ℕ}
    (hc : A.IsCertified n)
    (z : A.chartProd ⊗[gluedSubalgebra A] A.ThetaPieceProd (π := π) a)
    (p : D.index × D.index) (l : D.index) :
    hc.thetaOverlapProdBaseChangeToTripleEquiv A a
        (((A.thetaIntrinsicDeltaLeftCP (π := π) a).restrictScalars
          (gluedSubalgebra A)).baseChange A.chartProd z) p l =
      A.thetaOverlapToTriple (π := π) a l p.1 p.1 p.2 l
        (A.thetaTripleOpen_le_pair31 p.1 p.2 l)
        (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc z
          (l, p.1)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul b s =>
      rw [LinearMap.baseChange_tmul]
      rw [hc.thetaOverlapProdBaseChangeToTripleEquiv_tmul_apply]
      simp only [LinearMap.coe_restrictScalars]
      rw [A.thetaIntrinsicDeltaLeftCP_apply]
      rw [A.thetaPieceProdBaseChangeToOverlapEquiv_tmul]
      rw [A.thetaOverlapToTriple_smulColength]
      rw [A.ovlToTriple_toOvlLeft_pair31]
      rw [A.thetaToTriple_from_first_reversed]

set_option maxHeartbeats 1000000 in
-- Both finite-product comparisons are expanded on pure tensors in this detector formula.
set_option synthInstance.maxHeartbeats 500000 in
-- The chart, overlap, and triple quotient module towers are all dependent on the indices.
/-- After the triple-product comparison, the base-changed right face is restriction of the
pairwise comparison through the reversed overlap `(l,j)`. -/
theorem IsCertified.thetaTriple_rightFace_apply {n : ℕ}
    (hc : A.IsCertified n)
    (z : A.chartProd ⊗[gluedSubalgebra A] A.ThetaPieceProd (π := π) a)
    (p : D.index × D.index) (l : D.index) :
    hc.thetaOverlapProdBaseChangeToTripleEquiv A a
        ((A.thetaIntrinsicDeltaRightGlued (π := π) a).baseChange
          A.chartProd z) p l =
      A.thetaOverlapToTriple (π := π) a l p.2 p.1 p.2 l
        (A.thetaTripleOpen_le_pair32 p.1 p.2 l)
        (A.thetaPieceProdBaseChangeToOverlapEquiv (π := π) a hc z
          (l, p.2)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul b s =>
      rw [LinearMap.baseChange_tmul]
      rw [hc.thetaOverlapProdBaseChangeToTripleEquiv_tmul_apply]
      change A.pieceToTripleThird p.1 p.2 l (b l) •
          A.thetaOverlapToTriple (π := π) a p.1 p.2 p.1 p.2 l
            (A.thetaTripleOpen_le_pair12 p.1 p.2 l)
            (A.thetaToOverlapRight (π := π) a p.1 p.2 (s p.2)) = _
      rw [A.thetaPieceProdBaseChangeToOverlapEquiv_tmul]
      rw [A.thetaOverlapToTriple_smulColength]
      rw [A.ovlToTriple_toOvlLeft_pair32]
      rw [A.thetaToTriple_from_second_reversed]

set_option maxHeartbeats 1000000 in
-- The injective triple-product detector expands both base-changed face formulas.
set_option synthInstance.maxHeartbeats 500000 in
-- All three dependent coordinate module towers are retained in the comparison.
/-- The two base-changed intrinsic Cech faces agree on every theta coaction value. -/
theorem IsCertified.thetaIntrinsic_baseChange_faces_coaction {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a) :
    ((A.thetaIntrinsicDeltaLeftCP (π := π) a).restrictScalars
        (gluedSubalgebra A)).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) =
      (A.thetaIntrinsicDeltaRightGlued (π := π) a).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) := by
  apply (hc.thetaOverlapProdBaseChangeToTripleEquiv A a).injective
  funext p l
  rw [hc.thetaTriple_leftFace_apply A a, hc.thetaTriple_rightFace_apply A a]
  rw [A.thetaPieceProdBaseChangeToOverlapEquiv_coaction_apply
    (π := π) a hc s (l, p.1)]
  rw [A.thetaPieceProdBaseChangeToOverlapEquiv_coaction_apply
    (π := π) a hc s (l, p.2)]
  exact A.thetaToTriple_from_third_reversed (π := π) a p.1 p.2 l (s l)

set_option maxHeartbeats 1000000 in
-- The coassociativity criterion transports through the pairwise and triple comparisons.
set_option synthInstance.maxHeartbeats 500000 in
-- The source and both iterated base changes carry dependent product module structures.
/-- The intrinsic theta coaction satisfies the coassociativity law of module descent. -/
theorem IsCertified.thetaDescentCoaction_coassoc {n : ℕ}
    (hc : A.IsCertified n) (s : A.ThetaPieceProd (π := π) a) :
    ((A.thetaDescentCoaction (π := π) a hc).restrictScalars
        (gluedSubalgebra A)).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) =
      (TensorProduct.mk (gluedSubalgebra A) A.chartProd
        (A.ThetaPieceProd (π := π) a) 1).baseChange A.chartProd
        (A.thetaDescentCoaction (π := π) a hc s) := by
  exact (A.thetaDescentCoaction_coassoc_iff_baseChange_faces
    (π := π) a hc s).2
      (hc.thetaIntrinsic_baseChange_faces_coaction A a s)

set_option synthInstance.maxHeartbeats 500000 in
-- Packaging retains the dependent product module and scalar-tower instances.
/-- The product of local intrinsic theta lines with its canonical faithfully-flat descent
datum. -/
noncomputable def IsCertified.thetaDescentDatum {n : ℕ}
    (hc : A.IsCertified n) :
    Module.DescentDatum (gluedSubalgebra A) A.chartProd
      (A.ThetaPieceProd (π := π) a) where
  coaction := A.thetaDescentCoaction (π := π) a hc
  counit := A.thetaDescentCoaction_counit (π := π) a hc
  coassoc := hc.thetaDescentCoaction_coassoc A a

end


end AffAdaptation

end AlgebraicGeometry
