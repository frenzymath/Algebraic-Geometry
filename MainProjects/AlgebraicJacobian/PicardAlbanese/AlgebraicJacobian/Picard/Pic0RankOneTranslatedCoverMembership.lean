/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverPicZero
import AlgebraicJacobian.Picard.Pic0RankOneNativePresentationSplit

/-!
# Translated rank-one cover membership in the public locus

The separably closed translated-cover producer places every degree-zero field class, after
translation by a base-field class of degree `genus C`, in the genus-degree layer with a split
witness.  The split-class producer independently shows that a split field class belongs to
`PicRankOneOpen`, because each of its affine pullbacks receives a native presentation.

This file composes the two: the translated layer element itself is a member of the public
rank-one locus.  This is the phase-5 endpoint of the recovery route — the translated cover now
lands in the actual public interface rather than stopping at the fieldwise split witness.  No
new witness carrier is introduced; the statement re-exposes the exact translator-degree and
base-subtraction compatibility conjuncts needed by the future covering argument.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k]
variable {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

section Membership

variable [IsSepClosed k]
variable {K : Type u} [Field K] [Algebra k K]

/-- Phase-5 endpoint: over a separably closed base, every degree-zero class over a field
extension acquires, after translation by a base-field class of degree `genus C`, membership in
the public rank-one locus `PicRankOneOpen`.

The first conclusion is the translator degree; the second re-exposes the finite-support,
residue-degree-one, and base-subtraction compatibility of the exact subtraction divisor; the
last is the new content — the translated layer element belongs to `PicRankOneOpen`, i.e. every
affine pullback of it carries a native rank-one presentation. -/
theorem exists_sepClosedTranslated_mem_picRankOneOpen
    (pi : C.left ⟶ P1 k) [IsFinite pi]
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (mu : pic0Subgroup C (overSpec k K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L)
        (_ : Algebra.IsSeparable K L)
        (d : SepClosedTranslatedDropData (C := C) (L := L) mu.1)
        (r : SepClosedTranslatedDropResult (C := C) (L := L) mu.1 d),
      classDeg k (chartTwistClass C d.m r.Z) = (genus C : Int) ∧
        (Set.Finite (r.S.support : Set {x : (C ⊗ overSpec k L).left //
            x ≠ genericPoint (C ⊗ overSpec k L).left}) ∧
          (∀ p : {x : (C ⊗ overSpec k L).left //
              x ≠ genericPoint (C ⊗ overSpec k L).left},
            p ∈ r.S.support →
              (C ⊗ overSpec k L).left.residueDeg L p.1 = 1) ∧
          Scheme.CurveDivisor.picClass L r.S =
            Scheme.CechPic.map (relCurveMap C k L)
              ((chartTwistClass C 0 r.Z)⁻¹)) ∧
        r.rankOneLayer mu.1 d ∈ (PicRankOneOpen pi).obj (op (overSpec k K)) := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r, hdeg, hsupp, hsplit⟩ :=
    exists_sepClosedTranslatedRankOneLayer_pic0 (C := C) mu
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  exact ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r, hdeg, hsupp,
    mem_picRankOneOpen_of_isSplitWitness pi hpi _ hsplit⟩

end Membership

end

end AlgebraicGeometry
