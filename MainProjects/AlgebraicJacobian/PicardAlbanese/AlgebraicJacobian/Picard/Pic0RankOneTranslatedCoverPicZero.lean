/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverLayer

/-!
# The translated rank-one cover on Picard degree zero

The general translated-drop producer accepts an arbitrary field-valued Picard class.  The
separably closed cover used for `Pic^0` needs one additional degree statement: when the input
class has degree zero, the base-field translating class itself has degree `genus C`.

This file derives that statement from the existing `rankOneLayer` degree certificate.  It also
records that the exact subtraction divisor used by `baseSubtraction` has finite support, residue
degree one at every support point, and the existing base-class identity.  No parallel witness
carrier is introduced, and membership in `PicRankOneOpen` remains contingent on the protected
arbitrary-affine local-presentation producer.
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

section Compatibility

variable {K L : Type u} [Field K] [Algebra k K] [Field L] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- For a degree-zero input, the base-field class which translates the input into the
rank-one layer has degree `genus C`.

The proof reads the degree of the exact translated class at the identity field point, then
separates its two factors.  The input contributes zero by `mu.2`, while the base-field factor
contributes its `classDeg` by `degAt_thetaFamily`. -/
theorem SepClosedTranslatedDropResult.translator_classDeg_of_pic0
    (mu : pic0Subgroup C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) mu.1)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) mu.1 d) :
    classDeg k (chartTwistClass C d.m r.Z) = (genus C : Int) := by
  have hdegree :=
    (r.rankOneLayer mu.1 d).2 K (CategoryTheory.CategoryStruct.id (overSpec k K))
  rw [SepClosedTranslatedDropResult.rankOneLayer_coe, degAt_mul,
    mu.2 K (CategoryTheory.CategoryStruct.id (overSpec k K)),
    degAt_thetaFamily, zero_add] at hdegree
  exact hdegree

end Compatibility

section PicZeroProducer

variable [IsSepClosed k]
variable {K : Type u} [Field K] [Algebra k K]

/-- The general per-field translated rank-one producer in the `Pic^0` indexing required by the
separably closed cover.

The output is the existing lambda-tied data/result pair.  Its first conclusion says that the
base-field translator has degree `genus C`; its second conclusion makes the precise
finite-support/residue-one/base-subtraction compatibility available; and its last conclusion is
the existing rank-one-layer `IsSplitWitness`.  Thus this is a specialization and immediate
consumer of the general producer, not a fieldwise replacement for `PicRankOneOpen`. -/
theorem exists_sepClosedTranslatedRankOneLayer_pic0
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
        IsSplitWitness C (r.rankOneLayer mu.1 d).1 := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r, hsplit⟩ :=
    exists_sepClosedTranslatedRankOneLayer_general (C := C) mu.1
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  exact ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r,
    r.translator_classDeg_of_pic0 mu d,
    r.baseSubtraction_compatibility mu.1 d,
    hsplit⟩

end PicZeroProducer

end

end AlgebraicGeometry
