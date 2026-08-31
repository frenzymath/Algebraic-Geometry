/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Cohomology.DatumDescent
import AlgebraicJacobian.Cohomology.GluedSheafExtraction
import AlgebraicJacobian.Picard.PicRepColimitResidual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-!
# Cech Picard classes descend to finite subextensions

Over an algebraic field extension, every Cech Picard class on the base-changed curve is
defined over a finite intermediate extension.  The proof extracts a pinned basic-open
cocycle datum, descends its finitely many coefficients, and uses algebraicity to turn the
resulting finitely generated subalgebra into a finite intermediate field.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every Cech Picard class over an algebraic field extension is pulled back from a finite
subextension. -/
theorem exists_finSubext_cechPic_model
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] (π : C.left ⟶ P1 k) [IsFinite π]
    (c : (relCurve C K).CechPic) :
    ∃ L : DatG0.FinSubext k K, ∃ cL : (relCurve C L.1).CechPic,
      Scheme.CechPic.map (relCurveMap C L.1 K) cL = c := by
  classical
  obtain ⟨D, hD⟩ :=
    BasicOpenCocycleDatum.exists_cechPicClass_eq (C := C) (B := K) (π := π) c
  obtain ⟨A0, hA0, D0, hbase⟩ := D.exists_fg_subalgebra_baseChange_eq
  letI : Algebra.IsAlgebraic k A0 :=
    Algebra.IsAlgebraic.of_injective A0.val Subtype.val_injective
  let L0 : IntermediateField k K := Algebra.IsAlgebraic.toIntermediateField A0
  letI : Algebra.FiniteType k L0 := by
    change Algebra.FiniteType k A0
    exact (Subalgebra.fg_iff_finiteType A0).mp hA0
  letI : Module.Finite k L0 := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let L : DatG0.FinSubext k K := ⟨L0, inferInstance⟩
  refine ⟨L, D0.cechPicClass, ?_⟩
  rw [← hD]
  exact (BasicOpenCocycleDatum.descent_cechPicClass (C := C) hbase).symm

end AlgebraicGeometry
