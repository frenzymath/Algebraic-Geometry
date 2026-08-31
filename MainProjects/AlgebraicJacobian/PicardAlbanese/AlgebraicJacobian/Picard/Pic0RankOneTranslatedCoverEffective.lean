/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0RankOneTranslatedCoverGeneral
import AlgebraicJacobian.RiemannRoch.SectionBound

/-!
# Effective residual representatives for the translated rank-one cover

The greedy translated-drop package records `h⁰ = 1` for `W₀ - S`, but it does not
assert that this chosen divisor is effective.  A positive global section nevertheless
produces an effective representative of the same class.  This file exposes that
representative with its degree-genus certificate, while retaining the input class and
the existing translated `IsSplitWitness` consumer.
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

variable {k : Type u} [Field k] [IsSepClosed k]
variable {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

section ResidualRepresentative

variable {K L : Type u} [Field K] [Algebra k K]
  [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Module.Finite K L] [Algebra.IsSeparable K L]

/-! The product curve instances are the same base-change package used by the
general producer.  `exists_effective_of_h0_pos` does not require the finite
cohomology instances, so this bridge only installs the geometric hypotheses. -/

omit [IsSepClosed k] [Module.Finite K L] [Algebra.IsSeparable K L] in
theorem exists_effective_residual_degree_genus
    (μ : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) μ)
    (r : SepClosedTranslatedDropResult (C := C) (L := L) μ d) :
    ∃ E : ((C ⊗ overSpec k L).left).CurveDivisor,
      0 ≤ E ∧
        Scheme.CurveDivisor.deg L E = (d.genusValue : ℤ) ∧
        Scheme.CurveDivisor.picClass L E =
          Scheme.CurveDivisor.picClass L (d.W₀ - r.S) := by
  haveI : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L
  haveI : SmoothOfRelativeDimension 1
      (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instSmoothOfRelativeDimensionBaseChange C L
  haveI : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    instQuasiCompactBaseChange C L
  have hpos : 0 < Sheaf.h0
      ((C ⊗ overSpec k L).left.divisorSheaf L (d.W₀ - r.S)) := by
    rw [r.h0_one]
    norm_num
  obtain ⟨E, hE, hEc⟩ :=
    exists_effective_of_h0_pos (K := L) (d.W₀ - r.S) hpos
  have hdegResidual : Scheme.CurveDivisor.deg L (d.W₀ - r.S) =
      (d.genusValue : ℤ) := by
    rw [Scheme.CurveDivisor.deg_sub' L, d.hdeg, r.degree]
    ring
  exact ⟨E, hE,
    (deg_eq_deg_of_picClass_eq (K := L) hEc).trans hdegResidual,
    hEc⟩

/-! The general consumer keeps the finite separable extension and the exact
input class in scope, and adds the effective degree-genus representative to
the already landed translated-drop result. -/

theorem exists_sepClosedTranslatedDropEffective_general
    (μ : picEt C (overSpec k K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L)
        (_ : Algebra.IsSeparable K L)
        (d : SepClosedTranslatedDropData (C := C) (L := L) μ)
        (r : SepClosedTranslatedDropResult (C := C) (L := L) μ d)
        (E : ((C ⊗ overSpec k L).left).CurveDivisor),
      0 ≤ E ∧
        Scheme.CurveDivisor.deg L E = (d.genusValue : ℤ) ∧
        Scheme.CurveDivisor.picClass L E =
          Scheme.CurveDivisor.picClass L (d.W₀ - r.S) ∧
        IsSplitWitness C
          (μ * thetaFamily C (chartTwistClass C d.m r.Z) (overSpec k K)) := by
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, ⟨r⟩⟩ :=
    exists_sepClosedTranslatedDropResult_general (C := C) μ
  letI := hLfield
  letI := hkL
  letI := hKL
  letI := htow
  letI := hfin
  letI := hsep
  obtain ⟨E, hE, hEdeg, hEclass⟩ :=
    exists_effective_residual_degree_genus μ d r
  exact ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, d, r, E,
    hE, hEdeg, hEclass, r.translated⟩

end ResidualRepresentative

end

end AlgebraicGeometry
