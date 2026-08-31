/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.Pic0ChartCoverageNoDrop
import AlgebraicJacobian.RiemannRoch.CoverageDrop
import AlgebraicJacobian.RiemannRoch.ThetaDegree

/-!
# The translated rank-one cover brick

This file records the part of the separably-closed cover argument that is already consumable by
the landed fibre API.  A `BaseFieldTranslationDrop` keeps the input class `lambda` in the
presentation equation, chooses its base-field translating class explicitly, and records the
positive-twist/point-subtraction output.  The consumer below turns that output into the exact
`IsSplitWitness` shape used by `chartLocus`.

The arbitrary-affine family of `PicRankOneLocalPresentation` objects required by
`PicRankOneOpen` is deliberately not inferred from `h0 = 1` and `H1 = 0`: no such producer is
landed in the current API.  The final theorem therefore exposes the field-level consumer and
keeps that family producer as an explicit integration obligation.
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

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The positive-twist input -/

section PositiveTwist

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]

/-- The FLV class theorem in the spelling used by the translated-cover lane.

The class `l` is the presenting class of the input fibre, while `theta` is the positive
base-field twist.  Keeping this as a named wrapper makes the positive-twist step visible at the
call site; it does not manufacture a presentation or hide the input class in an unrelated
existential. -/
theorem exists_positive_twist_vanishing
    (π : Y ⟶ P1 K) [IsFinite π] [IsDominant π]
    (hπ : π ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))
    (l θ : Y.CechPic) (hθ : 1 ≤ classDeg K θ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ W : Y.CurveDivisor,
      Scheme.CurveDivisor.picClass K W = l * θ ^ n →
        Subsingleton (Sheaf.HModule (Y.divisorSheaf K W) 1) := by
  exact exists_subsingleton_hModule_one_of_one_le_classDeg_of_isFinite_toP1
    π hπ l θ hθ

end PositiveTwist

/-! ## The lambda-tied drop package -/

section DropPackage

variable {K L : Type u} [Field K] [Algebra k K]
  [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Module.Finite K L] [Algebra.IsSeparable K L]

/-- Data for the positive twist and the subsequent point subtraction.

`hM₀` ties the splitting field presentation to the particular input `mu`; `hW₀` says that the
divisor being reduced is in the positive twist class (the chart index is zero at this stage).
`baseSubtraction` is intentionally an explicit class-level bridge: it says that the divisor
returned by the greedy reduction is represented by a base-field divisor.  The current tree has
the graph-class version of this bridge but no divisor pullback operation, so this hypothesis is
kept visible rather than replaced by a fieldwise existential. -/
structure SepClosedTranslatedDropData (μ : picEt C (overSpec k K)) where
  m : ℕ
  M₀ : (relCurve C L).CechPic
  hM₀ : PicEtAff.map C L (picEtAffineEquiv C K μ) =
    PicEtAff.unit C L (relPicMk C (overSpec k L) M₀)
  W₀ : ((C ⊗ overSpec k L).left).CurveDivisor
  hW₀ : Scheme.CurveDivisor.picClass L W₀ =
    M₀ * Scheme.CechPic.map (relCurveMap C k L)
      (chartTwistClass C m (0 : (C ⊗ overSpec k k).left.CurveDivisor))
  genusValue : ℕ
  excess : ℕ
  hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genusValue : ℤ)
  hdeg : Scheme.CurveDivisor.deg L W₀ = (genusValue : ℤ) + excess
  h1 : Subsingleton (Sheaf.HModule
    ((C ⊗ overSpec k L).left.divisorSheaf L W₀) 1)
  P : Set ((C ⊗ overSpec k L).left)
  hdense : ∀ U : ((C ⊗ overSpec k L).left).Opens,
    (U : Set ((C ⊗ overSpec k L).left)).Nonempty → (P ∩ U).Nonempty
  hPcl : ∀ x ∈ P, x ≠ genericPoint ((C ⊗ overSpec k L).left)
  hPdeg : ∀ x ∈ P, ((C ⊗ overSpec k L).left).residueDeg L x = 1
  baseSubtraction : ∀ (S : ((C ⊗ overSpec k L).left).CurveDivisor),
    0 ≤ S → Scheme.CurveDivisor.deg L S = (excess : ℤ) →
      (∀ (x : (C ⊗ overSpec k L).left) (hx : x ≠ genericPoint _),
        coeffAt hx S ≠ 0 → x ∈ P) →
      ∃ Z : (C ⊗ overSpec k k).left.CurveDivisor,
        Scheme.CurveDivisor.picClass L S =
          Scheme.CechPic.map (relCurveMap C k L)
            ((chartTwistClass C 0 Z)⁻¹)

/-- The output of the positive-twist/drop construction, tied to both the input class and the
base-field translating divisor.

The final field is the existing fibre consumer.  In particular, `S` is not merely a divisor
with the right cohomology: `baseClass` identifies its class with the base change of `Z`, and
`translated` is about `mu` translated by the resulting base-field class
`chartTwistClass C d.m Z`. -/
structure SepClosedTranslatedDropResult (μ : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) μ) where
  S : ((C ⊗ overSpec k L).left).CurveDivisor
  Z : (C ⊗ overSpec k k).left.CurveDivisor
  nonnegative : 0 ≤ S
  degree : Scheme.CurveDivisor.deg L S = (d.excess : ℤ)
  support : ∀ (x : (C ⊗ overSpec k L).left) (hx : x ≠ genericPoint _),
    coeffAt hx S ≠ 0 → x ∈ d.P
  baseClass : Scheme.CurveDivisor.picClass L S =
    Scheme.CechPic.map (relCurveMap C k L) ((chartTwistClass C 0 Z)⁻¹)
  h0_one : Sheaf.h0
    ((C ⊗ overSpec k L).left.divisorSheaf L (d.W₀ - S)) = 1
  h1_vanishing : Subsingleton (Sheaf.HModule
    ((C ⊗ overSpec k L).left.divisorSheaf L (d.W₀ - S)) 1)
  translated : IsSplitWitness C
    (μ * thetaFamily C (chartTwistClass C d.m Z) (overSpec k K))

/-- Positive twisting followed by point subtraction produces the exact field-level translated
rank-one witness.

The greedy theorem supplies `S`, `h0 = 1`, and preservation of `H1 = 0`.  The explicit
`baseSubtraction` bridge then supplies the base divisor `Z`; class arithmetic shows that
`W₀ - S` presents `mu` translated by the base-field class `chartTwistClass C d.m Z`.  The last
line applies the existing `IsSplitWitness` consumer, so no unrelated Picard class can satisfy
the conclusion. -/
theorem exists_sepClosedTranslatedDropResult
    (μ : picEt C (overSpec k K))
    (d : SepClosedTranslatedDropData (C := C) (L := L) μ) :
    Nonempty (SepClosedTranslatedDropResult (C := C) (L := L) μ d) := by
  obtain ⟨-, S, hS0, hSdeg, hSsupport, hS0one, hS1⟩ :=
    exists_isSplitWitness_of_drop C μ d.m
      (0 : (C ⊗ overSpec k k).left.CurveDivisor)
      d.genusValue d.excess d.hχ d.M₀ d.hM₀ d.W₀ d.hW₀ d.hdeg d.h1
      d.P d.hdense d.hPcl d.hPdeg
  obtain ⟨Z, hSZ⟩ := d.baseSubtraction S hS0 hSdeg hSsupport
  have hW : Scheme.CurveDivisor.picClass L (d.W₀ - S) =
      d.M₀ * Scheme.CechPic.map (relCurveMap C k L)
        (chartTwistClass C d.m Z) := by
    have hW₀ := d.hW₀
    unfold relCurveMap relCurve at hW₀ hSZ ⊢
    rw [sub_eq_add_neg, Scheme.CurveDivisor.picClass_add, Scheme.picClass_neg,
      hW₀, hSZ]
    simp only [map_inv, inv_inv]
    rw [mul_assoc, ← map_mul]
    simp only [chartTwistClass, Scheme.CurveDivisor.picClass_zero, inv_one, mul_one,
      pow_zero, one_mul]
  have htranslated : IsSplitWitness C
      (μ * thetaFamily C (chartTwistClass C d.m Z) (overSpec k K)) :=
    isSplitWitness_of_witness_twistClass C μ d.m Z d.M₀ d.hM₀
      (d.W₀ - S) hW hS1
  exact ⟨{
    S := S
    Z := Z
    nonnegative := hS0
    degree := hSdeg
    support := hSsupport
    baseClass := hSZ
    h0_one := hS0one
    h1_vanishing := hS1
    translated := htranslated
  }⟩

end DropPackage

end

end AlgebraicGeometry
