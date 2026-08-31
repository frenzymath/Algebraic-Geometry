/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartRangeAff

/-!
# The widened classifier-clause endpoint

`DivRepChartRangeAff` proves widened classifier surjectivity from a class on every carve chart
whose classifier is the chart map.  A universal certified family naturally supplies the
stronger characterizing clause `IsDivRepClassifyAff`, rather than that equality directly.
This file is the small bridge between those interfaces; it does not duplicate the atlas
factorization or away-span gluing.

## Main declarations

* `AlgebraicGeometry.DivRepChartFamilyAff.IsChartClause` -- every universal chart class
  satisfies the widened classifier clause at the canonical chart map.
* `AlgebraicGeometry.divRepClassifyZarAff_surjective_of_chartClause` -- the clause implies
  classifier surjectivity via the chart-range theorem.
* `AlgebraicGeometry.divFunctorAff_representableBy_of_chartClause` -- the final widened
  representability producer in the clause spelling.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepClassifyZarAffSurj :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

namespace DivRepChartFamilyAff

/-- Every supplied widened chart class is classified by its canonical chart map. -/
def IsChartClause
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g) : Prop :=
  ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
    IsDivRepClassifyAff hpi g r1 r2 b1 b2 (U i j) (ChartMap i j)

end DivRepChartFamilyAff

include hO hchi in
/-- The characterizing clause identifies the canonical classifier with the chart map. -/
theorem divRepClassifyZarAff_left_eq_chartMap
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : DivRepChartFamilyAff.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U)
    (i : (glueData k g r1).J) (j : (glueData k g r2).J) :
    (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 (ChartRing i j) (U i j)).left
      = ChartMap i j :=
  isDivRepClassifyAff_unique hpi g hO hchi r1 r2 b1 b2 (U i j)
    (divRepClassifyZarAff_isDivRepClassifyAff hpi g hO hchi r1 r2 b1 b2 (U i j))
    (hU i j)

include hO hchi in
/-- The clause form of the universal chart family implies affine classifier surjectivity. -/
theorem divRepClassifyZarAff_surjective_of_chartClause
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : DivRepChartFamilyAff.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] :
    Function.Surjective
      (divRepClassifyZarAff (C := C) (pi := pi) hpi g hO hchi r1 r2 b1 b2 S) :=
  fun v => exists_divRepClassifyZarAff_eq_of_chartRange
    hpi g hO hchi r1 r2 b1 b2 U
      (divRepClassifyZarAff_left_eq_chartMap hpi g hO hchi r1 r2 b1 b2 U hU) S v

include hO hchi in
/-- Universal widened chart classes satisfying the characterizing clause represent the
widened divisor functor by `DivScheme`. -/
noncomputable def divFunctorAff_representableBy_of_chartClause
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : DivRepChartFamilyAff.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U) :
    (divFunctorAff C g).RepresentableBy DivOver :=
  divFunctorAff_representableBy_of_chartRange hpi g hO hchi r1 r2 b1 b2 U
    (divRepClassifyZarAff_left_eq_chartMap hpi g hO hchi r1 r2 b1 b2 U hU)

/-- The characterizing clause identifies the off-diagonal classifier with the chart map. -/
theorem divRepClassifyZarAff_left_eq_chartMap_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : DivRepChartFamilyAff.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U)
    (i : (glueData k g r1).J) (j : (glueData k g r2).J) :
    (divRepClassifyZarAff_at (S := ChartRing i j) (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)).left = ChartMap i j :=
  isDivRepClassifyAff_unique_at (gamma := gamma)
    hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)
    (divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
      hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j))
    (hU i j)

/-- The clause form implies surjectivity of the classifier at an independent curve parameter. -/
theorem divRepClassifyZarAff_surjective_of_chartClause_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : DivRepChartFamilyAff.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U)
    (S : Type u) [CommRing S] [Algebra k S] :
    Function.Surjective
      (divRepClassifyZarAff_at (C := C) (pi := pi) (S := S) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma) :=
  fun v => exists_divRepClassifyZarAff_eq_of_chartRange_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma) U
    (divRepClassifyZarAff_left_eq_chartMap_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) U hU) S v

/-- Universal chart classes satisfying the clause represent the degree-`g` divisor functor
when the curve parameter is any `gamma ≤ g`. -/
noncomputable def divFunctorAff_representableBy_of_chartClause_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : DivRepChartFamilyAff.IsChartClause (hpi := hpi) g r1 r2 b1 b2 U) :
    (divFunctorAff C g).RepresentableBy DivOver :=
  divFunctorAff_representableBy_of_chartRange_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma) U
    (divRepClassifyZarAff_left_eq_chartMap_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma) U hU)

end Curve

end AlgebraicGeometry
