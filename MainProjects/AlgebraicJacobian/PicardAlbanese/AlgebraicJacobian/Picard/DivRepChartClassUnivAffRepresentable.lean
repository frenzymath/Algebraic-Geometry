/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAffRange
import AlgebraicJacobian.Picard.DivRepChartClassUnivFree
import AlgebraicJacobian.Picard.DivisorFamilyAffDegreeZeroRep

/-!
# Representability of the widened divisor functor

The universal widened class on every divisor chart satisfies the classifier clause, hence
represents the positive-genus divisor functor by `DivScheme`.  The window bound follows from
nonzero genus.  In genus zero the widened functor is terminal, so choosing finite bases internally
gives an unconditional representer without adding a hypothesis to the curve data.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section Curve

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftDivRepChartClassUnivAffRepresentable :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g : Nat)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))

section Based

variable (r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

include hO hchi in
/-- For nonzero genus, the universal widened chart classes represent the divisor functor by
the existing divisor scheme. -/
noncomputable def divFunctorAff_representableBy_divScheme_of_ne_zero (hg : g ≠ 0) :
    (divFunctorAff C g).RepresentableBy DivOver := by
  let hb := windowBound_pos_of_genus_ne_zero pi hpi g hg hO hchi
  exact divFunctorAff_representableBy_of_chartClause hpi g hO hchi r1 r2 b1 b2
    (fun i j => PointwiseAchiever.divFamZarAffUniv C hpi g r1 r2 b1
      (b2.map (windowShiftEquiv hpi g).symm) i j hO hchi hb)
    (fun i j => PointwiseAchiever.isDivRepClassifyAff_divFamZarAffUniv
      C hpi g r1 r2 b1 b2 hO hchi i j hb)

omit hchi in
include hO in
/-- At independent curve parameter `gamma ≤ g`, the universal widened chart classes
represent the degree-`g` divisor functor by the existing divisor scheme. -/
noncomputable def divFunctorAff_representableBy_divScheme_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    (divFunctorAff C g).RepresentableBy DivOver :=
  divFunctorAff_representableBy_of_chartClause_at
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r1 := r1) (r2 := r2)
    (b1 := b1) (b2 := b2) (hOAt := hO) (gamma := gamma)
    (hgamma := hgamma) (hchiGamma := hchiGamma)
    (fun i j => PointwiseAchiever.divFamZarAffUniv_at C hpi g r1 r2 b1
      (b2.map (windowShiftEquiv hpi g).symm) i j hgamma hchiGamma)
    (fun i j => PointwiseAchiever.isDivRepClassifyAff_divFamZarAffUniv_at
      C hpi g r1 r2 b1 b2 i j hgamma hchiGamma)

end Based

omit hchi in
include hO in
/-- The degree-`g` widened divisor functor has a chosen representer when the curve Euler
parameter is any `gamma ≤ g`. The degree-zero branch remains the terminal object. -/
noncomputable def divFunctorAffRepresenter_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    Σ D : Over (Spec (.of k)), (divFunctorAff C g).RepresentableBy D := by
  classical
  clear hchi
  by_cases hg : g = 0
  · subst g
    exact ⟨Over.mk (𝟙 (Spec (.of k))),
      divFunctorAffZeroRepresentableBy (C := C) (pi := pi)⟩
  · let r1 := Module.finrank k
      ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤)
    let r2 := Module.finrank k ↥(divisorSections k
      ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤)
    let b1 : Module.Basis (Fin r1) k
        ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤) :=
      Module.finBasis k _
    let b2 : Module.Basis (Fin r2) k ↥(divisorSections k
        ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤) :=
      Module.finBasis k _
    exact ⟨divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
        (b2.map (windowShiftEquiv hpi g).symm),
      divFunctorAff_representableBy_divScheme_at
        (C := C) (pi := pi) (hpi := hpi) (g := g) (hO := hO)
        (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
        (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)⟩

include hO hchi in
/-- The diagonal widened divisor representer, specialized from the arbitrary-degree producer. -/
noncomputable def divFunctorAffRepresenter :
    Σ D : Over (Spec (.of k)), (divFunctorAff C g).RepresentableBy D :=
  divFunctorAffRepresenter_at (C := C) (pi := pi) (hpi := hpi) (g := g)
    (hO := hO) (gamma := g) (Nat.le_refl g) hchi

/-- A chosen scheme representing the widened divisor functor. -/
noncomputable def divRepAffScheme : Over (Spec (.of k)) :=
  (divFunctorAffRepresenter C hpi g hO hchi).1

omit hchi in
/-- A chosen scheme representing the degree-`g` widened divisor functor at independent
curve parameter `gamma ≤ g`. -/
noncomputable def divRepAffScheme_at {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    Over (Spec (.of k)) :=
  (divFunctorAffRepresenter_at (C := C) (pi := pi) (hpi := hpi) (g := g)
    (hO := hO) (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)).1

/-- The widened divisor functor is represented by its chosen scheme, with no genus or chart-basis
hypothesis. -/
noncomputable def divFunctorAff_representableBy :
    (divFunctorAff C g).RepresentableBy (divRepAffScheme C hpi g hO hchi) :=
  (divFunctorAffRepresenter C hpi g hO hchi).2

omit hchi in
/-- The degree-`g` widened divisor functor is represented at every independent curve
parameter `gamma ≤ g`. -/
noncomputable def divFunctorAff_representableBy_at
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int)) :
    (divFunctorAff C g).RepresentableBy
      (divRepAffScheme_at (C := C) (hpi := hpi) (g := g)
        (hO := hO) (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)) :=
  (divFunctorAffRepresenter_at (C := C) (pi := pi) (hpi := hpi) (g := g)
    (hO := hO) (gamma := gamma) (hgamma := hgamma) (hchiGamma := hchiGamma)).2

end Curve

end AlgebraicGeometry
