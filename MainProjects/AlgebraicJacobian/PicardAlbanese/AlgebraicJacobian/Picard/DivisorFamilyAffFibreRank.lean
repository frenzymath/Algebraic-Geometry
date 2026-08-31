/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFibreData
import AlgebraicJacobian.Picard.DivSchemeSeedUnivFibre

/-!
# Fibre rank of the widened divisor window

A widened certified adaptation cuts a degree-`g` divisor on every field-valued fibre.
At a high theta window, the function-field dictionary identifies the complete window
with `H^0(O(N(a)))` and its divisor window with `H^0(O(N(a) - d_K))`.  Both divisors
have vanishing `H^1`, so Riemann--Roch and `deg(d_K) = g` show that the quotient has
dimension `g`.

The theorem below is intrinsic to the cover-independent `divisorWindow`.  In particular,
it does not add a chart-typing premise or transport the widened certificate to an auxiliary
chart adaptation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule
  Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (R : Type u) [CommRing R] [Algebra k R]
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

section FibreRank

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [IsDominant pi] [IsIntegral C.left]

attribute [local instance] instOverCleftWFT

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]

noncomputable local instance instIsIntegralRelCurveAffRank (K : Type u) [Field K]
    [Algebra k K] : IsIntegral (relCurve C K) :=
  instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveAffRank (K : Type u) [Field K]
    [Algebra k K] :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveAffRank (K : Type u) [Field K]
    [Algebra k K] : QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveAffRank (K : Type u) [Field K]
    [Algebra k K] : LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveAffRank (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K
      (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveAffRank (K : Type u) [Field K]
    [Algebra k K] : Module.Finite K
      (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

omit [IsDominant pi] [IsIntegral C.left] in
set_option linter.unusedSectionVars false in
private lemma chi_relCurve_of_chi_aff_rank (g : Nat)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    (K : Type u) [Field K] [Algebra k K] :
    Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : Int) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have h1 : Sheaf.chi ((relCurve C K).moduleKSheaf K)
      = 1 - (genus (baseChangeBundle C K) : Int) :=
    chi_moduleKSheaf (baseChangeBundle C K)
  have h2 : genus (baseChangeBundle C K) = genus C := genus_baseField C K
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : Int) :=
    chi_moduleKSheaf C
  have h4 : (genus C : Int) = (g : Int) := by
    rw [h3] at hchi
    linarith
  rw [h1, h2, h4]

namespace AffAdaptation

/-- On every field-valued fibre, the cover-independent high-window quotient cut out by a
widened degree-`g` certificate has dimension exactly `g`. -/
theorem IsCertified.finrank_windowQuotient_pulledEquations
    {K : Type u} [Field K] [Algebra k K]
    [Algebra R K] [IsScalarTower k R K]
    {D : AffCoverData C R} {d : (relCurve C R).LocalEquations}
    {A : AffAdaptation D d} {g : Nat} (hc : A.IsCertified g)
    (hpi : pi ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
    {a : Nat} (ha1 : Subsingleton (relTwistPair C k pi (relThetaCocycle C k pi a)).H1)
    (hMa : windowM_choice pi hpi g ≤ a) :
    Module.finrank K
      ((K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
        divisorWindow (A.pulledEquations K hc.projective_colength) ha1) = g := by
  let dK := A.pulledEquations K hc.projective_colength
  let E := Scheme.presentationDivisor K dK.presentation
  change Module.finrank K
    ((K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤)) ⧸
      divisorWindow dK ha1) = g
  have hchiK : Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : Int) :=
    chi_relCurve_of_chi_aff_rank C g hchi K
  have hdeg : Scheme.CurveDivisor.deg K E = (g : Int) := by
    dsimp [E, dK]
    exact hc.deg_presentationDivisor_pulledEquations (C := C) (R := R) (K := K)
  have hN1 : Subsingleton (Sheaf.HModule
      ((relCurve C K).divisorSheaf K (windowTransportDivisor C K pi a)) 1) :=
    subsingleton_h1_windowTransportDivisor C K pi a ha1
  have hE1 : Subsingleton (Sheaf.HModule ((relCurve C K).divisorSheaf K
      (windowTransportDivisor C K pi a - E)) 1) :=
    subsingleton_h1_windowTransportDivisor_sub C pi hpi K g a
      ha1 hMa hO hchi hchiK E (by rw [hdeg]; omega)
  have hNrr :
      (Sheaf.h0 ((relCurve C K).divisorSheaf K
        (windowTransportDivisor C K pi a)) : Int)
        = Scheme.CurveDivisor.deg K (windowTransportDivisor C K pi a)
          + Sheaf.chi ((relCurve C K).moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ hN1
  have hErr :
      (Sheaf.h0 ((relCurve C K).divisorSheaf K
        (windowTransportDivisor C K pi a - E)) : Int)
        = Scheme.CurveDivisor.deg K (windowTransportDivisor C K pi a - E)
          + Sheaf.chi ((relCurve C K).moduleKSheaf K) :=
    h0_eq_deg_add_chi_of_subsingleton_hModule_one _ hE1
  have hamb : Module.finrank K
      (K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤))
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowTransportDivisor C K pi a)) := by
    calc
      Module.finrank K
          (K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor pi) ⊤))
          = Module.finrank K ↥(⊤ : Submodule K
              (K ⊗[k] ↥(Scheme.divisorSections k
                (a • fiberWeilDivisor pi) ⊤))) := by simp
      _ = Module.finrank K ↥(Submodule.map (divFamPhi C K pi a ha1) ⊤) :=
        (finrank_map_divFamPhi C K pi a ha1 ⊤).symm
      _ = Module.finrank K ↥(Scheme.divisorSections K
          (windowTransportDivisor C K pi a) ⊤) := by
        rw [map_divFamPhi_top C K pi a ha1]
      _ = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowTransportDivisor C K pi a)) :=
        finrank_divisorSections_top K _
  have hker : Module.finrank K ↥(divisorWindow dK ha1)
      = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowTransportDivisor C K pi a - E)) := by
    calc
      Module.finrank K ↥(divisorWindow dK ha1)
          = Module.finrank K ↥(Submodule.map (divFamPhi C K pi a ha1)
              (divisorWindow dK ha1)) :=
        (finrank_map_divFamPhi C K pi a ha1 _).symm
      _ = Module.finrank K ↥(Scheme.divisorSections K
          (windowTransportDivisor C K pi a - E) ⊤) := by
        rw [map_divFamPhi_divisorWindow C K pi a ha1 dK]
      _ = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowTransportDivisor C K pi a - E)) :=
        finrank_divisorSections_top K _
  have hdiffZ :
      (Sheaf.h0 ((relCurve C K).divisorSheaf K
        (windowTransportDivisor C K pi a - E)) : Int) + (g : Int)
        = (Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowTransportDivisor C K pi a)) : Int) := by
    rw [hErr, hNrr, sub_eq_add_neg, Scheme.CurveDivisor.deg_add,
      Scheme.CurveDivisor.deg_neg, hdeg]
    ring
  have hdiff :
      Sheaf.h0 ((relCurve C K).divisorSheaf K
        (windowTransportDivisor C K pi a - E)) + g
        = Sheaf.h0 ((relCurve C K).divisorSheaf K
          (windowTransportDivisor C K pi a)) := by
    exact_mod_cast hdiffZ
  have hq := Submodule.finrank_quotient_add_finrank (divisorWindow dK ha1)
  rw [hker, hamb] at hq
  omega

end AffAdaptation

end FibreRank

end AlgebraicGeometry
