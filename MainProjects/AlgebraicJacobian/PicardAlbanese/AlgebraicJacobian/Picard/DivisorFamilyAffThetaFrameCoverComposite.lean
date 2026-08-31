/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaFrameCover
import AlgebraicJacobian.Picard.DivisorFamilyAffAwayRep
import AlgebraicJacobian.Picard.DivisorFamilyAffClassDegree
import AlgebraicJacobian.Picard.DivisorFamilyZarGlueKit

/-!
# The widened certificate and frame cover on canonical carriers

This file composes the widened certificate cover with the carrier-free intrinsic-window frame
cover.  The intermediate frame localizations are transported to canonical away localizations
of the original base ring, and the numerator products are flattened to a finite spanning
family.  No chart typing or containment hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftAffThetaFrameCoverComposite :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

section WindowTransport

set_option linter.unusedSectionVars false

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable {S T B : Type u} [CommRing S] [Algebra k S]
variable [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
variable [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]

set_option maxHeartbeats 800000 in
-- The proof unfolds the quotient point over both legs of an arbitrary algebra tower.
/-- The carrier-free intrinsic-window point commutes with an arbitrary structure-compatible
map `T → B` over its base `S`. -/
theorem map_divisorWindowGrOfQuot_algHom
    (d : (relCurve C S).LocalEquations)
    [Module.Finite S ((S ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective S ((S ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) p = g)
    (β : T →ₐ[k] B)
    (hβ : β.toRingHom.comp (algebraMap S T) = algebraMap S B) :
    Module.Grassmannian.map β (divisorWindowGrOfQuot g a ha1 d T hrank)
      = divisorWindowGrOfQuot g a ha1 d B hrank := by
  letI : Algebra T B := β.toAlgebra
  letI : IsScalarTower k T B :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k _ _)
  haveI htowerS : IsScalarTower S T B := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact hβ.symm
  refine Module.Grassmannian.ext ?_
  rw [Module.Grassmannian.map_toSubmodule β
      (divisorWindowGrOfQuot g a ha1 d T hrank),
    divisorWindowGrOfQuot_toSubmodule]
  haveI : Module.Projective T
      ((T ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        windowBaseChange T (divisorWindow d ha1)) :=
    (divisorWindowGrOfQuot g a ha1 d T hrank).projective_quotient
  rw [Grassmannian.ker_baseChangeMkQ_eq_map_baseChange B
      (windowBaseChange T (divisorWindow d ha1)),
    divisorWindowGrOfQuot_toSubmodule]
  exact windowBaseChange_windowBaseChange T B (divisorWindow d ha1)

set_option maxHeartbeats 800000 in
-- The coordinate comparison instantiates `congrAmbient` and the quotient point on both legs.
/-- A coordinate frame for a carrier-free window over `T` transports along an arbitrary
structure-compatible map `T → B`. -/
theorem map_windowFrameOfQuot_toSubmodule {r : ℕ}
    (b : Module.Basis (Fin r) k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (d : (relCurve C S).LocalEquations)
    [Module.Finite S ((S ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective S ((S ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) p = g)
    (β : T →ₐ[k] B)
    (hβ : β.toRingHom.comp (algebraMap S T) = algebraMap S B)
    (y : Grassmannian.grFunctorAff k (Fin r → k) g T)
    (hy : y.toSubmodule = Submodule.map
      (LinearMap.baseChange T b.equivFun.toLinearMap)
      (windowBaseChange T (divisorWindow d ha1))) :
    (Module.Grassmannian.map β y).toSubmodule
      = Submodule.map (LinearMap.baseChange B b.equivFun.toLinearMap)
          (windowBaseChange B (divisorWindow d ha1)) := by
  have hyeq : y = congrAmbient b.equivFun
      (divisorWindowGrOfQuot g a ha1 d T hrank) := by
    refine Module.Grassmannian.ext ?_
    rw [hy, congrAmbient_toSubmodule, divisorWindowGrOfQuot_toSubmodule]
  rw [hyeq,
    map_congrAmbient β b.equivFun (divisorWindowGrOfQuot g a ha1 d T hrank),
    map_divisorWindowGrOfQuot_algHom g a ha1 d hrank β hβ,
    congrAmbient_toSubmodule, divisorWindowGrOfQuot_toSubmodule]

end WindowTransport

variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
variable {S : Type u} [CommRing S] [Algebra k S]

namespace CertifiedDivisorFamilyAff

set_option maxHeartbeats 2000000 in
-- The two off-diagonal quotient packages and their pullback naturality are instantiated at
-- both pinned windows.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Every certified widened family admits a finite pair-chart frame cover when the curve
parameter is independent of the certified divisor degree. -/
theorem exists_frameCover_at
    (F : CertifiedDivisorFamilyAff C S g)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    ∃ (m : ℕ) (f : Fin m → S), Ideal.span (Set.range f) = ⊤ ∧
      ∀ t : Fin m,
        ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
          (F.mapAlg (Localization.Away (f t)) g
            F.cover.hasAffineOverlaps_of_isProper).IsPairChartFramed
              hπ g b₁ b₂ i j w := by
  have hfin₁ := F.certified.finite_intrinsicWindowQuotient_at hπ hgamma hχgamma
    (relThetaPairH1_windowM C π hπ g) le_rfl
  have hproj₁ := F.certified.projective_intrinsicWindowQuotient_at
    (π := π) F.adaptation (windowM_choice π hπ g) hπ hgamma hχgamma
    (relThetaPairH1_windowM C π hπ g) le_rfl
  have hrank₁ := fun p : PrimeSpectrum S =>
    F.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := π) F.adaptation (windowM_choice π hπ g) hπ hgamma hχgamma
      (relThetaPairH1_windowM C π hπ g) le_rfl p
  have hfin₂ := F.certified.finite_intrinsicWindowQuotient_at hπ hgamma hχgamma
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  have hproj₂ := F.certified.projective_intrinsicWindowQuotient_at
    (π := π) F.adaptation
      (windowM_choice π hπ g + windowS_choice π hπ g) hπ hgamma hχgamma
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  have hrank₂ := fun p : PrimeSpectrum S =>
    F.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := π) F.adaptation
        (windowM_choice π hπ g + windowS_choice π hπ g) hπ hgamma hχgamma
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) p
  obtain ⟨m, f, hspan, hframe⟩ := divisorWindow_exists_frameCover
    hπ g r₁ r₂ b₁ b₂ F.eqns hfin₁ hproj₁ hrank₁ hfin₂ hproj₂ hrank₂
  refine ⟨m, f, hspan, fun t => ?_⟩
  obtain ⟨i, j, w, hw₁, hw₂⟩ := hframe t
  refine ⟨i, j, w, ?_⟩
  change (_ = Submodule.map _
      (divisorWindow
        (F.adaptation.pulledEquations (Localization.Away (f t))
          F.certified.projective_colength)
        (relThetaPairH1_windowM C π hπ g))) ∧
    (_ = Submodule.map _
      (divisorWindow
        (F.adaptation.pulledEquations (Localization.Away (f t))
          F.certified.projective_colength)
        (relThetaPairH1_windowMS C π hπ g)))
  constructor
  · rw [F.certified.divisorWindow_pulledEquations_eq_at
      (R' := Localization.Away (f t)) hπ hgamma hχgamma
      (relThetaPairH1_windowM C π hπ g) le_rfl]
    exact hw₁
  · rw [F.certified.divisorWindow_pulledEquations_eq_at
      (R' := Localization.Away (f t)) hπ hgamma hχgamma
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)]
    exact hw₂

end CertifiedDivisorFamilyAff

set_option maxHeartbeats 2400000 in
-- Both intrinsic windows are transported across an away-localization equivalence.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- One widened certified representative and one of its frame pieces transport to the
canonical away localization of the original base ring. -/
private theorem exists_certChart_piece_aff (F₀ : DivFamZarAff C S g)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (h₀ : S) [IsLocalization.Away h₀ A]
    (G₀ : CertifiedDivisorFamilyAff C A g)
    (hZ : G₀.toZarAff = DivFamZarAff.mapAlg A g F₀)
    (f₀ : A) (a₀ : S) (hassoc : Associated (algebraMap S A a₀) f₀)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away f₀)
    (hw : (G₀.mapAlg (Localization.Away f₀) g
      G₀.cover.hasAffineOverlaps_of_isProper).IsPairChartFramed hπ g b₁ b₂ i j w) :
    ∃ (G : CertifiedDivisorFamilyAff C (Localization.Away (a₀ * h₀)) g)
      (i' : (glueData k g r₁).J) (j' : (glueData k g r₂).J)
      (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] Localization.Away (a₀ * h₀)),
      G.toZarAff = DivFamZarAff.mapAlg (Localization.Away (a₀ * h₀)) g F₀ ∧
      G.IsPairChartFramed hπ g b₁ b₂ i' j' w' := by
  haveI hAwayNum : IsLocalization.Away (algebraMap S A a₀) (Localization.Away f₀) :=
    IsLocalization.Away.of_associated hassoc.symm
  haveI hAwayV : IsLocalization.Away (a₀ * h₀) (Localization.Away f₀) :=
    IsLocalization.Away.mul A (Localization.Away f₀) h₀ a₀
  let e : Localization.Away (a₀ * h₀) ≃ₐ[S] Localization.Away f₀ :=
    IsLocalization.algEquiv (Submonoid.powers (a₀ * h₀)) _ _
  let β : Localization.Away f₀ →ₐ[k] Localization.Away (a₀ * h₀) :=
    e.symm.toAlgHom.restrictScalars k
  letI : Algebra A (Localization.Away (a₀ * h₀)) :=
    (IsLocalization.Away.lift (S := A) h₀
      (g := algebraMap S (Localization.Away (a₀ * h₀)))
      (IsLocalization.Away.isUnit_of_dvd (x := a₀ * h₀) (dvd_mul_left h₀ a₀))).toAlgebra
  haveI : IsScalarTower S A (Localization.Away (a₀ * h₀)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k A (Localization.Away (a₀ * h₀)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  have hβ : β.toRingHom.comp (algebraMap A (Localization.Away f₀))
      = algebraMap A (Localization.Away (a₀ * h₀)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers h₀) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S A (Localization.Away f₀),
      RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp]
    exact AlgHom.comp_algebraMap e.symm.toAlgHom
  let hinf : G₀.cover.HasAffineOverlaps := G₀.cover.hasAffineOverlaps_of_isProper
  haveI hfin₁ := G₀.certified.finite_intrinsicWindowQuotient hπ hO hχ
    (relThetaPairH1_windowM C π hπ g) le_rfl
  haveI hproj₁ := G₀.certified.projective_intrinsicWindowQuotient
    (π := π) G₀.adaptation (windowM_choice π hπ g) hπ hO hχ
    (relThetaPairH1_windowM C π hπ g) le_rfl
  have hrank₁ := fun p : PrimeSpectrum A =>
    G₀.certified.rankAtStalk_intrinsicWindowQuotient
      (π := π) G₀.adaptation (windowM_choice π hπ g) hπ hO hχ
      (relThetaPairH1_windowM C π hπ g) le_rfl p
  haveI hfin₂ := G₀.certified.finite_intrinsicWindowQuotient hπ hO hχ
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  haveI hproj₂ := G₀.certified.projective_intrinsicWindowQuotient
    (π := π) G₀.adaptation
      (windowM_choice π hπ g + windowS_choice π hπ g) hπ hO hχ
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  have hrank₂ := fun p : PrimeSpectrum A =>
    G₀.certified.rankAtStalk_intrinsicWindowQuotient
      (π := π) G₀.adaptation
        (windowM_choice π hπ g + windowS_choice π hπ g) hπ hO hχ
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) p
  have hw₁ :
      (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away f₀) b₁.equivFun.toLinearMap)
            (windowBaseChange (Localization.Away f₀)
              (divisorWindow G₀.eqns (relThetaPairH1_windowM C π hπ g))) := by
    rw [← G₀.certified.divisorWindow_pulledEquations_eq
      (R' := Localization.Away f₀) hπ hO hχ
      (relThetaPairH1_windowM C π hπ g) le_rfl]
    exact hw.1
  have hw₂ :
      (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away f₀) b₂.equivFun.toLinearMap)
            (windowBaseChange (Localization.Away f₀)
              (divisorWindow G₀.eqns (relThetaPairH1_windowMS C π hπ g))) := by
    rw [← G₀.certified.divisorWindow_pulledEquations_eq
      (R' := Localization.Away f₀) hπ hO hχ
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)]
    exact hw.2
  refine ⟨G₀.mapAlg (Localization.Away (a₀ * h₀)) g hinf,
    i, j, β.comp w, ?_, ?_⟩
  · rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ]
    exact DivFamZarAff.mapAlg_comp A g (Localization.Away (a₀ * h₀)) F₀
  · change (_ = Submodule.map _
        (divisorWindow
          (G₀.adaptation.pulledEquations (Localization.Away (a₀ * h₀))
            G₀.certified.projective_colength)
          (relThetaPairH1_windowM C π hπ g))) ∧
      (_ = Submodule.map _
        (divisorWindow
          (G₀.adaptation.pulledEquations (Localization.Away (a₀ * h₀))
            G₀.certified.projective_colength)
          (relThetaPairH1_windowMS C π hπ g)))
    constructor
    · rw [G₀.certified.divisorWindow_pulledEquations_eq
        (R' := Localization.Away (a₀ * h₀)) hπ hO hχ
        (relThetaPairH1_windowM C π hπ g) le_rfl]
      have emap : Module.Grassmannian.map (β.comp w)
          (pairTautFst k g r₁ r₂ i j)
          = Module.Grassmannian.map β
              (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
        Module.Grassmannian.map_comp (f := w) (g := β)
          (N := pairTautFst k g r₁ r₂ i j)
      exact (congrArg Module.Grassmannian.toSubmodule emap).trans
        (map_windowFrameOfQuot_toSubmodule g (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) b₁ G₀.eqns hrank₁ β hβ
          (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) hw₁)
    · rw [G₀.certified.divisorWindow_pulledEquations_eq
        (R' := Localization.Away (a₀ * h₀)) hπ hO hχ
        (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)]
      have emap : Module.Grassmannian.map (β.comp w)
          (pairTautSnd k g r₁ r₂ i j)
          = Module.Grassmannian.map β
              (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
        Module.Grassmannian.map_comp (f := w) (g := β)
          (N := pairTautSnd k g r₁ r₂ i j)
      exact (congrArg Module.Grassmannian.toSubmodule emap).trans
        (map_windowFrameOfQuot_toSubmodule g
          (windowM_choice π hπ g + windowS_choice π hπ g)
          (relThetaPairH1_windowMS C π hπ g) b₂ G₀.eqns hrank₂ β hβ
          (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) hw₂)

set_option maxHeartbeats 2400000 in
-- Both off-diagonal intrinsic windows are transported across an away-localization equivalence.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- A framed widened representative transports to the canonical away localization when the
curve parameter is independent of its certified divisor degree. -/
private theorem exists_certChart_piece_aff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (h₀ : S) [IsLocalization.Away h₀ A]
    (G₀ : CertifiedDivisorFamilyAff C A g)
    (hZ : G₀.toZarAff = DivFamZarAff.mapAlg A g F₀)
    (f₀ : A) (a₀ : S) (hassoc : Associated (algebraMap S A a₀) f₀)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away f₀)
    (hw : (G₀.mapAlg (Localization.Away f₀) g
      G₀.cover.hasAffineOverlaps_of_isProper).IsPairChartFramed hπ g b₁ b₂ i j w) :
    ∃ (G : CertifiedDivisorFamilyAff C (Localization.Away (a₀ * h₀)) g)
      (i' : (glueData k g r₁).J) (j' : (glueData k g r₂).J)
      (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] Localization.Away (a₀ * h₀)),
      G.toZarAff = DivFamZarAff.mapAlg (Localization.Away (a₀ * h₀)) g F₀ ∧
      G.IsPairChartFramed hπ g b₁ b₂ i' j' w' := by
  haveI hAwayNum : IsLocalization.Away (algebraMap S A a₀) (Localization.Away f₀) :=
    IsLocalization.Away.of_associated hassoc.symm
  haveI hAwayV : IsLocalization.Away (a₀ * h₀) (Localization.Away f₀) :=
    IsLocalization.Away.mul A (Localization.Away f₀) h₀ a₀
  let e : Localization.Away (a₀ * h₀) ≃ₐ[S] Localization.Away f₀ :=
    IsLocalization.algEquiv (Submonoid.powers (a₀ * h₀)) _ _
  let β : Localization.Away f₀ →ₐ[k] Localization.Away (a₀ * h₀) :=
    e.symm.toAlgHom.restrictScalars k
  letI : Algebra A (Localization.Away (a₀ * h₀)) :=
    (IsLocalization.Away.lift (S := A) h₀
      (g := algebraMap S (Localization.Away (a₀ * h₀)))
      (IsLocalization.Away.isUnit_of_dvd (x := a₀ * h₀) (dvd_mul_left h₀ a₀))).toAlgebra
  haveI : IsScalarTower S A (Localization.Away (a₀ * h₀)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k A (Localization.Away (a₀ * h₀)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  have hβ : β.toRingHom.comp (algebraMap A (Localization.Away f₀))
      = algebraMap A (Localization.Away (a₀ * h₀)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers h₀) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S A (Localization.Away f₀),
      RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp]
    exact AlgHom.comp_algebraMap e.symm.toAlgHom
  let hinf : G₀.cover.HasAffineOverlaps := G₀.cover.hasAffineOverlaps_of_isProper
  haveI hfin₁ := G₀.certified.finite_intrinsicWindowQuotient_at
    hπ hgamma hχgamma (relThetaPairH1_windowM C π hπ g) le_rfl
  haveI hproj₁ := G₀.certified.projective_intrinsicWindowQuotient_at
    (π := π) G₀.adaptation (windowM_choice π hπ g) hπ hgamma hχgamma
    (relThetaPairH1_windowM C π hπ g) le_rfl
  have hrank₁ := fun p : PrimeSpectrum A =>
    G₀.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := π) G₀.adaptation (windowM_choice π hπ g) hπ hgamma hχgamma
      (relThetaPairH1_windowM C π hπ g) le_rfl p
  haveI hfin₂ := G₀.certified.finite_intrinsicWindowQuotient_at
    hπ hgamma hχgamma (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  haveI hproj₂ := G₀.certified.projective_intrinsicWindowQuotient_at
    (π := π) G₀.adaptation
      (windowM_choice π hπ g + windowS_choice π hπ g) hπ hgamma hχgamma
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  have hrank₂ := fun p : PrimeSpectrum A =>
    G₀.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := π) G₀.adaptation
        (windowM_choice π hπ g + windowS_choice π hπ g) hπ hgamma hχgamma
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) p
  have hw₁ :
      (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away f₀) b₁.equivFun.toLinearMap)
            (windowBaseChange (Localization.Away f₀)
              (divisorWindow G₀.eqns (relThetaPairH1_windowM C π hπ g))) := by
    rw [← G₀.certified.divisorWindow_pulledEquations_eq_at
      (R' := Localization.Away f₀) hπ hgamma hχgamma
      (relThetaPairH1_windowM C π hπ g) le_rfl]
    exact hw.1
  have hw₂ :
      (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away f₀) b₂.equivFun.toLinearMap)
            (windowBaseChange (Localization.Away f₀)
              (divisorWindow G₀.eqns (relThetaPairH1_windowMS C π hπ g))) := by
    rw [← G₀.certified.divisorWindow_pulledEquations_eq_at
      (R' := Localization.Away f₀) hπ hgamma hχgamma
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)]
    exact hw.2
  refine ⟨G₀.mapAlg (Localization.Away (a₀ * h₀)) g hinf,
    i, j, β.comp w, ?_, ?_⟩
  · rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ]
    exact DivFamZarAff.mapAlg_comp A g (Localization.Away (a₀ * h₀)) F₀
  · change (_ = Submodule.map _
        (divisorWindow
          (G₀.adaptation.pulledEquations (Localization.Away (a₀ * h₀))
            G₀.certified.projective_colength)
          (relThetaPairH1_windowM C π hπ g))) ∧
      (_ = Submodule.map _
        (divisorWindow
          (G₀.adaptation.pulledEquations (Localization.Away (a₀ * h₀))
            G₀.certified.projective_colength)
          (relThetaPairH1_windowMS C π hπ g)))
    constructor
    · rw [G₀.certified.divisorWindow_pulledEquations_eq_at
        (R' := Localization.Away (a₀ * h₀)) hπ hgamma hχgamma
        (relThetaPairH1_windowM C π hπ g) le_rfl]
      have emap : Module.Grassmannian.map (β.comp w)
          (pairTautFst k g r₁ r₂ i j)
          = Module.Grassmannian.map β
              (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
        Module.Grassmannian.map_comp (f := w) (g := β)
          (N := pairTautFst k g r₁ r₂ i j)
      exact (congrArg Module.Grassmannian.toSubmodule emap).trans
        (map_windowFrameOfQuot_toSubmodule g (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) b₁ G₀.eqns hrank₁ β hβ
          (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) hw₁)
    · rw [G₀.certified.divisorWindow_pulledEquations_eq_at
        (R' := Localization.Away (a₀ * h₀)) hπ hgamma hχgamma
        (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)]
      have emap : Module.Grassmannian.map (β.comp w)
          (pairTautSnd k g r₁ r₂ i j)
          = Module.Grassmannian.map β
              (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
        Module.Grassmannian.map_comp (f := w) (g := β)
          (N := pairTautSnd k g r₁ r₂ i j)
      exact (congrArg Module.Grassmannian.toSubmodule emap).trans
        (map_windowFrameOfQuot_toSubmodule g
          (windowM_choice π hπ g + windowS_choice π hπ g)
          (relThetaPairH1_windowMS C π hπ g) b₂ G₀.eqns hrank₂ β hβ
          (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) hw₂)

set_option maxHeartbeats 2400000 in
-- The dependent finite frame covers are flattened through the numerator-product span lemma.
include hO hχ in
/-- The widened analogue of `DivFamZar.exists_certChartCover`: a widened locally certified
class admits a finite spanning family of canonical away localizations carrying widened
certified representatives together with pair-chart framings. -/
theorem DivFamZarAff.exists_certChartCover (F₀ : DivFamZarAff C S g) :
    ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧
      ∀ p : Fin m,
        ∃ (G : CertifiedDivisorFamilyAff C (Localization.Away (r p)) g)
          (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (r p)),
          G.toZarAff = DivFamZarAff.mapAlg (Localization.Away (r p)) g F₀ ∧
          G.IsPairChartFramed hπ g b₁ b₂ i j w := by
  classical
  obtain ⟨mc, h, hspanH, hGl⟩ := DivFamZarAff.exists_certified_away_rep F₀
  choose Gl hZl using hGl
  have hFC := fun l : Fin mc =>
    (Gl l).exists_frameCover hπ g r₁ r₂ b₁ b₂ hO hχ
  choose mf f hspanF hframe using hFC
  choose ci cj cw hcw using hframe
  have hassoc : ∀ (l : Fin mc) (t : Fin (mf l)),
      Associated (algebraMap S (Localization.Away (h l))
        ((IsLocalization.Away.sec (h l) (f l t)).1)) (f l t) :=
    fun l t => IsLocalization.Away.associated_sec_fst (h l) (f l t)
  have hspanH' : Ideal.span
      (Set.range fun l : ULift.{u} (Fin mc) => h l.down) = ⊤ := by
    have hrange : (Set.range fun l : ULift.{u} (Fin mc) => h l.down)
        = Set.range h := ULift.down_surjective.range_comp h
    rw [hrange, hspanH]
  have hr : Ideal.span (Set.range
      fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
        (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1 * h p.1.down)
      = ⊤ :=
    span_range_num_mul_eq_top (fun l : ULift.{u} (Fin mc) => h l.down)
      (fun l => Localization.Away (h l.down)) hspanH'
      (fun l => f l.down) (fun l => hspanF l.down)
      (fun l t => (IsLocalization.Away.sec (h l.down) (f l.down t)).1)
      (fun l t => hassoc l.down t)
  let e : Fin (Fintype.card (Σ l : ULift.{u} (Fin mc), Fin (mf l.down)))
      ≃ Σ l : ULift.{u} (Fin mc), Fin (mf l.down) :=
    (Fintype.equivFin (Σ l : ULift.{u} (Fin mc), Fin (mf l.down))).symm
  refine ⟨Fintype.card (Σ l : ULift.{u} (Fin mc), Fin (mf l.down)),
    fun q => (IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1
      * h (e q).1.down, ?_, ?_⟩
  · have hrange : (Set.range fun q =>
        (IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1
          * h (e q).1.down)
        = Set.range (fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
            (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1
              * h p.1.down) :=
      e.surjective.range_comp
        (fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
          (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1 * h p.1.down)
    rw [hrange, hr]
  · intro q
    exact exists_certChart_piece_aff hπ g hO hχ r₁ r₂ b₁ b₂ F₀
      (h (e q).1.down) (Gl (e q).1.down) (hZl (e q).1.down)
      (f (e q).1.down (e q).2)
      ((IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1)
      (hassoc (e q).1.down (e q).2) (cw (e q).1.down (e q).2)
      (hcw (e q).1.down (e q).2)

set_option maxHeartbeats 2400000 in
-- The off-diagonal finite frame covers are flattened through the numerator-product span lemma.
/-- A widened locally certified class admits a finite certified pair-chart cover when the
curve parameter is independent of the divisor-family degree. -/
theorem DivFamZarAff.exists_certChartCover_at
    (F₀ : DivFamZarAff C S g) {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧
      ∀ p : Fin m,
        ∃ (G : CertifiedDivisorFamilyAff C (Localization.Away (r p)) g)
          (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (r p)),
          G.toZarAff = DivFamZarAff.mapAlg (Localization.Away (r p)) g F₀ ∧
          G.IsPairChartFramed hπ g b₁ b₂ i j w := by
  classical
  obtain ⟨mc, h, hspanH, hGl⟩ := DivFamZarAff.exists_certified_away_rep F₀
  choose Gl hZl using hGl
  have hFC := fun l : Fin mc =>
    (Gl l).exists_frameCover_at hπ g r₁ r₂ b₁ b₂ hgamma hχgamma
  choose mf f hspanF hframe using hFC
  choose ci cj cw hcw using hframe
  have hassoc : ∀ (l : Fin mc) (t : Fin (mf l)),
      Associated (algebraMap S (Localization.Away (h l))
        ((IsLocalization.Away.sec (h l) (f l t)).1)) (f l t) :=
    fun l t => IsLocalization.Away.associated_sec_fst (h l) (f l t)
  have hspanH' : Ideal.span
      (Set.range fun l : ULift.{u} (Fin mc) => h l.down) = ⊤ := by
    have hrange : (Set.range fun l : ULift.{u} (Fin mc) => h l.down)
        = Set.range h := ULift.down_surjective.range_comp h
    rw [hrange, hspanH]
  have hr : Ideal.span (Set.range
      fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
        (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1 * h p.1.down)
      = ⊤ :=
    span_range_num_mul_eq_top (fun l : ULift.{u} (Fin mc) => h l.down)
      (fun l => Localization.Away (h l.down)) hspanH'
      (fun l => f l.down) (fun l => hspanF l.down)
      (fun l t => (IsLocalization.Away.sec (h l.down) (f l.down t)).1)
      (fun l t => hassoc l.down t)
  let e : Fin (Fintype.card (Σ l : ULift.{u} (Fin mc), Fin (mf l.down)))
      ≃ Σ l : ULift.{u} (Fin mc), Fin (mf l.down) :=
    (Fintype.equivFin (Σ l : ULift.{u} (Fin mc), Fin (mf l.down))).symm
  refine ⟨Fintype.card (Σ l : ULift.{u} (Fin mc), Fin (mf l.down)),
    fun q => (IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1
      * h (e q).1.down, ?_, ?_⟩
  · have hrange : (Set.range fun q =>
        (IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1
          * h (e q).1.down)
        = Set.range (fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
            (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1
              * h p.1.down) :=
      e.surjective.range_comp
        (fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
          (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1 * h p.1.down)
    rw [hrange, hr]
  · intro q
    exact exists_certChart_piece_aff_at hπ g r₁ r₂ b₁ b₂ hgamma hχgamma F₀
      (h (e q).1.down) (Gl (e q).1.down) (hZl (e q).1.down)
      (f (e q).1.down (e q).2)
      ((IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1)
      (hassoc (e q).1.down (e q).2) (cw (e q).1.down (e q).2)
      (hcw (e q).1.down (e q).2)

end Curve

end AlgebraicGeometry
