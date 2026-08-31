/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaWindowBaseChange
import AlgebraicJacobian.Picard.DivisorFamilyAffFrameCover
import AlgebraicJacobian.Picard.DivisorFamilyAffMapAlg

/-!
# A carrier-free frame cover for the two intrinsic divisor windows

The frame-cover argument depends only on finite-projective constant-rank data for the two
window quotients.  This file assembles the carrier-free atoms from
`DivisorFamilyAffFrameCover` into the finite pair-chart cover needed by divisor
representability.  Its input is a raw system of local equations; no adaptation, chart typing,
or containment hypothesis appears.
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

noncomputable local instance instOverCleftAffThetaFrameCover :
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
variable {R : Type u} [CommRing R] [Algebra k R]

set_option maxHeartbeats 800000 in
-- The transport instantiates the Grassmannian comparison over two localizations.
/-- Transport one matrix presentation to the numerator-stage localization and factor it
through its Grassmannian chart. -/
private theorem map_component_chart_of_windowQuot {a r : ℕ}
    (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (b : Module.Basis (Fin r) k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (d : (relCurve C R).LocalEquations)
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ divisorWindow d ha1)]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d ha1) p = g)
    (h u : R) (β : Localization.Away h →ₐ[k] Localization.Away u)
    (hβ : β.toRingHom.comp (algebraMap R (Localization.Away h))
      = algebraMap R (Localization.Away u))
    (X : Matrix (Fin g) (Fin r) (Localization.Away h))
    (hX : Function.Surjective (matrixProj k g r (Localization.Away h) X))
    (I : Finset (Fin r)) (hI : I.card = g)
    (hu : IsUnit (β (frameMinor k g r (Localization.Away h) X I hI).det))
    (heq : matrixPoint k g r (Localization.Away h) X hX
      = congrAmbient b.equivFun
          (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank)) :
    Module.Grassmannian.map
        (chartFrameMap k g r (Localization.Away u) (X.map β) I hI)
        (chartTautologicalPoint k g r I hI)
      = congrAmbient b.equivFun
          (divisorWindowGrOfQuot g a ha1 d (Localization.Away u) hrank) := by
  have hX' : Function.Surjective (matrixProj k g r (Localization.Away u) (X.map β)) :=
    matrixProj_surjective_map k g r β X hX
  have hminor : IsUnit (frameMinor k g r (Localization.Away u) (X.map β) I hI).det := by
    have hdet : (frameMinor k g r (Localization.Away u) (X.map β) I hI).det
        = β (frameMinor k g r (Localization.Away h) X I hI).det := by
      rw [frameMinor, Matrix.submatrix_map]
      exact (RingHom.map_det β.toRingHom _).symm
    rw [hdet]
    exact hu
  rw [← matrixPoint_eq_map_chartTautologicalPoint_of_isUnit k g r (Localization.Away u)
      (X.map β) hX' I hI hminor,
    ← map_matrixPoint k g r β X hX hX', heq,
    map_congrAmbient β b.equivFun
      (divisorWindowGrOfQuot g a ha1 d (Localization.Away h) hrank),
    map_divisorWindowGrOfQuot g a ha1 d hrank h u β hβ]

variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))

set_option maxHeartbeats 1600000 in
-- The per-prime assembly instantiates the matrix kit at both pinned windows.
/-- Around one prime, the two raw divisor windows lie in a common pair chart. -/
private theorem exists_frame_chart_at_prime_of_windowQuot
    (d : (relCurve C R).LocalEquations)
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g))]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g))]
    [Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g))]
    [Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g))]
    (hrank₁ : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g)) p = g)
    (hrank₂ : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g)) p = g)
    (p : PrimeSpectrum R) :
    ∃ u : R, u ∉ p.asIdeal ∧
      ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
        (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away u),
        (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
          = Submodule.map
              (LinearMap.baseChange (Localization.Away u) b₁.equivFun.toLinearMap)
              (windowBaseChange (Localization.Away u)
                (divisorWindow d (relThetaPairH1_windowM C π hπ g))) ∧
        (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
          = Submodule.map
              (LinearMap.baseChange (Localization.Away u) b₂.equivFun.toLinearMap)
              (windowBaseChange (Localization.Away u)
                (divisorWindow d (relThetaPairH1_windowMS C π hπ g))) := by
  obtain ⟨h, hh, hfree₁, hfree₂⟩ := exists_away_free_pair p
    ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g))
    ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g))
  obtain ⟨pl, hpl⟩ : p ∈ Set.range
      (PrimeSpectrum.comap (algebraMap R (Localization.Away h))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away h) h]
    exact hh
  have hq : Ideal.comap (algebraMap R (Localization.Away h)) pl.asIdeal = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hpl
  obtain ⟨X₁, hX₁, I, hI, hdet₁, heq₁⟩ :=
    exists_component_matrix_of_windowQuot g (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) b₁ d hrank₁ h pl hfree₁
  obtain ⟨X₂, hX₂, J, hJ, hdet₂, heq₂⟩ :=
    exists_component_matrix_of_windowQuot g
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) b₂ d hrank₂ h pl hfree₂
  have hc : (frameMinor k g r₁ (Localization.Away h) X₁ I hI).det
      * (frameMinor k g r₂ (Localization.Away h) X₂ J hJ).det ∉ pl.asIdeal := fun hmem =>
    (pl.isPrime.mem_or_mem hmem).elim hdet₁ hdet₂
  obtain ⟨u, hup, hdvd, hβu⟩ := exists_away_isUnit_of_notMem h hh hq _ hc
  have hxu : IsUnit (algebraMap R (Localization.Away u) h) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R (Localization.Away u)) hdvd)
      (IsLocalization.Away.algebraMap_isUnit u)
  set β : Localization.Away h →ₐ[k] Localization.Away u :=
    awayLiftAlgHom h (IsScalarTower.toAlgHom k R (Localization.Away u)) hxu with hβdef
  have hβcomp : β.toRingHom.comp (algebraMap R (Localization.Away h))
      = algebraMap R (Localization.Away u) :=
    congrArg AlgHom.toRingHom
      (awayLiftAlgHom_comp_algHom h (IsScalarTower.toAlgHom k R (Localization.Away u)) hxu)
  have hβc : IsUnit (β ((frameMinor k g r₁ (Localization.Away h) X₁ I hI).det
      * (frameMinor k g r₂ (Localization.Away h) X₂ J hJ).det)) :=
    hβu (Localization.Away u) β.toRingHom hβcomp
  rw [map_mul] at hβc
  have hu₁ : IsUnit (β (frameMinor k g r₁ (Localization.Away h) X₁ I hI).det) :=
    isUnit_of_mul_isUnit_left hβc
  have hu₂ : IsUnit (β (frameMinor k g r₂ (Localization.Away h) X₂ J hJ).det) :=
    isUnit_of_mul_isUnit_right hβc
  have hcomp₁ := map_component_chart_of_windowQuot g
    (relThetaPairH1_windowM C π hπ g) b₁ d hrank₁ h u β hβcomp
    X₁ hX₁ I hI hu₁ heq₁
  have hcomp₂ := map_component_chart_of_windowQuot g
    (relThetaPairH1_windowMS C π hπ g) b₂ d hrank₂ h u β hβcomp
    X₂ hX₂ J hJ hu₂ heq₂
  refine ⟨u, hup, ULift.up ⟨I, hI⟩, ULift.up ⟨J, hJ⟩,
    Algebra.TensorProduct.productMap
      (chartFrameMap k g r₁ (Localization.Away u) (X₁.map β) I hI)
      (chartFrameMap k g r₂ (Localization.Away u) (X₂.map β) J hJ), ?_, ?_⟩
  · have hpt : Module.Grassmannian.map
        (Algebra.TensorProduct.productMap
          (chartFrameMap k g r₁ (Localization.Away u) (X₁.map β) I hI)
          (chartFrameMap k g r₂ (Localization.Away u) (X₂.map β) J hJ))
        (pairTautFst k g r₁ r₂ (ULift.up ⟨I, hI⟩) (ULift.up ⟨J, hJ⟩))
        = congrAmbient b₁.equivFun
            (divisorWindowGrOfQuot g (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) d (Localization.Away u) hrank₁) := by
      rw [pairTautFst, ← Module.Grassmannian.map_comp,
        Algebra.TensorProduct.productMap_left]
      exact hcomp₁
    rw [hpt, congrAmbient_toSubmodule, divisorWindowGrOfQuot_toSubmodule]
  · have hpt : Module.Grassmannian.map
        (Algebra.TensorProduct.productMap
          (chartFrameMap k g r₁ (Localization.Away u) (X₁.map β) I hI)
          (chartFrameMap k g r₂ (Localization.Away u) (X₂.map β) J hJ))
        (pairTautSnd k g r₁ r₂ (ULift.up ⟨I, hI⟩) (ULift.up ⟨J, hJ⟩))
        = congrAmbient b₂.equivFun
            (divisorWindowGrOfQuot g
              (windowM_choice π hπ g + windowS_choice π hπ g)
              (relThetaPairH1_windowMS C π hπ g) d (Localization.Away u) hrank₂) := by
      rw [pairTautSnd, ← Module.Grassmannian.map_comp,
        Algebra.TensorProduct.productMap_right]
      exact hcomp₂
    rw [hpt, congrAmbient_toSubmodule, divisorWindowGrOfQuot_toSubmodule]

set_option maxHeartbeats 1600000 in
-- Choosing and finitely extracting the prime-indexed chart data unfolds both window types.
/-- A finite pair-chart cover for the two windows of raw local equations, assuming only that
their quotients are finite projective of constant rank `g`. -/
theorem divisorWindow_exists_frameCover
    (d : (relCurve C R).LocalEquations)
    (hfin₁ : Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g)))
    (hproj₁ : Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g)))
    (hrank₁ : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowM C π hπ g)) p = g)
    (hfin₂ : Module.Finite R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g)))
    (hproj₂ : Module.Projective R ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g)))
    (hrank₂ : ∀ p : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d (relThetaPairH1_windowMS C π hπ g)) p = g) :
    ∃ (m : ℕ) (f : Fin m → R), Ideal.span (Set.range f) = ⊤ ∧
      ∀ t : Fin m,
        ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
          (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
            = Submodule.map
                (LinearMap.baseChange (Localization.Away (f t)) b₁.equivFun.toLinearMap)
                (windowBaseChange (Localization.Away (f t))
                  (divisorWindow d (relThetaPairH1_windowM C π hπ g))) ∧
          (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
            = Submodule.map
                (LinearMap.baseChange (Localization.Away (f t)) b₂.equivFun.toLinearMap)
                (windowBaseChange (Localization.Away (f t))
                  (divisorWindow d (relThetaPairH1_windowMS C π hπ g))) := by
  letI := hfin₁
  letI := hproj₁
  letI := hfin₂
  letI := hproj₂
  choose U hU hdata using exists_frame_chart_at_prime_of_windowQuot
    hπ g r₁ r₂ b₁ b₂ d hrank₁ hrank₂
  have hspan : Ideal.span (Set.range U) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    refine hU ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ?_))
    exact Set.mem_range_self _
  have h1 : (1 : R) ∈ Ideal.span (Set.range U) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨t, hts, h1t⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨t.card, fun i => (t.equivFin.symm i : R), ?_, ?_⟩
  · have hrange : Set.range (fun i : Fin t.card => (t.equivFin.symm i : R)) = ↑t := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (t.equivFin.symm i).2
      · intro hx
        exact ⟨t.equivFin ⟨x, hx⟩, by simp⟩
    rw [hrange, Ideal.eq_top_iff_one]
    exact h1t
  · intro tt
    obtain ⟨p, hp⟩ : ((t.equivFin.symm tt : R)) ∈ Set.range U :=
      hts (t.equivFin.symm tt).2
    have hgoal := hdata p
    rw [hp] at hgoal
    exact hgoal

namespace CertifiedDivisorFamilyAff

set_option maxHeartbeats 2000000 in
-- The two effective quotient packages and their pullback naturality are instantiated at
-- both pinned windows.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Every certified widened family admits a finite pair-chart frame cover.  On each basic
open, the chart frames the actual base-changed widened family, not merely an abstract window
submodule. -/
theorem exists_frameCover
    (F : CertifiedDivisorFamilyAff C R g)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    ∃ (m : ℕ) (f : Fin m → R), Ideal.span (Set.range f) = ⊤ ∧
      ∀ t : Fin m,
        ∃ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (f t)),
          (F.mapAlg (Localization.Away (f t)) g
            F.cover.hasAffineOverlaps_of_isProper).IsPairChartFramed
              hπ g b₁ b₂ i j w := by
  have hfin₁ := F.certified.finite_intrinsicWindowQuotient hπ hO hχ
    (relThetaPairH1_windowM C π hπ g) le_rfl
  have hproj₁ := F.certified.projective_intrinsicWindowQuotient
    (π := π) F.adaptation (windowM_choice π hπ g) hπ hO hχ
    (relThetaPairH1_windowM C π hπ g) le_rfl
  have hrank₁ := fun p : PrimeSpectrum R =>
    F.certified.rankAtStalk_intrinsicWindowQuotient
      (π := π) F.adaptation (windowM_choice π hπ g) hπ hO hχ
      (relThetaPairH1_windowM C π hπ g) le_rfl p
  have hfin₂ := F.certified.finite_intrinsicWindowQuotient hπ hO hχ
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  have hproj₂ := F.certified.projective_intrinsicWindowQuotient
    (π := π) F.adaptation
      (windowM_choice π hπ g + windowS_choice π hπ g) hπ hO hχ
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)
  have hrank₂ := fun p : PrimeSpectrum R =>
    F.certified.rankAtStalk_intrinsicWindowQuotient
      (π := π) F.adaptation
        (windowM_choice π hπ g + windowS_choice π hπ g) hπ hO hχ
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
  · rw [F.certified.divisorWindow_pulledEquations_eq
      (R' := Localization.Away (f t)) hπ hO hχ
      (relThetaPairH1_windowM C π hπ g) le_rfl]
    exact hw₁
  · rw [F.certified.divisorWindow_pulledEquations_eq
      (R' := Localization.Away (f t)) hπ hO hχ
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _)]
    exact hw₂

end CertifiedDivisorFamilyAff

end Curve

end AlgebraicGeometry
