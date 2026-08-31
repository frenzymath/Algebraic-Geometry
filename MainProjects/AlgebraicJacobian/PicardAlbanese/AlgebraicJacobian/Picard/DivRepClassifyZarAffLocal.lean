/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaFrameCoverComposite
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaCarve
import AlgebraicJacobian.Picard.DivSchemeClassifyAff

/-!
# Local classification of widened certified divisor families

This file supplies the two local inputs of the widened backward classifier:

* a pair-chart frame of a widened certified family transports along any algebra base change;
* a framed widened certified family factors uniquely through `DivScheme`.

Both statements depend only on the two intrinsic divisor windows.  No chart typing or
containment hypothesis is introduced.
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
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftRepClassifyZarAffLocal :
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

section WindowBaseChange

variable {R : Type u} [CommRing R] [Algebra k R]
variable {H : Type u} [AddCommGroup H] [Module k H]

/-- Cancelling an identity base change on a canonical generator is the identity. -/
theorem cancelBaseChange_self_one_tmul (x : R ⊗[k] H) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange k R R R H (1 ⊗ₜ[R] x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul r h =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      simp

/-- Pushing a window submodule along the identity algebra structure changes nothing. -/
theorem windowBaseChange_self (N : Submodule R (R ⊗[k] H)) :
    windowBaseChange R N = N := by
  apply le_antisymm
  · rw [windowBaseChange_le_iff]
    intro x hx
    rwa [cancelBaseChange_self_one_tmul]
  · intro x hx
    have hmem := cancelBaseChange_one_tmul_mem_windowBaseChange
      (R' := R) (N := N) hx
    rwa [cancelBaseChange_self_one_tmul] at hmem

end WindowBaseChange

variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

namespace CertifiedDivisorFamilyAff

set_option maxHeartbeats 2400000 in
-- Both intrinsic quotient certificates and their coordinate maps are transported.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hO hchi in
/-- A pair-chart framing of a widened certified family remains a framing after arbitrary
base change. -/
theorem IsPairChartFramed.mapAlg
    {R B : Type u} [CommRing R] [Algebra k R]
    [CommRing B] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    (F : CertifiedDivisorFamilyAff C R g) (hinf : F.cover.HasAffineOverlaps)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] R)
    (hw : F.IsPairChartFramed hpi g b₁ b₂ i j w) :
    (F.mapAlg B g hinf).IsPairChartFramed hpi g b₁ b₂ i j
      ((IsScalarTower.toAlgHom k R B).comp w) := by
  let beta : R →ₐ[k] B := IsScalarTower.toAlgHom k R B
  have hbeta : beta.toRingHom.comp (algebraMap R R) = algebraMap R B := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
    rfl
  haveI hfin₁ := F.certified.finite_intrinsicWindowQuotient hpi hO hchi
    (relThetaPairH1_windowM C pi hpi g) le_rfl
  haveI hproj₁ := F.certified.projective_intrinsicWindowQuotient
    (π := pi) F.adaptation (windowM_choice pi hpi g) hpi hO hchi
    (relThetaPairH1_windowM C pi hpi g) le_rfl
  have hrank₁ := fun p : PrimeSpectrum R =>
    F.certified.rankAtStalk_intrinsicWindowQuotient
      (π := pi) F.adaptation (windowM_choice pi hpi g) hpi hO hchi
      (relThetaPairH1_windowM C pi hpi g) le_rfl p
  haveI hfin₂ := F.certified.finite_intrinsicWindowQuotient hpi hO hchi
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)
  haveI hproj₂ := F.certified.projective_intrinsicWindowQuotient
    (π := pi) F.adaptation
      (windowM_choice pi hpi g + windowS_choice pi hpi g) hpi hO hchi
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)
  have hrank₂ := fun p : PrimeSpectrum R =>
    F.certified.rankAtStalk_intrinsicWindowQuotient
      (π := pi) F.adaptation
        (windowM_choice pi hpi g + windowS_choice pi hpi g) hpi hO hchi
      (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _) p
  change (_ = Submodule.map _
      (divisorWindow
        (F.adaptation.pulledEquations B F.certified.projective_colength)
        (relThetaPairH1_windowM C pi hpi g))) ∧
    (_ = Submodule.map _
      (divisorWindow
        (F.adaptation.pulledEquations B F.certified.projective_colength)
        (relThetaPairH1_windowMS C pi hpi g)))
  constructor
  · rw [F.certified.divisorWindow_pulledEquations_eq
      (R' := B) hpi hO hchi (relThetaPairH1_windowM C pi hpi g) le_rfl]
    have emap : Module.Grassmannian.map (beta.comp w)
        (pairTautFst k g r₁ r₂ i j)
        = Module.Grassmannian.map beta
            (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := beta)
        (N := pairTautFst k g r₁ r₂ i j)
    refine (congrArg Module.Grassmannian.toSubmodule emap).trans ?_
    apply map_windowFrameOfQuot_toSubmodule g (windowM_choice pi hpi g)
      (relThetaPairH1_windowM C pi hpi g) b₁ F.eqns hrank₁ beta hbeta
    simpa [CertifiedDivisorFamilyAff.eps_fst, windowBaseChange_self] using hw.1
  · rw [F.certified.divisorWindow_pulledEquations_eq
      (R' := B) hpi hO hchi
      (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)]
    have emap : Module.Grassmannian.map (beta.comp w)
        (pairTautSnd k g r₁ r₂ i j)
        = Module.Grassmannian.map beta
            (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := beta)
        (N := pairTautSnd k g r₁ r₂ i j)
    refine (congrArg Module.Grassmannian.toSubmodule emap).trans ?_
    apply map_windowFrameOfQuot_toSubmodule g
      (windowM_choice pi hpi g + windowS_choice pi hpi g)
      (relThetaPairH1_windowMS C pi hpi g) b₂ F.eqns hrank₂ beta hbeta
    simpa [CertifiedDivisorFamilyAff.eps_snd, windowBaseChange_self] using hw.2

set_option maxHeartbeats 2400000 in
-- Both off-diagonal quotient packages and their coordinate maps are transported.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- A pair-chart framing remains a framing after arbitrary base change when the curve
parameter is independent of the certified divisor degree. -/
theorem IsPairChartFramed.mapAlg_at
    {R B : Type u} [CommRing R] [Algebra k R]
    [CommRing B] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    (F : CertifiedDivisorFamilyAff C R g) (hinf : F.cover.HasAffineOverlaps)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] R)
    (hw : F.IsPairChartFramed hpi g b₁ b₂ i j w) :
    (F.mapAlg B g hinf).IsPairChartFramed hpi g b₁ b₂ i j
      ((IsScalarTower.toAlgHom k R B).comp w) := by
  let beta : R →ₐ[k] B := IsScalarTower.toAlgHom k R B
  have hbeta : beta.toRingHom.comp (algebraMap R R) = algebraMap R B := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
    rfl
  haveI hfin₁ := F.certified.finite_intrinsicWindowQuotient_at hpi hgamma hchiGamma
    (relThetaPairH1_windowM C pi hpi g) le_rfl
  haveI hproj₁ := F.certified.projective_intrinsicWindowQuotient_at
    (π := pi) F.adaptation (windowM_choice pi hpi g) hpi hgamma hchiGamma
    (relThetaPairH1_windowM C pi hpi g) le_rfl
  have hrank₁ := fun p : PrimeSpectrum R =>
    F.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := pi) F.adaptation (windowM_choice pi hpi g) hpi hgamma hchiGamma
      (relThetaPairH1_windowM C pi hpi g) le_rfl p
  haveI hfin₂ := F.certified.finite_intrinsicWindowQuotient_at hpi hgamma hchiGamma
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)
  haveI hproj₂ := F.certified.projective_intrinsicWindowQuotient_at
    (π := pi) F.adaptation
      (windowM_choice pi hpi g + windowS_choice pi hpi g) hpi hgamma hchiGamma
    (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)
  have hrank₂ := fun p : PrimeSpectrum R =>
    F.certified.rankAtStalk_intrinsicWindowQuotient_at
      (π := pi) F.adaptation
        (windowM_choice pi hpi g + windowS_choice pi hpi g) hpi hgamma hchiGamma
      (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _) p
  change (_ = Submodule.map _
      (divisorWindow
        (F.adaptation.pulledEquations B F.certified.projective_colength)
        (relThetaPairH1_windowM C pi hpi g))) ∧
    (_ = Submodule.map _
      (divisorWindow
        (F.adaptation.pulledEquations B F.certified.projective_colength)
        (relThetaPairH1_windowMS C pi hpi g)))
  constructor
  · rw [F.certified.divisorWindow_pulledEquations_eq_at
      (R' := B) hpi hgamma hchiGamma (relThetaPairH1_windowM C pi hpi g) le_rfl]
    have emap : Module.Grassmannian.map (beta.comp w)
        (pairTautFst k g r₁ r₂ i j)
        = Module.Grassmannian.map beta
            (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := beta)
        (N := pairTautFst k g r₁ r₂ i j)
    refine (congrArg Module.Grassmannian.toSubmodule emap).trans ?_
    apply map_windowFrameOfQuot_toSubmodule g (windowM_choice pi hpi g)
      (relThetaPairH1_windowM C pi hpi g) b₁ F.eqns hrank₁ beta hbeta
    simpa [CertifiedDivisorFamilyAff.eps_fst, windowBaseChange_self] using hw.1
  · rw [F.certified.divisorWindow_pulledEquations_eq_at
      (R' := B) hpi hgamma hchiGamma
      (relThetaPairH1_windowMS C pi hpi g) (Nat.le_add_right _ _)]
    have emap : Module.Grassmannian.map (beta.comp w)
        (pairTautSnd k g r₁ r₂ i j)
        = Module.Grassmannian.map beta
            (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := beta)
        (N := pairTautSnd k g r₁ r₂ i j)
    refine (congrArg Module.Grassmannian.toSubmodule emap).trans ?_
    apply map_windowFrameOfQuot_toSubmodule g
      (windowM_choice pi hpi g + windowS_choice pi hpi g)
      (relThetaPairH1_windowMS C pi hpi g) b₂ F.eqns hrank₂ beta hbeta
    simpa [CertifiedDivisorFamilyAff.eps_snd, windowBaseChange_self] using hw.2

set_option maxHeartbeats 800000 in
-- The generic carve-scheme universal property elaborates both Grassmannian components.
set_option linter.unusedSectionVars false in
/-- A framed widened certified divisor family factors uniquely through `DivScheme`. -/
theorem existsUnique_divClassify
    {R : Type u} [CommRing R] [Algebra k R]
    (F : CertifiedDivisorFamilyAff C R g)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] R)
    (hw : F.IsPairChartFramed hpi g b₁ b₂ i j w) :
    ∃! v : Spec (CommRingCat.of R) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      v ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom)
            ≫ pairChartMap k g r₁ g r₂ i j := by
  refine existsUnique_carveScheme_factor_of_map_pairTaut k g r₁ r₂
    (divCarveMul k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) r₁ r₂ b₁
      (b₂.map (windowShiftEquiv hpi g).symm)) i j w hw.1 hw.2 ?_
  intro a
  exact (carvePairArrow_divCarveMul_eq_zero_iff hpi g r₁ r₂ b₁ b₂
    (F.eps hpi g).1 (F.eps hpi g).2 a).mpr (F.eps_carve hpi g a)

end CertifiedDivisorFamilyAff

end Curve

end AlgebraicGeometry
