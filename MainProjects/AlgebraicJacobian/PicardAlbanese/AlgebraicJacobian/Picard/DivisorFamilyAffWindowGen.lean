/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffFieldWindowGen
import AlgebraicJacobian.Picard.DivisorFamilyAffStalkUpgrade
import AlgebraicJacobian.Picard.DivisorFamilyAffThetaWindowBaseChange
import AlgebraicJacobian.Picard.DivisorFamilyAffFibre
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeRel

/-!
# Window generation for widened divisor families

This file lifts unconditional field window recovery to every commutative test ring.  An
auxiliary finite chart adaptation of the same local equations is used only to restrict the
two components of a theta section to affine opens.  Certification, base change, flatness and
the final Nakayama upgrade all remain on the original arbitrary affine cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.stalkOverAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

attribute [local instance] instOverCleftWFT

variable [hsmC : SmoothOfRelativeDimension 1 C.hom] [hprC : IsProper C.hom]
  [hgiC : GeometricallyIrreducible C.hom]
variable [hsmL : SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))]
  [hintL : IsIntegral C.left]
  [hlftL : LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [hqcL : QuasiCompact (C.left ↘ Spec (.of k))]
  [hdom : IsDominant π]
variable [hfin0 : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [hfin1 : Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

noncomputable local instance instIsIntegralRelCurveAffWindowGen
    (K : Type u) [Field K] [Algebra k K] : IsIntegral (relCurve C K) :=
  instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveAffWindowGen
    (K : Type u) [Field K] [Algebra k K] :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveAffWindowGen
    (K : Type u) [Field K] [Algebra k K] :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveAffWindowGen
    (K : Type u) [Field K] [Algebra k K] :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

noncomputable local instance instFinH0RelCurveAffWindowGen
    (K : Type u) [Field K] [Algebra k K] :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0) :=
  instModuleFiniteHModuleZeroBaseChange C K

noncomputable local instance instFinH1RelCurveAffWindowGen
    (K : Type u) [Field K] [Algebra k K] :
    Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1) :=
  instModuleFiniteHModuleOneBaseChange C K

omit hsmL hintL hlftL hqcL hfin0 hfin1 in
private lemma h0_relCurve_affWindowGen (K : Type u) [Field K] [Algebra k K] :
    Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1 := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  exact h0_moduleKSheaf (baseChangeBundle C K)

omit hsmL hintL hlftL hqcL hfin0 hfin1 in
private lemma chi_relCurve_affWindowGen (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (K : Type u) [Field K] [Algebra k K] :
    Sheaf.chi ((relCurve C K).moduleKSheaf K) = 1 - (g : ℤ) := by
  haveI : IsProper (baseChangeBundle C K).hom := instIsProperSndLeft C K
  haveI : SmoothOfRelativeDimension 1 (baseChangeBundle C K).hom :=
    instSmoothOfRelativeDimensionSndLeft C K
  haveI : GeometricallyIrreducible (baseChangeBundle C K).hom :=
    instGeometricallyIrreducibleSndLeft C K
  have h1 : Sheaf.chi ((relCurve C K).moduleKSheaf K)
      = 1 - (genus (baseChangeBundle C K) : ℤ) := chi_moduleKSheaf (baseChangeBundle C K)
  have h2 : genus (baseChangeBundle C K) = genus C := genus_baseField C K
  have h3 : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (genus C : ℤ) := chi_moduleKSheaf C
  have h4 : (genus C : ℤ) = (g : ℤ) := by rw [h3] at hχ; linarith
  rw [h1, h2, h4]

variable (R) in
/-- The first-window germ set of a bare local-equation system over an arbitrary test ring. -/
noncomputable def eqnsWindowGermSetRel (g : ℕ)
    (d : (relCurve C R).LocalEquations) (z : relCurve C R) :
    Set ((relCurve C R).presheaf.stalk z) :=
  Scheme.twistGermSet
    ((↑(Submodule.map (relThetaWindowEquiv C R π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)).toLinearMap
        (divisorWindow d (relThetaPairH1_windowM C π hπ g))) :
      Set (relThetaSections C R π (windowM_choice π hπ g)))) z

set_option linter.unusedSectionVars false in
/-- Window germs lie in the stalk ideal over every commutative test ring. -/
theorem span_eqnsWindowGermSetRel_le (g : ℕ)
    (d : (relCurve C R).LocalEquations) (z : relCurve C R) :
    Ideal.span (eqnsWindowGermSetRel R hπ g d z) ≤ d.stalkIdeal z := by
  refine span_twistGermSet_le_stalkIdeal d ?_ z
  have hmap : Submodule.map
      (relThetaWindowEquiv C R π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)).toLinearMap
      (divisorWindow d (relThetaPairH1_windowM C π hπ g)) =
      d.vanishingSubmodule R (relCover C R (fiberTwoCover π)).V₀
        (relCover C R (fiberTwoCover π)).V₁
        (relThetaCocycle C R π (windowM_choice π hπ g)) := by
    rw [divisorWindow]
    exact Submodule.map_comap_eq_of_surjective
      (relThetaWindowEquiv C R π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)).surjective _
  rw [hmap]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
-- The total-ring, residue-field and theta-window instance towers elaborate together here.
set_option synthInstance.maxHeartbeats 800000 in
/-- Fibre clearance on one piece of an auxiliary chart refinement.  The refinement carries
no certificate: the widened family supplies field window generation and all base-change
facts, while the auxiliary piece supplies only an affine theta trivialization. -/
theorem CertifiedDivisorFamilyAff.exists_smul_auxEqn_mem_window_sup_at
    (g : ℕ) {gamma : ℕ} (hgamma : gamma ≤ g)
    (F : CertifiedDivisorFamilyAff C R g)
    (B : DivisorAdaptation C R π F.eqns)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (s : Ideal R) [s.IsPrime] (j : B.index) :
    ∃ t : R, t ∉ s ∧
      t • B.eqn j
        ∈ Ideal.span ((fun x ↦ B.toFinCoverData.windowRes
              (windowM_choice π hπ g) j
              (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) x)) ''
            ↑((F.eps hπ g).1))
          ⊔ Ideal.map (algebraMap R Γ(relCurve C R, B.pieces j)) s := by
  let FK := F.mapAlg s.ResidueField g F.cover.hasAffineOverlaps_of_isProper
  have hOK : Sheaf.h0 ((relCurve C s.ResidueField).moduleKSheaf s.ResidueField) = 1 :=
    h0_relCurve_affWindowGen s.ResidueField
  have hχK : Sheaf.chi ((relCurve C s.ResidueField).moduleKSheaf s.ResidueField)
      = 1 - (gamma : ℤ) := chi_relCurve_affWindowGen gamma hχk s.ResidueField
  have hepsEq : (FK.eps hπ g).1 = windowBaseChange s.ResidueField (F.eps hπ g).1 := by
    dsimp [FK]
    exact F.certified.divisorWindow_pulledEquations_eq_at
      (R' := s.ResidueField) hπ hgamma hχk
        (relThetaPairH1_windowM C π hπ g) le_rfl
  have hJ : B.pulledEqn s.ResidueField j
      ∈ Ideal.span (B.toFinCoverData.piecesMap s.ResidueField j ''
          ((fun x ↦ B.toFinCoverData.windowRes
              (windowM_choice π hπ g) j
              (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) x)) ''
            ↑((F.eps hπ g).1))) := by
    refine ((B.toFinCoverData.baseChange
      s.ResidueField).isAffineOpen_pieces j).mem_of_germ_mem_map ?_
    intro z hz
    have hgen : ((relCurve C s.ResidueField).presheaf.germ
        ((B.toFinCoverData.baseChange s.ResidueField).pieces j) z hz).hom
        (B.pulledEqn s.ResidueField j) ∈ FK.eqns.stalkIdeal z := by
      obtain ⟨v, hv⟩ := B.exists_germ_pulledEqn_eq_unit_mul_pullbackEqn
        (R' := s.ResidueField) j z hz
      rw [hv]
      apply Ideal.mul_mem_left
      change ((relCurve C s.ResidueField).presheaf.germ
          (FK.eqns.cover.opens z) z (FK.eqns.cover.mem_opens z)).hom
          (FK.eqns.eqn z) ∈ FK.eqns.stalkIdeal z
      exact Ideal.subset_span rfl
    have hle1 := FK.stalkIdeal_le_span_windowGerm_of_field_at hπ g hgamma
      hOk hχk hOK hχK z
    have hset : eqnsWindowGermSet s.ResidueField hπ g FK.eqns z =
        Scheme.twistGermSet
          (A := s.ResidueField)
          (V₀ := (relCover C s.ResidueField (fiberTwoCover π)).V₀)
          (V₁ := (relCover C s.ResidueField (fiberTwoCover π)).V₁)
          (gc := relThetaCocycle C s.ResidueField π (windowM_choice π hπ g))
          (↑(Submodule.map (relThetaWindowEquiv C s.ResidueField π
              (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
            (windowBaseChange s.ResidueField (F.eps hπ g).1))) z := by
      unfold eqnsWindowGermSet
      rw [show divisorWindow FK.eqns (relThetaPairH1_windowM C π hπ g) =
          windowBaseChange s.ResidueField (F.eps hπ g).1 from hepsEq]
    rw [hset] at hle1
    cases j with
    | inl ℓ =>
      have hchain := span_twistGermSet_le_map_germ_fst
        (A := s.ResidueField)
        (V₀ := (relCover C s.ResidueField (fiberTwoCover π)).V₀)
        (V₁ := (relCover C s.ResidueField (fiberTwoCover π)).V₁)
        (gc := relThetaCocycle C s.ResidueField π (windowM_choice π hπ g))
        (T := ↑(Submodule.map (relThetaWindowEquiv C s.ResidueField π
            (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
          (windowBaseChange s.ResidueField (F.eps hπ g).1)))
        (le_inf le_top ((B.toFinCoverData.baseChange
          s.ResidueField).pieces_inl_le ℓ)) z hz
      have hpush := span_resFst_windowBaseChange_le (R' := s.ResidueField)
        (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
        B.toFinCoverData ℓ (F.eps hπ g).1
      exact Ideal.map_mono hpush (hchain (hle1 hgen))
    | inr ℓ =>
      have hchain := span_twistGermSet_le_map_germ_snd
        (A := s.ResidueField)
        (V₀ := (relCover C s.ResidueField (fiberTwoCover π)).V₀)
        (V₁ := (relCover C s.ResidueField (fiberTwoCover π)).V₁)
        (gc := relThetaCocycle C s.ResidueField π (windowM_choice π hπ g))
        (T := ↑(Submodule.map (relThetaWindowEquiv C s.ResidueField π
            (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)).toLinearMap
          (windowBaseChange s.ResidueField (F.eps hπ g).1)))
        (le_inf le_top ((B.toFinCoverData.baseChange
          s.ResidueField).pieces_inr_le ℓ)) z hz
      have hpush := span_resSnd_windowBaseChange_le (R' := s.ResidueField)
        (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
        B.toFinCoverData ℓ (F.eps hπ g).1
      exact Ideal.map_mono hpush (hchain (hle1 hgen))
  have h1 : B.toFinCoverData.pieceTermBaseChange s.ResidueField j
      ((1 : s.ResidueField) ⊗ₜ[R] B.eqn j) = B.pulledEqn s.ResidueField j :=
    B.toFinCoverData.pieceTermBaseChange_one_tmul s.ResidueField j (B.eqn j)
  have hspan_le : Ideal.span (B.toFinCoverData.piecesMap s.ResidueField j ''
        ((fun x ↦ B.toFinCoverData.windowRes
            (windowM_choice π hπ g) j
            (relThetaWindowEquiv C R π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) x)) ''
          ↑((F.eps hπ g).1))) ≤
      Ideal.map ((B.toFinCoverData.pieceTermBaseChange
            s.ResidueField j).toRingEquiv : _ →+* _)
          (Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := s.ResidueField))
            (Ideal.span ((fun x ↦ B.toFinCoverData.windowRes
                (windowM_choice π hπ g) j
                (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                  (relThetaPairH1_windowM C π hπ g) x)) ''
              ↑((F.eps hπ g).1)))) := by
    rw [Ideal.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw1 : B.toFinCoverData.piecesMap s.ResidueField j w =
        B.toFinCoverData.pieceTermBaseChange s.ResidueField j
          ((1 : s.ResidueField) ⊗ₜ[R] w) :=
      (B.toFinCoverData.pieceTermBaseChange_one_tmul s.ResidueField j w).symm
    rw [hw1]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hw))
  have hmem : (1 : s.ResidueField) ⊗ₜ[R] B.eqn j ∈
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := s.ResidueField))
        (Ideal.span ((fun x ↦ B.toFinCoverData.windowRes
            (windowM_choice π hπ g) j
            (relThetaWindowEquiv C R π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) x)) ''
          ↑((F.eps hπ g).1))) := by
    refine (Ideal.apply_mem_of_equiv_iff
      (f := (B.toFinCoverData.pieceTermBaseChange
        s.ResidueField j).toRingEquiv)).mp ?_
    have h2 : (B.toFinCoverData.pieceTermBaseChange
        s.ResidueField j).toRingEquiv
        ((1 : s.ResidueField) ⊗ₜ[R] B.eqn j) = B.pulledEqn s.ResidueField j := h1
    rw [h2]
    exact hspan_le hJ
  exact exists_smul_mem_sup_map_of_one_tmul_mem_map s hmem

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The diagonal specialization of
`CertifiedDivisorFamilyAff.exists_smul_auxEqn_mem_window_sup_at`. -/
theorem CertifiedDivisorFamilyAff.exists_smul_auxEqn_mem_window_sup (g : ℕ)
    (F : CertifiedDivisorFamilyAff C R g)
    (B : DivisorAdaptation C R π F.eqns)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (s : Ideal R) [s.IsPrime] (j : B.index) :
    ∃ t : R, t ∉ s ∧
      t • B.eqn j
        ∈ Ideal.span ((fun x ↦ B.toFinCoverData.windowRes
              (windowM_choice π hπ g) j
              (relThetaWindowEquiv C R π (windowM_choice π hπ g)
                (relThetaPairH1_windowM C π hπ g) x)) ''
            ↑((F.eps hπ g).1))
          ⊔ Ideal.map (algebraMap R Γ(relCurve C R, B.pieces j)) s :=
  F.exists_smul_auxEqn_mem_window_sup_at
    (gamma := g) hπ g le_rfl B hOk hχk s j

omit hsmC hprC hgiC in
set_option maxRecDepth 8000 in
/-- The germ of an auxiliary piece restriction of a widened window element belongs to the
cover-independent window germ set. -/
private lemma germ_auxWindowRes_mem (g : ℕ) (F : CertifiedDivisorFamilyAff C R g)
    (B : DivisorAdaptation C R π F.eqns) (j : B.index)
    {z : relCurve C R} (hz : z ∈ B.pieces j)
    {x : R ⊗[k] ↑(Scheme.divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hx : x ∈ (F.eps hπ g).1) :
    ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom
      (B.toFinCoverData.windowRes (windowM_choice π hπ g) j
        (relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) x))
      ∈ eqnsWindowGermSetRel R hπ g F.eqns z := by
  unfold eqnsWindowGermSetRel
  cases j with
  | inl ℓ =>
    refine Set.mem_union_left _
      ⟨relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) x,
        Submodule.mem_map_of_mem hx,
        le_inf le_top (B.toFinCoverData.pieces_inl_le ℓ) hz, ?_⟩
    exact germ_resHom
      (le_inf le_top (B.toFinCoverData.pieces_inl_le ℓ)) z hz _
  | inr ℓ =>
    refine Set.mem_union_right _
      ⟨relThetaWindowEquiv C R π (windowM_choice π hπ g)
          (relThetaPairH1_windowM C π hπ g) x,
        Submodule.mem_map_of_mem hx,
        le_inf le_top (B.toFinCoverData.pieces_inr_le ℓ) hz, ?_⟩
    exact germ_resHom
      (le_inf le_top (B.toFinCoverData.pieces_inr_le ℓ)) z hz _

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
-- The localization, widened certificate and auxiliary restriction towers meet here.
set_option synthInstance.maxHeartbeats 800000 in
/-- Every stalk ideal of a widened certified family is exactly the ideal generated by its
first-window germs, over an arbitrary commutative test ring. -/
theorem CertifiedDivisorFamilyAff.stalkIdeal_eq_span_windowGerm_at
    (g : ℕ) {gamma : ℕ} (hgamma : gamma ≤ g)
    (F : CertifiedDivisorFamilyAff C R g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (z : relCurve C R) :
    F.eqns.stalkIdeal z = Ideal.span (eqnsWindowGermSetRel R hπ g F.eqns z) := by
  obtain ⟨B⟩ := exists_divisorAdaptation C R π F.eqns
  obtain ⟨j, hz⟩ := B.toFinCoverData.exists_mem_pieces z
  let s : Ideal R :=
    (IsLocalRing.maximalIdeal ((relCurve C R).presheaf.stalk z)).comap
      (algebraMap R ((relCurve C R).presheaf.stalk z))
  obtain ⟨t, ht, hmem⟩ := F.exists_smul_auxEqn_mem_window_sup_at
    hπ g hgamma B hOk hχk s j
  refine F.adaptation.stalkIdeal_eq_of_le_sup_map F.certified.projective_colength
    (s := s) (fun r hr ↦ hr)
    (span_eqnsWindowGermSetRel_le hπ g F.eqns z) ?_
  letI : Algebra Γ(relCurve C R, B.pieces j)
      ((relCurve C R).presheaf.stalk z) :=
    (relCurve C R).presheaf.algebra_section_stalk ⟨z, hz⟩
  haveI htower : IsScalarTower R Γ(relCurve C R, B.pieces j)
      ((relCurve C R).presheaf.stalk z) :=
    Scheme.stalkOverAlgebra_isScalarTower R hz
  rw [B.stalkIdeal_eq_span_germ_eqn j hz, Ideal.span_le,
    Set.singleton_subset_iff]
  have hpush : ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom
      (t • B.eqn j) ∈
      Ideal.span (eqnsWindowGermSetRel R hπ g F.eqns z) ⊔
        Ideal.map (algebraMap R ((relCurve C R).presheaf.stalk z)) s := by
    have h0 := Ideal.mem_map_of_mem
      ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom hmem
    rw [Ideal.map_sup] at h0
    have hleft : Ideal.map
        ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom
        (Ideal.span ((fun x ↦ B.toFinCoverData.windowRes
            (windowM_choice π hπ g) j
            (relThetaWindowEquiv C R π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g) x)) ''
          ↑((F.eps hπ g).1))) ≤
        Ideal.span (eqnsWindowGermSetRel R hπ g F.eqns z) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact Ideal.subset_span (germ_auxWindowRes_mem hπ g F B j hz hx)
    have hright : Ideal.map
        ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom
        (Ideal.map (algebraMap R Γ(relCurve C R, B.pieces j)) s) ≤
          Ideal.map (algebraMap R ((relCurve C R).presheaf.stalk z)) s := by
      rw [Ideal.map_map]
      refine le_of_eq (congrArg (Ideal.map · s) ?_)
      exact RingHom.ext fun r ↦ Scheme.germ_algebraMap_overSections R hz r
    exact sup_le_sup hleft hright h0
  have hgermsmul : ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom
      (t • B.eqn j) = algebraMap R ((relCurve C R).presheaf.stalk z) t *
        ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom (B.eqn j) := by
    rw [Algebra.smul_def, map_mul, Scheme.germ_algebraMap_overSections]
  have hunit : IsUnit (algebraMap R ((relCurve C R).presheaf.stalk z) t) := by
    by_contra hnu
    exact ht (Ideal.mem_comap.mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)))
  obtain ⟨u, hu⟩ := hunit
  have hval : ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom (B.eqn j) =
      ↑u⁻¹ * ((relCurve C R).presheaf.germ (B.pieces j) z hz).hom
        (t • B.eqn j) := by
    rw [hgermsmul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hval]
  exact Ideal.mul_mem_left _ _ hpush

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- The diagonal specialization of
`CertifiedDivisorFamilyAff.stalkIdeal_eq_span_windowGerm_at`. -/
theorem CertifiedDivisorFamilyAff.stalkIdeal_eq_span_windowGerm (g : ℕ)
    (F : CertifiedDivisorFamilyAff C R g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (z : relCurve C R) :
    F.eqns.stalkIdeal z = Ideal.span (eqnsWindowGermSetRel R hπ g F.eqns z) :=
  F.stalkIdeal_eq_span_windowGerm_at
    (gamma := g) hπ g le_rfl hOk hχk z

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
-- Two independently recovered stalk ideals elaborate in the same geometric instance tower.
/-- Equal epsilon pairs cut divisor-equal local-equation systems for arbitrary widened
certified families over every commutative test ring. -/
theorem CertifiedDivisorFamilyAff.divEq_of_eps_eq_at
    (g : ℕ) {gamma : ℕ} (hgamma : gamma ≤ g)
    (F F' : CertifiedDivisorFamilyAff C R g)
    (heps : F.eps hπ g = F'.eps hπ g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    F.eqns.DivEq F'.eqns := by
  refine Scheme.LocalEquations.divEq_of_stalkIdeal_eq fun z ↦ ?_
  have hwin : divisorWindow F.eqns (relThetaPairH1_windowM C π hπ g) =
      divisorWindow F'.eqns (relThetaPairH1_windowM C π hπ g) :=
    congrArg Prod.fst heps
  have hset : eqnsWindowGermSetRel R hπ g F.eqns z =
      eqnsWindowGermSetRel R hπ g F'.eqns z := by
    unfold eqnsWindowGermSetRel
    rw [hwin]
  rw [F.stalkIdeal_eq_span_windowGerm_at hπ g hgamma hOk hχk z,
    F'.stalkIdeal_eq_span_windowGerm_at hπ g hgamma hOk hχk z, hset]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
/-- The diagonal specialization of `CertifiedDivisorFamilyAff.divEq_of_eps_eq_at`. -/
theorem CertifiedDivisorFamilyAff.divEq_of_eps_eq (g : ℕ)
    (F F' : CertifiedDivisorFamilyAff C R g)
    (heps : F.eps hπ g = F'.eps hπ g)
    (hOk : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχk : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ)) :
    F.eqns.DivEq F'.eqns :=
  F.divEq_of_eps_eq_at (gamma := g) hπ g le_rfl F' heps hOk hχk

end AlgebraicGeometry
