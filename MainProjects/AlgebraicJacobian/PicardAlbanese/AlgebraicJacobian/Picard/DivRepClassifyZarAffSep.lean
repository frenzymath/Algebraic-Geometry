/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarAff
import AlgebraicJacobian.Picard.DivRepClassifyZarSep
import AlgebraicJacobian.Picard.DivisorFamilyAffWindowGen

/-!
# Separation for the widened affine divisor classifier

Two widened classes classified by the same morphism agree.  Pair-chart equality recovers
their base-changed epsilon frames, and unconditional widened window generation recovers the
Cartier divisor from those frames over every common carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits
open scoped TensorProduct Pointwise

namespace AlgebraicGeometry

open Scheme Grassmannian

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftDivRepAffSep :
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
variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↑(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↑(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 2400000 in
-- Both framed families transport their intrinsic quotient data to the common carrier.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hO hχ in
/-- At a common carrier, two framed widened representatives of classes classified by one
morphism determine the same widened class. -/
private theorem mapAlg_eq_of_certChartFramesAff
    {B : Type u} [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    {A₀ : Type u} [CommRing A₀] [Algebra k A₀] [Algebra S A₀] [IsScalarTower k S A₀]
    [Algebra A₀ B] [IsScalarTower k A₀ B] [IsScalarTower S A₀ B]
    {A₁ : Type u} [CommRing A₁] [Algebra k A₁] [Algebra S A₁] [IsScalarTower k S A₁]
    [Algebra A₁ B] [IsScalarTower k A₁ B] [IsScalarTower S A₁ B]
    (F₀ F₁ : DivFamZarAff C S g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (h₀ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₀ v)
    (h₁ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₁ v)
    (G₀ : CertifiedDivisorFamilyAff C A₀ g)
    (hZ₀ : G₀.toZarAff = DivFamZarAff.mapAlg A₀ g F₀)
    {i₀ : (glueData k g r₁).J} {j₀ : (glueData k g r₂).J}
    (w₀ : PairChartRing k g r₁ g r₂ i₀ j₀ →ₐ[k] A₀)
    (hw₀ : G₀.IsPairChartFramed hπ g b₁ b₂ i₀ j₀ w₀)
    (G₁ : CertifiedDivisorFamilyAff C A₁ g)
    (hZ₁ : G₁.toZarAff = DivFamZarAff.mapAlg A₁ g F₁)
    {i₁ : (glueData k g r₁).J} {j₁ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] A₁)
    (hw₁ : G₁.IsPairChartFramed hπ g b₁ b₂ i₁ j₁ w₁) :
    DivFamZarAff.mapAlg B g F₀ = DivFamZarAff.mapAlg B g F₁ := by
  let β₀ : A₀ →ₐ[k] B := IsScalarTower.toAlgHom k A₀ B
  let β₁ : A₁ →ₐ[k] B := IsScalarTower.toAlgHom k A₁ B
  have hpush : ∀ {A : Type u} [CommRing A] [Algebra k A] [Algebra S A]
      [IsScalarTower k S A] [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
      {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
      (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] A),
      Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v ≫
          divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm) =
        Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j →
      Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ v ≫
          divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm) =
        Spec.map (CommRingCat.ofHom
            ((IsScalarTower.toAlgHom k A B).comp w).toRingHom) ≫
          pairChartMap k g r₁ g r₂ i j := by
    intro A _ _ _ _ _ _ _ i j w hA
    have hSB : CommRingCat.ofHom (algebraMap S A) ≫
        CommRingCat.ofHom (algebraMap A B) = CommRingCat.ofHom (algebraMap S B) := by
      rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hwB : CommRingCat.ofHom w.toRingHom ≫ CommRingCat.ofHom (algebraMap A B) =
        CommRingCat.ofHom ((IsScalarTower.toAlgHom k A B).comp w).toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      rfl
    rw [← hSB, Spec.map_comp, Category.assoc, hA, ← Category.assoc,
      ← Spec.map_comp, hwB]
  have hE₀ := hpush (A := A₀) w₀ (h₀ A₀ G₀ hZ₀ i₀ j₀ w₀ hw₀)
  have hE₁ := hpush (A := A₁) w₁ (h₁ A₁ G₁ hZ₁ i₁ j₁ w₁ hw₁)
  have hchart : Spec.map (CommRingCat.ofHom (β₀.comp w₀).toRingHom) ≫
        pairChartMap k g r₁ g r₂ i₀ j₀ =
      Spec.map (CommRingCat.ofHom (β₁.comp w₁).toRingHom) ≫
        pairChartMap k g r₁ g r₂ i₁ j₁ := hE₀.symm.trans hE₁
  have htf := map_pairTautFst_eq_of_specMap_pairChartMap_eq k g r₁ r₂
    (β₀.comp w₀) (β₁.comp w₁) hchart
  have hts := map_pairTautSnd_eq_of_specMap_pairChartMap_eq k g r₁ r₂
    (β₀.comp w₀) (β₁.comp w₁) hchart
  let hinf₀ : G₀.cover.HasAffineOverlaps := G₀.cover.hasAffineOverlaps_of_isProper
  let hinf₁ : G₁.cover.HasAffineOverlaps := G₁.cover.hasAffineOverlaps_of_isProper
  let E₀ := G₀.mapAlg B g hinf₀
  let E₁ := G₁.mapAlg B g hinf₁
  have hfr₀ := hw₀.mapAlg (B := B) hπ g hO hχ r₁ r₂ b₁ b₂ G₀ hinf₀ w₀
  have hfr₁ := hw₁.mapAlg (B := B) hπ g hO hχ r₁ r₂ b₁ b₂ G₁ hinf₁ w₁
  have hepsf : (E₀.eps hπ g).1 = (E₁.eps hπ g).1 :=
    submodule_eq_of_map_baseChange_equivFun_eq b₁ B
      (hfr₀.1.symm.trans ((congrArg Module.Grassmannian.toSubmodule htf).trans hfr₁.1))
  have hepss : (E₀.eps hπ g).2 = (E₁.eps hπ g).2 :=
    submodule_eq_of_map_baseChange_equivFun_eq b₂ B
      (hfr₀.2.symm.trans ((congrArg Module.Grassmannian.toSubmodule hts).trans hfr₁.2))
  have hdiv : E₀.eqns.DivEq E₁.eqns :=
    E₀.divEq_of_eps_eq hπ g E₁ (Prod.ext hepsf hepss) hO hχ
  have hclass : E₀.toZarAff = E₁.toZarAff := DivFamZarAff.mk_eq_mk_iff.mpr hdiv
  have e₀ : E₀.toZarAff = DivFamZarAff.mapAlg B g F₀ := by
    dsimp [E₀]
    rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ₀,
      DivFamZarAff.mapAlg_comp]
  have e₁ : E₁.toZarAff = DivFamZarAff.mapAlg B g F₁ := by
    dsimp [E₁]
    rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ₁,
      DivFamZarAff.mapAlg_comp]
  exact e₀.symm.trans (hclass.trans e₁)

set_option maxHeartbeats 1600000 in
-- Two widened certificate-frame covers elaborate with both localization towers.
include hO hχ in
/-- Two widened divisor classes classified by the same morphism are equal. -/
theorem eq_of_isDivRepClassifyAff (F₀ F₁ : DivFamZarAff C S g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (h₀ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₀ v)
    (h₁ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₁ v) : F₀ = F₁ := by
  classical
  obtain ⟨m₀, c₀, hspan₀, hdata₀⟩ :=
    DivFamZarAff.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  obtain ⟨m₁, c₁, hspan₁, hdata₁⟩ :=
    DivFamZarAff.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₁
  choose G₀ ci₀ cj₀ cw₀ hZ₀ hframe₀ using hdata₀
  choose G₁ ci₁ cj₁ cw₁ hZ₁ hframe₁ using hdata₁
  have hspan : Ideal.span (Set.range
      fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) ↦ c₀ p.1.down * c₁ p.2.down) = ⊤ := by
    have hsurj : Function.Surjective
        (fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) ↦
          (p.1.down, p.2.down)) := by
      rintro ⟨a, b⟩
      exact ⟨(⟨a⟩, ⟨b⟩), rfl⟩
    have hrange := hsurj.range_comp
      (fun q : Fin m₀ × Fin m₁ ↦ c₀ q.1 * c₁ q.2)
    exact hrange ▸ span_range_mul_eq_top c₀ c₁ hspan₀ hspan₁
  refine DivFamZarAff.eq_of_away_eq g
    (fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) ↦
      c₀ p.1.down * c₁ p.2.down)
    (fun p ↦ Localization.Away (c₀ p.1.down * c₁ p.2.down)) hspan ?_
  rintro ⟨⟨p₀⟩, ⟨p₁⟩⟩
  letI : Algebra (Localization.Away (c₀ p₀))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    (IsLocalization.Away.lift (S := Localization.Away (c₀ p₀)) (c₀ p₀)
      (g := algebraMap S (Localization.Away (c₀ p₀ * c₁ p₁)))
      (IsLocalization.Away.isUnit_of_dvd (x := c₀ p₀ * c₁ p₁)
        (dvd_mul_right (c₀ p₀) (c₁ p₁)))).toAlgebra
  haveI : IsScalarTower S (Localization.Away (c₀ p₀))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k (Localization.Away (c₀ p₀))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  letI : Algebra (Localization.Away (c₁ p₁))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    (IsLocalization.Away.lift (S := Localization.Away (c₁ p₁)) (c₁ p₁)
      (g := algebraMap S (Localization.Away (c₀ p₀ * c₁ p₁)))
      (IsLocalization.Away.isUnit_of_dvd (x := c₀ p₀ * c₁ p₁)
        (dvd_mul_left (c₁ p₁) (c₀ p₀)))).toAlgebra
  haveI : IsScalarTower S (Localization.Away (c₁ p₁))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k (Localization.Away (c₁ p₁))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  exact mapAlg_eq_of_certChartFramesAff hπ g hO hχ r₁ r₂ b₁ b₂ F₀ F₁ h₀ h₁
    (G₀ p₀) (hZ₀ p₀) (cw₀ p₀) (hframe₀ p₀)
    (G₁ p₁) (hZ₁ p₁) (cw₁ p₁) (hframe₁ p₁)

include hO hχ in
/-- The widened affine classifier is injective. -/
theorem divRepClassifyZarAff_injective :
    Function.Injective
      (divRepClassifyZarAff (C := C) (pi := π) hπ g hO hχ r₁ r₂ b₁ b₂ S) := by
  intro F₀ F₁ h
  refine eq_of_isDivRepClassifyAff hπ g hO hχ r₁ r₂ b₁ b₂ F₀ F₁
    (v := (divRepClassifyZarAff hπ g hO hχ r₁ r₂ b₁ b₂ S F₁).left)
    ?_ (divRepClassifyZarAff_isDivRepClassifyAff hπ g hO hχ r₁ r₂ b₁ b₂ F₁)
  rw [← h]
  exact divRepClassifyZarAff_isDivRepClassifyAff hπ g hO hχ r₁ r₂ b₁ b₂ F₀

set_option maxHeartbeats 2400000 in
-- Both off-diagonal framed families transport their quotient data to the common carrier.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- At an independent curve parameter, two framed representatives classified by one morphism
determine the same class after passage to a common carrier. -/
private theorem mapAlg_eq_of_certChartFramesAff_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {B : Type u} [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    {A₀ : Type u} [CommRing A₀] [Algebra k A₀] [Algebra S A₀] [IsScalarTower k S A₀]
    [Algebra A₀ B] [IsScalarTower k A₀ B] [IsScalarTower S A₀ B]
    {A₁ : Type u} [CommRing A₁] [Algebra k A₁] [Algebra S A₁] [IsScalarTower k S A₁]
    [Algebra A₁ B] [IsScalarTower k A₁ B] [IsScalarTower S A₁ B]
    (F₀ F₁ : DivFamZarAff C S g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (h₀ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₀ v)
    (h₁ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₁ v)
    (G₀ : CertifiedDivisorFamilyAff C A₀ g)
    (hZ₀ : G₀.toZarAff = DivFamZarAff.mapAlg A₀ g F₀)
    {i₀ : (glueData k g r₁).J} {j₀ : (glueData k g r₂).J}
    (w₀ : PairChartRing k g r₁ g r₂ i₀ j₀ →ₐ[k] A₀)
    (hw₀ : G₀.IsPairChartFramed hπ g b₁ b₂ i₀ j₀ w₀)
    (G₁ : CertifiedDivisorFamilyAff C A₁ g)
    (hZ₁ : G₁.toZarAff = DivFamZarAff.mapAlg A₁ g F₁)
    {i₁ : (glueData k g r₁).J} {j₁ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] A₁)
    (hw₁ : G₁.IsPairChartFramed hπ g b₁ b₂ i₁ j₁ w₁) :
    DivFamZarAff.mapAlg B g F₀ = DivFamZarAff.mapAlg B g F₁ := by
  let β₀ : A₀ →ₐ[k] B := IsScalarTower.toAlgHom k A₀ B
  let β₁ : A₁ →ₐ[k] B := IsScalarTower.toAlgHom k A₁ B
  have hpush : ∀ {A : Type u} [CommRing A] [Algebra k A] [Algebra S A]
      [IsScalarTower k S A] [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
      {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
      (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] A),
      Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v ≫
          divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm) =
        Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j →
      Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ v ≫
          divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm) =
        Spec.map (CommRingCat.ofHom
            ((IsScalarTower.toAlgHom k A B).comp w).toRingHom) ≫
          pairChartMap k g r₁ g r₂ i j := by
    intro A _ _ _ _ _ _ _ i j w hA
    have hSB : CommRingCat.ofHom (algebraMap S A) ≫
        CommRingCat.ofHom (algebraMap A B) = CommRingCat.ofHom (algebraMap S B) := by
      rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hwB : CommRingCat.ofHom w.toRingHom ≫ CommRingCat.ofHom (algebraMap A B) =
        CommRingCat.ofHom ((IsScalarTower.toAlgHom k A B).comp w).toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      rfl
    rw [← hSB, Spec.map_comp, Category.assoc, hA, ← Category.assoc,
      ← Spec.map_comp, hwB]
  have hE₀ := hpush (A := A₀) w₀ (h₀ A₀ G₀ hZ₀ i₀ j₀ w₀ hw₀)
  have hE₁ := hpush (A := A₁) w₁ (h₁ A₁ G₁ hZ₁ i₁ j₁ w₁ hw₁)
  have hchart : Spec.map (CommRingCat.ofHom (β₀.comp w₀).toRingHom) ≫
        pairChartMap k g r₁ g r₂ i₀ j₀ =
      Spec.map (CommRingCat.ofHom (β₁.comp w₁).toRingHom) ≫
        pairChartMap k g r₁ g r₂ i₁ j₁ := hE₀.symm.trans hE₁
  have htf := map_pairTautFst_eq_of_specMap_pairChartMap_eq k g r₁ r₂
    (β₀.comp w₀) (β₁.comp w₁) hchart
  have hts := map_pairTautSnd_eq_of_specMap_pairChartMap_eq k g r₁ r₂
    (β₀.comp w₀) (β₁.comp w₁) hchart
  let hinf₀ : G₀.cover.HasAffineOverlaps := G₀.cover.hasAffineOverlaps_of_isProper
  let hinf₁ : G₁.cover.HasAffineOverlaps := G₁.cover.hasAffineOverlaps_of_isProper
  let E₀ := G₀.mapAlg B g hinf₀
  let E₁ := G₁.mapAlg B g hinf₁
  have hfr₀ := CertifiedDivisorFamilyAff.IsPairChartFramed.mapAlg_at
    (C := C) (pi := π) (hpi := hπ) (g := g) (r₁ := r₁) (r₂ := r₂) (B := B)
    (b₁ := b₁) (b₂ := b₂) (F := G₀) (hinf := hinf₀) (gamma := gamma)
    (hgamma := hgamma) (hchiGamma := hχgamma) (w := w₀) (hw := hw₀)
  have hfr₁ := CertifiedDivisorFamilyAff.IsPairChartFramed.mapAlg_at
    (C := C) (pi := π) (hpi := hπ) (g := g) (r₁ := r₁) (r₂ := r₂) (B := B)
    (b₁ := b₁) (b₂ := b₂) (F := G₁) (hinf := hinf₁) (gamma := gamma)
    (hgamma := hgamma) (hchiGamma := hχgamma) (w := w₁) (hw := hw₁)
  have hepsf : (E₀.eps hπ g).1 = (E₁.eps hπ g).1 :=
    submodule_eq_of_map_baseChange_equivFun_eq b₁ B
      (hfr₀.1.symm.trans ((congrArg Module.Grassmannian.toSubmodule htf).trans hfr₁.1))
  have hepss : (E₀.eps hπ g).2 = (E₁.eps hπ g).2 :=
    submodule_eq_of_map_baseChange_equivFun_eq b₂ B
      (hfr₀.2.symm.trans ((congrArg Module.Grassmannian.toSubmodule hts).trans hfr₁.2))
  have hdiv : E₀.eqns.DivEq E₁.eqns :=
    E₀.divEq_of_eps_eq_at (gamma := gamma)
      hπ g hgamma E₁ (Prod.ext hepsf hepss) hOAt hχgamma
  have hclass : E₀.toZarAff = E₁.toZarAff := DivFamZarAff.mk_eq_mk_iff.mpr hdiv
  have e₀ : E₀.toZarAff = DivFamZarAff.mapAlg B g F₀ := by
    dsimp [E₀]
    rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ₀,
      DivFamZarAff.mapAlg_comp]
  have e₁ : E₁.toZarAff = DivFamZarAff.mapAlg B g F₁ := by
    dsimp [E₁]
    rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ₁,
      DivFamZarAff.mapAlg_comp]
  exact e₀.symm.trans (hclass.trans e₁)

set_option maxHeartbeats 1600000 in
-- Two off-diagonal certificate-frame covers elaborate with both localization towers.
/-- Two widened classes classified by the same morphism agree when the curve parameter is
independent of their certified divisor degree. -/
theorem eq_of_isDivRepClassifyAff_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ F₁ : DivFamZarAff C S g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (h₀ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₀ v)
    (h₁ : IsDivRepClassifyAff hπ g r₁ r₂ b₁ b₂ F₁ v) : F₀ = F₁ := by
  classical
  obtain ⟨m₀, c₀, hspan₀, hdata₀⟩ :=
    DivFamZarAff.exists_certChartCover_at (gamma := gamma)
      hπ g r₁ r₂ b₁ b₂ F₀ hgamma hχgamma
  obtain ⟨m₁, c₁, hspan₁, hdata₁⟩ :=
    DivFamZarAff.exists_certChartCover_at (gamma := gamma)
      hπ g r₁ r₂ b₁ b₂ F₁ hgamma hχgamma
  choose G₀ ci₀ cj₀ cw₀ hZ₀ hframe₀ using hdata₀
  choose G₁ ci₁ cj₁ cw₁ hZ₁ hframe₁ using hdata₁
  have hspan : Ideal.span (Set.range
      fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) ↦ c₀ p.1.down * c₁ p.2.down) = ⊤ := by
    have hsurj : Function.Surjective
        (fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) ↦
          (p.1.down, p.2.down)) := by
      rintro ⟨a, b⟩
      exact ⟨(⟨a⟩, ⟨b⟩), rfl⟩
    have hrange := hsurj.range_comp
      (fun q : Fin m₀ × Fin m₁ ↦ c₀ q.1 * c₁ q.2)
    exact hrange ▸ span_range_mul_eq_top c₀ c₁ hspan₀ hspan₁
  refine DivFamZarAff.eq_of_away_eq g
    (fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) ↦
      c₀ p.1.down * c₁ p.2.down)
    (fun p ↦ Localization.Away (c₀ p.1.down * c₁ p.2.down)) hspan ?_
  rintro ⟨⟨p₀⟩, ⟨p₁⟩⟩
  letI : Algebra (Localization.Away (c₀ p₀))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    (IsLocalization.Away.lift (S := Localization.Away (c₀ p₀)) (c₀ p₀)
      (g := algebraMap S (Localization.Away (c₀ p₀ * c₁ p₁)))
      (IsLocalization.Away.isUnit_of_dvd (x := c₀ p₀ * c₁ p₁)
        (dvd_mul_right (c₀ p₀) (c₁ p₁)))).toAlgebra
  haveI : IsScalarTower S (Localization.Away (c₀ p₀))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k (Localization.Away (c₀ p₀))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  letI : Algebra (Localization.Away (c₁ p₁))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    (IsLocalization.Away.lift (S := Localization.Away (c₁ p₁)) (c₁ p₁)
      (g := algebraMap S (Localization.Away (c₀ p₀ * c₁ p₁)))
      (IsLocalization.Away.isUnit_of_dvd (x := c₀ p₀ * c₁ p₁)
        (dvd_mul_left (c₁ p₁) (c₀ p₀)))).toAlgebra
  haveI : IsScalarTower S (Localization.Away (c₁ p₁))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k (Localization.Away (c₁ p₁))
      (Localization.Away (c₀ p₀ * c₁ p₁)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  exact mapAlg_eq_of_certChartFramesAff_at
    (hπ := hπ) (g := g) (r₁ := r₁) (r₂ := r₂) (b₁ := b₁) (b₂ := b₂)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma) (hχgamma := hχgamma)
    F₀ F₁ h₀ h₁
    (G₀ p₀) (hZ₀ p₀) (cw₀ p₀) (hframe₀ p₀)
    (G₁ p₁) (hZ₁ p₁) (cw₁ p₁) (hframe₁ p₁)

/-- The off-diagonal widened affine classifier is injective. -/
theorem divRepClassifyZarAff_injective_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hχgamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ)) :
    Function.Injective
      (divRepClassifyZarAff_at (C := C) (pi := π) (S := S)
        (gamma := gamma) hπ g r₁ r₂ b₁ b₂ hgamma hχgamma) := by
  intro F₀ F₁ h
  refine eq_of_isDivRepClassifyAff_at
    (hπ := hπ) (g := g) (r₁ := r₁) (r₂ := r₂) (b₁ := b₁) (b₂ := b₂)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma) (hχgamma := hχgamma)
    F₀ F₁
    (v := (divRepClassifyZarAff_at (S := S) (gamma := gamma)
      hπ g r₁ r₂ b₁ b₂ hgamma hχgamma F₁).left)
    ?_ (divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
      hπ g r₁ r₂ b₁ b₂ hgamma hχgamma F₁)
  rw [← h]
  exact divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
    hπ g r₁ r₂ b₁ b₂ hgamma hχgamma F₀

end Curve

end AlgebraicGeometry
