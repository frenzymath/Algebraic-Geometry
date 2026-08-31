/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarAffLocal
import AlgebraicJacobian.Picard.DivRepClassifyZarCompat

/-!
# Overlap compatibility for the widened divisor classifier

Two framed widened certified representatives of the same `DivFamZarAff` class determine the
same chart morphism after base change to a common ring.  Equality of widened classes unwraps to
`DivEq`; divisor-window invariance then identifies both transported epsilon pairs, and the
existing pair-chart comparison applies.

The tensor-product specialization is the `glueMorphisms` obligation for the widened backward
classifier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftRepClassifyZarAffCompat :
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
variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

set_option maxHeartbeats 2400000 in
-- Both framed families transport their certified intrinsic quotient data to the common ring.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
include hO hchi in
/-- Two widened pair-chart frames whose base-changed certified families name the same class
present the same morphism to the Grassmannian pair. -/
theorem specMap_pairChartMap_eq_of_aff_window_frames
    {S₁ S₂ B : Type u}
    [CommRing S₁] [Algebra k S₁] [CommRing S₂] [Algebra k S₂]
    [CommRing B] [Algebra k B]
    [Algebra S₁ B] [IsScalarTower k S₁ B]
    [Algebra S₂ B] [IsScalarTower k S₂ B]
    (F₁ : CertifiedDivisorFamilyAff C S₁ g)
    (F₂ : CertifiedDivisorFamilyAff C S₂ g)
    (hinf₁ : F₁.cover.HasAffineOverlaps) (hinf₂ : F₂.cover.HasAffineOverlaps)
    (hclass : (F₁.mapAlg B g hinf₁).toZarAff = (F₂.mapAlg B g hinf₂).toZarAff)
    {i₁ i₂ : (glueData k g r₁).J} {j₁ j₂ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] S₁)
    (w₂ : PairChartRing k g r₁ g r₂ i₂ j₂ →ₐ[k] S₂)
    (hw₁ : F₁.IsPairChartFramed hpi g b₁ b₂ i₁ j₁ w₁)
    (hw₂ : F₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂ w₂) :
    Spec.map (CommRingCat.ofHom
        ((IsScalarTower.toAlgHom k S₁ B).comp w₁).toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i₁ j₁
      = Spec.map (CommRingCat.ofHom
          ((IsScalarTower.toAlgHom k S₂ B).comp w₂).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂ := by
  let E₁ := F₁.mapAlg B g hinf₁
  let E₂ := F₂.mapAlg B g hinf₂
  have hdiv : E₁.eqns.DivEq E₂.eqns :=
    DivFamZarAff.mk_eq_mk_iff.mp hclass
  have hframe₁ : E₁.IsPairChartFramed hpi g b₁ b₂ i₁ j₁
      ((IsScalarTower.toAlgHom k S₁ B).comp w₁) :=
    hw₁.mapAlg hpi g hO hchi r₁ r₂ b₁ b₂ F₁ hinf₁ w₁
  have hframe₂ : E₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂
      ((IsScalarTower.toAlgHom k S₂ B).comp w₂) :=
    hw₂.mapAlg hpi g hO hchi r₁ r₂ b₁ b₂ F₂ hinf₂ w₂
  have heps₁ : (E₁.eps hpi g).1 = (E₂.eps hpi g).1 := by
    rw [CertifiedDivisorFamilyAff.eps_fst, CertifiedDivisorFamilyAff.eps_fst,
      divisorWindow_eq_of_divEq hdiv]
  have heps₂ : (E₁.eps hpi g).2 = (E₂.eps hpi g).2 := by
    rw [CertifiedDivisorFamilyAff.eps_snd, CertifiedDivisorFamilyAff.eps_snd,
      divisorWindow_eq_of_divEq hdiv]
  refine specMap_pairChartMap_eq_of_map_pairTaut_eq k g r₁ r₂ i₁ i₂ j₁ j₂
    ((IsScalarTower.toAlgHom k S₁ B).comp w₁)
    ((IsScalarTower.toAlgHom k S₂ B).comp w₂) ?_ ?_
  · refine Module.Grassmannian.ext ?_
    rw [hframe₁.1, hframe₂.1, heps₁]
  · refine Module.Grassmannian.ext ?_
    rw [hframe₁.2, hframe₂.2, heps₂]

variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 2400000 in
-- The tensor overlap carries both algebra towers and the pullback-Spec comparison.
include hO hchi in
/-- The local widened classifications of two certified representatives of one widened class
agree on their basic-open pullback overlap. -/
theorem pullback_divClassifyAff_compat (F₀ : DivFamZarAff C S g)
    {S₁ : Type u} [CommRing S₁] [Algebra k S₁] [Algebra S S₁]
    [IsScalarTower k S S₁]
    {S₂ : Type u} [CommRing S₂] [Algebra k S₂] [Algebra S S₂]
    [IsScalarTower k S S₂]
    (F₁ : CertifiedDivisorFamilyAff C S₁ g)
    (F₂ : CertifiedDivisorFamilyAff C S₂ g)
    (hZ₁ : F₁.toZarAff = DivFamZarAff.mapAlg S₁ g F₀)
    (hZ₂ : F₂.toZarAff = DivFamZarAff.mapAlg S₂ g F₀)
    {i₁ i₂ : (glueData k g r₁).J} {j₁ j₂ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] S₁)
    (w₂ : PairChartRing k g r₁ g r₂ i₂ j₂ →ₐ[k] S₂)
    (hw₁ : F₁.IsPairChartFramed hpi g b₁ b₂ i₁ j₁ w₁)
    (hw₂ : F₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂ w₂)
    {v₁ : Spec (CommRingCat.of S₁) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv₁ : v₁ ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom w₁.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₁ j₁)
    {v₂ : Spec (CommRingCat.of S₂) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv₂ : v₂ ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom w₂.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
        (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ≫ v₁
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
          (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ≫ v₂ := by
  let B := TensorProduct S S₁ S₂
  letI : Algebra S₂ B :=
    (Algebra.TensorProduct.includeRight (R := S) (A := S₁) (B := S₂)).toRingHom.toAlgebra
  haveI : IsScalarTower k S B :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower S S₁ B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k S₁ B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S S₂ B :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  haveI : IsScalarTower k S₂ B := isScalarTower_left_of_isScalarTower (R₀ := S)
  let hinf₁ : F₁.cover.HasAffineOverlaps := F₁.cover.hasAffineOverlaps_of_isProper
  let hinf₂ : F₂.cover.HasAffineOverlaps := F₂.cover.hasAffineOverlaps_of_isProper
  have hclass : (F₁.mapAlg B g hinf₁).toZarAff = (F₂.mapAlg B g hinf₂).toZarAff := by
    rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg,
      CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ₁, hZ₂]
    exact (DivFamZarAff.mapAlg_comp S₁ g B F₀).trans
      (DivFamZarAff.mapAlg_comp S₂ g B F₀).symm
  have hcore := specMap_pairChartMap_eq_of_aff_window_frames hpi g hO hchi
    r₁ r₂ b₁ b₂ F₁ F₂ hinf₁ hinf₂ hclass w₁ w₂ hw₁ hw₂
  have hleft : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* B))
        ≫ Spec.map (CommRingCat.ofHom w₁.toRingHom)
      = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₁ B).comp w₁).toRingHom)) := by
    rw [← Spec.map_comp]
    rfl
  have hright : Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight (R := S) (A := S₁) (B := S₂)) :
          S₂ →+* B))
        ≫ Spec.map (CommRingCat.ofHom w₂.toRingHom)
      = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₂ B).comp w₂).toRingHom)) := by
    rw [← Spec.map_comp]
    rfl
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hpi g).symm) _ _ ?_
  rw [Category.assoc, Category.assoc, hv₁, hv₂,
    ← cancel_epi (pullbackSpecIso S S₁ S₂).inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  calc
    _ = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₁ B).comp w₁).toRingHom))
          ≫ pairChartMap k g r₁ g r₂ i₁ j₁ := by
        rw [← Category.assoc, hleft]
    _ = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₂ B).comp w₂).toRingHom))
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂ := hcore
    _ = _ := by
      rw [← Category.assoc, hright]

set_option maxHeartbeats 2400000 in
-- The arbitrary framed test is first factored locally, then compared on the tensor overlap.
include hO hchi in
/-- A framed widened representative over an arbitrary test agrees on the pullback overlap with
the local classification of any other representative of the same widened class. -/
theorem pullback_chart_divClassifyAff_compat (F₀ : DivFamZarAff C S g)
    {T : Type u} [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (G : CertifiedDivisorFamilyAff C T g)
    (hZG : G.toZarAff = DivFamZarAff.mapAlg T g F₀)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (hw : G.IsPairChartFramed hpi g b₁ b₂ i j w)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (F₂ : CertifiedDivisorFamilyAff C A g)
    (hZ₂ : F₂.toZarAff = DivFamZarAff.mapAlg A g F₀)
    {i₂ : (glueData k g r₁).J} {j₂ : (glueData k g r₂).J}
    (w₂ : PairChartRing k g r₁ g r₂ i₂ j₂ →ₐ[k] A)
    (hw₂ : F₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂ w₂)
    {v₂ : Spec (CommRingCat.of A) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv₂ : v₂ ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom w₂.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i j
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A)))
          ≫ v₂ ≫ divSchemeι k
            (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm) := by
  let u := (G.existsUnique_divClassify hpi g r₁ r₂ b₁ b₂ w hw).choose
  have hu := (G.existsUnique_divClassify hpi g r₁ r₂ b₁ b₂ w hw).choose_spec.1
  have hcompat := pullback_divClassifyAff_compat hpi g hO hchi r₁ r₂ b₁ b₂
    F₀ G F₂ hZG hZ₂ w w₂ hw hw₂ hu hv₂
  calc
    _ = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≫
          (u ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm)) := by
        rw [hu]
    _ = (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≫ u) ≫
          divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm) := by
        rw [Category.assoc]
    _ = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≫ v₂) ≫
          divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm) :=
        congrArg (fun z => z ≫ divSchemeι k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)) hcompat
    _ = _ := by rw [Category.assoc]

set_option maxHeartbeats 2400000 in
-- Both off-diagonal framed families transport to the common coefficient ring.
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- Two widened pair-chart frames whose base-changed certified families name the same class
present the same morphism when the curve parameter is independent of the divisor degree. -/
theorem specMap_pairChartMap_eq_of_aff_window_frames_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {S₁ S₂ B : Type u}
    [CommRing S₁] [Algebra k S₁] [CommRing S₂] [Algebra k S₂]
    [CommRing B] [Algebra k B]
    [Algebra S₁ B] [IsScalarTower k S₁ B]
    [Algebra S₂ B] [IsScalarTower k S₂ B]
    (F₁ : CertifiedDivisorFamilyAff C S₁ g)
    (F₂ : CertifiedDivisorFamilyAff C S₂ g)
    (hinf₁ : F₁.cover.HasAffineOverlaps) (hinf₂ : F₂.cover.HasAffineOverlaps)
    (hclass : (F₁.mapAlg B g hinf₁).toZarAff = (F₂.mapAlg B g hinf₂).toZarAff)
    {i₁ i₂ : (glueData k g r₁).J} {j₁ j₂ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] S₁)
    (w₂ : PairChartRing k g r₁ g r₂ i₂ j₂ →ₐ[k] S₂)
    (hw₁ : F₁.IsPairChartFramed hpi g b₁ b₂ i₁ j₁ w₁)
    (hw₂ : F₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂ w₂) :
    Spec.map (CommRingCat.ofHom
        ((IsScalarTower.toAlgHom k S₁ B).comp w₁).toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i₁ j₁
      = Spec.map (CommRingCat.ofHom
          ((IsScalarTower.toAlgHom k S₂ B).comp w₂).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂ := by
  let E₁ := F₁.mapAlg B g hinf₁
  let E₂ := F₂.mapAlg B g hinf₂
  have hdiv : E₁.eqns.DivEq E₂.eqns :=
    DivFamZarAff.mk_eq_mk_iff.mp hclass
  have hframe₁ : E₁.IsPairChartFramed hpi g b₁ b₂ i₁ j₁
      ((IsScalarTower.toAlgHom k S₁ B).comp w₁) :=
    CertifiedDivisorFamilyAff.IsPairChartFramed.mapAlg_at
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r₁ := r₁) (r₂ := r₂)
      (b₁ := b₁) (b₂ := b₂) (F := F₁) (hinf := hinf₁) (gamma := gamma)
      (hgamma := hgamma) (hchiGamma := hchiGamma) (w := w₁) (hw := hw₁)
  have hframe₂ : E₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂
      ((IsScalarTower.toAlgHom k S₂ B).comp w₂) :=
    CertifiedDivisorFamilyAff.IsPairChartFramed.mapAlg_at
      (C := C) (pi := pi) (hpi := hpi) (g := g) (r₁ := r₁) (r₂ := r₂)
      (b₁ := b₁) (b₂ := b₂) (F := F₂) (hinf := hinf₂) (gamma := gamma)
      (hgamma := hgamma) (hchiGamma := hchiGamma) (w := w₂) (hw := hw₂)
  have heps₁ : (E₁.eps hpi g).1 = (E₂.eps hpi g).1 := by
    rw [CertifiedDivisorFamilyAff.eps_fst, CertifiedDivisorFamilyAff.eps_fst,
      divisorWindow_eq_of_divEq hdiv]
  have heps₂ : (E₁.eps hpi g).2 = (E₂.eps hpi g).2 := by
    rw [CertifiedDivisorFamilyAff.eps_snd, CertifiedDivisorFamilyAff.eps_snd,
      divisorWindow_eq_of_divEq hdiv]
  refine specMap_pairChartMap_eq_of_map_pairTaut_eq k g r₁ r₂ i₁ i₂ j₁ j₂
    ((IsScalarTower.toAlgHom k S₁ B).comp w₁)
    ((IsScalarTower.toAlgHom k S₂ B).comp w₂) ?_ ?_
  · refine Module.Grassmannian.ext ?_
    rw [hframe₁.1, hframe₂.1, heps₁]
  · refine Module.Grassmannian.ext ?_
    rw [hframe₁.2, hframe₂.2, heps₂]

set_option maxHeartbeats 2400000 in
-- The off-diagonal tensor overlap carries both algebra towers and the Spec comparison.
/-- The local widened classifications of two representatives of one widened class agree on
their pullback overlap when the curve parameter is independent of the divisor degree. -/
theorem pullback_divClassifyAff_compat_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g)
    {S₁ : Type u} [CommRing S₁] [Algebra k S₁] [Algebra S S₁]
    [IsScalarTower k S S₁]
    {S₂ : Type u} [CommRing S₂] [Algebra k S₂] [Algebra S S₂]
    [IsScalarTower k S S₂]
    (F₁ : CertifiedDivisorFamilyAff C S₁ g)
    (F₂ : CertifiedDivisorFamilyAff C S₂ g)
    (hZ₁ : F₁.toZarAff = DivFamZarAff.mapAlg S₁ g F₀)
    (hZ₂ : F₂.toZarAff = DivFamZarAff.mapAlg S₂ g F₀)
    {i₁ i₂ : (glueData k g r₁).J} {j₁ j₂ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] S₁)
    (w₂ : PairChartRing k g r₁ g r₂ i₂ j₂ →ₐ[k] S₂)
    (hw₁ : F₁.IsPairChartFramed hpi g b₁ b₂ i₁ j₁ w₁)
    (hw₂ : F₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂ w₂)
    {v₁ : Spec (CommRingCat.of S₁) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv₁ : v₁ ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom w₁.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₁ j₁)
    {v₂ : Spec (CommRingCat.of S₂) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv₂ : v₂ ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom w₂.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
        (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ≫ v₁
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
          (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ≫ v₂ := by
  let B := TensorProduct S S₁ S₂
  letI : Algebra S₂ B :=
    (Algebra.TensorProduct.includeRight (R := S) (A := S₁) (B := S₂)).toRingHom.toAlgebra
  haveI : IsScalarTower k S B :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower S S₁ B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k S₁ B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S S₂ B :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  haveI : IsScalarTower k S₂ B := isScalarTower_left_of_isScalarTower (R₀ := S)
  let hinf₁ : F₁.cover.HasAffineOverlaps := F₁.cover.hasAffineOverlaps_of_isProper
  let hinf₂ : F₂.cover.HasAffineOverlaps := F₂.cover.hasAffineOverlaps_of_isProper
  have hclass : (F₁.mapAlg B g hinf₁).toZarAff = (F₂.mapAlg B g hinf₂).toZarAff := by
    rw [CertifiedDivisorFamilyAff.toZarAff_mapAlg,
      CertifiedDivisorFamilyAff.toZarAff_mapAlg, hZ₁, hZ₂]
    exact (DivFamZarAff.mapAlg_comp S₁ g B F₀).trans
      (DivFamZarAff.mapAlg_comp S₂ g B F₀).symm
  have hcore := specMap_pairChartMap_eq_of_aff_window_frames_at
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r₁ := r₁) (r₂ := r₂)
    (b₁ := b₁) (b₂ := b₂) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma) (F₁ := F₁) (F₂ := F₂) (hinf₁ := hinf₁)
    (hinf₂ := hinf₂) (hclass := hclass) (w₁ := w₁) (w₂ := w₂)
    (hw₁ := hw₁) (hw₂ := hw₂)
  have hleft : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* B))
        ≫ Spec.map (CommRingCat.ofHom w₁.toRingHom)
      = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₁ B).comp w₁).toRingHom)) := by
    rw [← Spec.map_comp]
    rfl
  have hright : Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight (R := S) (A := S₁) (B := S₂)) :
          S₂ →+* B))
        ≫ Spec.map (CommRingCat.ofHom w₂.toRingHom)
      = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₂ B).comp w₂).toRingHom)) := by
    rw [← Spec.map_comp]
    rfl
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hpi g).symm) _ _ ?_
  rw [Category.assoc, Category.assoc, hv₁, hv₂,
    ← cancel_epi (pullbackSpecIso S S₁ S₂).inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  calc
    _ = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₁ B).comp w₁).toRingHom))
          ≫ pairChartMap k g r₁ g r₂ i₁ j₁ := by
        rw [← Category.assoc, hleft]
    _ = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k S₂ B).comp w₂).toRingHom))
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂ := hcore
    _ = _ := by
      rw [← Category.assoc, hright]

set_option maxHeartbeats 2400000 in
-- The arbitrary off-diagonal framed test is compared on the tensor overlap.
/-- A framed representative over an arbitrary test agrees on the pullback overlap with the
local classification of another representative at an independent curve parameter. -/
theorem pullback_chart_divClassifyAff_compat_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g)
    {T : Type u} [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (G : CertifiedDivisorFamilyAff C T g)
    (hZG : G.toZarAff = DivFamZarAff.mapAlg T g F₀)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (hw : G.IsPairChartFramed hpi g b₁ b₂ i j w)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (F₂ : CertifiedDivisorFamilyAff C A g)
    (hZ₂ : F₂.toZarAff = DivFamZarAff.mapAlg A g F₀)
    {i₂ : (glueData k g r₁).J} {j₂ : (glueData k g r₂).J}
    (w₂ : PairChartRing k g r₁ g r₂ i₂ j₂ →ₐ[k] A)
    (hw₂ : F₂.IsPairChartFramed hpi g b₁ b₂ i₂ j₂ w₂)
    {v₂ : Spec (CommRingCat.of A) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv₂ : v₂ ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom w₂.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i₂ j₂) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i j
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A)))
          ≫ v₂ ≫ divSchemeι k
            (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm) := by
  let u := (G.existsUnique_divClassify hpi g r₁ r₂ b₁ b₂ w hw).choose
  have hu := (G.existsUnique_divClassify hpi g r₁ r₂ b₁ b₂ w hw).choose_spec.1
  have hcompat := pullback_divClassifyAff_compat_at
    (C := C) (pi := pi) (hpi := hpi) (g := g) (r₁ := r₁) (r₂ := r₂)
    (b₁ := b₁) (b₂ := b₂) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma) (F₀ := F₀) (F₁ := G) (F₂ := F₂)
    (hZ₁ := hZG) (hZ₂ := hZ₂) (w₁ := w) (w₂ := w₂) (hw₁ := hw)
    (hw₂ := hw₂) (hv₁ := hu) (hv₂ := hv₂)
  calc
    _ = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≫
          (u ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm)) := by
        rw [hu]
    _ = (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≫ u) ≫
          divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm) := by
        rw [Category.assoc]
    _ = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≫ v₂) ≫
          divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm) :=
        congrArg (fun z => z ≫ divSchemeι k
          (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)) hcompat
    _ = _ := by rw [Category.assoc]

end Curve

end AlgebraicGeometry
