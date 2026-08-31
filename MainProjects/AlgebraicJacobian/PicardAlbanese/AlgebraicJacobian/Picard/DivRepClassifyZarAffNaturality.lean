/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarAff
import AlgebraicJacobian.Picard.DivisorFamilyAffFace

/-!
# Naturality of the widened affine backward classifier

The refinement-stable characterizing clause is preserved by arbitrary algebra base change.
Uniqueness therefore makes `divRepClassifyZarAff` natural on affine tests, without any forward
universal-family hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftRepClassifyZarAffNaturality :
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

set_option maxHeartbeats 1600000 in
-- The proof changes algebra structures twice to compare instance and explicit base-change faces.
include hO hchi in
/-- Naturality of the underlying scheme morphism of the widened affine classifier. -/
theorem specMap_comp_divRepClassifyZarAff
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] B) (F : DivFamZarAff C A g) :
    Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
        (divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ A F).left
      = (divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ B
          (DivFamZarAff.mapAlgHom phi F)).left := by
  letI : Algebra A B := phi.toRingHom.toAlgebra
  haveI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun a => (phi.commutes a).symm
  refine isDivRepClassifyAff_unique hpi g hO hchi r₁ r₂ b₁ b₂
    (DivFamZarAff.mapAlgHom phi F) ?_
    (divRepClassifyZarAff_isDivRepClassifyAff hpi g hO hchi r₁ r₂ b₁ b₂
      (DivFamZarAff.mapAlgHom phi F))
  intro T _ _ _ _ G hG i j w hw
  let psi : B →ₐ[k] T := IsScalarTower.toAlgHom k B T
  letI : Algebra A T := (psi.comp phi).toRingHom.toAlgebra
  haveI : IsScalarTower k A T :=
    IsScalarTower.of_algebraMap_eq fun a => ((psi.comp phi).commutes a).symm
  haveI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmap : DivFamZarAff.mapAlg T g (DivFamZarAff.mapAlgHom phi F)
      = DivFamZarAff.mapAlg T g F := by
    calc
      _ = DivFamZarAff.mapAlgHom psi (DivFamZarAff.mapAlgHom phi F) :=
        (DivFamZarAff.mapAlgHom_eq_mapAlg psi (fun _ => rfl) _).symm
      _ = DivFamZarAff.mapAlgHom (psi.comp phi) F :=
        (DivFamZarAff.mapAlgHom_comp phi psi F).symm
      _ = DivFamZarAff.mapAlg T g F :=
        DivFamZarAff.mapAlgHom_eq_mapAlg (psi.comp phi) (fun _ => rfl) F
  have hbase := divRepClassifyZarAff_isDivRepClassifyAff hpi g hO hchi
    r₁ r₂ b₁ b₂ F T G (hG.trans hmap) i j w hw
  have hstep : Spec.map (CommRingCat.ofHom (algebraMap B T)) ≫
        (Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
          (divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ A F).left)
      = Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫
          (divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ A F).left := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, hstep, Category.assoc]
  exact hbase

set_option maxHeartbeats 800000 in
-- `Over` extensionality exposes exactly the scheme-level naturality above.
include hO hchi in
/-- Naturality of the widened affine classifier as a morphism over `Spec k`. -/
theorem overSpecMap_comp_divRepClassifyZarAff
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] B) (F : DivFamZarAff C A g) :
    Over.overSpecMap phi ≫ divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ A F
      = divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ B
          (DivFamZarAff.mapAlgHom phi F) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.overSpecMap_left]
  exact specMap_comp_divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ phi F

set_option maxHeartbeats 1600000 in
-- The proof changes algebra structures twice for the off-diagonal classifier faces.
/-- Naturality of the underlying scheme morphism of the off-diagonal widened classifier. -/
theorem specMap_comp_divRepClassifyZarAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] B) (F : DivFamZarAff C A g) :
    Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
        (divRepClassifyZarAff_at (S := A) hpi g r₁ r₂ b₁ b₂
          (gamma := gamma) hgamma hchiGamma F).left
      = (divRepClassifyZarAff_at (S := B) hpi g r₁ r₂ b₁ b₂
          (gamma := gamma) hgamma hchiGamma
          (DivFamZarAff.mapAlgHom phi F)).left := by
  letI : Algebra A B := phi.toRingHom.toAlgebra
  haveI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun a => (phi.commutes a).symm
  refine isDivRepClassifyAff_unique_at (gamma := gamma)
    hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma (DivFamZarAff.mapAlgHom phi F) ?_
    (divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
      hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma (DivFamZarAff.mapAlgHom phi F))
  intro T _ _ _ _ G hG i j w hw
  let psi : B →ₐ[k] T := IsScalarTower.toAlgHom k B T
  letI : Algebra A T := (psi.comp phi).toRingHom.toAlgebra
  haveI : IsScalarTower k A T :=
    IsScalarTower.of_algebraMap_eq fun a => ((psi.comp phi).commutes a).symm
  haveI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmap : DivFamZarAff.mapAlg T g (DivFamZarAff.mapAlgHom phi F)
      = DivFamZarAff.mapAlg T g F := by
    calc
      _ = DivFamZarAff.mapAlgHom psi (DivFamZarAff.mapAlgHom phi F) :=
        (DivFamZarAff.mapAlgHom_eq_mapAlg psi (fun _ => rfl) _).symm
      _ = DivFamZarAff.mapAlgHom (psi.comp phi) F :=
        (DivFamZarAff.mapAlgHom_comp phi psi F).symm
      _ = DivFamZarAff.mapAlg T g F :=
        DivFamZarAff.mapAlgHom_eq_mapAlg (psi.comp phi) (fun _ => rfl) F
  have hbase := divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
    hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F T G (hG.trans hmap) i j w hw
  have hstep : Spec.map (CommRingCat.ofHom (algebraMap B T)) ≫
        (Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
          (divRepClassifyZarAff_at (S := A) hpi g r₁ r₂ b₁ b₂
            (gamma := gamma) hgamma hchiGamma F).left)
      = Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫
          (divRepClassifyZarAff_at (S := A) hpi g r₁ r₂ b₁ b₂
            (gamma := gamma) hgamma hchiGamma F).left := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, hstep, Category.assoc]
  exact hbase

set_option maxHeartbeats 800000 in
-- `Over` extensionality exposes the off-diagonal scheme-level naturality square.
/-- Naturality of the off-diagonal widened classifier as a morphism over `Spec k`. -/
theorem overSpecMap_comp_divRepClassifyZarAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (phi : A →ₐ[k] B) (F : DivFamZarAff C A g) :
    Over.overSpecMap phi ≫
        divRepClassifyZarAff_at (S := A) hpi g r₁ r₂ b₁ b₂
          (gamma := gamma) hgamma hchiGamma F
      = divRepClassifyZarAff_at (S := B) hpi g r₁ r₂ b₁ b₂
          (gamma := gamma) hgamma hchiGamma (DivFamZarAff.mapAlgHom phi F) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.overSpecMap_left]
  exact specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
    hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma phi F

end Curve

end AlgebraicGeometry
