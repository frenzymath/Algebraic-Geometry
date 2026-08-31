/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAwaySpanGlueAff
import AlgebraicJacobian.Picard.DivRepClassifyZarAffNaturality
import AlgebraicJacobian.Picard.DivRepClassifyZarAffSep
import AlgebraicJacobian.Picard.DivRepGlobalClassifyAff
import AlgebraicJacobian.Picard.DivSchemeAtlasFactor

/-!
# Chart range implies surjectivity of the widened affine classifier

If every carve-chart map is the classifier of a widened locally certified class, then every
affine morphism to `DivScheme` is a classifier.  The proof factors the morphism through the
finite chart atlas, pulls the chart classes to the factorization pieces, and glues them with
the widened away-span theorem.  Classifier naturality and injectivity supply all overlap and
choice compatibility.
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

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepChartRangeAff :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))] [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable (g : Nat)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : Int))
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

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

/-- Pull a widened chart class along a point of its chart. -/
noncomputable def divRepPullAtAff
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    {S : Type u} [CommRing S] [Algebra k S]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S) : DivFamZarAff C S g :=
  DivFamZarAff.mapAlgHom omega (U i j)

set_option linter.unusedSectionVars false in
@[simp]
theorem divRepPullAtAff_comp
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    {S T : Type u} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
    (i : (glueData k g r1).J) (j : (glueData k g r2).J)
    (omega : ChartRing i j →ₐ[k] S) (phi : S →ₐ[k] T) :
    DivFamZarAff.mapAlgHom phi (divRepPullAtAff hpi g r1 r2 b1 b2 U i j omega) =
      divRepPullAtAff hpi g r1 r2 b1 b2 U i j (phi.comp omega) :=
  (DivFamZarAff.mapAlgHom_comp omega phi (U i j)).symm

set_option linter.unusedSectionVars false in
private theorem specMap_chartMap_pushforward
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {A B : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
    {i : (glueData k g r1).J} {j : (glueData k g r2).J}
    (omega : ChartRing i j →ₐ[k] A)
    (homega : Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j =
      Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v.left) :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j) =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ v.left := by
  have hSB : CommRingCat.ofHom (algebraMap S A) ≫ CommRingCat.ofHom (algebraMap A B) =
      CommRingCat.ofHom (algebraMap S B) := by
    rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [homega, ← Category.assoc, ← Spec.map_comp, hSB]

set_option maxHeartbeats 1600000 in
-- Both classifier naturality squares elaborate over the common localization tower.
/-- Pulls of chart-range witnesses agree over any common carrier. -/
theorem divRepPullAtAff_mapAlgHom_eq_of_chartFactor
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
        (ChartRing i j) (U i j)).left = ChartMap i j)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {A A' B : Type u}
    [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    [CommRing A'] [Algebra k A'] [Algebra S A'] [IsScalarTower k S A']
    [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
    [Algebra A' B] [IsScalarTower k A' B] [IsScalarTower S A' B]
    {i : (glueData k g r1).J} {j : (glueData k g r2).J}
    {i' : (glueData k g r1).J} {j' : (glueData k g r2).J}
    (omega : ChartRing i j →ₐ[k] A) (omega' : ChartRing i' j' →ₐ[k] A')
    (homega : Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j =
      Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v.left)
    (homega' : Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j' =
      Spec.map (CommRingCat.ofHom (algebraMap S A')) ≫ v.left) :
    DivFamZarAff.mapAlgHom (IsScalarTower.toAlgHom k A B)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U i j omega) =
      DivFamZarAff.mapAlgHom (IsScalarTower.toAlgHom k A' B)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U i' j' omega') := by
  apply divRepClassifyZarAff_injective hpi g hO hchi r1 r2 b1 b2
  apply Over.OverMorphism.ext
  let phi : A →ₐ[k] B := IsScalarTower.toAlgHom k A B
  let phi' : A' →ₐ[k] B := IsScalarTower.toAlgHom k A' B
  let FA := divRepPullAtAff hpi g r1 r2 b1 b2 U i j omega
  let FA' := divRepPullAtAff hpi g r1 r2 b1 b2 U i' j' omega'
  calc
    (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 B
        (DivFamZarAff.mapAlgHom phi FA)).left =
        Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
          (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 A FA).left :=
      (specMap_comp_divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 phi FA).symm
    _ = Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫
          (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
            (ChartRing i j) (U i j)).left) := by
      apply congrArg (fun z => Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ z)
      exact (specMap_comp_divRepClassifyZarAff hpi g hO hchi
        r1 r2 b1 b2 omega (U i j)).symm
    _ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j) := by
      rw [hU i j]
      rfl
    _ = Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ v.left :=
      specMap_chartMap_pushforward hpi g r1 r2 b1 b2 v omega homega
    _ = Spec.map (CommRingCat.ofHom (algebraMap A' B)) ≫
        (Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j') :=
      (specMap_chartMap_pushforward hpi g r1 r2 b1 b2 v omega' homega').symm
    _ = Spec.map (CommRingCat.ofHom phi'.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫
          (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
            (ChartRing i' j') (U i' j')).left) := by
      rw [hU i' j']
      rfl
    _ = Spec.map (CommRingCat.ofHom phi'.toRingHom) ≫
        (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 A' FA').left := by
      apply congrArg (fun z => Spec.map (CommRingCat.ofHom phi'.toRingHom) ≫ z)
      exact specMap_comp_divRepClassifyZarAff hpi g hO hchi
        r1 r2 b1 b2 omega' (U i' j')
    _ = (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 B
        (DivFamZarAff.mapAlgHom phi' FA')).left :=
      specMap_comp_divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 phi' FA'

set_option maxHeartbeats 1600000 in
-- The canonical overlap installs the two localization algebra structures at once.
theorem divRepPullAtAff_awayMul_compat
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
        (ChartRing i j) (U i j)).left = ChartMap i j)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m : Nat} (f : Fin m → S)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t, Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫
      ChartMap (ci t) (cj t) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left)
    (p q : Fin m) :
    DivFamZarAff.mapAlgHom (DivFamZar.awayMulLeft (k := k) f p q)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U (ci p) (cj p) (cw p)) =
      DivFamZarAff.mapAlgHom (DivFamZar.awayMulRight (k := k) f p q)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U (ci q) (cj q) (cw q)) := by
  classical
  letI : Algebra (Localization.Away (f p)) (Localization.Away (f p * f q)) :=
    (DivFamZar.awayMulLeft (k := k) f p q).toRingHom.toAlgebra
  letI : Algebra (Localization.Away (f q)) (Localization.Away (f p * f q)) :=
    (DivFamZar.awayMulRight (k := k) f p q).toRingHom.toAlgebra
  haveI : IsScalarTower S (Localization.Away (f p))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f p * f q) (f p) (f q) rfl x).symm)
  haveI : IsScalarTower S (Localization.Away (f q))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f p * f q) (f q) (f p) (mul_comm _ _) x).symm)
  haveI : IsScalarTower k (Localization.Away (f p))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulLeft (k := k) f p q).commutes x).symm)
  haveI : IsScalarTower k (Localization.Away (f q))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulRight (k := k) f p q).commutes x).symm)
  have hL : IsScalarTower.toAlgHom k (Localization.Away (f p))
      (Localization.Away (f p * f q)) = DivFamZar.awayMulLeft (k := k) f p q :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f p)) (Localization.Away (f p * f q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  have hR : IsScalarTower.toAlgHom k (Localization.Away (f q))
      (Localization.Away (f p * f q)) = DivFamZar.awayMulRight (k := k) f p q :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f q)) (Localization.Away (f p * f q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  rw [← hL, ← hR]
  exact divRepPullAtAff_mapAlgHom_eq_of_chartFactor hpi g hO hchi
    r1 r2 b1 b2 U hU v (cw p) (cw q) (hcw p) (hcw q)

set_option maxHeartbeats 2400000 in
-- Atlas factorization, widened class gluing, and classifier naturality elaborate together.
/-- Every affine morphism to `DivScheme` is classified once every chart map is in range. -/
theorem exists_divRepClassifyZarAff_eq_of_chartRange
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
        (ChartRing i j) (U i j)).left = ChartMap i j)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    ∃ F : DivFamZarAff C S g,
      divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 S F = v := by
  classical
  obtain ⟨m, f, hspan, hdata⟩ := divScheme_exists_chartFactor
    k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
      (b2.map (windowShiftEquiv hpi g).symm) S v
  choose ci cj cw hcw using hdata
  obtain ⟨F, hF⟩ := DivFamZarAff.exists_glue_of_awaySpan f hspan
    (fun t => divRepPullAtAff hpi g r1 r2 b1 b2 U (ci t) (cj t) (cw t))
    (divRepPullAtAff_awayMul_compat hpi g hO hchi r1 r2 b1 b2
      U hU v f ci cj cw hcw)
  refine ⟨F, ?_⟩
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hspan).openCover
      _ _ fun t => ?_
  let q : Fin m := t
  let phi : S →ₐ[k] Localization.Away (f q) :=
    IsScalarTower.toAlgHom k S (Localization.Away (f q))
  change Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
      (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 S F).left =
    Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ v.left
  calc
    _ = (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
        (Localization.Away (f q)) (DivFamZarAff.mapAlgHom phi F)).left :=
      specMap_comp_divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2 phi F
    _ = (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
        (Localization.Away (f q))
          (divRepPullAtAff hpi g r1 r2 b1 b2 U (ci q) (cj q) (cw q))).left := by
      rw [hF q]
    _ = Spec.map (CommRingCat.ofHom (cw q).toRingHom) ≫
        (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
          (ChartRing (ci q) (cj q)) (U (ci q) (cj q))).left :=
      (specMap_comp_divRepClassifyZarAff hpi g hO hchi
        r1 r2 b1 b2 (cw q) (U (ci q) (cj q))).symm
    _ = Spec.map (CommRingCat.ofHom (cw q).toRingHom) ≫
        ChartMap (ci q) (cj q) := by rw [hU (ci q) (cj q)]
    _ = Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ v.left := by
      have hphi : phi.toRingHom = algebraMap S (Localization.Away (f q)) := rfl
      rw [hphi]
      exact hcw q

/-- Chart-range witnesses represent the widened divisor functor by `DivScheme`. -/
noncomputable def divFunctorAff_representableBy_of_chartRange
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff hpi g hO hchi r1 r2 b1 b2
        (ChartRing i j) (U i j)).left = ChartMap i j) :
    (divFunctorAff C g).RepresentableBy DivOver :=
  DivRepAffinePullbackAff.representableBy hpi g hO hchi r1 r2 b1 b2
    (DivRepAffinePullbackAff.ofClassifierSurjective hpi g hO hchi r1 r2 b1 b2
      (fun S _ _ v =>
        exists_divRepClassifyZarAff_eq_of_chartRange
          hpi g hO hchi r1 r2 b1 b2 U hU S v))

set_option maxHeartbeats 1600000 in
-- Both off-diagonal classifier naturality squares elaborate over the common carrier.
/-- Pulls of off-diagonal chart-range witnesses agree over any common carrier. -/
theorem divRepPullAtAff_mapAlgHom_eq_of_chartFactor_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff_at (S := ChartRing i j) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)).left = ChartMap i j)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {A A' B : Type u}
    [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    [CommRing A'] [Algebra k A'] [Algebra S A'] [IsScalarTower k S A']
    [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
    [Algebra A' B] [IsScalarTower k A' B] [IsScalarTower S A' B]
    {i : (glueData k g r1).J} {j : (glueData k g r2).J}
    {i' : (glueData k g r1).J} {j' : (glueData k g r2).J}
    (omega : ChartRing i j →ₐ[k] A) (omega' : ChartRing i' j' →ₐ[k] A')
    (homega : Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j =
      Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫ v.left)
    (homega' : Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j' =
      Spec.map (CommRingCat.ofHom (algebraMap S A')) ≫ v.left) :
    DivFamZarAff.mapAlgHom (IsScalarTower.toAlgHom k A B)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U i j omega) =
      DivFamZarAff.mapAlgHom (IsScalarTower.toAlgHom k A' B)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U i' j' omega') := by
  apply divRepClassifyZarAff_injective_at
    (hπ := hpi) (g := g) (r₁ := r1) (r₂ := r2) (b₁ := b1) (b₂ := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma) (hχgamma := hchiGamma)
  apply Over.OverMorphism.ext
  let phi : A →ₐ[k] B := IsScalarTower.toAlgHom k A B
  let phi' : A' →ₐ[k] B := IsScalarTower.toAlgHom k A' B
  let FA := divRepPullAtAff hpi g r1 r2 b1 b2 U i j omega
  let FA' := divRepPullAtAff hpi g r1 r2 b1 b2 U i' j' omega'
  calc
    (divRepClassifyZarAff_at (S := B) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma
        (DivFamZarAff.mapAlgHom phi FA)).left =
        Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
          (divRepClassifyZarAff_at (S := A) (gamma := gamma)
            hpi g r1 r2 b1 b2 hgamma hchiGamma FA).left :=
      (specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma phi FA).symm
    _ = Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫
          (divRepClassifyZarAff_at (S := ChartRing i j) (gamma := gamma)
            hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)).left) := by
      apply congrArg (fun z => Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ z)
      exact (specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma omega (U i j)).symm
    _ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        (Spec.map (CommRingCat.ofHom omega.toRingHom) ≫ ChartMap i j) := by
      rw [hU i j]
      rfl
    _ = Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫ v.left :=
      specMap_chartMap_pushforward hpi g r1 r2 b1 b2 v omega homega
    _ = Spec.map (CommRingCat.ofHom (algebraMap A' B)) ≫
        (Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫ ChartMap i' j') :=
      (specMap_chartMap_pushforward hpi g r1 r2 b1 b2 v omega' homega').symm
    _ = Spec.map (CommRingCat.ofHom phi'.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom omega'.toRingHom) ≫
          (divRepClassifyZarAff_at (S := ChartRing i' j') (gamma := gamma)
            hpi g r1 r2 b1 b2 hgamma hchiGamma (U i' j')).left) := by
      rw [hU i' j']
      rfl
    _ = Spec.map (CommRingCat.ofHom phi'.toRingHom) ≫
        (divRepClassifyZarAff_at (S := A') (gamma := gamma)
          hpi g r1 r2 b1 b2 hgamma hchiGamma FA').left := by
      apply congrArg (fun z => Spec.map (CommRingCat.ofHom phi'.toRingHom) ≫ z)
      exact specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma omega' (U i' j')
    _ = (divRepClassifyZarAff_at (S := B) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma
        (DivFamZarAff.mapAlgHom phi' FA')).left :=
      specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma phi' FA'

set_option maxHeartbeats 1600000 in
-- The off-diagonal overlap installs both localization algebra structures at once.
/-- Off-diagonal chart pulls agree on every canonical double localization. -/
theorem divRepPullAtAff_awayMul_compat_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff_at (S := ChartRing i j) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)).left = ChartMap i j)
    {S : Type u} [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver)
    {m : Nat} (f : Fin m → S)
    (ci : Fin m → (glueData k g r1).J) (cj : Fin m → (glueData k g r2).J)
    (cw : ∀ t, ChartRing (ci t) (cj t) →ₐ[k] Localization.Away (f t))
    (hcw : ∀ t, Spec.map (CommRingCat.ofHom (cw t).toRingHom) ≫
      ChartMap (ci t) (cj t) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f t)))) ≫ v.left)
    (p q : Fin m) :
    DivFamZarAff.mapAlgHom (DivFamZar.awayMulLeft (k := k) f p q)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U (ci p) (cj p) (cw p)) =
      DivFamZarAff.mapAlgHom (DivFamZar.awayMulRight (k := k) f p q)
        (divRepPullAtAff hpi g r1 r2 b1 b2 U (ci q) (cj q) (cw q)) := by
  classical
  letI : Algebra (Localization.Away (f p)) (Localization.Away (f p * f q)) :=
    (DivFamZar.awayMulLeft (k := k) f p q).toRingHom.toAlgebra
  letI : Algebra (Localization.Away (f q)) (Localization.Away (f p * f q)) :=
    (DivFamZar.awayMulRight (k := k) f p q).toRingHom.toAlgebra
  haveI : IsScalarTower S (Localization.Away (f p))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f p * f q) (f p) (f q) rfl x).symm)
  haveI : IsScalarTower S (Localization.Away (f q))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact (DivFamZar.awayMulOfDvd_algebraMap
        (k := k) (f p * f q) (f q) (f p) (mul_comm _ _) x).symm)
  haveI : IsScalarTower k (Localization.Away (f p))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulLeft (k := k) f p q).commutes x).symm)
  haveI : IsScalarTower k (Localization.Away (f q))
      (Localization.Away (f p * f q)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      exact ((DivFamZar.awayMulRight (k := k) f p q).commutes x).symm)
  have hL : IsScalarTower.toAlgHom k (Localization.Away (f p))
      (Localization.Away (f p * f q)) = DivFamZar.awayMulLeft (k := k) f p q :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f p)) (Localization.Away (f p * f q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  have hR : IsScalarTower.toAlgHom k (Localization.Away (f q))
      (Localization.Away (f p * f q)) = DivFamZar.awayMulRight (k := k) f p q :=
    AlgHom.ext fun x => by
      change algebraMap (Localization.Away (f q)) (Localization.Away (f p * f q)) x = _
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  rw [← hL, ← hR]
  exact divRepPullAtAff_mapAlgHom_eq_of_chartFactor_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma) U hU v (cw p) (cw q) (hcw p) (hcw q)

set_option maxHeartbeats 2400000 in
-- Atlas factorization, off-diagonal gluing, and classifier naturality elaborate together.
/-- Every affine morphism is classified when every chart map lies in the off-diagonal range. -/
theorem exists_divRepClassifyZarAff_eq_of_chartRange_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff_at (S := ChartRing i j) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)).left = ChartMap i j)
    (S : Type u) [CommRing S] [Algebra k S] (v : overSpec k S ⟶ DivOver) :
    ∃ F : DivFamZarAff C S g,
      divRepClassifyZarAff_at (S := S) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma F = v := by
  classical
  obtain ⟨m, f, hspan, hdata⟩ := divScheme_exists_chartFactor
    k (windowS_choice pi hpi g • fiberWeilDivisor pi)
      (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
      (b2.map (windowShiftEquiv hpi g).symm) S v
  choose ci cj cw hcw using hdata
  obtain ⟨F, hF⟩ := DivFamZarAff.exists_glue_of_awaySpan f hspan
    (fun t => divRepPullAtAff hpi g r1 r2 b1 b2 U (ci t) (cj t) (cw t))
    (divRepPullAtAff_awayMul_compat_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
      (hchiGamma := hchiGamma) U hU v f ci cj cw hcw)
  refine ⟨F, ?_⟩
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hspan).openCover
      _ _ fun t => ?_
  let q : Fin m := t
  let phi : S →ₐ[k] Localization.Away (f q) :=
    IsScalarTower.toAlgHom k S (Localization.Away (f q))
  change Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
      (divRepClassifyZarAff_at (S := S) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma F).left =
    Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ v.left
  calc
    _ = (divRepClassifyZarAff_at (S := Localization.Away (f q)) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (DivFamZarAff.mapAlgHom phi F)).left :=
      specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma phi F
    _ = (divRepClassifyZarAff_at (S := Localization.Away (f q)) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma
        (divRepPullAtAff hpi g r1 r2 b1 b2 U (ci q) (cj q) (cw q))).left := by
      rw [hF q]
    _ = Spec.map (CommRingCat.ofHom (cw q).toRingHom) ≫
        (divRepClassifyZarAff_at (S := ChartRing (ci q) (cj q)) (gamma := gamma)
          hpi g r1 r2 b1 b2 hgamma hchiGamma (U (ci q) (cj q))).left :=
      (specMap_comp_divRepClassifyZarAff_at (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (cw q) (U (ci q) (cj q))).symm
    _ = Spec.map (CommRingCat.ofHom (cw q).toRingHom) ≫
        ChartMap (ci q) (cj q) := by rw [hU (ci q) (cj q)]
    _ = Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ v.left := by
      have hphi : phi.toRingHom = algebraMap S (Localization.Away (f q)) := rfl
      rw [hphi]
      exact hcw q

/-- Off-diagonal chart-range witnesses represent the degree-`g` divisor functor. -/
noncomputable def divFunctorAff_representableBy_of_chartRange_at
    (hOAt : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    {gamma : Nat} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : Int))
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZarAff C (ChartRing i j) g)
    (hU : ∀ i j,
      (divRepClassifyZarAff_at (S := ChartRing i j) (gamma := gamma)
        hpi g r1 r2 b1 b2 hgamma hchiGamma (U i j)).left = ChartMap i j) :
    (divFunctorAff C g).RepresentableBy DivOver :=
  DivRepAffinePullbackAff.representableBy_at
    (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
    (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
    (hchiGamma := hchiGamma)
    (DivRepAffinePullbackAff.ofClassifierSurjective_at
      (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
      (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
      (hchiGamma := hchiGamma)
      (fun S _ _ v =>
        exists_divRepClassifyZarAff_eq_of_chartRange_at
          (hpi := hpi) (g := g) (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2)
          (hOAt := hOAt) (gamma := gamma) (hgamma := hgamma)
          (hchiGamma := hchiGamma) U hU S v))

end Curve

end AlgebraicGeometry
