/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarAffCompat
import AlgebraicJacobian.Picard.DivSchemeKeyChart

/-!
# The widened affine backward divisor classifier

Every widened locally certified divisor class over an affine test determines a unique morphism
to `DivScheme`.  The construction glues the local factors supplied by the canonical widened
certificate-and-frame cover.  Its characterizing clause quantifies over every widened certified
representative on every algebra test, so it is stable under refinement and change of
representative.

This is the unconditional hom-side classifier for `DivFamZarAff`; it introduces no chart typing
or additional certificate hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Grassmannian Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftRepClassifyZarAff :
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
variable {S : Type u} [CommRing S] [Algebra k S]

/-- The refinement-stable characterizing clause for the widened backward classifier. -/
def IsDivRepClassifyAff (F₀ : DivFamZarAff C S g)
    (v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (G : CertifiedDivisorFamilyAff C T g),
    G.toZarAff = DivFamZarAff.mapAlg T g F₀ →
    ∀ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
      (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T),
      G.IsPairChartFramed hpi g b₁ b₂ i j w →
      Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ v ≫
          divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
            (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hpi g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom)
            ≫ pairChartMap k g r₁ g r₂ i j

set_option maxHeartbeats 2400000 in
-- The cover glue and its arbitrary-test pullback instantiate the tensor-overlap comparison.
include hO hchi in
/-- Every widened affine divisor class admits a morphism satisfying the characterizing clause. -/
theorem exists_isDivRepClassifyAff (F₀ : DivFamZarAff C S g) :
    ∃ v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v := by
  classical
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZarAff.exists_certChartCover hpi g hO hchi r₁ r₂ b₁ b₂ F₀
  choose G ci cj cw hZ hframe using hdata
  have hv : ∀ p : Fin m,
      ∃ vp : Spec (CommRingCat.of (Localization.Away (r p))) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      vp ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
        = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
            ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) := fun p =>
    ((G p).existsUnique_divClassify hpi g r₁ r₂ b₁ b₂
      (cw p) (hframe p)).exists
  choose v hvc using hv
  have hglue : ∀ p q : Fin m,
      pullback.fst ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) r hspan).openCover.f p)
        ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) r hspan).openCover.f q) ≫ v p
      = pullback.snd _ _ ≫ v q := fun p q =>
    pullback_divClassifyAff_compat hpi g hO hchi r₁ r₂ b₁ b₂ F₀
      (G p) (G q) (hZ p) (hZ q) (cw p) (cw q) (hframe p) (hframe q)
      (hvc p) (hvc q)
  refine ⟨(Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of S) r hspan).openCover.glueMorphisms v hglue, ?_⟩
  intro T _ _ _ _ GT hGT i j w hw
  refine Scheme.Cover.hom_ext
    ((Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) r hspan).openCover.pullback₁
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    _ _ fun p => ?_
  change pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
  rw [← Category.assoc, pullback.condition, Category.assoc,
    Scheme.Cover.ι_glueMorphisms_assoc]
  exact (pullback_chart_divClassifyAff_compat hpi g hO hchi r₁ r₂ b₁ b₂
    F₀ GT hGT w hw (G p) (hZ p) (cw p) (hframe p) (hvc p)).symm

set_option maxHeartbeats 800000 in
-- Uniqueness instantiates the characterizing clause on every piece of the composite cover.
include hO hchi in
/-- The widened characterizing clause determines its morphism uniquely. -/
theorem isDivRepClassifyAff_unique (F₀ : DivFamZarAff C S g)
    {v v' : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv : IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v)
    (hv' : IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v') : v = v' := by
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZarAff.exists_certChartCover hpi g hO hchi r₁ r₂ b₁ b₂ F₀
  choose G ci cj cw hZ hframe using hdata
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) r hspan).openCover _ _ fun p => ?_
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hpi g).symm) _ _ ?_
  have h₁ : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) r hspan).openCover.f p ≫ v ≫
        divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) :=
    hv (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hframe p)
  have h₂ : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) r hspan).openCover.f p ≫ v' ≫
        divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) :=
    hv' (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hframe p)
  rw [Category.assoc, Category.assoc]
  exact h₁.trans h₂.symm

include hO hchi in
/-- A widened affine divisor class classifies to a unique clause-satisfying morphism. -/
theorem divClassifyZarAff (F₀ : DivFamZarAff C S g) :
    ∃! v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v := by
  obtain ⟨v, hv⟩ := exists_isDivRepClassifyAff hpi g hO hchi r₁ r₂ b₁ b₂ F₀
  exact ⟨v, hv, fun v' hv' =>
    isDivRepClassifyAff_unique hpi g hO hchi r₁ r₂ b₁ b₂ F₀ hv' hv⟩

include hO hchi in
/-- The widened classified morphism, packaged in the slice over `Spec k`. -/
theorem exists_overHom_isDivRepClassifyAff (F₀ : DivFamZarAff C S g) :
    ∃ u : overSpec k S ⟶
        divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ u.left := by
  obtain ⟨v, hv⟩ := exists_isDivRepClassifyAff hpi g hO hchi r₁ r₂ b₁ b₂ F₀
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZarAff.exists_certChartCover hpi g hO hchi r₁ r₂ b₁ b₂ F₀
  choose G ci cj cw hZ hframe using hdata
  exact ⟨divSchemeOverHomMk k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hpi g).symm) v r hspan
    (fun p => ⟨ci p, cj p, cw p,
      hv (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hframe p)⟩), hv⟩

variable (S) in
/-- The widened backward classification as a morphism over `Spec k`. -/
noncomputable def divRepClassifyZarAff (F₀ : DivFamZarAff C S g) :
    overSpec k S ⟶
      divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm) :=
  (exists_overHom_isDivRepClassifyAff hpi g hO hchi r₁ r₂ b₁ b₂ F₀).choose

include hO hchi in
/-- The widened classified morphism satisfies its refinement-stable clause. -/
theorem divRepClassifyZarAff_isDivRepClassifyAff (F₀ : DivFamZarAff C S g) :
    IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀
      (divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ S F₀).left :=
  (exists_overHom_isDivRepClassifyAff hpi g hO hchi r₁ r₂ b₁ b₂ F₀).choose_spec

include hO hchi in
/-- Any over-morphism satisfying the widened clause is the classified morphism. -/
theorem divRepClassifyZarAff_eq_of_isDivRepClassifyAff (F₀ : DivFamZarAff C S g)
    (u : overSpec k S ⟶
      divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm))
    (hu : IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ u.left) :
    u = divRepClassifyZarAff hpi g hO hchi r₁ r₂ b₁ b₂ S F₀ :=
  Over.OverMorphism.ext (isDivRepClassifyAff_unique hpi g hO hchi r₁ r₂ b₁ b₂
    F₀ hu (divRepClassifyZarAff_isDivRepClassifyAff hpi g hO hchi r₁ r₂ b₁ b₂ F₀))

set_option maxHeartbeats 2400000 in
-- The off-diagonal cover glue and arbitrary-test pullback share the compatibility branch.
/-- Every widened affine divisor class admits a clause-satisfying morphism when the curve
parameter is independent of the divisor-family degree. -/
theorem exists_isDivRepClassifyAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g) :
    ∃ v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v := by
  classical
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZarAff.exists_certChartCover_at hpi g r₁ r₂ b₁ b₂ F₀ hgamma hchiGamma
  choose G ci cj cw hZ hframe using hdata
  have hv : ∀ p : Fin m,
      ∃ vp : Spec (CommRingCat.of (Localization.Away (r p))) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      vp ≫ divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
        = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
            ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) := fun p =>
    ((G p).existsUnique_divClassify hpi g r₁ r₂ b₁ b₂
      (cw p) (hframe p)).exists
  choose v hvc using hv
  have hglue : ∀ p q : Fin m,
      pullback.fst ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) r hspan).openCover.f p)
        ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) r hspan).openCover.f q) ≫ v p
      = pullback.snd _ _ ≫ v q := fun p q =>
    pullback_divClassifyAff_compat_at (gamma := gamma) hpi g r₁ r₂ b₁ b₂
      hgamma hchiGamma F₀ (G p) (G q) (hZ p) (hZ q) (cw p) (cw q)
      (hframe p) (hframe q) (hvc p) (hvc q)
  refine ⟨(Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of S) r hspan).openCover.glueMorphisms v hglue, ?_⟩
  intro T _ _ _ _ GT hGT i j w hw
  refine Scheme.Cover.hom_ext
    ((Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) r hspan).openCover.pullback₁
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    _ _ fun p => ?_
  change pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
  rw [← Category.assoc, pullback.condition, Category.assoc,
    Scheme.Cover.ι_glueMorphisms_assoc]
  exact (pullback_chart_divClassifyAff_compat_at (gamma := gamma)
    hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀ GT hGT w hw
    (G p) (hZ p) (cw p) (hframe p) (hvc p)).symm

set_option maxHeartbeats 800000 in
-- Uniqueness uses the off-diagonal certificate-frame cover on every glued piece.
/-- The widened characterizing clause determines its morphism uniquely at an independent
curve parameter. -/
theorem isDivRepClassifyAff_unique_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g)
    {v v' : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm)}
    (hv : IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v)
    (hv' : IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v') : v = v' := by
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZarAff.exists_certChartCover_at hpi g r₁ r₂ b₁ b₂ F₀ hgamma hchiGamma
  choose G ci cj cw hZ hframe using hdata
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) r hspan).openCover _ _ fun p => ?_
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hpi g).symm) _ _ ?_
  have h₁ : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) r hspan).openCover.f p ≫ v ≫
        divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) :=
    hv (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hframe p)
  have h₂ : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) r hspan).openCover.f p ≫ v' ≫
        divSchemeι k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm)
      = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) :=
    hv' (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hframe p)
  rw [Category.assoc, Category.assoc]
  exact h₁.trans h₂.symm

/-- A widened affine divisor class classifies to a unique morphism at an independent curve
parameter. -/
theorem divClassifyZarAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g) :
    ∃! v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ v := by
  obtain ⟨v, hv⟩ := exists_isDivRepClassifyAff_at
    (gamma := gamma) hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀
  exact ⟨v, hv, fun v' hv' =>
    isDivRepClassifyAff_unique_at (gamma := gamma)
      hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀ hv' hv⟩

/-- The widened classified morphism over `Spec k` at an independent curve parameter. -/
theorem exists_overHom_isDivRepClassifyAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g) :
    ∃ u : overSpec k S ⟶
        divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
          (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hpi g).symm),
      IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ u.left := by
  obtain ⟨v, hv⟩ := exists_isDivRepClassifyAff_at
    (gamma := gamma) hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZarAff.exists_certChartCover_at hpi g r₁ r₂ b₁ b₂ F₀ hgamma hchiGamma
  choose G ci cj cw hZ hframe using hdata
  exact ⟨divSchemeOverHomMk k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hpi g).symm) v r hspan
    (fun p => ⟨ci p, cj p, cw p,
      hv (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hframe p)⟩), hv⟩

variable (S) in
/-- The widened backward classifier at an independent curve parameter. -/
noncomputable def divRepClassifyZarAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g) :
    overSpec k S ⟶
      divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm) :=
  (exists_overHom_isDivRepClassifyAff_at
    (gamma := gamma) hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀).choose

/-- The off-diagonal widened classifier satisfies its refinement-stable clause. -/
theorem divRepClassifyZarAff_isDivRepClassifyAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g) :
    IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀
      (divRepClassifyZarAff_at (S := S) hpi g r₁ r₂ b₁ b₂
        (gamma := gamma) hgamma hchiGamma F₀).left :=
  (exists_overHom_isDivRepClassifyAff_at
    (gamma := gamma) hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀).choose_spec

/-- Any over-morphism satisfying the widened clause is the off-diagonal classified morphism. -/
theorem divRepClassifyZarAff_eq_of_isDivRepClassifyAff_at
    {gamma : ℕ} (hgamma : gamma ≤ g)
    (hchiGamma : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (gamma : ℤ))
    (F₀ : DivFamZarAff C S g)
    (u : overSpec k S ⟶
      divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hpi g).symm))
    (hu : IsDivRepClassifyAff hpi g r₁ r₂ b₁ b₂ F₀ u.left) :
    u = divRepClassifyZarAff_at (S := S) hpi g r₁ r₂ b₁ b₂
      (gamma := gamma) hgamma hchiGamma F₀ :=
  Over.OverMorphism.ext
    (isDivRepClassifyAff_unique_at (gamma := gamma)
      hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀ hu
      (divRepClassifyZarAff_isDivRepClassifyAff_at (gamma := gamma)
        hpi g r₁ r₂ b₁ b₂ hgamma hchiGamma F₀))

end Curve

end AlgebraicGeometry
