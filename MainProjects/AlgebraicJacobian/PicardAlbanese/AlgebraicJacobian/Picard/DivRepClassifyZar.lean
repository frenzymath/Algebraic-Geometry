/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarCompat
import AlgebraicJacobian.Picard.DivSchemeEpsCarve
import AlgebraicJacobian.Picard.DivSchemeKeyChart

/-!
# F4 — the backward direction of `divRepAff` at the Zar layer
(`informal/w4-ddr9-worksheet.md` §2.1, steps 1, 3, 5, 6)

A locally certified divisor class `F₀ : DivFamZar C S π g` over an affine test `S`
classifies to a **unique** morphism `overSpec k S ⟶ divSchemeOver g` — the content of
`divRepAff.symm`.  Construction: the composite certificate × frame cover of the Kit
(`DivFamZar.exists_certChartCover`), `divClassify` fired at each certified
representative with the carve discharged by DDR-9.0 (`divFamEps_carve`), the glue by
`Scheme.Cover.glueMorphisms` with overlap agreement through the clause-transport
layer, and the Over packaging by `divSchemeOverHomMk` (F2).

* `AlgebraicGeometry.IsDivRepClassify` — **the characterizing clause** (the
  refinement-stable form F6 consumes): over EVERY `k`/`S`-tower test `T` carrying a
  certified representative `G` of the restricted class and a pair-chart framing of
  `ε (DivFam.mk G)`, the morphism chart-factors.  No localization hypothesis on `T`
  — stability under refinement of covers and change of representative is built into
  the quantifier.
* `AlgebraicGeometry.divClassifyZar` — **the ∃!-keystone**: `F₀` classifies to a
  unique clause-satisfier `Spec S ⟶ DivScheme g` (overlap layer:
  `Picard/DivRepClassifyZarCompat.lean`).
* `AlgebraicGeometry.divRepClassifyZar` — **the keystone map**
  `DivFamZar C S π g → (overSpec k S ⟶ divSchemeOver g)`, with the characterizing
  lemma `divRepClassifyZar_isDivRepClassify` and the well-definedness lemma
  `divRepClassifyZar_eq_of_isDivRepClassify` (any Over-hom whose scheme morphism
  satisfies the clause IS the classified one — Law 2's uniqueness input).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftRepClassifyZar :
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
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
variable {S : Type u} [CommRing S] [Algebra k S]

/-- **The characterizing clause of the backward classification** (w4-ddr9 §2.1
step 6, the refinement-stable form): over EVERY `k`/`S`-tower test `T` carrying a
certified representative `G` of the restriction of `F₀` and a pair-chart framing of
`ε (DivFam.mk G)`, the restriction of `v` composes with `divSchemeι` to the chart
morphism of the framing.  Quantifying over all tests and all representatives makes
the clause stable under refinement of covers and change of representative by
construction — F6's Law 1/Law 2 consume it without unfolding any choice. -/
def IsDivRepClassify (F₀ : DivFamZar C S π g)
    (v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (G : CertifiedDivisorFamily C T π g),
    (DivFam.mk G).toZar = DivFamZar.mapAlg T g F₀ →
    ∀ (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
      (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T),
      (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
          = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
              (divFamEps hπ g (DivFam.mk G)).1 →
      (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
          = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
              (divFamEps hπ g (DivFam.mk G)).2 →
      Spec.map (CommRingCat.ofHom (algebraMap S T))
          ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j

/-! ## The keystone -/

set_option maxHeartbeats 1600000 in
include hO hχ in
/-- **Existence half of the backward classification** (w4-ddr9 §2.1 steps 3 and 5):
the per-piece `divClassify` outputs over the composite certificate × frame cover —
with the carve discharged by DDR-9.0 (`divFamEps_carve`) — glue to a morphism
`Spec S ⟶ DivScheme g` satisfying the characterizing clause. -/
theorem exists_isDivRepClassify (F₀ : DivFamZar C S π g) :
    ∃ v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
      IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ v := by
  classical
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZar.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  choose G ci cj cw hZ hcw₁ hcw₂ using hdata
  have hv : ∀ p : Fin m,
      ∃ vp : Spec (CommRingCat.of (Localization.Away (r p))) ⟶
        DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
      DivClassifyClause hπ g r₁ r₂ b₁ b₂ (DivFam.mk (G p)) vp := fun p =>
    (divClassify hπ g hO hχ r₁ r₂ b₁ b₂ (DivFam.mk (G p))
      (fun a => divFamEps_carve C π hπ g (Localization.Away (r p)) (G p) a)).exists
  choose v hvc using hv
  have hglue : ∀ p q : Fin m,
      pullback.fst ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) r hspan).openCover.f p)
        ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) r hspan).openCover.f q) ≫ v p
      = pullback.snd _ _ ≫ v q := fun p q =>
    pullback_divClassifyClause_compat hπ g hO hχ r₁ r₂ b₁ b₂ F₀
      (DivFam.mk (G p)) (DivFam.mk (G q)) (hZ p) (hZ q) (hvc p) (hvc q)
  refine ⟨(Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of S) r hspan).openCover.glueMorphisms v hglue, ?_⟩
  intro T _ _ _ _ GT hGT i j ω hω₁ hω₂
  refine Scheme.Cover.hom_ext
    ((Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) r hspan).openCover.pullback₁
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    _ _ fun p => ?_
  change pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
  rw [← Category.assoc, pullback.condition, Category.assoc,
    Scheme.Cover.ι_glueMorphisms_assoc]
  exact (pullback_chart_divClassifyClause_compat hπ g hO hχ r₁ r₂ b₁ b₂ F₀
    GT hGT ω hω₁ hω₂ (DivFam.mk (G p)) (hZ p) (hvc p)).symm

set_option maxHeartbeats 800000 in
include hO hχ in
/-- **Uniqueness / full choice-independence** (w4-ddr9 §2.1 step 6): any two
morphisms satisfying the characterizing clause for `F₀` agree — compare over the
composite certificate × frame cover (`divScheme_hom_ext` per piece,
`Scheme.Cover.hom_ext` globally).  In particular the classified morphism does not
depend on the choice of representatives, certificate cover, or frame covers. -/
theorem isDivRepClassify_unique (F₀ : DivFamZar C S π g)
    {v v' : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ v)
    (hv' : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ v') : v = v' := by
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZar.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  choose G ci cj cw hZ hcw₁ hcw₂ using hdata
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) r hspan).openCover _ _ fun p => ?_
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁ (b₂.map (windowShiftEquiv hπ g).symm)
    _ _ ?_
  have h1 : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) r hspan).openCover.f p
        ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) :=
    hv (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hcw₁ p) (hcw₂ p)
  have h2 : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) r hspan).openCover.f p
        ≫ v' ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom (cw p).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci p) (cj p) :=
    hv' (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p) (hcw₁ p) (hcw₂ p)
  rw [Category.assoc, Category.assoc]
  exact h1.trans h2.symm

include hO hχ in
/-- **The ∃!-keystone of the backward direction** (w4-ddr9 §2.1): a locally
certified divisor class over an affine test classifies to a UNIQUE morphism
`Spec S ⟶ DivScheme g` satisfying the characterizing clause. -/
theorem divClassifyZar (F₀ : DivFamZar C S π g) :
    ∃! v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
      IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ v := by
  obtain ⟨v, hv⟩ := exists_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  exact ⟨v, hv, fun v' hv' =>
    isDivRepClassify_unique hπ g hO hχ r₁ r₂ b₁ b₂ F₀ hv' hv⟩

/-! ## The Over packaging -/

include hO hχ in
/-- **The classified morphism, packaged over `Spec k`**: the clause-satisfier carries
the Over-triangle — its `divSchemeι`-composite is chart-presented over the composite
certificate × frame cover, so `divSchemeOverHomMk` (F2) applies. -/
theorem exists_overHom_isDivRepClassify (F₀ : DivFamZar C S π g) :
    ∃ u : overSpec k S ⟶
        divSchemeOver k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
      IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ u.left := by
  obtain ⟨v, hv⟩ := exists_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  obtain ⟨m, r, hspan, hdata⟩ :=
    DivFamZar.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  choose G ci cj cw hZ hcw₁ hcw₂ using hdata
  exact ⟨divSchemeOverHomMk k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
    (b₂.map (windowShiftEquiv hπ g).symm) v r hspan
    (fun p => ⟨ci p, cj p, cw p,
      hv (Localization.Away (r p)) (G p) (hZ p) (ci p) (cj p) (cw p)
        (hcw₁ p) (hcw₂ p)⟩), hv⟩

variable (S) in
/-- **The keystone of F4** (w4-ddr9 §2.1, `divRepAff.symm`'s content): the backward
classification of locally certified divisor classes over an affine test, as a
morphism of `Over (Spec k)`.  Characterized by `divRepClassifyZar_isDivRepClassify`;
independent of every choice by `divRepClassifyZar_eq_of_isDivRepClassify`. -/
noncomputable def divRepClassifyZar (F₀ : DivFamZar C S π g) :
    overSpec k S ⟶
      divSchemeOver k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm) :=
  (exists_overHom_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀).choose

include hO hχ in
/-- **The characterizing lemma of `divRepClassifyZar`** (the F6 interface): the
classified morphism satisfies the clause — over every `k`/`S`-tower test with a
certified representative of the restricted class and a pair-chart framing of its ε
pair, it restricts to the chart morphism. -/
theorem divRepClassifyZar_isDivRepClassify (F₀ : DivFamZar C S π g) :
    IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀
      (divRepClassifyZar hπ g hO hχ r₁ r₂ b₁ b₂ S F₀).left :=
  (exists_overHom_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀).choose_spec

include hO hχ in
/-- **Well-definedness / the uniqueness interface of `divRepClassifyZar`** (Law 2's
input): ANY morphism of `Over (Spec k)` whose underlying scheme morphism satisfies
the characterizing clause for `F₀` is the classified morphism. -/
theorem divRepClassifyZar_eq_of_isDivRepClassify (F₀ : DivFamZar C S π g)
    (u : overSpec k S ⟶
      divSchemeOver k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm))
    (hu : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ u.left) :
    u = divRepClassifyZar hπ g hO hχ r₁ r₂ b₁ b₂ S F₀ :=
  Over.OverMorphism.ext (isDivRepClassify_unique hπ g hO hχ r₁ r₂ b₁ b₂ F₀ hu
    (divRepClassifyZar_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀))

end Curve

end AlgebraicGeometry
