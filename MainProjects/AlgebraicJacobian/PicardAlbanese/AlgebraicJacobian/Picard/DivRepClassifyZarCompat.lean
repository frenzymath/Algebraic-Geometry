/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZarKit

/-!
# F4 — the overlap comparisons of the backward Zar classification
(`informal/w4-ddr9-worksheet.md` §2.1, the step-5/step-6 overlap layer)

The comparison lemmas consumed by `Picard/DivRepClassifyZar.lean`: two `divClassify`
clause-satisfiers for representatives of one Zar class agree on common overlap rings,
and a clause-satisfier agrees with any chart framing of a representative on the
pullback overlap of their tests.

* `AlgebraicGeometry.specMap_eq_of_divClassifyClauses` — the hom-side W3 at the Zar
  layer: clause-satisfiers for `F₁`, `F₂` with `mapAlg B g F₁ = mapAlg B g F₂` have
  equal `divSchemeι`-composites on `Spec B` — `Scheme.Cover.hom_ext` over a frame
  cover of the restricted family, clause transport (`DivClassifyClause.extend`) on
  each piece.
* `AlgebraicGeometry.pullback_divClassifyClause_compat` — the `glueMorphisms`
  obligation over the certificate cover: `divScheme_hom_ext` + `pullbackSpecIso`
  conjugation into `S₁ ⊗[S] S₂`, family agreement by `toZar` injectivity
  (`DivFam.mapAlg_eq_mapAlg_of_toZar_restrict`), then the clause comparison.
* `AlgebraicGeometry.pullback_chart_divClassifyClause_compat` — the clause obligation
  of the glued morphism against an arbitrary framed test: the framing pushes along
  `includeLeft` (`map_window_frame_toSubmodule` at the identity tower), the families
  agree on `T ⊗[S] A`, and clause transport closes.

All statements are in the `Spec.map (algebraMap ‥)` spelling (I-0237 gotcha (a));
cover-spelled obligations consume them by `exact` (defeq).
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

noncomputable local instance instOverCleftRepClassifyCompat :
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

/-! ## The overlap comparisons -/

set_option maxHeartbeats 800000 in
-- Window/clause transports unfold `divFamEps`/`DivFam.window` defeq (I-0239 precedent).
set_option maxRecDepth 8000 in
include hO hχ in
/-- (Implementation) **One frame piece of an overlap ring, against a clause**: if `v`
satisfies the `divClassify` clause for `F` over `S₀` and the restriction of `F` to a
frame piece `Localization.Away x` of a `k`/`S₀`-tower ring `B` is chart-framed, then
the further restriction of `v` chart-factors there — the clause transport
(`DivClassifyClause.extend`) at the composite tower `S₀ → B → Away x`. -/
private theorem specMap_awayPiece_eq_of_clause
    {S₀ : Type u} [CommRing S₀] [Algebra k S₀]
    {B : Type u} [CommRing B] [Algebra k B] [Algebra S₀ B] [IsScalarTower k S₀ B]
    (F : DivFam C S₀ π g)
    {v : Spec (CommRingCat.of S₀) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F v)
    (x : B) {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (ω : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away x)
    (hω₁ : (Module.Grassmannian.map ω (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away x) b₁.equivFun.toLinearMap)
          (divFamEps hπ g
            (DivFam.mapAlg (Localization.Away x) g (DivFam.mapAlg B g F))).1)
    (hω₂ : (Module.Grassmannian.map ω (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away x) b₂.equivFun.toLinearMap)
          (divFamEps hπ g
            (DivFam.mapAlg (Localization.Away x) g (DivFam.mapAlg B g F))).2) :
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away x)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap S₀ B))
        ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom ω.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j := by
  -- the ambient `Algebra S₀ (Localization ‥)` instance IS the composite tower
  haveI : IsScalarTower S₀ B (Localization.Away x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k B (Localization.Away x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k S₀ (Localization.Away x) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq k B (Localization.Away x),
        IsScalarTower.algebraMap_eq k S₀ B,
        IsScalarTower.algebraMap_eq S₀ B (Localization.Away x),
        RingHom.comp_assoc])
  have hcomp : DivFam.mapAlg (Localization.Away x) g (DivFam.mapAlg B g F)
      = DivFam.mapAlg (Localization.Away x) g F :=
    DivFam.mapAlg_comp B g (Localization.Away x) F
  have hω₁' : (Module.Grassmannian.map ω (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away x) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away x) g F)).1 :=
    hω₁.trans (congrArg (fun F' => Submodule.map
      (LinearMap.baseChange (Localization.Away x) b₁.equivFun.toLinearMap)
      (divFamEps hπ g F').1) hcomp)
  have hω₂' : (Module.Grassmannian.map ω (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away x) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away x) g F)).2 :=
    hω₂.trans (congrArg (fun F' => Submodule.map
      (LinearMap.baseChange (Localization.Away x) b₂.equivFun.toLinearMap)
      (divFamEps hπ g F').2) hcomp)
  have hmain := DivClassifyClause.extend hπ g hO hχ r₁ r₂ b₁ b₂ F hv
    (Localization.Away x) i j ω hω₁' hω₂'
  have hstep : Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away x)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap S₀ B))
      = Spec.map (CommRingCat.ofHom (algebraMap S₀ (Localization.Away x))) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hstep]
  exact hmain

set_option maxHeartbeats 800000 in
-- Window/clause transports unfold `divFamEps`/`DivFam.window` defeq (I-0239 precedent).
set_option maxRecDepth 8000 in
include hO hχ in
/-- **Two clause-satisfiers agree on a common overlap ring** (the hom-side W3 at the
Zar layer): if `v₁`, `v₂` satisfy the `divClassify` clauses for families `F₁`, `F₂`
whose base changes to a `k`-tower ring `B` agree, then the two restrictions to
`Spec B` have equal `divSchemeι`-composites — `Scheme.Cover.hom_ext` over a frame
cover of the common restricted family, with the clause transport on each piece. -/
theorem specMap_eq_of_divClassifyClauses
    {S₁ : Type u} [CommRing S₁] [Algebra k S₁]
    {S₂ : Type u} [CommRing S₂] [Algebra k S₂]
    (B : Type u) [CommRing B] [Algebra k B]
    [Algebra S₁ B] [IsScalarTower k S₁ B] [Algebra S₂ B] [IsScalarTower k S₂ B]
    (F₁ : DivFam C S₁ π g) (F₂ : DivFam C S₂ π g)
    (hFB : DivFam.mapAlg B g F₁ = DivFam.mapAlg B g F₂)
    {v₁ : Spec (CommRingCat.of S₁) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv₁ : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F₁ v₁)
    {v₂ : Spec (CommRingCat.of S₂) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv₂ : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F₂ v₂) :
    Spec.map (CommRingCat.ofHom (algebraMap S₁ B))
        ≫ v₁ ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom (algebraMap S₂ B))
          ≫ v₂ ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm) := by
  obtain ⟨m, e, hspan, hdata⟩ :=
    divFamEps_exists_frameCover hπ g hO hχ r₁ r₂ b₁ b₂ (DivFam.mapAlg B g F₁)
  choose ci cj cw hcw₁ hcw₂ using hdata
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of B) e hspan).openCover
    _ _ fun t => ?_
  have h₁ : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of B) e hspan).openCover.f t
        ≫ Spec.map (CommRingCat.ofHom (algebraMap S₁ B))
        ≫ v₁ ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom (cw t).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci t) (cj t) :=
    specMap_awayPiece_eq_of_clause hπ g hO hχ r₁ r₂ b₁ b₂ F₁ hv₁ (e t) (cw t)
      (hcw₁ t) (hcw₂ t)
  have h₂ : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of B) e hspan).openCover.f t
        ≫ Spec.map (CommRingCat.ofHom (algebraMap S₂ B))
        ≫ v₂ ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom (cw t).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci t) (cj t) :=
    specMap_awayPiece_eq_of_clause hπ g hO hχ r₁ r₂ b₁ b₂ F₂ hv₂ (e t) (cw t)
      ((hcw₁ t).trans (congrArg (fun F' => Submodule.map
        (LinearMap.baseChange (Localization.Away (e t)) b₁.equivFun.toLinearMap)
        (divFamEps hπ g (DivFam.mapAlg (Localization.Away (e t)) g F')).1) hFB))
      ((hcw₂ t).trans (congrArg (fun F' => Submodule.map
        (LinearMap.baseChange (Localization.Away (e t)) b₂.equivFun.toLinearMap)
        (divFamEps hπ g (DivFam.mapAlg (Localization.Away (e t)) g F')).2) hFB))
  exact h₁.trans h₂.symm

set_option maxHeartbeats 800000 in
-- Window/clause transports unfold `divFamEps`/`DivFam.window` defeq (I-0239 precedent).
set_option maxRecDepth 8000 in
include hO hχ in
/-- **The `glueMorphisms` obligation over the certificate cover** (w4-ddr9 §2.1
step 5): the per-piece classifications of two certified representatives of one Zar
class agree on the basic-open pullback overlap — `divScheme_hom_ext` reduces to the
`divSchemeι`-composites, `pullbackSpecIso` conjugates into the abstract tensor
overlap ring, where the two restricted families agree (`toZar` injectivity) and the
clause comparison closes. -/
theorem pullback_divClassifyClause_compat (F₀ : DivFamZar C S π g)
    {S₁ : Type u} [CommRing S₁] [Algebra k S₁] [Algebra S S₁] [IsScalarTower k S S₁]
    {S₂ : Type u} [CommRing S₂] [Algebra k S₂] [Algebra S S₂] [IsScalarTower k S S₂]
    (F₁ : DivFam C S₁ π g) (F₂ : DivFam C S₂ π g)
    (hZ₁ : F₁.toZar = DivFamZar.mapAlg S₁ g F₀)
    (hZ₂ : F₂.toZar = DivFamZar.mapAlg S₂ g F₀)
    {v₁ : Spec (CommRingCat.of S₁) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv₁ : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F₁ v₁)
    {v₂ : Spec (CommRingCat.of S₂) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv₂ : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F₂ v₂) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
        (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ≫ v₁
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
          (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ≫ v₂ := by
  letI : Algebra S₂ (TensorProduct S S₁ S₂) :=
    (Algebra.TensorProduct.includeRight (R := S) (A := S₁)
      (B := S₂)).toRingHom.toAlgebra
  haveI : IsScalarTower k S (TensorProduct S S₁ S₂) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower S S₁ (TensorProduct S S₁ S₂) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k S₁ (TensorProduct S S₁ S₂) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S S₂ (TensorProduct S S₁ S₂) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  haveI : IsScalarTower k S₂ (TensorProduct S S₁ S₂) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  have hFB : DivFam.mapAlg (TensorProduct S S₁ S₂) g F₁
      = DivFam.mapAlg (TensorProduct S S₁ S₂) g F₂ :=
    DivFam.mapAlg_eq_mapAlg_of_toZar_restrict g F₀ F₁ F₂ hZ₁ hZ₂
  have hcore := specMap_eq_of_divClassifyClauses hπ g hO hχ r₁ r₂ b₁ b₂
    (TensorProduct S S₁ S₂) F₁ F₂ hFB hv₁ hv₂
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁ (b₂.map (windowShiftEquiv hπ g).symm)
    _ _ ?_
  rw [Category.assoc, Category.assoc, ← cancel_epi (pullbackSpecIso S S₁ S₂).inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  exact hcore

set_option maxHeartbeats 800000 in
-- Window/clause transports unfold `divFamEps`/`DivFam.window` defeq (I-0239 precedent).
set_option maxRecDepth 8000 in
include hO hχ in
/-- **The clause obligation against an arbitrary framed test** (w4-ddr9 §2.1 step 6's
per-piece comparison): a chart framing of a certified representative `G` over a test
`T` and a `divClassify` clause-satisfier for a representative `F₂` over `A` — both
restricting `F₀` — agree on the pullback overlap of `Spec T` and `Spec A`.
`pullbackSpecIso` conjugates into `T ⊗[S] A`; the framing pushes along the left leg
(`map_window_frame_toSubmodule` at the identity tower); the families agree there
(`toZar` injectivity); clause transport closes. -/
theorem pullback_chart_divClassifyClause_compat (F₀ : DivFamZar C S π g)
    {T : Type u} [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (G : CertifiedDivisorFamily C T π g)
    (hZG : (DivFam.mk G).toZar = DivFamZar.mapAlg T g F₀)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mk G)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mk G)).2)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (F₂ : DivFam C A π g) (hZ₂ : F₂.toZar = DivFamZar.mapAlg A g F₀)
    {v₂ : Spec (CommRingCat.of A) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv₂ : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F₂ v₂) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S A)))
          ≫ v₂ ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm) := by
  letI : Algebra A (TensorProduct S T A) :=
    (Algebra.TensorProduct.includeRight (R := S) (A := T)
      (B := A)).toRingHom.toAlgebra
  haveI : IsScalarTower k S (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  haveI : IsScalarTower S T (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k T (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S A (TensorProduct S T A) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra]
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  haveI : IsScalarTower k A (TensorProduct S T A) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  have hFB : DivFam.mapAlg (TensorProduct S T A) g (DivFam.mk G)
      = DivFam.mapAlg (TensorProduct S T A) g F₂ :=
    DivFam.mapAlg_eq_mapAlg_of_toZar_restrict g F₀ (DivFam.mk G) F₂ hZG hZ₂
  -- the left-leg pushforward of the framing, through the identity tower at `T`
  have hβ : (IsScalarTower.toAlgHom k T (TensorProduct S T A)).toRingHom.comp
        (algebraMap T T)
      = algebraMap T (TensorProduct S T A) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
    rfl
  have hy₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g (DivFam.mk G))).1 :=
    hw₁.trans (congrArg (fun F' => Submodule.map
      (LinearMap.baseChange T b₁.equivFun.toLinearMap) (divFamEps hπ g F').1)
      (DivFam.mapAlg_id g (DivFam.mk G)).symm)
  have hy₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g (DivFam.mk G))).2 :=
    hw₂.trans (congrArg (fun F' => Submodule.map
      (LinearMap.baseChange T b₂.equivFun.toLinearMap) (divFamEps hπ g F').2)
      (DivFam.mapAlg_id g (DivFam.mk G)).symm)
  have hωB₁ := map_window_frame_toSubmodule hπ g hO hχ (windowM_choice π hπ g)
    (relThetaPairH1_windowM C π hπ g) le_rfl b₁ (DivFam.mk G)
    (IsScalarTower.toAlgHom k T (TensorProduct S T A)) hβ
    (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) hy₁
  have hωB₂ := map_window_frame_toSubmodule hπ g hO hχ
    (windowM_choice π hπ g + windowS_choice π hπ g)
    (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ (DivFam.mk G)
    (IsScalarTower.toAlgHom k T (TensorProduct S T A)) hβ
    (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) hy₂
  have hcomp₁ : Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautFst k g r₁ r₂ i j)
      = Module.Grassmannian.map (IsScalarTower.toAlgHom k T (TensorProduct S T A))
          (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
    Module.Grassmannian.map_comp (f := w)
      (g := IsScalarTower.toAlgHom k T (TensorProduct S T A))
      (N := pairTautFst k g r₁ r₂ i j)
  have hcomp₂ : Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautSnd k g r₁ r₂ i j)
      = Module.Grassmannian.map (IsScalarTower.toAlgHom k T (TensorProduct S T A))
          (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
    Module.Grassmannian.map_comp (f := w)
      (g := IsScalarTower.toAlgHom k T (TensorProduct S T A))
      (N := pairTautSnd k g r₁ r₂ i j)
  have hext₁ : (Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (TensorProduct S T A) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (TensorProduct S T A) g F₂)).1 :=
    (congrArg Module.Grassmannian.toSubmodule hcomp₁).trans (hωB₁.trans
      (congrArg (fun F' => Submodule.map
        (LinearMap.baseChange (TensorProduct S T A) b₁.equivFun.toLinearMap)
        (divFamEps hπ g F').1) hFB))
  have hext₂ : (Module.Grassmannian.map
        ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w)
        (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (TensorProduct S T A) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (TensorProduct S T A) g F₂)).2 :=
    (congrArg Module.Grassmannian.toSubmodule hcomp₂).trans (hωB₂.trans
      (congrArg (fun F' => Submodule.map
        (LinearMap.baseChange (TensorProduct S T A) b₂.equivFun.toLinearMap)
        (divFamEps hπ g F').2) hFB))
  have hmain := DivClassifyClause.extend hπ g hO hχ r₁ r₂ b₁ b₂ F₂ hv₂
    (TensorProduct S T A) i j
    ((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp w) hext₁ hext₂
  have hL : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct S T A))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom)
      = Spec.map (CommRingCat.ofHom
          (((IsScalarTower.toAlgHom k T (TensorProduct S T A)).comp
            w).toRingHom)) := by
    rw [← Spec.map_comp]
    rfl
  rw [← cancel_epi (pullbackSpecIso S T A).inv, pullbackSpecIso_inv_fst_assoc,
    pullbackSpecIso_inv_snd_assoc, ← Category.assoc, hL]
  exact hmain.symm


end Curve

end AlgebraicGeometry
