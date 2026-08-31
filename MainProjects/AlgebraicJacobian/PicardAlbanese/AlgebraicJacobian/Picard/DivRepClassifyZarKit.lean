/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeClassifyGlobal
import AlgebraicJacobian.Picard.DivisorFamilyZarMapAlg
import AlgebraicJacobian.Picard.DivisorFamilyZarGlueKit

/-!
# F4 Kit — certificate-cover extraction and the clause-transport layer
(`informal/w4-ddr9-worksheet.md` §2.1, steps 1 and the W3/clause plumbing)

The reusable layer beneath `Picard/DivRepClassifyZar.lean` (the backward direction of
`divRepAff` at the Zar layer).

* `AlgebraicGeometry.DivFam.toZar_injective` — both quotients are by `DivEq`.
* `AlgebraicGeometry.DivFamZar.exists_certified_away_rep` — **step 1, the certificate
  cover**: certified representatives over canonical `Localization.Away (h l)` whose
  `DivFam.toZar` classes restrict `F₀` (the carrier pattern of
  `DivFamZar.exists_glue_of_away_compat`'s proof, made public).
* `AlgebraicGeometry.DivFam.mapAlg_eq_mapAlg_of_toZar_restrict` — two families
  restricting one Zar class agree after any common base change.
* `AlgebraicGeometry.DivClassifyClause` — the characterizing clause of `divClassify`
  (`Picard/DivSchemeClassifyGlobal.lean`), named for threading.
* `AlgebraicGeometry.specMap_chart_overlap_tower` /
  `AlgebraicGeometry.pullback_chartMap_compat_tower` — the W3 overlap comparison of
  `DivSchemeClassifyGlobal` at ARBITRARY `k`/`S`-tower tests `T`, `T'` (the landed
  proofs used no localization fact).
* `AlgebraicGeometry.DivClassifyClause.extend` — **clause transport**: the clause
  extends to any `k`/`S`-tower test carrying a framing — `Scheme.Cover.hom_ext` over
  the pullback of the frame cover along `Spec T ⟶ Spec S`, W3 at each piece.
* `AlgebraicGeometry.DivFamZar.exists_certChartCover` — **the composite certificate ×
  frame cover on canonical carriers**: certificate cover × frame covers × the
  numerator trick (`span_range_num_mul_eq_top`), each frame chart transported to the
  canonical carrier along `IsLocalization.algEquiv`.
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

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

/-! ## The Zar layer: `toZar` injectivity and the certificate cover -/

section Zar

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {S : Type u} [CommRing S] [Algebra k S]
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}

/-- **`toZar` is injective**: both `DivFam` and `DivFamZar` are quotients by divisor
equality of the underlying local-equation systems, and `toZar` is induced by the
identity on representatives. -/
theorem DivFam.toZar_injective :
    Function.Injective (DivFam.toZar (C := C) (R := S) (π := π) (n := n)) := by
  intro F G h
  induction F using Quotient.inductionOn with
  | h F =>
    induction G using Quotient.inductionOn with
    | h G => exact DivFam.mk_eq_mk_iff.mpr (DivFamZar.mk_eq_mk_iff.mp h)

/-- **Step 1 — the certificate cover** (`informal/w4-ddr9-worksheet.md` §2.1 step 1;
the carrier pattern inside `DivFamZar.exists_glue_of_away_compat`, made public): a
locally certified divisor class over `S` restricts, on a finite span-⊤ family of
basic opens, to classes of certified divisor families on the canonical
away-localizations. -/
theorem DivFamZar.exists_certified_away_rep (F₀ : DivFamZar C S π n) :
    ∃ (m : ℕ) (h : Fin m → S), Ideal.span (Set.range h) = ⊤ ∧
      ∀ l : Fin m, ∃ G : CertifiedDivisorFamily C (Localization.Away (h l)) π n,
        (DivFam.mk G).toZar = DivFamZar.mapAlg (Localization.Away (h l)) n F₀ := by
  obtain ⟨dp, hdp⟩ := Quotient.exists_rep F₀
  obtain ⟨m, h, hspan, hG⟩ := dp.2
  refine ⟨m, h, hspan, fun l => ?_⟩
  haveI : IsOpenImmersion (relCurveMap C S (Localization.Away (h l))) :=
    isOpenImmersion_relCurveMap_away C S (Localization.Away (h l)) (h l)
  have hG' : ∃ G : CertifiedDivisorFamily C (Localization.Away (h l)) π n,
      Scheme.LocalEquations.DivEq G.eqns
        (dp.1.pullback (relCurveMap C S (Localization.Away (h l)))
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C S (Localization.Away (h l))) dp.1)) := hG l
  obtain ⟨G, hGdiv⟩ := hG'
  refine ⟨G, ?_⟩
  rw [← hdp]
  exact DivFamZar.mk_eq_mk_iff.mpr hGdiv

variable (n) in
/-- **Restricted representatives of one Zar class agree after common base change**:
if `F₁` over `S₁` and `F₂` over `S₂` both restrict the class `F₀` over `S`, their
`mapAlg`s to a common `k`/`S`-tower ring `B` agree — `toZar` is injective and
intertwines the total maps, and the Zar-level base change composes over towers. -/
theorem DivFam.mapAlg_eq_mapAlg_of_toZar_restrict
    {S₁ : Type u} [CommRing S₁] [Algebra k S₁] [Algebra S S₁] [IsScalarTower k S S₁]
    {S₂ : Type u} [CommRing S₂] [Algebra k S₂] [Algebra S S₂] [IsScalarTower k S S₂]
    {B : Type u} [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    [Algebra S₁ B] [IsScalarTower k S₁ B] [IsScalarTower S S₁ B]
    [Algebra S₂ B] [IsScalarTower k S₂ B] [IsScalarTower S S₂ B]
    (F₀ : DivFamZar C S π n) (F₁ : DivFam C S₁ π n) (F₂ : DivFam C S₂ π n)
    (hZ₁ : F₁.toZar = DivFamZar.mapAlg S₁ n F₀)
    (hZ₂ : F₂.toZar = DivFamZar.mapAlg S₂ n F₀) :
    DivFam.mapAlg B n F₁ = DivFam.mapAlg B n F₂ := by
  refine DivFam.toZar_injective ?_
  rw [DivFam.toZar_mapAlg, DivFam.toZar_mapAlg, hZ₁, hZ₂,
    DivFamZar.mapAlg_comp S₁ n B F₀, DivFamZar.mapAlg_comp S₂ n B F₀]

end Zar

/-! ## The classify layer: the named clause, the tower W3, and clause transport -/

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftRepClassifyKit :
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

/-- **The characterizing clause of `divClassify`**
(`Picard/DivSchemeClassifyGlobal.lean`), named: `v` composes, over every
away-localization carrying a pair-chart framing of the restricted ε pair, with
`divSchemeι` to the chart morphism of the framing.  Definitionally the body of the
`divClassify` ∃!. -/
def DivClassifyClause (F : DivFam C S π g)
    (v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)) : Prop :=
  ∀ (f₀ : S) (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away f₀),
    (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away f₀) b₁.equivFun.toLinearMap)
            (divFamEps hπ g (DivFam.mapAlg (Localization.Away f₀) g F)).1 →
    (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away f₀) b₂.equivFun.toLinearMap)
            (divFamEps hπ g (DivFam.mapAlg (Localization.Away f₀) g F)).2 →
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f₀)))
        ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j

set_option maxHeartbeats 800000 in
include hO hχ in
/-- **W3 at the tensor overlap of two arbitrary test towers** (the
`specMap_chart_overlap` of `Picard/DivSchemeClassifyGlobal.lean` with the two
away-localizations generalized to arbitrary `k`/`S`-tower algebras `T`, `T'` — its
proof used no localization fact): two framed chart maps over `T`, `T'` present the
same morphism from `Spec` of the abstract overlap ring `T ⊗[S] T'`. -/
theorem specMap_chart_overlap_tower (F : DivFam C S π g)
    (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (T' : Type u) [CommRing T'] [Algebra k T'] [Algebra S T'] [IsScalarTower k S T']
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] T')
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).2)
    (hw₁' : (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map (LinearMap.baseChange T' b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T' g F)).1)
    (hw₂' : (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map (LinearMap.baseChange T' b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T' g F)).2) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct S T T'))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
            T' →ₐ[S] TensorProduct S T T').toRingHom))
          ≫ Spec.map (CommRingCat.ofHom w'.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i' j' := by
  haveI htower : IsScalarTower k S (TensorProduct S T T') :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  have hβ : (Algebra.TensorProduct.includeLeft (S := k) :
        T →ₐ[k] TensorProduct S T T').toRingHom.comp (algebraMap S T)
      = algebraMap S (TensorProduct S T T') :=
    rfl
  have hβ' : ((Algebra.TensorProduct.includeRight :
        T' →ₐ[S] TensorProduct S T T').restrictScalars k).toRingHom.comp
        (algebraMap S T')
      = algebraMap S (TensorProduct S T T') :=
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := S) (A := T) (B := T')).symm
  have hW3 := specMap_pairChartMap_eq_of_window_frames hπ g hO hχ r₁ r₂ b₁ b₂ F
    (Algebra.TensorProduct.includeLeft (S := k)) hβ
    ((Algebra.TensorProduct.includeRight (R := S) (A := T)
      (B := T')).restrictScalars k) hβ'
    w w' hw₁ hw₂ hw₁' hw₂'
  have hL : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct S T T'))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom)
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft (S := k) :
          T →ₐ[k] TensorProduct S T T').comp w).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hR : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        T' →ₐ[S] TensorProduct S T T').toRingHom))
        ≫ Spec.map (CommRingCat.ofHom w'.toRingHom)
      = Spec.map (CommRingCat.ofHom (((Algebra.TensorProduct.includeRight :
          T' →ₐ[S] TensorProduct S T T').restrictScalars k).comp w').toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hL, ← Category.assoc, hR]
  exact hW3

set_option maxHeartbeats 800000 in
include hO hχ in
/-- **The tower `glueMorphisms`-shape overlap** (the `pullback_chartMap_compat` of
`Picard/DivSchemeClassifyGlobal.lean` at arbitrary test towers): the two framed chart
morphisms agree after the pullback projections of `Spec T ×_{Spec S} Spec T'` —
`pullbackSpecIso` conjugates into the abstract tensor ring and the tower W3 closes.
Stated in the `Spec.map (algebraMap ‥)` spelling; cover-spelled obligations consume it
by `exact` (defeq). -/
theorem pullback_chartMap_compat_tower (F : DivFam C S π g)
    (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (T' : Type u) [CommRing T'] [Algebra k T'] [Algebra S T'] [IsScalarTower k S T']
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] T')
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).2)
    (hw₁' : (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map (LinearMap.baseChange T' b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T' g F)).1)
    (hw₂' : (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map (LinearMap.baseChange T' b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T' g F)).2) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S T)))
        (Spec.map (CommRingCat.ofHom (algebraMap S T')))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S T)))
          (Spec.map (CommRingCat.ofHom (algebraMap S T')))
          ≫ Spec.map (CommRingCat.ofHom w'.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i' j' := by
  rw [← cancel_epi (pullbackSpecIso S T T').inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  exact specMap_chart_overlap_tower hπ g hO hχ r₁ r₂ b₁ b₂ F T T' w w'
    hw₁ hw₂ hw₁' hw₂'

set_option maxHeartbeats 800000 in
include hO hχ in
/-- **Clause transport to an arbitrary test tower** (w4-ddr9 §2.1, the arbitrary-`f₀`
pattern freed from localizations): a morphism satisfying the `divClassify` clause for
`F` over `S` chart-factors over ANY `k`/`S`-tower test `T` carrying a pair-chart
framing of the restricted ε pair — `Scheme.Cover.hom_ext` over the pullback of the
frame cover along `Spec T ⟶ Spec S`, the clause at each frame piece, and the tower W3
on the overlaps. -/
theorem DivClassifyClause.extend (F : DivFam C S π g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (hv : DivClassifyClause hπ g r₁ r₂ b₁ b₂ F v)
    (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).2) :
    Spec.map (CommRingCat.ofHom (algebraMap S T))
        ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j := by
  obtain ⟨m, f, hspan, hdata⟩ :=
    divFamEps_exists_frameCover hπ g hO hχ r₁ r₂ b₁ b₂ F
  choose ci cj cw hcw₁ hcw₂ using hdata
  refine Scheme.Cover.hom_ext
    ((Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of S) f hspan).openCover.pullback₁
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    _ _ fun t => ?_
  have hveq : (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) f hspan).openCover.f t
        ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
      = Spec.map (CommRingCat.ofHom (cw t).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ (ci t) (cj t) :=
    hv (f t) (ci t) (cj t) (cw t) (hcw₁ t) (hcw₂ t)
  change pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
  rw [← Category.assoc, pullback.condition, Category.assoc, hveq]
  exact (pullback_chartMap_compat_tower hπ g hO hχ r₁ r₂ b₁ b₂ F T
    (Localization.Away (f t)) w (cw t) hw₁ hw₂ (hcw₁ t) (hcw₂ t)).symm

/-! ## The composite certificate × frame cover on canonical carriers -/

set_option maxHeartbeats 800000 in
-- The window transports unfold `divFamEps`/`DivFam.window` defeq (I-0239 precedent).
set_option maxRecDepth 8000 in
include hπ hO hχ in
/-- (Implementation) **One composite piece on the canonical carrier**: a certified
representative `G₀` over an `h₀`-away localization `A` of `S`, a frame chart over
`Localization.Away f₀` (`f₀ : A`) and a numerator `a₀ : S` of `f₀` transport to the
canonical `Localization.Away (a₀ * h₀)` along `IsLocalization.algEquiv`. -/
private theorem exists_certChart_piece (F₀ : DivFamZar C S π g)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra S A] [IsScalarTower k S A]
    (h₀ : S) [IsLocalization.Away h₀ A]
    (G₀ : CertifiedDivisorFamily C A π g)
    (hZ : (DivFam.mk G₀).toZar = DivFamZar.mapAlg A g F₀)
    (f₀ : A) (a₀ : S) (hassoc : Associated (algebraMap S A a₀) f₀)
    {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away f₀)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away f₀) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away f₀) g (DivFam.mk G₀))).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away f₀) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away f₀) g (DivFam.mk G₀))).2) :
    ∃ (G : CertifiedDivisorFamily C (Localization.Away (a₀ * h₀)) π g)
      (i' : (glueData k g r₁).J) (j' : (glueData k g r₂).J)
      (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] Localization.Away (a₀ * h₀)),
      (DivFam.mk G).toZar = DivFamZar.mapAlg (Localization.Away (a₀ * h₀)) g F₀ ∧
      (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away (a₀ * h₀))
              b₁.equivFun.toLinearMap)
            (divFamEps hπ g (DivFam.mk G)).1 ∧
      (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')).toSubmodule
        = Submodule.map
            (LinearMap.baseChange (Localization.Away (a₀ * h₀))
              b₂.equivFun.toLinearMap)
            (divFamEps hπ g (DivFam.mk G)).2 := by
  -- the frame carrier is an `a₀·h₀`-away localization of `S`
  haveI hAwayNum : IsLocalization.Away (algebraMap S A a₀) (Localization.Away f₀) :=
    IsLocalization.Away.of_associated hassoc.symm
  haveI hAwayV : IsLocalization.Away (a₀ * h₀) (Localization.Away f₀) :=
    IsLocalization.Away.mul A (Localization.Away f₀) h₀ a₀
  -- the `S`-algebra identification with the canonical carrier
  let e : Localization.Away (a₀ * h₀) ≃ₐ[S] Localization.Away f₀ :=
    IsLocalization.algEquiv (Submonoid.powers (a₀ * h₀)) _ _
  let β : Localization.Away f₀ →ₐ[k] Localization.Away (a₀ * h₀) :=
    (e.symm.toAlgHom.restrictScalars k)
  -- the `A`-algebra structure of the canonical carrier
  letI : Algebra A (Localization.Away (a₀ * h₀)) :=
    (IsLocalization.Away.lift (S := A) h₀
      (g := algebraMap S (Localization.Away (a₀ * h₀)))
      (IsLocalization.Away.isUnit_of_dvd (x := a₀ * h₀) (dvd_mul_left h₀ a₀))).toAlgebra
  haveI : IsScalarTower S A (Localization.Away (a₀ * h₀)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp])
  haveI : IsScalarTower k A (Localization.Away (a₀ * h₀)) :=
    isScalarTower_left_of_isScalarTower (R₀ := S)
  -- the transported frame chart is structure-compatible over `A`
  have hβ : β.toRingHom.comp (algebraMap A (Localization.Away f₀))
      = algebraMap A (Localization.Away (a₀ * h₀)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers h₀) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S A (Localization.Away f₀),
      RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_comp]
    exact AlgHom.comp_algebraMap e.symm.toAlgHom
  refine ⟨G₀.mapAlg (Localization.Away (a₀ * h₀)) g, i, j, β.comp w, ?_, ?_, ?_⟩
  · -- the transported representative restricts `F₀`
    have h1 : DivFam.mk (G₀.mapAlg (Localization.Away (a₀ * h₀)) g)
        = DivFam.mapAlg (Localization.Away (a₀ * h₀)) g (DivFam.mk G₀) := rfl
    rw [h1, DivFam.toZar_mapAlg, hZ]
    exact DivFamZar.mapAlg_comp A g (Localization.Away (a₀ * h₀)) F₀
  · -- the first framing transports along `β` (the W3 left-leg pushforward)
    have e₁ : Module.Grassmannian.map (β.comp w) (pairTautFst k g r₁ r₂ i j)
        = Module.Grassmannian.map β
            (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := β) (N := pairTautFst k g r₁ r₂ i j)
    exact (congrArg Module.Grassmannian.toSubmodule e₁).trans
      (map_window_frame_toSubmodule hπ g hO hχ (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g) le_rfl b₁ (DivFam.mk G₀) β hβ
        (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) hw₁)
  · -- the mirrored transport at the shifted window
    have e₂ : Module.Grassmannian.map (β.comp w) (pairTautSnd k g r₁ r₂ i j)
        = Module.Grassmannian.map β
            (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := β) (N := pairTautSnd k g r₁ r₂ i j)
    exact (congrArg Module.Grassmannian.toSubmodule e₂).trans
      (map_window_frame_toSubmodule hπ g hO hχ
        (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ (DivFam.mk G₀)
        β hβ (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) hw₂)

set_option maxHeartbeats 800000 in
include hO hχ in
/-- **The composite certificate × frame cover on canonical carriers**
(w4-ddr9 §2.1 steps 1–2, assembled): a finite span-⊤ family `r : Fin m → S` such
that over each canonical `Localization.Away (r p)` some certified representative of
the restricted class is framed by a pair chart — certificate cover × per-piece frame
covers × the numerator trick, pieces by `exists_certChart_piece`. -/
theorem DivFamZar.exists_certChartCover (F₀ : DivFamZar C S π g) :
    ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧
      ∀ p : Fin m,
        ∃ (G : CertifiedDivisorFamily C (Localization.Away (r p)) π g)
          (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
          (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away (r p)),
          (DivFam.mk G).toZar = DivFamZar.mapAlg (Localization.Away (r p)) g F₀ ∧
          (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
            = Submodule.map
                (LinearMap.baseChange (Localization.Away (r p))
                  b₁.equivFun.toLinearMap)
                (divFamEps hπ g (DivFam.mk G)).1 ∧
          (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
            = Submodule.map
                (LinearMap.baseChange (Localization.Away (r p))
                  b₂.equivFun.toLinearMap)
                (divFamEps hπ g (DivFam.mk G)).2 := by
  classical
  obtain ⟨mc, h, hspanH, hGl⟩ := DivFamZar.exists_certified_away_rep F₀
  choose Gl hZl using hGl
  have hFC := fun l : Fin mc =>
    divFamEps_exists_frameCover hπ g hO hχ r₁ r₂ b₁ b₂ (DivFam.mk (Gl l))
  choose mf f hspanF hframe using hFC
  choose ci cj cw hcw₁ hcw₂ using hframe
  have hassoc : ∀ (l : Fin mc) (t : Fin (mf l)),
      Associated (algebraMap S (Localization.Away (h l))
        ((IsLocalization.Away.sec (h l) (f l t)).1)) (f l t) :=
    fun l t => IsLocalization.Away.associated_sec_fst (h l) (f l t)
  -- the composite span-⊤ family, `ULift`ed into the working universe
  have hspanH' : Ideal.span
      (Set.range fun l : ULift.{u} (Fin mc) => h l.down) = ⊤ := by
    have hrange : (Set.range fun l : ULift.{u} (Fin mc) => h l.down)
        = Set.range h := ULift.down_surjective.range_comp h
    rw [hrange, hspanH]
  have hr : Ideal.span (Set.range
      fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
        (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1 * h p.1.down)
      = ⊤ :=
    span_range_num_mul_eq_top (fun l : ULift.{u} (Fin mc) => h l.down)
      (fun l => Localization.Away (h l.down)) hspanH'
      (fun l => f l.down) (fun l => hspanF l.down)
      (fun l t => (IsLocalization.Away.sec (h l.down) (f l.down t)).1)
      (fun l t => hassoc l.down t)
  -- reindex the sigma family by `Fin`
  let e : Fin (Fintype.card (Σ l : ULift.{u} (Fin mc), Fin (mf l.down)))
      ≃ Σ l : ULift.{u} (Fin mc), Fin (mf l.down) :=
    (Fintype.equivFin (Σ l : ULift.{u} (Fin mc), Fin (mf l.down))).symm
  refine ⟨Fintype.card (Σ l : ULift.{u} (Fin mc), Fin (mf l.down)),
    fun q => (IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1
      * h (e q).1.down, ?_, ?_⟩
  · have hrange : (Set.range fun q =>
        (IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1
          * h (e q).1.down)
        = Set.range (fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
            (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1
              * h p.1.down) :=
      e.surjective.range_comp
        (fun p : Σ l : ULift.{u} (Fin mc), Fin (mf l.down) =>
          (IsLocalization.Away.sec (h p.1.down) (f p.1.down p.2)).1 * h p.1.down)
    rw [hrange, hr]
  · intro q
    exact exists_certChart_piece hπ g hO hχ r₁ r₂ b₁ b₂ F₀ (h (e q).1.down)
      (Gl (e q).1.down) (hZl (e q).1.down) (f (e q).1.down (e q).2)
      ((IsLocalization.Away.sec (h (e q).1.down) (f (e q).1.down (e q).2)).1)
      (hassoc (e q).1.down (e q).2)
      (cw (e q).1.down (e q).2) (hcw₁ (e q).1.down (e q).2)
      (hcw₂ (e q).1.down (e q).2)

end Curve

end AlgebraicGeometry
