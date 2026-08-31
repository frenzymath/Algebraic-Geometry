/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeFrameCover
import AlgebraicJacobian.Picard.DivSchemeClassifyAff

/-!
# G-5 file 5 — the per-piece classification (`informal/w4-g5-worksheet.md` §2)

The transport layer between the frame-locus cover (`Picard/DivSchemeFrameCover.lean`)
and the per-piece application of `divClassifyAff` (`Picard/DivSchemeClassifyAff.lean`),
plus the transports that the global stitch (file 6, `DivSchemeClassifyGlobal.lean`)
pushes along overlap legs.  Everything is generic in a structure-compatible test tower
`S → T → B` of `k`-algebras — no localization hypotheses, no Noetherian hypotheses
(w4-ddr9 §0.4).

* `AlgebraicGeometry.map_divFamWindowGr_algHom` — the tower transport of the packaged
  ε window point along ANY structure-compatible `β : T →ₐ[k] B`
  (`β ∘ algebraMap S T = algebraMap S B`): the generalization of
  `map_divFamWindowGr` from away-localization towers to arbitrary test towers.
  Mechanism unchanged: `ker_baseChangeMkQ_eq_map_baseChange` inside the `β.toAlgebra`
  tower, then G-2 (`DivFam.window_mapAlg`) on both legs and `DivFam.mapAlg_comp`.
* `AlgebraicGeometry.map_window_frame_toSubmodule` — **the W3 left-leg pushforward**
  (w4-ddr9 §2.1 step 4): a Grassmannian point over `T` framing the restricted ε window
  through a boundary basis maps, along `β`, to the point framing the `B`-restricted
  window.  Identifies the point with `congrAmbient b.equivFun (divFamWindowGr …)` and
  transports by K4 (`map_congrAmbient`) + the tower transport.
* `AlgebraicGeometry.divFamEps_carvePairArrow_mapAlg` — **the carve transport**
  (worksheet §2 bottom): the carve `(♦)` of the ε pair over `S` descends to the ε pair
  of the restricted family over any test `T` —
  `baseChange_carvePairArrow_eq_zero_iff.mp` + the G-2 rewrite through
  `DivFam.window_mapAlg`.
* `AlgebraicGeometry.divClassifyLocal` — **the per-piece classify `vₜ`**: over any
  `S`-tower test `T`, a pair-chart framing of the restricted ε pair (the
  `divFamEps_exists_frameCover` output shape at `T = Localization.Away (f t)`) yields
  the unique factoring `v : Spec T ⟶ DivScheme g` through the pair chart —
  `divClassifyAff` at `DivFam.mapAlg T g F` with the transported carve.

The G-2 orientation seam is consumed exactly as pinned (I-0232):
`windowBaseChange` is definitionally the right-hand side of
`ker_baseChangeMkQ_eq_map_baseChange` (`Picard/DivCarveKit.lean:168`), so mathlib's
`Module.Grassmannian.map` kernels convert with no transport lemma.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

open Grassmannian

section Curve

open Scheme

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftClassifyLocal :
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

/-! ## The window transports along a structure-compatible test tower -/

section WindowTransport

variable (a : ℕ) (ha1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
variable (hMa : windowM_choice π hπ g ≤ a)
variable {S : Type u} [CommRing S] [Algebra k S]
variable {T : Type u} [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
variable {B : Type u} [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]

set_option maxHeartbeats 800000 in
-- Instantiates the G-2 window naturality at two test rings; elaboration cost.
/-- **The tower transport of the packaged ε point along an arbitrary
structure-compatible test map** (the `map_divFamWindowGr` mechanism of
`Picard/DivSchemeFrameCover.lean`, freed from away-localizations): mapping the
packaged point along `β : T →ₐ[k] B` with `β ∘ algebraMap S T = algebraMap S B`
yields the packaged point over `B` — `ker_baseChangeMkQ_eq_map_baseChange` inside the
`β.toAlgebra` tower, then G-2 on both legs and `DivFam.mapAlg_comp`. -/
theorem map_divFamWindowGr_algHom (F : DivFam C S π g) (β : T →ₐ[k] B)
    (hβ : β.toRingHom.comp (algebraMap S T) = algebraMap S B) :
    Module.Grassmannian.map β (divFamWindowGr hπ g hO hχ a ha1 hMa F T)
      = divFamWindowGr hπ g hO hχ a ha1 hMa F B := by
  letI : Algebra T B := β.toAlgebra
  letI : IsScalarTower k T B :=
    IsScalarTower.of_algebraMap_eq' (IsScalarTower.algebraMap_eq k _ _)
  haveI htowerS : IsScalarTower S T B := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra]
    exact hβ.symm
  refine Module.Grassmannian.ext ?_
  have h0 := Module.Grassmannian.map_toSubmodule β
    (divFamWindowGr hπ g hO hχ a ha1 hMa F T)
  rw [h0, divFamWindowGr_toSubmodule, divFamWindowGr_toSubmodule,
    ← DivFam.window_mapAlg hπ g hO hχ a ha1 hMa T F,
    ← DivFam.window_mapAlg hπ g hO hχ a ha1 hMa B F]
  haveI : Module.Projective T
      ((TensorProduct k T
        ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        (DivFam.mapAlg T g F).window ha1) :=
    DivFam.projective_window_quotient hπ g hO hχ a ha1 hMa _
  rw [Grassmannian.ker_baseChangeMkQ_eq_map_baseChange B
    ((DivFam.mapAlg T g F).window ha1)]
  have hcomp : DivFam.mapAlg B g (DivFam.mapAlg T g F) = DivFam.mapAlg B g F :=
    DivFam.mapAlg_comp T g B F
  exact ((DivFam.window_mapAlg hπ g hO hχ a ha1 hMa (R := T) B
      (DivFam.mapAlg T g F)).symm).trans
    (congrArg (fun F' => DivFam.window F' ha1) hcomp)

set_option maxHeartbeats 800000 in
-- Transports a chart framing through the packaged point; elaboration cost.
include hπ hO hχ hMa in
/-- **The W3 left-leg pushforward** (w4-ddr9 §2.1 step 4, single window): a coordinate
Grassmannian point over `T` whose submodule is the boundary-basis image of the
restricted ε window maps, along a structure-compatible `β : T →ₐ[k] B`, to the point
framing the `B`-restricted window.  Identify with `congrAmbient` of the packaged point
(`Module.Grassmannian.ext`), then K4 (`map_congrAmbient`) + the tower transport. -/
theorem map_window_frame_toSubmodule {r : ℕ}
    (b : Module.Basis (Fin r) k
      ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (F : DivFam C S π g) (β : T →ₐ[k] B)
    (hβ : β.toRingHom.comp (algebraMap S T) = algebraMap S B)
    (y : Grassmannian.grFunctorAff k (Fin r → k) g T)
    (hy : y.toSubmodule = Submodule.map (LinearMap.baseChange T b.equivFun.toLinearMap)
        ((DivFam.mapAlg T g F).window ha1)) :
    (Module.Grassmannian.map β y).toSubmodule
      = Submodule.map (LinearMap.baseChange B b.equivFun.toLinearMap)
          ((DivFam.mapAlg B g F).window ha1) := by
  have hyeq : y = congrAmbient b.equivFun (divFamWindowGr hπ g hO hχ a ha1 hMa F T) := by
    refine Module.Grassmannian.ext ?_
    rw [hy, congrAmbient_toSubmodule, divFamWindowGr_toSubmodule,
      ← DivFam.window_mapAlg hπ g hO hχ a ha1 hMa T F]
  rw [hyeq, map_congrAmbient β b.equivFun (divFamWindowGr hπ g hO hχ a ha1 hMa F T),
    map_divFamWindowGr_algHom hπ g hO hχ a ha1 hMa F β hβ,
    congrAmbient_toSubmodule, divFamWindowGr_toSubmodule,
    ← DivFam.window_mapAlg hπ g hO hχ a ha1 hMa B F]

end WindowTransport

/-! ## The carve transport -/

section CarveTransport

variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 800000 in
-- Instantiates the window layer at both ledger windows; elaboration cost.
include hO hχ in
/-- **The carve transport for the restricted family** (worksheet §2 bottom, generic
multiplier): the carve `(♦)` of the ε pair over `S` yields the carve of the ε pair of
the restricted family over any `S`-tower test `T`.  Route:
`carvePairArrow … = 0` base-changes to `0`, `baseChange_carvePairArrow_eq_zero_iff.mp`
gives the carve for the `ker (baseChangeMkQ)` pair, and G-2
(`DivFam.window_mapAlg` through the pinned `windowBaseChange` orientation) rewrites it
to the ε pair of `DivFam.mapAlg T g F`. -/
theorem divFamEps_carvePairArrow_mapAlg (F : DivFam C S π g)
    (μ : ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤) →ₗ[k]
      ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
    (h : carvePairArrow μ (divFamEps hπ g F).1 (divFamEps hπ g F).2 = 0)
    (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T] :
    carvePairArrow μ (divFamEps hπ g (DivFam.mapAlg T g F)).1
      (divFamEps hπ g (DivFam.mapAlg T g F)).2 = 0 := by
  haveI hp₁ : Module.Projective S
      ((TensorProduct k S ↥(Scheme.divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸ (divFamEps hπ g F).1) :=
    DivFam.projective_window_quotient hπ g hO hχ (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) le_rfl F
  haveI hp₂ : Module.Projective S
      ((TensorProduct k S ↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
        (divFamEps hπ g F).2) :=
    DivFam.projective_window_quotient hπ g hO hχ
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) F
  have h0 : LinearMap.baseChange T
      (carvePairArrow μ (divFamEps hπ g F).1 (divFamEps hπ g F).2) = 0 := by
    rw [h, LinearMap.baseChange_zero]
  have h1 := (baseChange_carvePairArrow_eq_zero_iff T μ
    (divFamEps hπ g F).1 (divFamEps hπ g F).2).mp h0
  have h2 : (divFamEps hπ g (DivFam.mapAlg T g F)).1
      = LinearMap.ker (Module.Grassmannian.baseChangeMkQ T (divFamEps hπ g F).1) :=
    (DivFam.window_mapAlg hπ g hO hχ (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) le_rfl T F).trans
      (windowBaseChange_eq_ker_baseChangeMkQ T (divFamEps hπ g F).1)
  have h3 : (divFamEps hπ g (DivFam.mapAlg T g F)).2
      = LinearMap.ker (Module.Grassmannian.baseChangeMkQ T (divFamEps hπ g F).2) :=
    (DivFam.window_mapAlg hπ g hO hχ
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) T F).trans
      (windowBaseChange_eq_ker_baseChangeMkQ T (divFamEps hπ g F).2)
  rw [h2, h3]
  exact h1

end CarveTransport

/-! ## The per-piece classification -/

section Classify

variable (r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(divisorSections k
    ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤))
variable {S : Type u} [CommRing S] [Algebra k S]

set_option maxHeartbeats 800000 in
-- Instantiates `divClassifyAff` at the restricted family; elaboration cost.
include hO hχ in
/-- **The per-piece classify `vₜ`** (`informal/w4-g5-worksheet.md` §2): a divisor
family `F` over `S` whose ε pair satisfies the carve, together with a pair-chart
framing of the restricted ε pair over an `S`-tower test `T` (the
`divFamEps_exists_frameCover` output shape at `T = Localization.Away (f t)`),
factors uniquely through `divSchemeι` over the pair chart — `divClassifyAff` at
`DivFam.mapAlg T g F` with the transported carve.  No Noetherian hypotheses
(w4-ddr9 §0.4). -/
theorem divClassifyLocal (F : DivFam C S π g)
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g F).1 (divFamEps hπ g F).2 = 0)
    (T : Type u) [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] T)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map (LinearMap.baseChange T b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg T g F)).2) :
    ∃! v : Spec (CommRingCat.of T) ⟶
        DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
      v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j :=
  divClassifyAff hπ g r₁ r₂ b₁ b₂ (DivFam.mapAlg T g F) i j w hw₁ hw₂
    (fun a => divFamEps_carvePairArrow_mapAlg hπ g hO hχ F (windowShiftMul hπ g a)
      (hcarve a) T)

end Classify

end Curve

end AlgebraicGeometry
