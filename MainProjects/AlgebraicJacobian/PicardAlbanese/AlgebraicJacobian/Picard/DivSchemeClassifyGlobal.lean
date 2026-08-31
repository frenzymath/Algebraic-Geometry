/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeClassifyLocal
import AlgebraicJacobian.Picard.GrassmannianPairCompare

/-!
# G-5 file 6 — W3 overlap agreement, the stitch, and `divClassify`
(`informal/w4-g5-worksheet.md` §3–§4)

The global classification keystone of the DDR-9 backward assembly: a divisor family
over an affine test `S` whose ε pair satisfies the carve `(♦)` glues the per-piece
classifications of the frame-locus cover (`divFamEps_exists_frameCover`, file 4;
`divClassifyLocal`, file 5) into a **unique** morphism `Spec S ⟶ DivScheme g`,
characterized by chart-factoring over EVERY localization-with-chart-framing — the
∃!-form of worksheet §4, **without the `[IsNoetherianRing S]` hypothesis** (dropped
per w4-ddr9 §0.4: every input is Noetherian-free).

* `AlgebraicGeometry.specMap_pairChartMap_eq_of_window_frames` — **W3** (w4-ddr9 §2.1
  step 4): two chart framings of the restricted ε pair over tests `T`, `T'`, pushed
  into a common overlap ring `B` along structure-compatible legs, present the same
  morphism `Spec B ⟶ grPair`.  The two pushed framings frame the SAME point — the
  coordinate image of `ε (DivFam.mapAlg B g F)`, by the file-5 left-leg pushforward
  (`map_window_frame_toSubmodule`) on each leg — and W2
  (`specMap_pairChartMap_eq_of_map_pairTaut_eq`) fires.  `B` needs NO hypotheses
  beyond the `k`/`S`-tower (no Noetherian, no localization).
* `AlgebraicGeometry.specMap_chart_overlap` — W3 instantiated at the abstract tensor
  overlap ring `Localization.Away fa ⊗[S] Localization.Away fb` with the
  `includeLeft`/`includeRight` legs (the `pullbackSpecIso` chart of the basic-open
  double overlap; no identification with `Away (fa·fb)` is ever made).
* `AlgebraicGeometry.pullback_chartFactor_compat` — the `glueMorphisms` obligation:
  two morphisms to `DivScheme g` factoring through framed charts over `Away fa`,
  `Away fb` agree on the pullback overlap (`divScheme_hom_ext` + `pullbackSpecIso`
  conjugation + W3).
* `AlgebraicGeometry.divClassify` — **the keystone** (worksheet §4): the ∃!-form,
  with the characterizing clause universally quantified over all
  `(f₀, i, j, w, hw₁, hw₂)` — stable under further localization by construction
  (the clause at any `f₀` is proven over the pullback cover of `Spec (Away f₀)`
  along the frame cover, the same W3 argument with `(f₀, f t)` in place of
  `(f t, f t')`).  Existence is `Scheme.Cover.glueMorphisms` on the frame cover
  (`Picard/Pic0SigmaSheaf.lean:97-105` precedent); uniqueness is `divScheme_hom_ext`
  piecewise + `Scheme.Cover.hom_ext`.
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

noncomputable local instance instOverCleftClassifyGlobal :
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

/-! ## W3 — overlap agreement over an abstract overlap ring -/

set_option maxHeartbeats 800000 in
-- Two instantiations of the file-5 window transports at both ledger windows.
include hO hχ in
/-- **W3 — the overlap agreement** (`informal/w4-ddr9-worksheet.md` §2.1 step 4, in
landed vocabulary): two pair-chart framings of the restricted ε pair over tests `T`,
`T'`, pushed along structure-compatible legs `β : T →ₐ[k] B ←ₐ[k] T' : β'` into a
common overlap ring, present the same morphism `Spec B ⟶ grPair`.  Both pushed
framings present the coordinate image of `ε (DivFam.mapAlg B g F)`
(`map_window_frame_toSubmodule` on each leg), so W2 fires.  No hypotheses on `B`
beyond the tower. -/
theorem specMap_pairChartMap_eq_of_window_frames (F : DivFam C S π g)
    {T : Type u} [CommRing T] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    {T' : Type u} [CommRing T'] [Algebra k T'] [Algebra S T'] [IsScalarTower k S T']
    {B : Type u} [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    (β : T →ₐ[k] B) (hβ : β.toRingHom.comp (algebraMap S T) = algebraMap S B)
    (β' : T' →ₐ[k] B) (hβ' : β'.toRingHom.comp (algebraMap S T') = algebraMap S B)
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
    Spec.map (CommRingCat.ofHom (β.comp w).toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = Spec.map (CommRingCat.ofHom (β'.comp w').toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i' j' := by
  refine specMap_pairChartMap_eq_of_map_pairTaut_eq k g r₁ r₂ i i' j j'
    (β.comp w) (β'.comp w') ?_ ?_
  · -- both pushed first components frame the coordinate image of `ε(F_B).1`
    have e : Module.Grassmannian.map (β.comp w) (pairTautFst k g r₁ r₂ i j)
        = Module.Grassmannian.map β
            (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := β) (N := pairTautFst k g r₁ r₂ i j)
    have e' : Module.Grassmannian.map (β'.comp w') (pairTautFst k g r₁ r₂ i' j')
        = Module.Grassmannian.map β'
            (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')) :=
      Module.Grassmannian.map_comp (f := w') (g := β')
        (N := pairTautFst k g r₁ r₂ i' j')
    refine Module.Grassmannian.ext ?_
    rw [e, e']
    exact (map_window_frame_toSubmodule hπ g hO hχ (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g) le_rfl b₁ F β hβ
        (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)) hw₁).trans
      (map_window_frame_toSubmodule hπ g hO hχ (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g) le_rfl b₁ F β' hβ'
        (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')) hw₁').symm
  · -- the mirrored chain at the shifted window
    have e : Module.Grassmannian.map (β.comp w) (pairTautSnd k g r₁ r₂ i j)
        = Module.Grassmannian.map β
            (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) :=
      Module.Grassmannian.map_comp (f := w) (g := β) (N := pairTautSnd k g r₁ r₂ i j)
    have e' : Module.Grassmannian.map (β'.comp w') (pairTautSnd k g r₁ r₂ i' j')
        = Module.Grassmannian.map β'
            (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')) :=
      Module.Grassmannian.map_comp (f := w') (g := β')
        (N := pairTautSnd k g r₁ r₂ i' j')
    refine Module.Grassmannian.ext ?_
    rw [e, e']
    exact (map_window_frame_toSubmodule hπ g hO hχ
        (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ F β hβ
        (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)) hw₂).trans
      (map_window_frame_toSubmodule hπ g hO hχ
        (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ F β' hβ'
        (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')) hw₂').symm

set_option maxHeartbeats 800000 in
-- W3 at the tensor overlap ring; the tower instances are provided by hand.
include hO hχ in
/-- **W3 at the basic-open double overlap** (worksheet §3.2): two framed chart maps
over `Localization.Away fa`, `Localization.Away fb` present the same morphism from
`Spec` of the abstract overlap ring `Away fa ⊗[S] Away fb` — the
`includeLeft`/`includeRight` legs of the `pullbackSpecIso` chart.  `B` stays
abstract; no identification with `Away (fa·fb)`. -/
theorem specMap_chart_overlap (F : DivFam C S π g) (fa fb : S)
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away fa)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] Localization.Away fb)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fa) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fa) g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fa) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fa) g F)).2)
    (hw₁' : (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fb) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fb) g F)).1)
    (hw₂' : (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fb) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fb) g F)).2) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away fa →+* TensorProduct S (Localization.Away fa)
          (Localization.Away fb)))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
            Localization.Away fb →ₐ[S] TensorProduct S (Localization.Away fa)
              (Localization.Away fb)).toRingHom))
          ≫ Spec.map (CommRingCat.ofHom w'.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i' j' := by
  haveI htower : IsScalarTower k S
      (TensorProduct S (Localization.Away fa) (Localization.Away fb)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [Algebra.TensorProduct.algebraMap_def, Algebra.TensorProduct.algebraMap_def,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  -- the two legs as structure-compatible `k`-algebra maps
  have hβ : (Algebra.TensorProduct.includeLeft (S := k) :
        Localization.Away fa →ₐ[k] TensorProduct S (Localization.Away fa)
          (Localization.Away fb)).toRingHom.comp (algebraMap S (Localization.Away fa))
      = algebraMap S (TensorProduct S (Localization.Away fa) (Localization.Away fb)) :=
    rfl
  have hβ' : ((Algebra.TensorProduct.includeRight :
        Localization.Away fb →ₐ[S] TensorProduct S (Localization.Away fa)
          (Localization.Away fb)).restrictScalars k).toRingHom.comp
          (algebraMap S (Localization.Away fb))
      = algebraMap S (TensorProduct S (Localization.Away fa) (Localization.Away fb)) :=
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := S) (A := Localization.Away fa) (B := Localization.Away fb)).symm
  have hW3 := specMap_pairChartMap_eq_of_window_frames hπ g hO hχ r₁ r₂ b₁ b₂ F
    (Algebra.TensorProduct.includeLeft (S := k)) hβ
    ((Algebra.TensorProduct.includeRight (R := S) (A := Localization.Away fa)
      (B := Localization.Away fb)).restrictScalars k) hβ'
    w w' hw₁ hw₂ hw₁' hw₂'
  have hL : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away fa →+* TensorProduct S (Localization.Away fa)
          (Localization.Away fb)))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom)
      = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft (S := k) :
          Localization.Away fa →ₐ[k] TensorProduct S (Localization.Away fa)
            (Localization.Away fb)).comp w).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hR : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        Localization.Away fb →ₐ[S] TensorProduct S (Localization.Away fa)
          (Localization.Away fb)).toRingHom))
        ≫ Spec.map (CommRingCat.ofHom w'.toRingHom)
      = Spec.map (CommRingCat.ofHom (((Algebra.TensorProduct.includeRight :
          Localization.Away fb →ₐ[S] TensorProduct S (Localization.Away fa)
            (Localization.Away fb)).restrictScalars k).comp w').toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  rw [← Category.assoc, hL, ← Category.assoc, hR]
  exact hW3

/-! ## The gluing obligation on the frame cover -/

set_option maxHeartbeats 800000 in
-- Conjugates the double overlap through `pullbackSpecIso`; elaboration cost.
include hO hχ in
/-- **W3 conjugated onto the scheme-level double overlap**: the two chart morphisms
of framed chart maps over `Away fa`, `Away fb` agree after the pullback projections —
`pullbackSpecIso` identifies the overlap with `Spec` of the abstract tensor ring and
`specMap_chart_overlap` closes.  Stated in the `Spec.map (algebraMap …)` spelling of
the frame-cover legs; the cover-spelled obligations consume it by `exact` (defeq). -/
theorem pullback_chartMap_compat (F : DivFam C S π g) (fa fb : S)
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away fa)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] Localization.Away fb)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fa) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fa) g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fa) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fa) g F)).2)
    (hw₁' : (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fb) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fb) g F)).1)
    (hw₂' : (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fb) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fb) g F)).2) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fa))))
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fb))))
        ≫ Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
      = pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fa))))
          (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fb))))
          ≫ Spec.map (CommRingCat.ofHom w'.toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i' j' := by
  rw [← cancel_epi
      (pullbackSpecIso S (Localization.Away fa) (Localization.Away fb)).inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  exact specMap_chart_overlap hπ g hO hχ r₁ r₂ b₁ b₂ F fa fb w w' hw₁ hw₂ hw₁' hw₂'

set_option maxHeartbeats 800000 in
-- Reduces to the `divSchemeι` composites and the conjugated overlap; elaboration cost.
include hO hχ in
/-- **The `glueMorphisms` obligation** (worksheet §3.2): two morphisms to
`DivScheme g` factoring through framed charts over `Away fa`, `Away fb` agree on the
basic-open pullback overlap — `divScheme_hom_ext` reduces to the `divSchemeι`
composites, `pullbackSpecIso` conjugates into the abstract overlap ring, and W3
closes. -/
theorem pullback_chartFactor_compat (F : DivFam C S π g) (fa fb : S)
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] Localization.Away fa)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] Localization.Away fb)
    (hw₁ : (Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fa) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fa) g F)).1)
    (hw₂ : (Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fa) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fa) g F)).2)
    (hw₁' : (Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fb) b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fb) g F)).1)
    (hw₂' : (Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j')).toSubmodule
      = Submodule.map
          (LinearMap.baseChange (Localization.Away fb) b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mapAlg (Localization.Away fb) g F)).2)
    (va : Spec (CommRingCat.of (Localization.Away fa)) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm))
    (hva : va ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j)
    (vb : Spec (CommRingCat.of (Localization.Away fb)) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm))
    (hvb : vb ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom w'.toRingHom)
            ≫ pairChartMap k g r₁ g r₂ i' j') :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fa))))
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fb)))) ≫ va
      = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fa))))
          (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away fb)))) ≫ vb := by
  refine divScheme_hom_ext k _ _ g r₁ r₂ b₁ (b₂.map (windowShiftEquiv hπ g).symm)
    _ _ ?_
  rw [Category.assoc, Category.assoc, hva, hvb]
  exact pullback_chartMap_compat hπ g hO hχ r₁ r₂ b₁ b₂ F fa fb w w'
    hw₁ hw₂ hw₁' hw₂'

/-! ## §4 — the keystone -/

set_option maxHeartbeats 1600000 in
-- The full stitch: cover choice + glue + the pullback-cover clause; elaboration cost.
include hO hχ in
/-- **`divClassify` — the G-5 keystone** (`informal/w4-g5-worksheet.md` §4,
Noetherian-free per w4-ddr9 §0.4): a divisor family `F` of degree `g` over an affine
test `S` whose ε pair satisfies the carve `(♦)` factors through `DivScheme g` by a
**unique** morphism `v : Spec S ⟶ DivScheme g`, characterized by: for EVERY
localization `Localization.Away f₀` carrying a pair-chart framing `(i, j, w)` of the
restricted ε pair, the restriction of `v` composes with `divSchemeι` to the chart
morphism of the framing.  The clause is stable under further localization by
construction (its proof at any `f₀` is the W3 pullback-cover comparison).

Existence: `Scheme.Cover.glueMorphisms` of the per-piece classifications
(`divClassifyLocal`) over the frame cover (`divFamEps_exists_frameCover`), glued by
W3; the clause at arbitrary `(f₀, i, j, w)` is `Scheme.Cover.hom_ext` on the pullback
cover of `Spec (Away f₀)` along the frame cover, with W3 at `(f₀, f t)`.
Uniqueness: any two clause-satisfiers agree on each frame-cover piece
(`divScheme_hom_ext`), hence agree (`Scheme.Cover.hom_ext`). -/
theorem divClassify (F : DivFam C S π g)
    (hcarve : ∀ a : ↥(divisorSections k
        (windowS_choice π hπ g • fiberWeilDivisor π) ⊤),
      carvePairArrow (windowShiftMul hπ g a)
        (divFamEps hπ g F).1 (divFamEps hπ g F).2 = 0) :
    ∃! v : Spec (CommRingCat.of S) ⟶
        DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm),
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
          = Spec.map (CommRingCat.ofHom w.toRingHom)
              ≫ pairChartMap k g r₁ g r₂ i j := by
  -- the frame cover and its per-piece classifications
  obtain ⟨m, f, hspan, hdata⟩ :=
    divFamEps_exists_frameCover hπ g hO hχ r₁ r₂ b₁ b₂ F
  choose ci cj cw hw₁ hw₂ using hdata
  have hv : ∀ t : Fin m, ∃ vt : Spec (CommRingCat.of (Localization.Away (f t))) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm),
      vt ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
          (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
          (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom (cw t).toRingHom)
            ≫ pairChartMap k g r₁ g r₂ (ci t) (cj t) := fun t =>
    (divClassifyLocal hπ g hO hχ r₁ r₂ b₁ b₂ F hcarve (Localization.Away (f t))
      (ci t) (cj t) (cw t) (hw₁ t) (hw₂ t)).exists
  choose v hveq using hv
  -- the gluing obligation, by W3 on each double overlap
  have hglue : ∀ t t' : Fin m,
      pullback.fst ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) f hspan).openCover.f t)
        ((Scheme.affineOpenCoverOfSpanRangeEqTop
          (R := CommRingCat.of S) f hspan).openCover.f t') ≫ v t
      = pullback.snd _ _ ≫ v t' := fun t t' =>
    pullback_chartFactor_compat hπ g hO hχ r₁ r₂ b₁ b₂ F (f t) (f t')
      (cw t) (cw t') (hw₁ t) (hw₂ t) (hw₁ t') (hw₂ t') (v t) (hveq t) (v t') (hveq t')
  refine ⟨(Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of S) f hspan).openCover.glueMorphisms v hglue, ?_, ?_⟩
  · -- the clause at arbitrary `(f₀, i, j, w, hw₁, hw₂)`: the pullback-cover comparison
    intro f₀ i j w hwf₁ hwf₂
    refine Scheme.Cover.hom_ext
      ((Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) f hspan).openCover.pullback₁
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f₀)))))
      _ _ fun t => ?_
    change pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc,
      Scheme.Cover.ι_glueMorphisms_assoc, hveq t]
    exact (pullback_chartMap_compat hπ g hO hχ r₁ r₂ b₁ b₂ F f₀ (f t) w (cw t)
      hwf₁ hwf₂ (hw₁ t) (hw₂ t)).symm
  · -- uniqueness: any clause-satisfier agrees with the glue on each piece
    intro v' hv'
    refine Scheme.Cover.hom_ext
      (Scheme.affineOpenCoverOfSpanRangeEqTop
        (R := CommRingCat.of S) f hspan).openCover _ _ fun t => ?_
    refine divScheme_hom_ext k _ _ g r₁ r₂ b₁ (b₂.map (windowShiftEquiv hπ g).symm)
      _ _ ?_
    rw [Category.assoc, Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc, hveq t]
    exact hv' (f t) (ci t) (cj t) (cw t) (hw₁ t) (hw₂ t)

end Curve

end AlgebraicGeometry
