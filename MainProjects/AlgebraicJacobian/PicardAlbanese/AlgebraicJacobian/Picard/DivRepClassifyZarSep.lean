/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepClassifyZar
import AlgebraicJacobian.Picard.DivSchemeMonoBridgeRel

/-!
# F5 — the class side of the backward classification: separation

`Picard/DivRepClassifyZar.lean` proves the *hom* side of the backward classification:
a locally certified divisor class determines a **unique** morphism satisfying the
characterizing clause (`isDivRepClassify_unique`).  This file proves the *class* side:
a morphism satisfying the clause determines the **class**.

* `AlgebraicGeometry.map_pairTautFst_eq_of_specMap_pairChartMap_eq` and its `Snd`
  mirror — **the W2 converse**: two pair-chart maps presenting the same morphism to
  `grPair` pull the tautological pair back equally.  The forward implication is
  `specMap_pairChartMap_eq_of_map_pairTaut_eq`
  (`Picard/GrassmannianPairCompare.lean`); the converse is the two chart-compatibility
  theorems of `Picard/DivCarvePairChart.lean` read in the `pairTaut` spelling.
* `AlgebraicGeometry.eq_of_isDivRepClassify` — **the separation theorem**: two locally
  certified divisor classes over an affine test whose classifying morphism is the same
  are equal.
* `AlgebraicGeometry.divRepClassifyZar_injective` — the packaged corollary.

The route is certificate-free and free of the DDR9-U ε-identity: it consumes only the
composite certificate × frame cover (`DivFamZar.exists_certChartCover`), the frame
transport `map_window_frame_toSubmodule`, the seam-free relative mono
`divFam_divEq_of_eps_eq_total` (DDR-8), and Zariski separation for `DivFamZar`
(`DivFamZar.eq_of_away_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits
open scoped TensorProduct Pointwise

namespace AlgebraicGeometry

/-! ## The W2 converse in the `pairTaut` spelling -/

section PairTautConverse

open Grassmannian

variable (k : Type u) [Field k] (g r₁ r₂ : ℕ)

/-- **W2, converse, first factor**: two pair-chart maps presenting the same morphism
`Spec B ⟶ grPair` pull the first tautological window back equally.  The exact converse
of `specMap_pairChartMap_eq_of_map_pairTaut_eq`; both are the `pairTaut` reading of
`map_includeLeft_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq`. -/
theorem map_pairTautFst_eq_of_specMap_pairChartMap_eq
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] B)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] B)
    (h : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
       = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k g r₁ g r₂ i' j') :
    Module.Grassmannian.map w (pairTautFst k g r₁ r₂ i j)
      = Module.Grassmannian.map w' (pairTautFst k g r₁ r₂ i' j') := by
  have h₁ := Grassmannian.map_includeLeft_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq
    k g r₁ g r₂ w w' h
  rw [pairTautFst, pairTautFst, ← Module.Grassmannian.map_comp,
    ← Module.Grassmannian.map_comp]
  exact h₁

/-- **W2, converse, second factor**: the `pairTautSnd` mirror of
`map_pairTautFst_eq_of_specMap_pairChartMap_eq`. -/
theorem map_pairTautSnd_eq_of_specMap_pairChartMap_eq
    {i i' : (glueData k g r₁).J} {j j' : (glueData k g r₂).J}
    {B : Type u} [CommRing B] [Algebra k B]
    (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] B)
    (w' : PairChartRing k g r₁ g r₂ i' j' →ₐ[k] B)
    (h : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j
       = Spec.map (CommRingCat.ofHom w'.toRingHom) ≫ pairChartMap k g r₁ g r₂ i' j') :
    Module.Grassmannian.map w (pairTautSnd k g r₁ r₂ i j)
      = Module.Grassmannian.map w' (pairTautSnd k g r₁ r₂ i' j') := by
  have h₂ := Grassmannian.map_includeRight_chartTautologicalPoint_eq_of_specMap_pairChartMap_eq
    k g r₁ g r₂ w w' h
  rw [pairTautSnd, pairTautSnd, ← Module.Grassmannian.map_comp,
    ← Module.Grassmannian.map_comp]
  exact h₂

end PairTautConverse

/-! ## Cancelling the coordinate embedding of a window -/

section WindowCancel

/-- **The coordinate embedding of a window is injective**: base change of a linear
equivalence along `k → B` is an equivalence, so `Submodule.map` along it reflects
equality.  This is what removes the `b.equivFun` coordinates from a frame identity. -/
theorem submodule_eq_of_map_baseChange_equivFun_eq
    {k : Type u} [Field k] {M : Type u} [AddCommGroup M] [Module k M] {r : ℕ}
    (b : Module.Basis (Fin r) k M) (B : Type u) [CommRing B] [Algebra k B]
    {P Q : Submodule B (TensorProduct k B M)}
    (h : Submodule.map (LinearMap.baseChange B b.equivFun.toLinearMap) P
       = Submodule.map (LinearMap.baseChange B b.equivFun.toLinearMap) Q) :
    P = Q := by
  have hcomp : (LinearMap.baseChange B b.equivFun.symm.toLinearMap).comp
      (LinearMap.baseChange B b.equivFun.toLinearMap) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp]
    simp
  have hinj : Function.Injective (LinearMap.baseChange B b.equivFun.toLinearMap) := by
    intro x y hxy
    have h1 := congrArg (LinearMap.baseChange B b.equivFun.symm.toLinearMap) hxy
    have h2 : (LinearMap.baseChange B b.equivFun.symm.toLinearMap).comp
        (LinearMap.baseChange B b.equivFun.toLinearMap) x
      = (LinearMap.baseChange B b.equivFun.symm.toLinearMap).comp
        (LinearMap.baseChange B b.equivFun.toLinearMap) y := h1
    rwa [hcomp, LinearMap.id_apply, LinearMap.id_apply] at h2
  exact Submodule.map_injective_of_injective hinj h

end WindowCancel

/-! ## Separation: the classifying morphism determines the class -/

section Curve

open Scheme Grassmannian

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftDivRepSep :
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

/-- **The product of two span-⊤ families is span-⊤**: the common refinement of two
finite affine covers of `Spec S`. -/
theorem span_range_mul_eq_top {m₀ m₁ : ℕ} (c₀ : Fin m₀ → S) (c₁ : Fin m₁ → S)
    (h₀ : Ideal.span (Set.range c₀) = ⊤) (h₁ : Ideal.span (Set.range c₁) = ⊤) :
    Ideal.span (Set.range fun p : Fin m₀ × Fin m₁ => c₀ p.1 * c₁ p.2) = ⊤ := by
  refine top_le_iff.mp ?_
  calc (⊤ : Ideal S) = Ideal.span (Set.range c₀) * Ideal.span (Set.range c₁) := by
        rw [h₀, h₁, Ideal.top_mul]
    _ = Ideal.span (Set.range c₀ * Set.range c₁) := Ideal.span_mul_span _ _
    _ ≤ Ideal.span (Set.range fun p : Fin m₀ × Fin m₁ => c₀ p.1 * c₁ p.2) := by
        refine Ideal.span_mono ?_
        rintro x ⟨y, ⟨a, rfl⟩, z, ⟨b, rfl⟩, rfl⟩
        exact ⟨(a, b), rfl⟩

set_option maxHeartbeats 1600000 in
-- The window transports unfold `divFamEps`/`DivFam.window` defeq (I-0239 precedent).
set_option maxRecDepth 8000 in
include hO hχ in
/-- (Implementation) **The separation core at one common carrier**: if the SAME morphism
`v` classifies `F₀` and `F₁`, and both classes have a certified representative framed by
a pair chart over an away carrier of `S`, then the two classes agree after base change
to any common `k`/`S`-tower ring `B` of the two carriers.

Route: the clause fires at each carrier, both chart presentations push to `B` along the
structure maps, so they present the SAME morphism `Spec B ⟶ grPair`; the W2 converse
turns that into equality of the pulled tautological pairs; the frame transport
(`map_window_frame_toSubmodule`) reads each side as the coordinate image of the
restricted `ε`; the coordinates cancel; and the seam-free relative mono
(`divFam_divEq_of_eps_eq_total`) concludes. -/
private theorem mapAlg_eq_of_certChartFrames
    {B : Type u} [CommRing B] [Algebra k B] [Algebra S B] [IsScalarTower k S B]
    {A₀ : Type u} [CommRing A₀] [Algebra k A₀] [Algebra S A₀] [IsScalarTower k S A₀]
    [Algebra A₀ B] [IsScalarTower k A₀ B] [IsScalarTower S A₀ B]
    {A₁ : Type u} [CommRing A₁] [Algebra k A₁] [Algebra S A₁] [IsScalarTower k S A₁]
    [Algebra A₁ B] [IsScalarTower k A₁ B] [IsScalarTower S A₁ B]
    (F₀ F₁ : DivFamZar C S π g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (h₀ : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ v)
    (h₁ : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₁ v)
    (G₀ : CertifiedDivisorFamily C A₀ π g)
    (hZ₀ : (DivFam.mk G₀).toZar = DivFamZar.mapAlg A₀ g F₀)
    {i₀ : (glueData k g r₁).J} {j₀ : (glueData k g r₂).J}
    (w₀ : PairChartRing k g r₁ g r₂ i₀ j₀ →ₐ[k] A₀)
    (hfst₀ : (Module.Grassmannian.map w₀ (pairTautFst k g r₁ r₂ i₀ j₀)).toSubmodule
      = Submodule.map (LinearMap.baseChange A₀ b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mk G₀)).1)
    (hsnd₀ : (Module.Grassmannian.map w₀ (pairTautSnd k g r₁ r₂ i₀ j₀)).toSubmodule
      = Submodule.map (LinearMap.baseChange A₀ b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mk G₀)).2)
    (G₁ : CertifiedDivisorFamily C A₁ π g)
    (hZ₁ : (DivFam.mk G₁).toZar = DivFamZar.mapAlg A₁ g F₁)
    {i₁ : (glueData k g r₁).J} {j₁ : (glueData k g r₂).J}
    (w₁ : PairChartRing k g r₁ g r₂ i₁ j₁ →ₐ[k] A₁)
    (hfst₁ : (Module.Grassmannian.map w₁ (pairTautFst k g r₁ r₂ i₁ j₁)).toSubmodule
      = Submodule.map (LinearMap.baseChange A₁ b₁.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mk G₁)).1)
    (hsnd₁ : (Module.Grassmannian.map w₁ (pairTautSnd k g r₁ r₂ i₁ j₁)).toSubmodule
      = Submodule.map (LinearMap.baseChange A₁ b₂.equivFun.toLinearMap)
          (divFamEps hπ g (DivFam.mk G₁)).2) :
    DivFamZar.mapAlg B g F₀ = DivFamZar.mapAlg B g F₁ := by
  -- the two structure maps into the common carrier, as `k`-algebra maps
  let β₀ : A₀ →ₐ[k] B := IsScalarTower.toAlgHom k A₀ B
  let β₁ : A₁ →ₐ[k] B := IsScalarTower.toAlgHom k A₁ B
  have hβ₀ : β₀.toRingHom.comp (algebraMap A₀ A₀) = algebraMap A₀ B := by
    ext x
    simp [β₀]
  have hβ₁ : β₁.toRingHom.comp (algebraMap A₁ A₁) = algebraMap A₁ B := by
    ext x
    simp [β₁]
  -- STEP 1: the clause fires at each carrier and both presentations push to `B`
  have hpush : ∀ {A : Type u} [CommRing A] [Algebra k A] [Algebra S A]
      [IsScalarTower k S A] [Algebra A B] [IsScalarTower k A B] [IsScalarTower S A B]
      {i : (glueData k g r₁).J} {j : (glueData k g r₂).J}
      (w : PairChartRing k g r₁ g r₂ i j →ₐ[k] A),
      Spec.map (CommRingCat.ofHom (algebraMap S A))
          ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom w.toRingHom) ≫ pairChartMap k g r₁ g r₂ i j →
      Spec.map (CommRingCat.ofHom (algebraMap S B))
          ≫ v ≫ divSchemeι k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
            (b₂.map (windowShiftEquiv hπ g).symm)
        = Spec.map (CommRingCat.ofHom
            ((IsScalarTower.toAlgHom k A B).comp w).toRingHom)
          ≫ pairChartMap k g r₁ g r₂ i j := by
    intro A _ _ _ _ _ _ _ i j w hA
    have hSB : CommRingCat.ofHom (algebraMap S A)
        ≫ CommRingCat.ofHom (algebraMap A B)
        = CommRingCat.ofHom (algebraMap S B) := by
      rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hwB : CommRingCat.ofHom w.toRingHom ≫ CommRingCat.ofHom (algebraMap A B)
        = CommRingCat.ofHom ((IsScalarTower.toAlgHom k A B).comp w).toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      rfl
    rw [← hSB, Spec.map_comp, Category.assoc, hA, ← Category.assoc, ← Spec.map_comp,
      hwB]
  have hE₀ := hpush (A := A₀) w₀ (h₀ A₀ G₀ hZ₀ i₀ j₀ w₀ hfst₀ hsnd₀)
  have hE₁ := hpush (A := A₁) w₁ (h₁ A₁ G₁ hZ₁ i₁ j₁ w₁ hfst₁ hsnd₁)
  have hchart : Spec.map (CommRingCat.ofHom (β₀.comp w₀).toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i₀ j₀
      = Spec.map (CommRingCat.ofHom (β₁.comp w₁).toRingHom)
        ≫ pairChartMap k g r₁ g r₂ i₁ j₁ := hE₀.symm.trans hE₁
  -- STEP 2: the W2 converse
  have htf := map_pairTautFst_eq_of_specMap_pairChartMap_eq k g r₁ r₂
    (β₀.comp w₀) (β₁.comp w₁) hchart
  have hts := map_pairTautSnd_eq_of_specMap_pairChartMap_eq k g r₁ r₂
    (β₀.comp w₀) (β₁.comp w₁) hchart
  -- STEP 3: the frame transports
  have htr₀f : (Module.Grassmannian.map (β₀.comp w₀)
        (pairTautFst k g r₁ r₂ i₀ j₀)).toSubmodule
      = Submodule.map (LinearMap.baseChange B b₁.equivFun.toLinearMap)
          ((DivFam.mapAlg B g (DivFam.mk G₀)).window
            (relThetaPairH1_windowM C π hπ g)) := by
    rw [Module.Grassmannian.map_comp]
    exact map_window_frame_toSubmodule hπ g hO hχ (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) le_rfl b₁ (DivFam.mk G₀) β₀ hβ₀
      (Module.Grassmannian.map w₀ (pairTautFst k g r₁ r₂ i₀ j₀))
      (by rw [DivFam.mapAlg_id]; exact hfst₀)
  have htr₀s : (Module.Grassmannian.map (β₀.comp w₀)
        (pairTautSnd k g r₁ r₂ i₀ j₀)).toSubmodule
      = Submodule.map (LinearMap.baseChange B b₂.equivFun.toLinearMap)
          ((DivFam.mapAlg B g (DivFam.mk G₀)).window
            (relThetaPairH1_windowMS C π hπ g)) := by
    rw [Module.Grassmannian.map_comp]
    exact map_window_frame_toSubmodule hπ g hO hχ
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ (DivFam.mk G₀) β₀ hβ₀
      (Module.Grassmannian.map w₀ (pairTautSnd k g r₁ r₂ i₀ j₀))
      (by rw [DivFam.mapAlg_id]; exact hsnd₀)
  have htr₁f : (Module.Grassmannian.map (β₁.comp w₁)
        (pairTautFst k g r₁ r₂ i₁ j₁)).toSubmodule
      = Submodule.map (LinearMap.baseChange B b₁.equivFun.toLinearMap)
          ((DivFam.mapAlg B g (DivFam.mk G₁)).window
            (relThetaPairH1_windowM C π hπ g)) := by
    rw [Module.Grassmannian.map_comp]
    exact map_window_frame_toSubmodule hπ g hO hχ (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) le_rfl b₁ (DivFam.mk G₁) β₁ hβ₁
      (Module.Grassmannian.map w₁ (pairTautFst k g r₁ r₂ i₁ j₁))
      (by rw [DivFam.mapAlg_id]; exact hfst₁)
  have htr₁s : (Module.Grassmannian.map (β₁.comp w₁)
        (pairTautSnd k g r₁ r₂ i₁ j₁)).toSubmodule
      = Submodule.map (LinearMap.baseChange B b₂.equivFun.toLinearMap)
          ((DivFam.mapAlg B g (DivFam.mk G₁)).window
            (relThetaPairH1_windowMS C π hπ g)) := by
    rw [Module.Grassmannian.map_comp]
    exact map_window_frame_toSubmodule hπ g hO hχ
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) b₂ (DivFam.mk G₁) β₁ hβ₁
      (Module.Grassmannian.map w₁ (pairTautSnd k g r₁ r₂ i₁ j₁))
      (by rw [DivFam.mapAlg_id]; exact hsnd₁)
  -- STEP 4: cancel the coordinates
  have hwf : (DivFam.mapAlg B g (DivFam.mk G₀)).window
        (relThetaPairH1_windowM C π hπ g)
      = (DivFam.mapAlg B g (DivFam.mk G₁)).window
        (relThetaPairH1_windowM C π hπ g) :=
    submodule_eq_of_map_baseChange_equivFun_eq b₁ B
      (htr₀f.symm.trans ((congrArg Module.Grassmannian.toSubmodule htf).trans htr₁f))
  have hws : (DivFam.mapAlg B g (DivFam.mk G₀)).window
        (relThetaPairH1_windowMS C π hπ g)
      = (DivFam.mapAlg B g (DivFam.mk G₁)).window
        (relThetaPairH1_windowMS C π hπ g) :=
    submodule_eq_of_map_baseChange_equivFun_eq b₂ B
      (htr₀s.symm.trans ((congrArg Module.Grassmannian.toSubmodule hts).trans htr₁s))
  -- STEP 5: the seam-free relative mono at `B`
  have heps : divFamEps hπ g (DivFam.mk (G₀.mapAlg B g))
      = divFamEps hπ g (DivFam.mk (G₁.mapAlg B g)) := by
    rw [← DivFam.mapAlg_mk, ← DivFam.mapAlg_mk]
    exact Prod.ext hwf hws
  have hmk : DivFam.mk (G₀.mapAlg B g) = DivFam.mk (G₁.mapAlg B g) :=
    divFam_divEq_of_eps_eq_total hπ g _ _ heps hO hχ
  -- STEP 6: back to the Zar classes
  have e₀ : (DivFam.mk (G₀.mapAlg B g)).toZar = DivFamZar.mapAlg B g F₀ := by
    rw [← DivFam.mapAlg_mk, DivFam.toZar_mapAlg, hZ₀, DivFamZar.mapAlg_comp]
  have e₁ : (DivFam.mk (G₁.mapAlg B g)).toZar = DivFamZar.mapAlg B g F₁ := by
    rw [← DivFam.mapAlg_mk, DivFam.toZar_mapAlg, hZ₁, DivFamZar.mapAlg_comp]
  exact e₀.symm.trans ((congrArg DivFam.toZar hmk).trans e₁)

set_option maxHeartbeats 800000 in
-- Two `exists_certChartCover` unfoldings plus the away-tower instance block; the
-- localization `lift`/`IsScalarTower` synthesis is what costs (I-0227 budget).
include hO hχ in
/-- **The separation theorem** (w4-ddr9 §2.1, the class side of step 6): two locally
certified divisor classes over an affine test that are classified by the SAME morphism
are equal.  Together with `isDivRepClassify_unique` — the hom side — the characterizing
clause is therefore a *bijective* correspondence on the nose.

Proof: the composite certificate × frame cover of each class, refined against the other
by the product cover (`span_range_mul_eq_top`); at each common away carrier the two
chart presentations of `v` coincide, so `mapAlg_eq_of_certChartFrames` equates the
restricted classes; `DivFamZar.eq_of_away_eq` globalizes.

No certificate over the whole chart ring and no DDR9-U ε-identity is consumed. -/
theorem eq_of_isDivRepClassify (F₀ F₁ : DivFamZar C S π g)
    {v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁
        (b₂.map (windowShiftEquiv hπ g).symm)}
    (h₀ : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₀ v)
    (h₁ : IsDivRepClassify hπ g r₁ r₂ b₁ b₂ F₁ v) : F₀ = F₁ := by
  classical
  obtain ⟨m₀, c₀, hspan₀, hdata₀⟩ :=
    DivFamZar.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₀
  obtain ⟨m₁, c₁, hspan₁, hdata₁⟩ :=
    DivFamZar.exists_certChartCover hπ g hO hχ r₁ r₂ b₁ b₂ F₁
  choose G₀ ci₀ cj₀ cw₀ hZ₀ hfst₀ hsnd₀ using hdata₀
  choose G₁ ci₁ cj₁ cw₁ hZ₁ hfst₁ hsnd₁ using hdata₁
  -- the product cover, `ULift`ed into the working universe
  have hspan : Ideal.span (Set.range
      fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) => c₀ p.1.down * c₁ p.2.down)
      = ⊤ := by
    have hsurj : Function.Surjective
        (fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) => (p.1.down, p.2.down)) := by
      rintro ⟨a, b⟩
      exact ⟨(⟨a⟩, ⟨b⟩), rfl⟩
    have hrange := hsurj.range_comp (fun q : Fin m₀ × Fin m₁ => c₀ q.1 * c₁ q.2)
    exact hrange ▸ span_range_mul_eq_top c₀ c₁ hspan₀ hspan₁
  refine DivFamZar.eq_of_away_eq
    (fun p : ULift.{u} (Fin m₀) × ULift.{u} (Fin m₁) => c₀ p.1.down * c₁ p.2.down)
    (fun p => Localization.Away (c₀ p.1.down * c₁ p.2.down)) hspan ?_
  rintro ⟨⟨p₀⟩, ⟨p₁⟩⟩
  -- the first carrier maps to the refinement
  letI : Algebra (Localization.Away (c₀ p₀)) (Localization.Away (c₀ p₀ * c₁ p₁)) :=
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
  -- and so does the second
  letI : Algebra (Localization.Away (c₁ p₁)) (Localization.Away (c₀ p₀ * c₁ p₁)) :=
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
  exact mapAlg_eq_of_certChartFrames hπ g hO hχ r₁ r₂ b₁ b₂ F₀ F₁ h₀ h₁
    (G₀ p₀) (hZ₀ p₀) (cw₀ p₀) (hfst₀ p₀) (hsnd₀ p₀)
    (G₁ p₁) (hZ₁ p₁) (cw₁ p₁) (hfst₁ p₁) (hsnd₁ p₁)

include hO hχ in
/-- **The keystone map is injective** (the F6 Law-1 input): distinct locally certified
divisor classes over an affine test classify to distinct morphisms.  Immediate from
`eq_of_isDivRepClassify` and the characterizing lemma. -/
theorem divRepClassifyZar_injective :
    Function.Injective (divRepClassifyZar (C := C) (π := π) hπ g hO hχ r₁ r₂ b₁ b₂ S) := by
  intro F₀ F₁ h
  refine eq_of_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀ F₁
    (v := (divRepClassifyZar hπ g hO hχ r₁ r₂ b₁ b₂ S F₁).left)
    ?_ (divRepClassifyZar_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₁)
  rw [← h]
  exact divRepClassifyZar_isDivRepClassify hπ g hO hχ r₁ r₂ b₁ b₂ F₀

end Curve

end AlgebraicGeometry
