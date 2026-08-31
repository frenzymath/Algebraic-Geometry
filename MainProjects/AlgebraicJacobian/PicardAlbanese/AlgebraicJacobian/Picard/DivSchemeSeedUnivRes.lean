/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssembleKappa

/-!
# G-4 — the seed fibre seam: `K_univ ⊗ κ(q)` spans the fibre window (worksheet §1.5 (b))

The REAL seam of the universal-seed achiever lift (I-0247 step (b)): the fibre of the
universal seed window `K_univ` at a field point `K` of a `Z(♦)`-chart ring **spans the
fibre window** `divUniversalFibreKM` — the base-change naturality of the window
identification at the two-step tower `R_{I,J} → R_Z → K`, in an intrinsic spelling.

* `AlgebraicGeometry.windowCompare` — the structure-free fibre comparison
  `S ⊗[k] H → S' ⊗[k] H` (`algebraMap` on the scalar leg), with the `cancelBaseChange`
  identification (`windowCompare_eq_cancelBaseChange` — the recorded I-0232 orientation
  seam), the tower law, the `baseChange` naturality, and the pure-tensor bridge
  `tmul_one_eq_zero_iff_windowCompare` (the Nakayama-neighbourhood transport);
* `Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare` — **the kernel-span seam**:
  over any algebra of the ambient ring, the kernel of the base-changed tautological
  quotient is the span of the compared kernel elements
  (`ker_baseChangeMkQ_eq_map_baseChange` + the span description of
  `Submodule.baseChange`);
* `divUniversalFst_toSubmodule_eq_span` / `divUniversalFstWindow_toSubmodule_eq_span` —
  the `Z(♦)`-chart instantiations: the universal (window) point is the span of the
  compared tautological kernel (the `Module.Grassmannian.map` `letI` seam closed
  against the ambient quotient instance);
* `divUniversalFibreKM_eq_span` — **THE SEAM KEYSTONE** (worksheet §1.5 (b)): at every
  field point `K` of the tower `R_{I,J} → R_Z → K`, the fibre window
  `divUniversalFibreKM` is the `K`-span of the `Φ`-read fibre comparisons of the
  universal window `divUniversalFstWindow` — every fibre-window element is a
  combination of fibres of relative seed sections, so fibre-window data (achievers,
  nonvanishing) is realized by relative seed sections
  (`divFamPhi_windowCompare_mem_divUniversalFibreKM` is the elementwise forward form).
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The structure-free window comparison `ρ` -/

section WindowCompare

variable {k : Type u} [Field k]
variable {H : Type u} [AddCommGroup H] [Module k H]
variable (S : Type u) [CommRing S] [Algebra k S]
variable (S' : Type u) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']

/-- **The window comparison** `ρ : S ⊗[k] H → S' ⊗[k] H` over a scalar change `S → S'`:
`algebraMap` on the scalar leg, the identity on the window leg — the intrinsic
(structure-free) spelling of the fibre restriction of free windows. -/
noncomputable def windowCompare : TensorProduct k S H →ₗ[k] TensorProduct k S' H :=
  LinearMap.rTensor H ((Algebra.linearMap S S').restrictScalars k)

@[simp]
lemma windowCompare_tmul (s : S) (h : H) :
    windowCompare S S' (s ⊗ₜ[k] h) = algebraMap S S' s ⊗ₜ[k] h :=
  rfl

/-- The window comparison is `algebraMap`-semilinear over the scalars. -/
lemma windowCompare_smul (s : S) (x : TensorProduct k S H) :
    windowCompare S S' (s • x) = algebraMap S S' s • windowCompare S S' x := by
  induction x with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add y z hy hz => rw [smul_add, map_add, hy, hz, map_add, smul_add]
  | tmul t h =>
    rw [TensorProduct.smul_tmul', windowCompare_tmul, windowCompare_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]

/-- **The tower law of the window comparison.** -/
lemma windowCompare_windowCompare (S'' : Type u) [CommRing S''] [Algebra k S'']
    [Algebra S S''] [Algebra S' S''] [IsScalarTower k S S''] [IsScalarTower k S' S'']
    [IsScalarTower S S' S'']
    (x : TensorProduct k S H) :
    windowCompare S' S'' (windowCompare S S' x) = windowCompare S S'' x := by
  induction x with
  | zero => rw [map_zero, map_zero, map_zero]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
  | tmul t h =>
    rw [windowCompare_tmul, windowCompare_tmul, windowCompare_tmul,
      ← IsScalarTower.algebraMap_apply]

/-- **The `cancelBaseChange` identification** (the recorded I-0232 orientation seam):
the window comparison is `cancelBaseChange` applied to `1 ⊗ₜ x` — the
`ker_baseChangeMkQ` normal form of `Picard/DivCarveKit.lean`. -/
lemma windowCompare_eq_cancelBaseChange (x : TensorProduct k S H) :
    windowCompare S S' x
      = TensorProduct.AlgebraTensorModule.cancelBaseChange k S S' S' H (1 ⊗ₜ x) := by
  induction x with
  | zero => rw [map_zero, TensorProduct.tmul_zero, map_zero]
  | add y z hy hz =>
    rw [map_add, hy, hz, TensorProduct.tmul_add, map_add]
  | tmul t h =>
    rw [windowCompare_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      Algebra.algebraMap_eq_smul_one]

/-- Naturality of the window comparison against base changes of `k`-linear maps of the
window leg. -/
lemma windowCompare_baseChange {H' : Type u} [AddCommGroup H'] [Module k H']
    (f : H →ₗ[k] H') (x : TensorProduct k S H) :
    windowCompare (H := H') S S' (LinearMap.baseChange S f x)
      = LinearMap.baseChange S' f (windowCompare S S' x) := by
  induction x with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | tmul t h =>
    rw [windowCompare_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      windowCompare_tmul]

/-- The two spellings of the base-changed window equivalence agree elementwise
(`LinearEquiv.baseChange` vs `LinearMap.baseChange` of the underlying map). -/
lemma baseChange_linearEquiv_apply {H' : Type u} [AddCommGroup H'] [Module k H']
    (e : H ≃ₗ[k] H') (x : TensorProduct k S H) :
    (LinearEquiv.baseChange k S H H' e).toLinearMap x
      = LinearMap.baseChange S e.toLinearMap x := by
  induction x with
  | zero => rw [map_zero, map_zero]
  | add y z hy hz => rw [map_add, map_add, hy, hz]
  | tmul t h =>
    rw [LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
    rfl

/-- **The pure-tensor bridge**: vanishing of `x ⊗ₜ 1` in the scalar extension of the
free window is vanishing of the window comparison — the transport between the
Nakayama-neighbourhood spelling (`Module.exists_forall_tmul_residueField_ne_zero`) and
the seam spelling. -/
lemma tmul_one_eq_zero_iff_windowCompare (x : TensorProduct k S H) :
    (x ⊗ₜ[S] (1 : S') : TensorProduct k S H ⊗[S] S') = 0
      ↔ windowCompare S S' x = 0 := by
  rw [windowCompare_eq_cancelBaseChange]
  constructor
  · intro h
    have h1 : (TensorProduct.comm S (TensorProduct k S H) S') (x ⊗ₜ[S] (1 : S'))
        = (1 : S') ⊗ₜ[S] x := rfl
    rw [← h1, h, map_zero, map_zero]
  · intro h
    have h1 : ((1 : S') ⊗ₜ[S] x : S' ⊗[S] TensorProduct k S H) = 0 :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k S S' S' H).injective
        (by rw [h, map_zero])
    have h2 := congrArg (TensorProduct.comm S (TensorProduct k S H) S').symm h1
    rw [map_zero] at h2
    exact h2

end WindowCompare

/-! ## The span collapse under a semilinear map -/

section SpanCollapse

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R₁ M₁] [Module R₂ M₂]

/-- The span of the image of a span under an additive `algebraMap`-semilinear map is
the span of the image of the generators. -/
lemma span_image_span_of_algebraMap_smul {F : M₁ → M₂} (h0 : F 0 = 0)
    (hadd : ∀ x y, F (x + y) = F x + F y)
    (hF : ∀ (r : R₁) (y : M₁), F (r • y) = algebraMap R₁ R₂ r • F y) (X : Set M₁) :
    Submodule.span R₂ (F '' ((Submodule.span R₁ X : Submodule R₁ M₁) : Set M₁))
      = Submodule.span R₂ (F '' X) := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨y, hy, rfl⟩
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Set.mem_image_of_mem _ hx)
  | zero =>
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [hadd]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [hF r x]
    exact Submodule.smul_mem _ _ hx

end SpanCollapse

/-! ## The kernel-span seam -/

namespace Grassmannian

variable {k : Type u} [Field k]
variable {H : Type u} [AddCommGroup H] [Module k H]

/-- **The kernel-span seam**: over any algebra `S` of the ambient ring `A`, the kernel
of the base-changed tautological quotient of a projective-quotient submodule
`N ⊆ A ⊗[k] H` is the `S`-span of the compared elements of `N` —
`ker_baseChangeMkQ_eq_map_baseChange` with the base change spelled as a span. -/
theorem ker_baseChangeMkQ_eq_span_windowCompare
    {A : Type u} [CommRing A] [Algebra k A] (N : Submodule A (TensorProduct k A H))
    [Module.Projective A (TensorProduct k A H ⧸ N)]
    (S : Type u) [CommRing S] [Algebra k S] [Algebra A S] [IsScalarTower k A S] :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ S N)
      = Submodule.span S
          (windowCompare A S '' (N : Set (TensorProduct k A H))) := by
  rw [Grassmannian.ker_baseChangeMkQ_eq_map_baseChange S N,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    ← Set.image_comp]
  refine congrArg (Submodule.span S) (Set.image_congr fun n _ => ?_)
  exact (windowCompare_eq_cancelBaseChange A S n).symm

end Grassmannian

/-! ## The `Z(♦)`-chart instantiation: the universal windows as spans -/

section Campaign

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
variable {π : C.left ⟶ P1 k} [IsFinite π] [IsDominant π]

noncomputable local instance instOverCleftSeedRes : C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r₁ r₂ : ℕ)
variable (b₁ : Module.Basis (Fin r₁) k
  ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤))
variable (b₂ : Module.Basis (Fin r₂) k
  ↥(Scheme.divisorSections k ((windowS_choice π hπ g • fiberWeilDivisor π)
    + (windowM_choice π hπ g • fiberWeilDivisor π)) ⊤))
variable (i : (glueData k g r₁).J) (j : (glueData k g r₂).J)

set_option linter.unusedSectionVars false in
/-- (Implementation) The `Module.Grassmannian.map` `letI` seam, closed: inside the
`toAlgebra` structure of the quotient presentation the universal first window is the
span of the compared tautological kernel; the comparison is intrinsic (`algebraMap` of
the ambient quotient instance is the quotient map), so the statement is `letI`-free. -/
private lemma divUniversalFst_toSubmodule_eq_span_aux :
    (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.span
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          (windowCompare (PairChartRing k g r₁ g r₂ i j)
              (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) ''
            ((pairTautFst k g r₁ r₂ i j).toSubmodule :
              Set (TensorProduct k (PairChartRing k g r₁ g r₂ i j) (Fin r₁ → k)))) := by
  letI : Algebra (PairChartRing k g r₁ g r₂ i j)
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) :=
    (divCarveChartMk k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toAlgebra
  letI : IsScalarTower k (PairChartRing k g r₁ g r₂ i j)
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq k _ _
  have h1 := Module.Grassmannian.map_toSubmodule
    (divCarveChartMk k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
    (pairTautFst k g r₁ r₂ i j)
  refine ((show (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule = _
    from h1).trans ?_)
  rw [Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare]

set_option linter.unusedSectionVars false in
/-- **The universal first window is the span of the compared tautological kernel** —
the `Z(♦)`-chart instantiation of the kernel-span seam, in the ambient quotient
instance. -/
theorem divUniversalFst_toSubmodule_eq_span :
    (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.span
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          (windowCompare (PairChartRing k g r₁ g r₂ i j)
              (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) ''
            ((pairTautFst k g r₁ r₂ i j).toSubmodule :
              Set (TensorProduct k (PairChartRing k g r₁ g r₂ i j) (Fin r₁ → k)))) :=
  divUniversalFst_toSubmodule_eq_span_aux C hπ g r₁ r₂ b₁ b₂ i j

set_option maxHeartbeats 800000 in
-- the campaign window ambients make the `congrAmbient` defeq checks heavy
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
/-- **The universal first window point, in the window ambient, as a span**: the
`b₁`-congruence of the compared tautological kernel. -/
theorem divUniversalFstWindow_toSubmodule_eq_span :
    (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.span
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
          ((fun n =>
              LinearMap.baseChange
                (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
                b₁.equivFun.symm.toLinearMap
              (windowCompare (PairChartRing k g r₁ g r₂ i j)
                (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) n)) ''
            ((pairTautFst k g r₁ r₂ i j).toSubmodule :
              Set (TensorProduct k (PairChartRing k g r₁ g r₂ i j) (Fin r₁ → k)))) := by
  have h0 : (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule
      = Submodule.map
          (LinearMap.baseChange
            (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
              (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
            b₁.equivFun.symm.toLinearMap)
          (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j).toSubmodule :=
    congrAmbient_toSubmodule b₁.equivFun.symm
      (divUniversalFst k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
  rw [h0, divUniversalFst_toSubmodule_eq_span C hπ g r₁ r₂ b₁ b₂ i j,
    Submodule.map_span, ← Set.image_comp]
  rfl

/-! ## The seam keystone: the fibre window is spanned by the seed fibres -/

section Kappa

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (PairChartRing k g r₁ g r₂ i j) K]
  [IsScalarTower k (PairChartRing k g r₁ g r₂ i j) K]
  [Algebra (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower k (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
    (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]
  [IsScalarTower (PairChartRing k g r₁ g r₂ i j)
    (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
      (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K]

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack).
noncomputable local instance instIsIntegralRelCurveSeedRes (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveSeedRes (L : Type u) [Field L]
    [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveSeedRes (L : Type u) [Field L]
    [Algebra k L] : QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instLFTRelCurveSeedRes (L : Type u) [Field L]
    [Algebra k L] : LocallyOfFiniteType (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  haveI : Smooth (relCurve C L ↘ Spec (CommRingCat.of L)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

set_option maxHeartbeats 1000000 in
-- base-changed tautological towers over the pair chart ring (the recorded hatch class)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **THE SEAM KEYSTONE** (worksheet §1.5 (b), I-0247 step (b)): at any field point `K`
of the tower `R_{I,J} → R_Z → K`, the fibre window `divUniversalFibreKM` is the
`K`-span of the `Φ`-read fibre comparisons of the elements of the universal window
`divUniversalFstWindow` — `K_univ ⊗ κ(q)` spans the fibre window, so fibre-window data
(achievers, nonvanishing) is realized by relative seed sections. -/
theorem divUniversalFibreKM_eq_span :
    divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K
      = Submodule.span K
          ((fun x => divFamPhi C K π (windowM_choice π hπ g)
              (relThetaPairH1_windowM C π hπ g)
              (windowCompare
                (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
                K x)) ''
            ((divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule :
              Set (TensorProduct k
                (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
                  (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
                ↥(Scheme.divisorSections k
                  (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)))) := by
  -- the right side: the window as a span, collapsed through the semilinear `Φ ∘ ρ`
  rw [divUniversalFstWindow_toSubmodule_eq_span C hπ g r₁ r₂ b₁ b₂ i j,
    span_image_span_of_algebraMap_smul
      (F := fun x => divFamPhi C K π (windowM_choice π hπ g)
        (relThetaPairH1_windowM C π hπ g)
        (windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x))
      (by rw [map_zero, map_zero])
      (fun x y => by rw [map_add, map_add])
      (fun r y => by rw [windowCompare_smul, map_smul])
      _,
    ← Set.image_comp]
  -- the left side: the kernel-span seam at `K` over the pair chart ring, pushed
  -- through the boundary equivalence and `Φ`
  rw [divUniversalFibreKM,
    Grassmannian.ker_baseChangeMkQ_eq_span_windowCompare
      (pairTautFst k g r₁ r₂ i j).toSubmodule K,
    Submodule.map_span, Submodule.map_span, ← Set.image_comp, ← Set.image_comp]
  -- generatorwise agreement: naturality of the comparison + the tower law
  refine congrArg (Submodule.span K) (Set.image_congr fun n _ => ?_)
  simp only [Function.comp_apply]
  rw [baseChange_linearEquiv_apply, windowCompare_baseChange,
    windowCompare_windowCompare]

set_option maxHeartbeats 800000 in
-- base-changed tautological towers over the pair chart ring (the recorded hatch class)
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSectionVars false in
/-- **The elementwise forward seam**: the `Φ`-read fibre comparison of any element of
the universal window lies in the fibre window. -/
theorem divFamPhi_windowCompare_mem_divUniversalFibreKM
    {x : TensorProduct k
      (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
        (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j)
      ↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hx : x ∈ (divUniversalFstWindow C π hπ g r₁ r₂ b₁ b₂ i j).toSubmodule) :
    divFamPhi C K π (windowM_choice π hπ g) (relThetaPairH1_windowM C π hπ g)
        (windowCompare
          (DivCarveChartRing k (windowS_choice π hπ g • fiberWeilDivisor π)
            (windowM_choice π hπ g • fiberWeilDivisor π) g r₁ r₂ b₁ b₂ i j) K x)
      ∈ divUniversalFibreKM C hπ g r₁ r₂ b₁ i j K := by
  rw [divUniversalFibreKM_eq_span C hπ g r₁ r₂ b₁ b₂ i j K]
  exact Submodule.subset_span (Set.mem_image_of_mem _ hx)

end Kappa

end Campaign

end AlgebraicGeometry
