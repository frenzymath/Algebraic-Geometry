/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeEpsCarveKit

/-!
# DDR-9.0 — the carve discharge `divFamEps_carve` (`informal/w4-ddr9-worksheet.md` §2.0)

Every landed consumer threads the carve `(♦)` of the ε-pair as a *hypothesis* `hcarve`
(`Picard/DivSchemeClassifyAff.lean`, `RiemannRoch/CarveDegree.lean`,
`Picard/DivisorFamilyEpsMono.lean`); this file discharges it for an ARBITRARY certified
family — the backward direction of `divRepAff` classifies an arbitrary functor value, so
without this there is no Equiv.  The theta-presentation substrate is
`AlgebraicJacobian.Picard.DivSchemeEpsCarveKit`.

* `AlgebraicGeometry.relThetaWindowEquiv_sectionMul_fst/_snd` — **the cross-exponent
  multiplicativity of the window identification**: for every multiplier section
  `a ∈ H⁰(𝒪(s·F))` and every `x ∈ R ⊗[k] H_M`, the `(M+s)`-window image of
  `(windowShiftMul a) ⊗ R` applied to `x` is, chart-componentwise, the product of the
  `Θˢ`-presentation of `a` pulled to `C_R` (`windowShiftTheta₀/₁`) with the `M`-window
  image of `x`.  Proved on pure tensors `1 ⊗ₜ m` and extended linearly (the I-0232
  crux-triangle pattern); the cocycle law `Θ^{M+s} = Θˢ·Θᴹ` enters as `pow_add` through
  the germ-at-η reading of the field-level bridge (the kit).
* `AlgebraicGeometry.divFamEps_carve` — **DDR-9.0, the carve discharge**: the ε-pair of
  any certified divisor family satisfies
  `carvePairArrow (windowShiftMul hπ g a) ε₁ ε₂ = 0` for every `a` — membership only,
  no fibres, no rank arithmetic: the window submodules are germ-vanishing loci
  (`mem_divisorWindow_iff`), and the stalk ideal absorbs the multiplier through
  `Ideal.mul_mem_left` once the componentwise product identity stands.
-/

set_option autoImplicit false
/- Statements mix `Γ(relCurve C R, ·)` with opens produced on the product spelling
`(C ⊗ overSpec k R).left`; see `AlgebraicJacobian.Cohomology.RelativeSectionsLinear`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance (priority := 50) instOverCleftEpsCarve :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

attribute [local instance 10000] relCurve.instOver

/-! ## KEYSTONE 1 — the cross-exponent multiplicativity of the window identification -/

section SectionMul

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
variable (R : Type u) [CommRing R] [Algebra k R]

/-- **The chart-0 multiplier section of the carve**: the `Θˢ`-presentation of
`a ∈ H⁰(𝒪(s·F))`, restricted to the first pinned chart and pulled to `relCurve C R`. -/
noncomputable def windowShiftTheta₀
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₀) :=
  relSectionsMap C k R (fiberTwoCover π).V₀
    ((relCurve C k).resHom (le_inf le_top le_rfl)
      ((relThetaFieldSection C π (windowS_choice π hπ g) a).val.1))

/-- **The chart-1 multiplier section of the carve** (mirror). -/
noncomputable def windowShiftTheta₁
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    Γ(relCurve C R, (relCover C R (fiberTwoCover π)).V₁) :=
  relSectionsMap C k R (fiberTwoCover π).V₁
    ((relCurve C k).resHom (le_inf le_top le_rfl)
      ((relThetaFieldSection C π (windowS_choice π hπ g) a).val.2))

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **DDR-9.0 keystone (compat), chart 0 — the cross-exponent multiplicativity of the
window identification** (`informal/w4-ddr9-worksheet.md` §2.0): for a multiplier section
`a ∈ H⁰(𝒪(s·F))` and any `x ∈ R ⊗[k] H_M`, the `(M+s)`-window image of the base-changed
window-shift multiplier applied to `x` is the product of the `Θˢ`-presentation of `a`
(pulled to `C_R`) with the `M`-window image of `x`, on the first chart.  Stated on pure
tensors and extended linearly; the cocycle law `Θ^{M+s} = Θˢ·Θᴹ` is `pow_add` inside the
field-level germ computation. -/
theorem relThetaWindowEquiv_sectionMul_fst
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (hH1M : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g))).H1)
    (hH1MS : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g + windowS_choice π hπ g))).H1)
    (x : R ⊗[k] ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R π (windowM_choice π hπ g + windowS_choice π hπ g)
          hH1MS (LinearMap.baseChange R (windowShiftMul hπ g a) x)).val.1)
      = windowShiftTheta₀ C π hπ g R a
        * (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M x).val.1) := by
  induction x with
  | zero => simp only [map_zero, Submodule.coe_zero, Prod.fst_zero, mul_zero]
  | add x y hx hy =>
    have h2 : (relThetaWindowEquiv C R π
          (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
          (LinearMap.baseChange R (windowShiftMul hπ g a) x
            + LinearMap.baseChange R (windowShiftMul hπ g a) y)).val.1
        = (relThetaWindowEquiv C R π
            (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
            (LinearMap.baseChange R (windowShiftMul hπ g a) x)).val.1
          + (relThetaWindowEquiv C R π
              (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
              (LinearMap.baseChange R (windowShiftMul hπ g a) y)).val.1 := by
      rw [map_add]
      rfl
    have h3 : (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M (x + y)).val.1
        = (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M x).val.1
          + (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M y).val.1 := by
      rw [map_add]
      rfl
    rw [map_add, h2, map_add, hx, hy, h3, map_add, mul_add]
  | tmul r m =>
    have hone : (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R π (windowM_choice π hπ g + windowS_choice π hπ g)
          hH1MS (1 ⊗ₜ (windowShiftMul hπ g a m))).val.1)
        = windowShiftTheta₀ C π hπ g R a
          * (relCurve C R).resHom (le_inf le_top le_rfl)
              ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M
                (1 ⊗ₜ m)).val.1) :=
      ((resHom_relThetaWindowEquiv_one_tmul_fst C π R
          (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
          (windowShiftMul hπ g a m)).trans
        ((congrArg (relSectionsMap C k R (fiberTwoCover π).V₀)
            (resHom_relThetaFieldSection_windowShiftMul_fst C π hπ g a m)).trans
          (map_mul (relSectionsMap C k R (fiberTwoCover π).V₀) _ _))).trans
        (congrArg (windowShiftTheta₀ C π hπ g R a * ·)
          (resHom_relThetaWindowEquiv_one_tmul_fst C π R
            (windowM_choice π hπ g) hH1M m).symm)
    have hbc : LinearMap.baseChange R (windowShiftMul hπ g a) (r ⊗ₜ m)
        = r • ((1 : R) ⊗ₜ (windowShiftMul hπ g a m)) := by
      rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hsm : (r ⊗ₜ m : R ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) = r • ((1 : R) ⊗ₜ m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e1 : (relThetaWindowEquiv C R π
          (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
          (LinearMap.baseChange R (windowShiftMul hπ g a) (r ⊗ₜ m))).val.1
        = r • (relThetaWindowEquiv C R π
            (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
            (1 ⊗ₜ (windowShiftMul hπ g a m))).val.1 := by
      rw [hbc, map_smul]
      rfl
    have e2 : (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M (r ⊗ₜ m)).val.1
        = r • (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M
            (1 ⊗ₜ m)).val.1 := by
      rw [hsm, map_smul]
      rfl
    have e2' : (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M (r ⊗ₜ m)).val.1)
        = r • (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M
              (1 ⊗ₜ m)).val.1) :=
      (congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e2).trans
        (resHom_smul_rel' C R _ _ _)
    refine ((congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e1).trans
      (resHom_smul_rel' C R _ _ _)).trans ?_
    refine (congrArg (r • ·) hone).trans ?_
    refine Eq.trans ?_ (congrArg (windowShiftTheta₀ C π hπ g R a * ·) e2'.symm)
    rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]

set_option maxHeartbeats 1000000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
/-- **DDR-9.0 keystone (compat), chart 1** (mirror of
`relThetaWindowEquiv_sectionMul_fst`). -/
theorem relThetaWindowEquiv_sectionMul_snd
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    (hH1M : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g))).H1)
    (hH1MS : Subsingleton (relTwistPair C k π
      (relThetaCocycle C k π (windowM_choice π hπ g + windowS_choice π hπ g))).H1)
    (x : R ⊗[k] ↥(divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R π (windowM_choice π hπ g + windowS_choice π hπ g)
          hH1MS (LinearMap.baseChange R (windowShiftMul hπ g a) x)).val.2)
      = windowShiftTheta₁ C π hπ g R a
        * (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M x).val.2) := by
  induction x with
  | zero => simp only [map_zero, Submodule.coe_zero, Prod.snd_zero, mul_zero]
  | add x y hx hy =>
    have h2 : (relThetaWindowEquiv C R π
          (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
          (LinearMap.baseChange R (windowShiftMul hπ g a) x
            + LinearMap.baseChange R (windowShiftMul hπ g a) y)).val.2
        = (relThetaWindowEquiv C R π
            (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
            (LinearMap.baseChange R (windowShiftMul hπ g a) x)).val.2
          + (relThetaWindowEquiv C R π
              (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
              (LinearMap.baseChange R (windowShiftMul hπ g a) y)).val.2 := by
      rw [map_add]
      rfl
    have h3 : (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M (x + y)).val.2
        = (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M x).val.2
          + (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M y).val.2 := by
      rw [map_add]
      rfl
    rw [map_add, h2, map_add, hx, hy, h3, map_add, mul_add]
  | tmul r m =>
    have hone : (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R π (windowM_choice π hπ g + windowS_choice π hπ g)
          hH1MS (1 ⊗ₜ (windowShiftMul hπ g a m))).val.2)
        = windowShiftTheta₁ C π hπ g R a
          * (relCurve C R).resHom (le_inf le_top le_rfl)
              ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M
                (1 ⊗ₜ m)).val.2) :=
      ((resHom_relThetaWindowEquiv_one_tmul_snd C π R
          (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
          (windowShiftMul hπ g a m)).trans
        ((congrArg (relSectionsMap C k R (fiberTwoCover π).V₁)
            (resHom_relThetaFieldSection_windowShiftMul_snd C π hπ g a m)).trans
          (map_mul (relSectionsMap C k R (fiberTwoCover π).V₁) _ _))).trans
        (congrArg (windowShiftTheta₁ C π hπ g R a * ·)
          (resHom_relThetaWindowEquiv_one_tmul_snd C π R
            (windowM_choice π hπ g) hH1M m).symm)
    have hbc : LinearMap.baseChange R (windowShiftMul hπ g a) (r ⊗ₜ m)
        = r • ((1 : R) ⊗ₜ (windowShiftMul hπ g a m)) := by
      rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hsm : (r ⊗ₜ m : R ⊗[k] ↥(divisorSections k
        (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) = r • ((1 : R) ⊗ₜ m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e1 : (relThetaWindowEquiv C R π
          (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
          (LinearMap.baseChange R (windowShiftMul hπ g a) (r ⊗ₜ m))).val.2
        = r • (relThetaWindowEquiv C R π
            (windowM_choice π hπ g + windowS_choice π hπ g) hH1MS
            (1 ⊗ₜ (windowShiftMul hπ g a m))).val.2 := by
      rw [hbc, map_smul]
      rfl
    have e2 : (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M (r ⊗ₜ m)).val.2
        = r • (relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M
            (1 ⊗ₜ m)).val.2 := by
      rw [hsm, map_smul]
      rfl
    have e2' : (relCurve C R).resHom (le_inf le_top le_rfl)
        ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M (r ⊗ₜ m)).val.2)
        = r • (relCurve C R).resHom (le_inf le_top le_rfl)
            ((relThetaWindowEquiv C R π (windowM_choice π hπ g) hH1M
              (1 ⊗ₜ m)).val.2) :=
      (congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e2).trans
        (resHom_smul_rel' C R _ _ _)
    refine ((congrArg ((relCurve C R).resHom (le_inf le_top le_rfl)) e1).trans
      (resHom_smul_rel' C R _ _ _)).trans ?_
    refine (congrArg (r • ·) hone).trans ?_
    refine Eq.trans ?_ (congrArg (windowShiftTheta₁ C π hπ g R a * ·) e2'.symm)
    rw [Scheme.overModule_smul_def, Scheme.overModule_smul_def, mul_left_comm]

end SectionMul

/-! ## KEYSTONE 2 — DDR-9.0, the carve discharge -/

section Carve

variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) (g : ℕ)
variable (R : Type u) [CommRing R] [Algebra k R]

/-- (Implementation) Germs commute with `resHom`. -/
private lemma germ_resHom_rel {X : Scheme.{u}} {W V : X.Opens} (h : W ≤ V) (z : X)
    (hz : z ∈ W) (t : Γ(X, V)) :
    (X.presheaf.germ W z hz).hom (X.resHom h t)
      = (X.presheaf.germ V z (h hz)).hom t :=
  X.presheaf.germ_res_apply (homOfLE h) z hz t

set_option maxHeartbeats 800000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- Multiplication by a section of the shift window preserves vanishing along arbitrary
local equations.  This is the certificate-free membership core of `divFamEps_carve`. -/
theorem windowShiftMul_mem_divisorWindow
    (d : (relCurve C R).LocalEquations)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤))
    {x : R ⊗[k] ↥(divisorSections k
      (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)}
    (hx : x ∈ divisorWindow d (relThetaPairH1_windowM C π hπ g)) :
    LinearMap.baseChange R (windowShiftMul hπ g a) x ∈
      divisorWindow d (relThetaPairH1_windowMS C π hπ g) := by
  have hmem := (Scheme.LocalEquations.mem_vanishingSubmodule_iff R).mp
    (mem_divisorWindow_iff.mp hx)
  rw [mem_divisorWindow_iff]
  refine (Scheme.LocalEquations.mem_vanishingSubmodule_iff R).mpr
    ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hkey := relThetaWindowEquiv_sectionMul_fst C π hπ g R a
      (relThetaPairH1_windowM C π hπ g) (relThetaPairH1_windowMS C π hπ g) x
    have heq := germ_resHom_rel (le_inf le_top le_rfl) z hz.2
      ((relThetaWindowEquiv C R π (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g)
        (LinearMap.baseChange R (windowShiftMul hπ g a) x)).val.1)
    rw [← heq, hkey, map_mul]
    refine Ideal.mul_mem_left _ _ ?_
    rw [germ_resHom_rel (le_inf le_top le_rfl) z hz.2]
    exact hmem.1 z hz
  · have hkey := relThetaWindowEquiv_sectionMul_snd C π hπ g R a
      (relThetaPairH1_windowM C π hπ g) (relThetaPairH1_windowMS C π hπ g) x
    have heq := germ_resHom_rel (le_inf le_top le_rfl) z hz.2
      ((relThetaWindowEquiv C R π (windowM_choice π hπ g + windowS_choice π hπ g)
        (relThetaPairH1_windowMS C π hπ g)
        (LinearMap.baseChange R (windowShiftMul hπ g a) x)).val.2)
    rw [← heq, hkey, map_mul]
    refine Ideal.mul_mem_left _ _ ?_
    rw [germ_resHom_rel (le_inf le_top le_rfl) z hz.2]
    exact hmem.2 z hz

set_option maxHeartbeats 800000 in
-- Mixed `relCurve`/twist spellings force heavy defeq checks (`respectTransparency false`).
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
/-- **DDR-9.0 — the carve discharge** (`informal/w4-ddr9-worksheet.md` §2.0, the brick no
scoreboard carried): the ε-pair of ANY certified divisor family over ANY affine test
ring satisfies the carve `(♦)` — `carvePairArrow (windowShiftMul hπ g a) ε₁ ε₂ = 0` for
every multiplier section `a ∈ H⁰(𝒪(s·F))`.  Route: membership only.  The carve arrow
vanishes iff the multiplier maps `ε₁ = K_M(d)` into `ε₂ = K_{M+s}(d)`
(`carvePairArrow_eq_zero_iff`); membership in the windows is germ-vanishing along `d`
(`mem_divisorWindow_iff`), the multiplied window image is the componentwise product of a
fixed theta section with the original image (`relThetaWindowEquiv_sectionMul_fst/_snd`),
and the stalk ideal absorbs the extra factor by `Ideal.mul_mem_left`. -/
theorem divFamEps_carve (G : CertifiedDivisorFamily C R π g)
    (a : ↥(divisorSections k (windowS_choice π hπ g • fiberWeilDivisor π) ⊤)) :
    Grassmannian.carvePairArrow (windowShiftMul hπ g a)
      (divFamEps hπ g (DivFam.mk G)).1 (divFamEps hπ g (DivFam.mk G)).2 = 0 := by
  rw [Grassmannian.carvePairArrow_eq_zero_iff]
  intro x hx
  rw [divFamEps_mk] at hx ⊢
  exact windowShiftMul_mem_divisorWindow C π hπ g R G.eqns a hx

end Carve

end AlgebraicGeometry
