/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeSeedUnivAssemble
import AlgebraicJacobian.Picard.DivSchemeWindowMulGeneral

/-!
# Coherence of transported divisor windows at arbitrary exponents

The field dictionary at exponent `p` differs from the concrete theta reading by
the shift unit `u_p = thetaFieldShiftUnit C K pi p`.  Consequently products at
arbitrary exponents `p` and `q` carry the fixed coherence factor

`u_p * u_q * u_(p+q)^-1`.

This file generalizes the seed-only `(M,s)` coherence API to all exponents.  It
records the divisor of the coherence factor, its action on divisor-section
spaces, and the corresponding multiplication laws for `thetaFieldRead` and
`divFamPhi`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section Coherence

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (K : Type u) [Field K] [Algebra k K]
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftHighWindowCoherence :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))] [IsDominant pi]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

/-- Germs commute with restriction maps. -/
private lemma germ_resHom_coherence {X : Scheme.{u}} {W V : X.Opens}
    (h : W ≤ V) (z : X) (hz : z ∈ W) (t : Γ(X, V)) :
    (X.presheaf.germ W z hz).hom (X.resHom h t) =
      (X.presheaf.germ V z (h hz)).hom t :=
  X.presheaf.germ_res_apply (homOfLE h) z hz t

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- The function-field theta reading is multiplicative on an arbitrary pure
left tensor and arbitrary scalar-extended right window. -/
theorem thetaFieldRead_relThetaWindowEquiv_thetaWindowMul_general
    (p q : Nat)
    (hH1p : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi p)).H1)
    (hH1q : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (hH1pq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi (p + q))).H1)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (x : K ⊗[k] ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    thetaFieldRead C K pi (p + q)
        (relThetaWindowEquiv C K pi (p + q) hH1pq
          (LinearMap.baseChange K
            (thetaWindowMul (C := C) (pi := pi) p q a) x)) =
      thetaFieldRead C K pi p
          (relThetaWindowEquiv C K pi p hH1p (1 ⊗ₜ a)) *
        thetaFieldRead C K pi q
          (relThetaWindowEquiv C K pi q hH1q x) := by
  by_cases hη : genericPoint (relCurve C K) ∈
      (relCover C K (fiberTwoCover pi)).V₀
  · have hcomp := relThetaWindowEquiv_thetaWindowMul_fst
      C pi K p q a hH1q hH1pq x
    simp only [thetaWindowMulSectionFst] at hcomp
    rw [← resHom_relThetaWindowEquiv_one_tmul_fst C pi K p hH1p a] at hcomp
    have hg := congrArg
      ((relCurve C K).presheaf.germ
        ((relCover C K (fiberTwoCover pi)).V₀)
        (genericPoint (relCurve C K)) hη).hom hcomp
    rw [map_mul, germ_resHom_coherence (le_inf le_top le_rfl),
      germ_resHom_coherence (le_inf le_top le_rfl),
      germ_resHom_coherence (le_inf le_top le_rfl)] at hg
    rw [thetaFieldRead_eq_germ_fst C K pi _ hη,
      thetaFieldRead_eq_germ_fst C K pi _ hη,
      thetaFieldRead_eq_germ_fst C K pi _ hη]
    exact hg
  · have hη₁ : genericPoint (relCurve C K) ∈
        (relCover C K (fiberTwoCover pi)).V₁ :=
      mem_V₁_of_notMem_V₀ C K pi hη
    have hcomp := relThetaWindowEquiv_thetaWindowMul_snd
      C pi K p q a hH1q hH1pq x
    simp only [thetaWindowMulSectionSnd] at hcomp
    rw [← resHom_relThetaWindowEquiv_one_tmul_snd C pi K p hH1p a] at hcomp
    have hg := congrArg
      ((relCurve C K).presheaf.germ
        ((relCover C K (fiberTwoCover pi)).V₁)
        (genericPoint (relCurve C K)) hη₁).hom hcomp
    rw [map_mul, germ_resHom_coherence (le_inf le_top le_rfl),
      germ_resHom_coherence (le_inf le_top le_rfl),
      germ_resHom_coherence (le_inf le_top le_rfl)] at hg
    rw [thetaFieldRead_eq_germ_snd C K pi _ hη,
      thetaFieldRead_eq_germ_snd C K pi _ hη,
      thetaFieldRead_eq_germ_snd C K pi _ hη]
    exact hg

/-- The coherence unit comparing the product of transported windows at `p`
and `q` with the transported window at `p + q`. -/
noncomputable def windowAddCoherenceUnit (p q : Nat) :
    (relCurve C K).functionFieldˣ :=
  thetaFieldShiftUnit C K pi p * thetaFieldShiftUnit C K pi q *
    (thetaFieldShiftUnit C K pi (p + q))⁻¹

/-- The divisor of the arbitrary-exponent coherence unit is exactly the
failure of the chosen transported divisor representatives to be additive. -/
theorem divOf_windowAddCoherenceUnit (p q : Nat) :
    windowTransportDivisor C K pi (p + q) -
        (windowTransportDivisor C K pi p + windowTransportDivisor C K pi q) =
      Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (windowAddCoherenceUnit (pi := pi) C K p q) := by
  have hinv : Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (thetaFieldShiftUnit C K pi (p + q))⁻¹ =
      -Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (thetaFieldShiftUnit C K pi (p + q)) := by
    have h0 := Scheme.divOf_mul
      (relCurve C K ↘ Spec (CommRingCat.of K))
      (thetaFieldShiftUnit C K pi (p + q))
      (thetaFieldShiftUnit C K pi (p + q))⁻¹
    rw [mul_inv_cancel, Scheme.divOf_one] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  rw [windowAddCoherenceUnit, Scheme.divOf_mul, Scheme.divOf_mul, hinv,
    ← divOf_thetaFieldShiftUnit C K pi p,
    ← divOf_thetaFieldShiftUnit C K pi q,
    ← divOf_thetaFieldShiftUnit C K pi (p + q),
    thetaFieldDivisor_add C K pi p q]
  abel

/-- Multiplication by the coherence unit translates the transported
`(p + q)` section space to the literal sum of the transported `p` and `q`
divisors, compatibly with subtracting an auxiliary divisor. -/
theorem map_mulLinear_windowAddCoherenceUnit (p q : Nat)
    (D : (relCurve C K).CurveDivisor) :
    Submodule.map
        (Scheme.mulLinear K
          ((windowAddCoherenceUnit (pi := pi) C K p q :
            (relCurve C K).functionFieldˣ) : (relCurve C K).functionField))
        (Scheme.divisorSections K
          (windowTransportDivisor C K pi (p + q) - D) ⊤) =
      Scheme.divisorSections K
        (windowTransportDivisor C K pi p +
          windowTransportDivisor C K pi q - D) ⊤ := by
  rw [map_mulLinear_divisorSections_top K
    (Units.ne_zero (windowAddCoherenceUnit (pi := pi) C K p q)) _]
  congr 1
  rw [show Units.mk0 _
      (Units.ne_zero (windowAddCoherenceUnit (pi := pi) C K p q)) =
      windowAddCoherenceUnit (pi := pi) C K p q from Units.ext rfl,
    ← divOf_windowAddCoherenceUnit (pi := pi) C K p q]
  abel

/-- Top-window form of `map_mulLinear_windowAddCoherenceUnit`. -/
theorem map_mulLinear_windowAddCoherenceUnit_top (p q : Nat) :
    Submodule.map
        (Scheme.mulLinear K
          ((windowAddCoherenceUnit (pi := pi) C K p q :
            (relCurve C K).functionFieldˣ) : (relCurve C K).functionField))
        (Scheme.divisorSections K
          (windowTransportDivisor C K pi (p + q)) ⊤) =
      Scheme.divisorSections K
        (windowTransportDivisor C K pi p +
          windowTransportDivisor C K pi q) ⊤ := by
  have h := map_mulLinear_windowAddCoherenceUnit (pi := pi) C K p q 0
  rwa [sub_zero, sub_zero] at h

/-- General `Phi` product law.  A pure `p`-window multiplier times an
arbitrary scalar-extended `q`-window value is the coherence unit times the
`(p + q)`-window value of the multiplied tensor. -/
theorem divFamPhi_one_tmul_mul_general
    (p q : Nat)
    (hH1p : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi p)).H1)
    (hH1q : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (hH1pq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi (p + q))).H1)
    (a : ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤))
    (x : K ⊗[k] ↥(divisorSections k (q • fiberWeilDivisor pi) ⊤)) :
    divFamPhi C K pi p hH1p (1 ⊗ₜ a) * divFamPhi C K pi q hH1q x =
      ((windowAddCoherenceUnit (pi := pi) C K p q :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
        divFamPhi C K pi (p + q) hH1pq
          (LinearMap.baseChange K
            (thetaWindowMul (C := C) (pi := pi) p q a) x) := by
  have hphi : ∀ (e : Nat)
      (hH1 : Subsingleton (relTwistPair C k pi
        (relThetaCocycle C k pi e)).H1)
      (y : K ⊗[k] ↥(divisorSections k (e • fiberWeilDivisor pi) ⊤)),
      divFamPhi C K pi e hH1 y =
        ((thetaFieldShiftUnit C K pi e :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
          thetaFieldRead C K pi e
            (relThetaWindowEquiv C K pi e hH1 y) :=
    fun _ _ _ => rfl
  rw [hphi, hphi, hphi,
    thetaFieldRead_relThetaWindowEquiv_thetaWindowMul_general
      C K p q hH1p hH1q hH1pq a x,
    windowAddCoherenceUnit, Units.val_mul, Units.val_mul]
  rw [Units.val_inv_eq_inv_val]
  have hne : ((thetaFieldShiftUnit C K pi (p + q) :
      (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) ≠ 0 :=
    Units.ne_zero _
  field_simp

end Coherence

end AlgebraicGeometry
