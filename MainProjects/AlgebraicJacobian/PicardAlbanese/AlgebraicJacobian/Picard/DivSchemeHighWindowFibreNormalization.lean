/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeHighWindowCoherence
import AlgebraicJacobian.Picard.DivSchemeHighWindowMulCompatibility
import AlgebraicJacobian.Picard.DivSchemeSeedUnivRes

/-!
# Residue-field normalization of the universal high-window ambients

At a field-valued point of a carve chart, cancelling the two-step scalar
extension identifies the relative high-window ambient with the scalar-extended
base-field window.  The `divFamPhi` dictionary then identifies that window with
the transported divisor-section space.

This file records the comparison uniformly at every exponent `M + n*S`.  It
also translates a successor window to the literal sum of the multiplier and
predecessor transported divisors.  The translation is valid after subtracting
an arbitrary divisor, and the resulting normalized successor read commutes
with multiplication.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

section HighWindowFibreNormalization

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftHighWindowFibreNormalization :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j
local notation "HS" => ↥( Scheme.divisorSections k
  (windowS_choice pi hpi g • fiberWeilDivisor pi) ⊤)
local notation "HW[" n "]" => divUniversalHighWindowSections
  (C := C) (pi := pi) hpi g n
local notation "Amb[" n "]" => divUniversalHighWindowAmbient
  (C := C) (pi := pi) (hpi := hpi) (g := g)
    (r1 := r1) (r2 := r2) (b1 := b1) (b2 := b2) (i := i) (j := j) n
local notation "exp[" n "]" => divUniversalHighWindowExponent
  (C := C) (pi := pi) hpi g n

variable (K : Type u) [Field K] [Algebra k K]
  [Algebra (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j) K]
  [IsScalarTower k (DivCarveChartRing k
    (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j) K]

noncomputable local instance instIsIntegralRelCurveHighWindowFibreNormalization :
    IsIntegral (relCurve C K) := instIsIntegralBaseChange C K

noncomputable local instance instSmoothRelCurveHighWindowFibreNormalization :
    SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instSmoothOfRelativeDimensionBaseChange C K

noncomputable local instance instQCRelCurveHighWindowFibreNormalization :
    QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  instQuasiCompactBaseChange C K

noncomputable local instance instLFTRelCurveHighWindowFibreNormalization :
    LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K)) :=
  haveI : Smooth (relCurve C K ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth 1 _
  inferInstance

/-! ## Cancelling and reading a high-window ambient -/

set_option maxHeartbeats 1200000 in
/-- Cancel the two-step extension `K ⊗[RZ] (RZ ⊗[k] H_n)` at an
arbitrary high-window stage. -/
noncomputable def divUniversalHighWindowAmbientCancelEquiv (n : Nat) :
    K ⊗[RZ] (RZ ⊗[k] HW[n]) ≃ₗ[K] K ⊗[k] HW[n] :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange k RZ K K HW[n]

set_option maxHeartbeats 1200000 in
/-- Cancellation is natural for a base-changed map on the window leg. -/
theorem divUniversalHighWindowAmbientCancelEquiv_baseChange
    {H1 H2 : Type u} [AddCommGroup H1] [Module k H1]
    [AddCommGroup H2] [Module k H2] (f : H1 →ₗ[k] H2)
    (x : K ⊗[RZ] (RZ ⊗[k] H1)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange k RZ K K H2
        (LinearMap.baseChange K (LinearMap.baseChange RZ f) x) =
      LinearMap.baseChange K f
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k RZ K K H1 x) := by
  exact (LinearMap.congr_fun
    (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
      k RZ K f) x).symm

set_option maxHeartbeats 1600000 in
/-- Named-wrapper specialization of cancellation naturality for one campaign
successor multiplication map. -/
theorem divUniversalHighWindowAmbientCancelEquiv_shiftMul
    (n : Nat) (a : HS) (x : K ⊗[RZ] Amb[n]) :
    divUniversalHighWindowAmbientCancelEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowShiftMul
              (C := C) (pi := pi) hpi g n a)) x) =
      LinearMap.baseChange K
        (divUniversalHighWindowShiftMul
          (C := C) (pi := pi) hpi g n a)
        (divUniversalHighWindowAmbientCancelEquiv (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j K n x) := by
  simpa only [divUniversalHighWindowAmbientCancelEquiv] using
    (divUniversalHighWindowAmbientCancelEquiv_baseChange
      (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K
      (divUniversalHighWindowShiftMul
        (C := C) (pi := pi) hpi g n a) x)

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 600000 in
/-- The `Phi` dictionary as an equivalence from the scalar-extended `n`-th
high window to the corresponding transported divisor-section space. -/
noncomputable def divUniversalHighWindowPhiEquiv (n : Nat) :
    K ⊗[k] HW[n] ≃ₗ[K]
      ↥(Scheme.divisorSections K (windowTransportDivisor C K pi exp[n]) ⊤) := by
  let f := (divFamPhi C K pi exp[n]
      (relThetaPairH1_windowM_add_mulS C pi hpi g n)).codRestrict
      (Scheme.divisorSections K (windowTransportDivisor C K pi exp[n]) ⊤)
      (fun x => divFamPhi_apply_mem C K pi exp[n]
        (relThetaPairH1_windowM_add_mulS C pi hpi g n) x)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply divFamPhi_injective C K pi exp[n]
      (relThetaPairH1_windowM_add_mulS C pi hpi g n)
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := exists_divFamPhi_eq C K pi exp[n]
      (relThetaPairH1_windowM_add_mulS C pi hpi g n) y.property
    exact ⟨x, Subtype.ext hx⟩

@[simp]
theorem divUniversalHighWindowPhiEquiv_apply (n : Nat) (x : K ⊗[k] HW[n]) :
    (divUniversalHighWindowPhiEquiv (C := C) (pi := pi)
        hpi g K n x : (relCurve C K).functionField) =
      divFamPhi C K pi exp[n]
        (relThetaPairH1_windowM_add_mulS C pi hpi g n) x :=
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 700000 in
/-- The normalized residue-field comparison for the complete ambient at every
high-window stage. -/
noncomputable def divUniversalHighWindowAmbientFibreEquiv (n : Nat) :
    K ⊗[RZ] Amb[n] ≃ₗ[K]
      ↥(Scheme.divisorSections K (windowTransportDivisor C K pi exp[n]) ⊤) :=
  (divUniversalHighWindowAmbientCancelEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j K n).trans
    (divUniversalHighWindowPhiEquiv (C := C) (pi := pi) hpi g K n)

set_option maxHeartbeats 1200000 in
/-- The ambient fibre equivalence is `Phi` after cancelling the two-step
scalar extension. -/
@[simp]
theorem divUniversalHighWindowAmbientFibreEquiv_apply
    (n : Nat) (x : K ⊗[RZ] Amb[n]) :
    (divUniversalHighWindowAmbientFibreEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j K n x : (relCurve C K).functionField) =
      divFamPhi C K pi exp[n]
        (relThetaPairH1_windowM_add_mulS C pi hpi g n)
        (divUniversalHighWindowAmbientCancelEquiv (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j K n x) :=
  rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
@[simp]
theorem divUniversalHighWindowAmbientFibreEquiv_one_tmul (n : Nat) (x : Amb[n]) :
    (divUniversalHighWindowAmbientFibreEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j K n (1 ⊗ₜ[RZ] x) :
        (relCurve C K).functionField) =
      divFamPhi C K pi exp[n]
        (relThetaPairH1_windowM_add_mulS C pi hpi g n)
        (windowCompare RZ K x) := by
  rw [windowCompare_eq_cancelBaseChange (k := k) (H := HW[n]) RZ K x]
  rw [divUniversalHighWindowAmbientFibreEquiv, LinearEquiv.trans_apply,
    divUniversalHighWindowPhiEquiv_apply]
  rfl

/-! ## Coherence normalization with an arbitrary divisor -/

set_option maxHeartbeats 1200000 in
/-- Multiplication by the arbitrary-exponent coherence unit as an equivalence
of divisor-section spaces.  The auxiliary subtracted divisor is unrestricted. -/
noncomputable def windowAddCoherenceDivisorEquiv (p q : Nat)
    (D : (relCurve C K).CurveDivisor) :
    ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi (p + q) - D) ⊤) ≃ₗ[K]
      ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi p +
          windowTransportDivisor C K pi q - D) ⊤) := by
  let source := Scheme.divisorSections K
    (windowTransportDivisor C K pi (p + q) - D) ⊤
  let target := Scheme.divisorSections K
    (windowTransportDivisor C K pi p +
      windowTransportDivisor C K pi q - D) ⊤
  let mul := Scheme.mulLinear K
    ((windowAddCoherenceUnit (pi := pi) C K p q :
      (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)
  let f := (mul.comp source.subtype).codRestrict target (fun x => by
    have hx : mul x ∈ Submodule.map mul source :=
      Submodule.mem_map_of_mem x.property
    rw [map_mulLinear_windowAddCoherenceUnit (pi := pi) C K p q D] at hx
    exact hx)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀
      (Units.ne_zero (windowAddCoherenceUnit (pi := pi) C K p q))
    exact congrArg Subtype.val hxy
  · intro y
    have hy : (y : (relCurve C K).functionField) ∈ Submodule.map mul source := by
      rw [map_mulLinear_windowAddCoherenceUnit (pi := pi) C K p q D]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp]
theorem windowAddCoherenceDivisorEquiv_apply (p q : Nat)
    (D : (relCurve C K).CurveDivisor)
    (x : ↥(Scheme.divisorSections K
      (windowTransportDivisor C K pi (p + q) - D) ⊤)) :
    (windowAddCoherenceDivisorEquiv (pi := pi) C K p q D x :
        (relCurve C K).functionField) =
      ((windowAddCoherenceUnit (pi := pi) C K p q :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) * x :=
  rfl

/-- The top-window specialization used to normalize a successor ambient. -/
noncomputable def windowAddCoherenceTopEquiv (p q : Nat) :
    ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi (p + q)) ⊤) ≃ₗ[K]
      ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi p +
          windowTransportDivisor C K pi q) ⊤) := by
  let E := windowAddCoherenceDivisorEquiv (pi := pi) C K p q 0
  rw [sub_zero, sub_zero] at E
  exact E

/-! ## Closed normalization to `N + n*S` -/

/-- The closed coherence unit comparing the transported window at `M+n*S`
with the literal divisor `N+n*S`. -/
noncomputable def divUniversalHighWindowClosedCoherenceUnit (n : Nat) :
    (relCurve C K).functionFieldˣ :=
  thetaFieldShiftUnit C K pi (windowM_choice pi hpi g) *
    thetaFieldShiftUnit C K pi (windowS_choice pi hpi g) ^ n *
      (thetaFieldShiftUnit C K pi exp[n])⁻¹

/-- The closed units satisfy the successor recurrence through the binary
coherence unit. -/
theorem divUniversalHighWindowClosedCoherenceUnit_succ (n : Nat) :
    divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K (n + 1) =
      divUniversalHighWindowClosedCoherenceUnit
          (C := C) (pi := pi) hpi g K n *
        windowAddCoherenceUnit (pi := pi) C K
          (windowS_choice pi hpi g) exp[n] := by
  rw [divUniversalHighWindowClosedCoherenceUnit,
    divUniversalHighWindowClosedCoherenceUnit, windowAddCoherenceUnit,
    pow_succ]
  simp only [divUniversalHighWindowExponent]
  have hexp : windowM_choice pi hpi g + (n + 1) * windowS_choice pi hpi g =
      windowS_choice pi hpi g +
        (windowM_choice pi hpi g + n * windowS_choice pi hpi g) := by
    rw [Nat.succ_mul]
    omega
  rw [hexp]
  let uM := thetaFieldShiftUnit C K pi (windowM_choice pi hpi g)
  let uS := thetaFieldShiftUnit C K pi (windowS_choice pi hpi g)
  let un := thetaFieldShiftUnit C K pi
    (windowM_choice pi hpi g + n * windowS_choice pi hpi g)
  let un1 := thetaFieldShiftUnit C K pi
    (windowS_choice pi hpi g +
      (windowM_choice pi hpi g + n * windowS_choice pi hpi g))
  change uM * (uS ^ n * uS) * un1⁻¹ =
    uM * uS ^ n * un⁻¹ * (uS * un * un1⁻¹)
  calc
    _ = uM * uS ^ n * uS * (un⁻¹ * un) * un1⁻¹ := by
      rw [inv_mul_cancel, mul_one]
      ac_rfl
    _ = _ := by ac_rfl

/-- At stage one, the closed unit is the seed `(M,S)` coherence unit. -/
theorem divUniversalHighWindowClosedCoherenceUnit_one :
    divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K 1 =
      msCoherenceUnit C K hpi g := by
  rw [divUniversalHighWindowClosedCoherenceUnit, msCoherenceUnit]
  simp only [pow_one, divUniversalHighWindowExponent, one_mul]
  rw [mul_comm (thetaFieldShiftUnit C K pi (windowM_choice pi hpi g))
    (thetaFieldShiftUnit C K pi (windowS_choice pi hpi g))]

set_option maxHeartbeats 1600000 in
/-- The divisor of the closed unit is precisely the discrepancy between the
transported exponent window and `N+n*S`. -/
theorem divOf_divUniversalHighWindowClosedCoherenceUnit (n : Nat) :
    windowTransportDivisor C K pi exp[n] -
        (windowN C K hpi g + n • windowS C K hpi g) =
      Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
        (divUniversalHighWindowClosedCoherenceUnit
          (C := C) (pi := pi) hpi g K n) := by
  induction n with
  | zero =>
      rw [divUniversalHighWindowClosedCoherenceUnit]
      simp only [divUniversalHighWindowExponent, zero_mul, add_zero,
        zero_nsmul, pow_zero, mul_one, mul_inv_cancel, Scheme.divOf_one,
        show windowTransportDivisor C K pi (windowM_choice pi hpi g) =
          windowN C K hpi g from rfl]
      exact sub_self _
  | succ n ih =>
      rw [divUniversalHighWindowClosedCoherenceUnit_succ,
        Scheme.divOf_mul, ← ih,
        ← divOf_windowAddCoherenceUnit (pi := pi) C K
          (windowS_choice pi hpi g) exp[n],
        divUniversalHighWindowExponent_succ
          (C := C) (pi := pi) hpi g n]
      change windowTransportDivisor C K pi exp[n + 1] -
          (windowN C K hpi g + (n + 1) • windowS C K hpi g) =
        (windowTransportDivisor C K pi exp[n] -
          (windowN C K hpi g + n • windowS C K hpi g)) +
        (windowTransportDivisor C K pi exp[n + 1] -
          (windowS C K hpi g + windowTransportDivisor C K pi exp[n]))
      rw [succ_nsmul]
      abel

set_option maxHeartbeats 1600000 in
/-- Multiplication by the closed unit translates every transported
`M+n*S` section space to the literal `N+n*S` space, after subtracting an
arbitrary divisor. -/
theorem map_mulLinear_divUniversalHighWindowClosedCoherenceUnit (n : Nat)
    (D : (relCurve C K).CurveDivisor) :
    Submodule.map
        (Scheme.mulLinear K
          ((divUniversalHighWindowClosedCoherenceUnit
            (C := C) (pi := pi) hpi g K n :
              (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField))
        (Scheme.divisorSections K
          (windowTransportDivisor C K pi exp[n] - D) ⊤) =
      Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g - D) ⊤ := by
  rw [map_mulLinear_divisorSections_top K
    (Units.ne_zero (divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n)) _]
  congr 1
  rw [show Units.mk0 _
      (Units.ne_zero (divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K n)) =
      divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K n from Units.ext rfl,
    ← divOf_divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n]
  abel

/-- Top-window form of the closed-unit translation. -/
theorem map_mulLinear_divUniversalHighWindowClosedCoherenceUnit_top (n : Nat) :
    Submodule.map
        (Scheme.mulLinear K
          ((divUniversalHighWindowClosedCoherenceUnit
            (C := C) (pi := pi) hpi g K n :
              (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField))
        (Scheme.divisorSections K
          (windowTransportDivisor C K pi exp[n]) ⊤) =
      Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤ := by
  have h := map_mulLinear_divUniversalHighWindowClosedCoherenceUnit
    (C := C) (pi := pi) hpi g K n 0
  rwa [sub_zero, sub_zero] at h

set_option maxHeartbeats 2000000 in
/-- Arbitrary-divisor closed normalization as a linear equivalence. -/
noncomputable def divUniversalHighWindowClosedCoherenceDivisorEquiv (n : Nat)
    (D : (relCurve C K).CurveDivisor) :
    ↥(Scheme.divisorSections K
      (windowTransportDivisor C K pi exp[n] - D) ⊤) ≃ₗ[K]
    ↥(Scheme.divisorSections K
      (windowN C K hpi g + n • windowS C K hpi g - D) ⊤) := by
  let source := Scheme.divisorSections K
    (windowTransportDivisor C K pi exp[n] - D) ⊤
  let target := Scheme.divisorSections K
    (windowN C K hpi g + n • windowS C K hpi g - D) ⊤
  let mul := Scheme.mulLinear K
    ((divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)
  let f := (mul.comp source.subtype).codRestrict target (fun x => by
    have hx : mul x ∈ Submodule.map mul source :=
      Submodule.mem_map_of_mem x.property
    rw [map_mulLinear_divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n D] at hx
    exact hx)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀
      (Units.ne_zero (divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K n))
    exact congrArg Subtype.val hxy
  · intro y
    have hy : (y : (relCurve C K).functionField) ∈ Submodule.map mul source := by
      rw [map_mulLinear_divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K n D]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp]
theorem divUniversalHighWindowClosedCoherenceDivisorEquiv_apply (n : Nat)
    (D : (relCurve C K).CurveDivisor)
    (x : ↥(Scheme.divisorSections K
      (windowTransportDivisor C K pi exp[n] - D) ⊤)) :
    (divUniversalHighWindowClosedCoherenceDivisorEquiv
        (C := C) (pi := pi) hpi g K n D x :
      (relCurve C K).functionField) =
    ((divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) * x :=
  rfl

set_option maxHeartbeats 1200000 in
/-- Top-window closed normalization. -/
noncomputable def divUniversalHighWindowClosedCoherenceTopEquiv (n : Nat) :
    ↥(Scheme.divisorSections K
      (windowTransportDivisor C K pi exp[n]) ⊤) ≃ₗ[K]
    ↥(Scheme.divisorSections K
      (windowN C K hpi g + n • windowS C K hpi g) ⊤) := by
  let source := Scheme.divisorSections K
    (windowTransportDivisor C K pi exp[n]) ⊤
  let target := Scheme.divisorSections K
    (windowN C K hpi g + n • windowS C K hpi g) ⊤
  let mul := Scheme.mulLinear K
    ((divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField)
  let f := (mul.comp source.subtype).codRestrict target (fun x => by
    have hx : mul x ∈ Submodule.map mul source :=
      Submodule.mem_map_of_mem x.property
    rw [map_mulLinear_divUniversalHighWindowClosedCoherenceUnit_top
      (C := C) (pi := pi) hpi g K n] at hx
    exact hx)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀
      (Units.ne_zero (divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K n))
    exact congrArg Subtype.val hxy
  · intro y
    have hy : (y : (relCurve C K).functionField) ∈ Submodule.map mul source := by
      rw [map_mulLinear_divUniversalHighWindowClosedCoherenceUnit_top
        (C := C) (pi := pi) hpi g K n]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp]
theorem divUniversalHighWindowClosedCoherenceTopEquiv_apply (n : Nat)
    (x : ↥(Scheme.divisorSections K
      (windowTransportDivisor C K pi exp[n]) ⊤)) :
    (divUniversalHighWindowClosedCoherenceTopEquiv
        (C := C) (pi := pi) hpi g K n x :
      (relCurve C K).functionField) =
    ((divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) * x :=
  rfl

set_option maxHeartbeats 2000000 in
/-- The fully normalized high-window ambient comparison, with literal target
`H⁰(N+n*S)`. -/
noncomputable def divUniversalHighWindowClosedAmbientFibreEquiv (n : Nat) :
    K ⊗[RZ] Amb[n] ≃ₗ[K]
      ↥(Scheme.divisorSections K
        (windowN C K hpi g + n • windowS C K hpi g) ⊤) :=
  (divUniversalHighWindowAmbientFibreEquiv (C := C) (pi := pi)
    hpi g r1 r2 b1 b2 i j K n).trans
      (divUniversalHighWindowClosedCoherenceTopEquiv
        (C := C) (pi := pi) hpi g K n)

set_option maxHeartbeats 1600000 in
/-- Evaluation of the fully normalized ambient comparison. -/
@[simp]
theorem divUniversalHighWindowClosedAmbientFibreEquiv_apply
    (n : Nat) (x : K ⊗[RZ] Amb[n]) :
    (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n x :
      (relCurve C K).functionField) =
    ((divUniversalHighWindowClosedCoherenceUnit
      (C := C) (pi := pi) hpi g K n :
        (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
      divFamPhi C K pi exp[n]
        (relThetaPairH1_windowM_add_mulS C pi hpi g n)
        (divUniversalHighWindowAmbientCancelEquiv (C := C) (pi := pi)
          hpi g r1 r2 b1 b2 i j K n x) :=
  rfl

/-! ## The normalized successor multiplication square -/

/-- Reindex a transported successor section space to the sum exponent. -/
noncomputable def divUniversalHighWindowSuccessorExponentFibreEquiv (n : Nat) :
    ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi exp[n + 1]) ⊤) ≃ₗ[K]
      ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi
          (windowS_choice pi hpi g + exp[n])) ⊤) :=
  LinearEquiv.ofEq _ _ (congrArg
    (fun m : Nat => Scheme.divisorSections K
      (windowTransportDivisor C K pi m) ⊤)
    (divUniversalHighWindowExponent_succ
      (C := C) (pi := pi) hpi g n).symm)

/-- The successor ambient read normalized to the literal divisor sum
`T(S) + T(M+nS)`. -/
noncomputable def divUniversalHighWindowNormalizedSuccessorFibreEquiv (n : Nat) :
    K ⊗[RZ] Amb[n + 1] ≃ₗ[K]
      ↥(Scheme.divisorSections K
        (windowTransportDivisor C K pi (windowS_choice pi hpi g) +
          windowTransportDivisor C K pi exp[n]) ⊤) :=
  (divUniversalHighWindowAmbientFibreEquiv (C := C) (pi := pi)
      hpi g r1 r2 b1 b2 i j K (n + 1)).trans
    ((divUniversalHighWindowSuccessorExponentFibreEquiv
      (C := C) (pi := pi) hpi g K n).trans
      (windowAddCoherenceTopEquiv (pi := pi) C K
        (windowS_choice pi hpi g) exp[n]))

/-- Closed-normalization multiplication law.  The `c_(n+1)`-normalized
successor read is the multiplier read times the `c_n`-normalized predecessor
read.  This is the function-field square underlying the literal
`H⁰(N+n*S)` ambient equivalences. -/
theorem divUniversalHighWindowClosedPhi_mul
    (n : Nat)
    (hsum : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi
        (windowS_choice pi hpi g + exp[n]))).H1)
    (a : HS) (x : K ⊗[k] HW[n]) :
    ((divUniversalHighWindowClosedCoherenceUnit
        (C := C) (pi := pi) hpi g K (n + 1) :
          (relCurve C K).functionFieldˣ) : (relCurve C K).functionField) *
      divFamPhi C K pi (windowS_choice pi hpi g + exp[n]) hsum
        (LinearMap.baseChange K
          (thetaWindowMul (C := C) (pi := pi)
            (windowS_choice pi hpi g) exp[n] a) x) =
      divFamPhi C K pi (windowS_choice pi hpi g)
          (relThetaPairH1_windowS C hpi g) (1 ⊗ₜ[k] a) *
        (((divUniversalHighWindowClosedCoherenceUnit
            (C := C) (pi := pi) hpi g K n :
              (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField) *
          divFamPhi C K pi exp[n]
            (relThetaPairH1_windowM_add_mulS C pi hpi g n) x) := by
  have hprod := divFamPhi_one_tmul_mul_general (pi := pi) C K
    (windowS_choice pi hpi g) exp[n]
    (relThetaPairH1_windowS C hpi g)
    (relThetaPairH1_windowM_add_mulS C pi hpi g n) hsum a x
  rw [divUniversalHighWindowClosedCoherenceUnit_succ, Units.val_mul]
  calc
    _ = ((divUniversalHighWindowClosedCoherenceUnit
          (C := C) (pi := pi) hpi g K n :
            (relCurve C K).functionFieldˣ) :
          (relCurve C K).functionField) *
        (((windowAddCoherenceUnit (pi := pi) C K
            (windowS_choice pi hpi g) exp[n] :
              (relCurve C K).functionFieldˣ) :
            (relCurve C K).functionField) *
          divFamPhi C K pi (windowS_choice pi hpi g + exp[n]) hsum
            (LinearMap.baseChange K
              (thetaWindowMul (C := C) (pi := pi)
                (windowS_choice pi hpi g) exp[n] a) x)) := by ring
    _ = ((divUniversalHighWindowClosedCoherenceUnit
          (C := C) (pi := pi) hpi g K n :
            (relCurve C K).functionFieldˣ) :
          (relCurve C K).functionField) *
        (divFamPhi C K pi (windowS_choice pi hpi g)
          (relThetaPairH1_windowS C hpi g) (1 ⊗ₜ[k] a) *
          divFamPhi C K pi exp[n]
            (relThetaPairH1_windowM_add_mulS C pi hpi g n) x) := by rw [← hprod]
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- `Phi` is invariant under reindexing a window along an equality of
exponents.  Stating the equality with variable endpoints makes the dependent
transport of the `H¹` witnesses explicit and reusable. -/
theorem divFamPhi_baseChange_divisorWindowExponentEquiv
    {p q : Nat} (h : p = q)
    (hp : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi p)).H1)
    (hq : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi q)).H1)
    (x : K ⊗[k] ↥(divisorSections k (p • fiberWeilDivisor pi) ⊤)) :
    divFamPhi C K pi q hq
        (LinearMap.baseChange K
          (divisorWindowExponentEquiv (C := C) (pi := pi) h).toLinearMap x) =
      divFamPhi C K pi p hp x := by
  subst q
  have hH1 : hq = hp := Subsingleton.elim _ _
  rw [hH1]
  have heq :
      (divisorWindowExponentEquiv (C := C) (pi := pi)
        (rfl : p = p)).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro y
    rfl
  rw [heq, LinearMap.baseChange_id, LinearMap.id_apply]

set_option maxHeartbeats 2400000 in
/-- Reindexing the generic `(S + (M+n*S))` product window to campaign stage
`n+1` does not change its `Phi` reading. -/
theorem divFamPhi_baseChange_divUniversalHighWindowShiftMul
    (n : Nat)
    (hsum : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi
        (windowS_choice pi hpi g + exp[n]))).H1)
    (a : HS) (x : K ⊗[k] HW[n]) :
    divFamPhi C K pi exp[n + 1]
        (relThetaPairH1_windowM_add_mulS C pi hpi g (n + 1))
        (LinearMap.baseChange K
          (divUniversalHighWindowShiftMul
            (C := C) (pi := pi) hpi g n a) x) =
      divFamPhi C K pi (windowS_choice pi hpi g + exp[n]) hsum
        (LinearMap.baseChange K
          (thetaWindowMul (C := C) (pi := pi)
            (windowS_choice pi hpi g) exp[n] a) x) := by
  rw [divUniversalHighWindowShiftMul_eq, LinearMap.baseChange_comp,
    LinearMap.comp_apply]
  simpa only [divUniversalHighWindowSuccExponentEquiv] using
    (divFamPhi_baseChange_divisorWindowExponentEquiv
      (C := C) (pi := pi) K
      (divUniversalHighWindowExponent_succ
        (C := C) (pi := pi) hpi g n)
      hsum (relThetaPairH1_windowM_add_mulS C pi hpi g (n + 1))
      (LinearMap.baseChange K
        (thetaWindowMul (C := C) (pi := pi)
          (windowS_choice pi hpi g) exp[n] a) x))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- The normalized multiplication square on the actual carve-chart ambient
after residue-field base change.  This is the `hconj` seam used to transport
the recursive high-window image relation to the literal fibre windows. -/
theorem divUniversalHighWindowClosedAmbientFibreEquiv_shiftMul
    (n : Nat) (a : HS) (x : K ⊗[RZ] Amb[n]) :
    (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K (n + 1)
        (LinearMap.baseChange K
          (LinearMap.baseChange RZ
            (divUniversalHighWindowShiftMul
              (C := C) (pi := pi) hpi g n a)) x) :
      (relCurve C K).functionField) =
    (divUniversalMultiplierFibreEquiv (π := pi) C hpi g K
        (1 ⊗ₜ[k] a) : (relCurve C K).functionField) *
      (divUniversalHighWindowClosedAmbientFibreEquiv
        (C := C) (pi := pi) hpi g r1 r2 b1 b2 i j K n x :
          (relCurve C K).functionField) := by
  let hsum : Subsingleton
      (relTwistPair C k pi (relThetaCocycle C k pi
        (windowS_choice pi hpi g + exp[n]))).H1 := by
    rw [divUniversalHighWindowExponent_succ
      (C := C) (pi := pi) hpi g n]
    exact relThetaPairH1_windowM_add_mulS C pi hpi g (n + 1)
  rw [divUniversalHighWindowClosedAmbientFibreEquiv_apply,
    divUniversalMultiplierFibreEquiv_apply,
    divUniversalHighWindowClosedAmbientFibreEquiv_apply]
  rw [divUniversalHighWindowAmbientCancelEquiv_shiftMul]
  rw [divFamPhi_baseChange_divUniversalHighWindowShiftMul
    (C := C) (pi := pi) hpi g K n hsum a]
  exact divUniversalHighWindowClosedPhi_mul
    (C := C) (pi := pi) hpi g K n hsum a
      (divUniversalHighWindowAmbientCancelEquiv (C := C) (pi := pi)
        hpi g r1 r2 b1 b2 i j K n x)

end HighWindowFibreNormalization

end AlgebraicGeometry
