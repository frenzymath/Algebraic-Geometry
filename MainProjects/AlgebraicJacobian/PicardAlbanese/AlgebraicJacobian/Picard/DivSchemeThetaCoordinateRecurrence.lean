/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeWindowMulGeneral
import AlgebraicJacobian.RiemannRoch.EffectiveUniqueness
import AlgebraicJacobian.RiemannRoch.SumIntersection
import AlgebraicJacobian.RiemannRoch.WindowLedger

/-!
# The two-coordinate recurrence in a field window

For `F = fiberWeilDivisor pi` and `u = fiberCoordUnit pi`, the two sections
`1` and `u⁻¹` of `O(F)` generate every sufficiently large window:

`H⁰(O((m + 1)F)) = H⁰(O(mF)) + u⁻¹ H⁰(O(mF))`.

The proof is the divisor-section form of the standard two-chart argument.  The
two shifted divisors are `mF` and `mF - div(u⁻¹)`; their supremum is
`(m + 1)F`, while the degree of their infimum is `(m - 1) deg(F)`.  Thus the
four `H¹` hypotheses needed by `divisorSections_sup` are discharged by the
window ledger as soon as `windowS ≤ m`.

The final pair theorem records the same recurrence through the existing field
theta presentation `thetaSectionPair`.  It is intentionally stated over a
field curve; residue-field specialisations can instantiate it without any
relative nilpotent-base assertion.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxRecDepth 6000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

section CoordinateRecurrence

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (pi : C.left ⟶ P1 k) [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftThetaCoordinateRecurrence :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

local notation "F" => fiberWeilDivisor pi
local notation "u" => fiberCoordUnit pi
local notation "H" n => ↥(divisorSections k (n • F) ⊤)

/-! ## Small coefficient helpers -/

private lemma coeffAt_nsmul (n : Nat) (D : C.left.CurveDivisor) {x : C.left}
    (hx : x ≠ genericPoint C.left) :
    coeffAt hx (n • D) = (n : Int) * coeffAt hx D := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, CurveDivisor.coeffAt_add, ih, Nat.cast_succ]
      ring

private lemma coeffAt_divOf_inv (v : C.left.functionFieldˣ) {x : C.left}
    (hx : x ≠ genericPoint C.left) :
    coeffAt hx (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) v⁻¹) =
      -coeffAt hx (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) v) := by
  have h : Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) v⁻¹ +
      Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) v = 0 := by
    rw [← Scheme.divOf_mul, inv_mul_cancel, Scheme.divOf_one]
  have hc := congrArg (coeffAt hx) h
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_zero] at hc
  linarith

/-! ## The two canonical field-window generators -/

/-- The field-window representative of `(t₀, 1)`. -/
noncomputable def thetaCoordinateFstOne
    (_hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) : H 1 :=
  ⟨1, by
    simpa only [one_smul] using
      (one_mem_divisorSections_top k (fiberWeilDivisor_nonneg pi))⟩

private theorem fiberCoordUnit_inv_mem_divisorSections :
    (((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField)) ∈
      divisorSections k (1 • F) ⊤ := by
  let v : C.left.functionFieldˣ := u⁻¹
  change (v : C.left.functionField) ∈ divisorSections k (1 • F) ⊤
  rw [mem_divisorSections_top_iff k (Units.ne_zero v)]
  refine CurveDivisor.le_iff_coeffAt.mpr (fun x hx => ?_)
  have hmk : Units.mk0 (v : C.left.functionField) (Units.ne_zero v) = v :=
    Units.ext rfl
  rw [CurveDivisor.coeffAt_zero, hmk, CurveDivisor.coeffAt_add, coeffAt_nsmul,
    fiberWeilDivisor_coeffAt pi, coeffAt_divOf_inv]
  have hleft : coeffAt hx
      (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) ≤
      max (coeffAt hx (Scheme.divOf
        (C.left ↘ Spec (CommRingCat.of k)) u)) 0 := le_max_left _ _
  norm_num

/-- The field-window representative of `(1, t₁)`: the inverse of the fibre unit. -/
noncomputable def thetaCoordinateSndOne
    (_hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k)) : H 1 :=
  ⟨((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField),
    fiberCoordUnit_inv_mem_divisorSections (C := C) pi⟩

@[simp]
theorem thetaCoordinateFstOne_coe :
    ((thetaCoordinateFstOne (C := C) pi hpi : H 1) : C.left.functionField) = 1 := rfl

@[simp]
theorem thetaCoordinateSndOne_coe :
    ((thetaCoordinateSndOne (C := C) pi hpi : H 1) : C.left.functionField) =
      ((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField) := rfl

noncomputable def thetaCoordinateSndDivisor (m : Nat) : C.left.CurveDivisor :=
  m • F - Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) (u⁻¹)

/-! ## Divisor arithmetic behind the recurrence -/

set_option maxHeartbeats 800000 in
-- The coefficientwise max/subtraction normalization is nonlinear in the order value.
theorem thetaCoordinate_sup (m : Nat) :
    (m • F) ⊔ thetaCoordinateSndDivisor (C := C) pi m = (1 + m) • F := by
  refine CurveDivisor.ext_coeffAt (fun x hx => ?_)
  rw [CurveDivisor.coeffAt_sup, thetaCoordinateSndDivisor,
    CurveDivisor.coeffAt_sub]
  simp only [coeffAt_nsmul, fiberWeilDivisor_coeffAt, coeffAt_divOf_inv]
  by_cases hd : coeffAt hx (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) ≤ 0
  · have hmax : max (coeffAt hx (Scheme.divOf
        (C.left ↘ Spec (CommRingCat.of k)) u)) 0 = 0 := max_eq_right hd
    simp only [hmax]
    have hcomp : (m : Int) * 0 - -coeffAt hx
        (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) ≤ (m : Int) * 0 := by
      simpa using hd
    rw [max_eq_left hcomp]
    norm_num
  · have hd' : 0 ≤ coeffAt hx
        (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) :=
      le_of_lt (lt_of_not_ge hd)
    have hmax : max (coeffAt hx (Scheme.divOf
        (C.left ↘ Spec (CommRingCat.of k)) u)) 0 =
        coeffAt hx (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) :=
      max_eq_left hd'
    simp only [hmax]
    have hcomp : (m : Int) * coeffAt hx
          (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) ≤
        (m : Int) * coeffAt hx
          (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) - -
          coeffAt hx (Scheme.divOf (C.left ↘ Spec (CommRingCat.of k)) u) := by
      nlinarith [Int.natCast_nonneg m, hd']
    rw [max_eq_right hcomp]
    push_cast
    ring

theorem thetaCoordinateSndDivisor_deg (m : Nat) :
    CurveDivisor.deg k (thetaCoordinateSndDivisor (C := C) pi m) =
      (m : Int) * windowδ pi := by
  rw [thetaCoordinateSndDivisor, Scheme.CurveDivisor.deg_sub' k,
    Scheme.CurveDivisor.deg_nsmul' k, deg_fiberWeilDivisor_windowδ,
    deg_divOf k, sub_zero]

private theorem thetaCoordinate_window_h1 (g m : Nat) (hm : windowS_choice pi hpi g ≤ m) :
    (Subsingleton (Sheaf.HModule (C.left.divisorSheaf k (m • F)) 1) ∧
      Subsingleton (Sheaf.HModule
        (C.left.divisorSheaf k (thetaCoordinateSndDivisor (C := C) pi m)) 1) ∧
      Subsingleton (Sheaf.HModule
        (C.left.divisorSheaf k ((m • F) ⊓
          thetaCoordinateSndDivisor (C := C) pi m)) 1) ∧
      Subsingleton (Sheaf.HModule
        (C.left.divisorSheaf k ((m • F) ⊔
          thetaCoordinateSndDivisor (C := C) pi m)) 1)) := by
  have hδ : 0 ≤ windowδ pi := windowδ_nonneg pi
  have hS : windowBound pi hpi + 2 * (g : Int) ≤
      ((windowS_choice pi hpi g : Int) - 1) * windowδ pi :=
    windowS_spec pi hpi g
  have hm' : (windowS_choice pi hpi g : Int) ≤ (m : Int) := by
    exact_mod_cast hm
  have hb0 : windowBound pi hpi ≤ (m : Int) * windowδ pi := by
    have hs0 : (windowS_choice pi hpi g : Int) * windowδ pi ≤
        (m : Int) * windowδ pi := by
      exact mul_le_mul_of_nonneg_right hm' hδ
    have := windowBound_le_S_mul pi hpi g
    linarith
  have hb1 : windowBound pi hpi ≤
      CurveDivisor.deg k (thetaCoordinateSndDivisor (C := C) pi m) := by
    rw [thetaCoordinateSndDivisor_deg]
    exact hb0
  have hsupdeg : CurveDivisor.deg k ((m • F) ⊔
      thetaCoordinateSndDivisor (C := C) pi m) =
      ((1 + m : Nat) : Int) * windowδ pi := by
    rw [thetaCoordinate_sup, Scheme.CurveDivisor.deg_nsmul' k,
      deg_fiberWeilDivisor_windowδ]
  have hinfdeg : CurveDivisor.deg k ((m • F) ⊓
      thetaCoordinateSndDivisor (C := C) pi m) =
      ((m : Int) - 1) * windowδ pi := by
    have hbal := Scheme.CurveDivisor.deg_inf_add_deg_sup k (m • F)
      (thetaCoordinateSndDivisor (C := C) pi m)
    rw [Scheme.CurveDivisor.deg_nsmul' k, deg_fiberWeilDivisor_windowδ,
      thetaCoordinateSndDivisor_deg, hsupdeg] at hbal
    push_cast at hbal ⊢
    nlinarith [hbal]
  have hbinf : windowBound pi hpi ≤
      CurveDivisor.deg k ((m • F) ⊓
        thetaCoordinateSndDivisor (C := C) pi m) := by
    rw [hinfdeg]
    have hm1 : ((windowS_choice pi hpi g : Int) - 1) * windowδ pi ≤
        ((m : Int) - 1) * windowδ pi := by
      exact mul_le_mul_of_nonneg_right (by linarith [hm']) hδ
    linarith
  have hbsup : windowBound pi hpi ≤
      CurveDivisor.deg k ((m • F) ⊔ thetaCoordinateSndDivisor (C := C) pi m) := by
    rw [hsupdeg]
    have hmono : (m : Int) * windowδ pi ≤
        ((1 + m : Nat) : Int) * windowδ pi := by
      exact mul_le_mul_of_nonneg_right (by omega) hδ
    linarith
  exact ⟨(by
      apply windowBound_spec pi hpi _
      rw [Scheme.CurveDivisor.deg_nsmul' k, deg_fiberWeilDivisor_windowδ]
      exact hb0),
    windowBound_spec pi hpi _ hb1,
    windowBound_spec pi hpi _ hbinf,
    windowBound_spec pi hpi _ hbsup⟩

/-! ## The field-window span and elementwise recurrence -/

set_option maxHeartbeats 1000000 in
-- Rewriting both principal-divisor images and the dependent lattice supremum is expensive.
theorem thetaCoordinate_window_span (g m : Nat)
    (hm : windowS_choice pi hpi g ≤ m) :
    Submodule.map (Scheme.mulLinear k (1 : C.left.functionField))
        (divisorSections k (m • F) ⊤) ⊔
      Submodule.map (Scheme.mulLinear k
        ((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField))
        (divisorSections k (m • F) ⊤) =
      divisorSections k ((1 + m) • F) ⊤ := by
  have hwin := thetaCoordinate_window_h1 (C := C) pi hpi g m hm
  have hfst := map_mulLinear_divisorSections_top k (f := (1 : C.left.functionField))
    one_ne_zero (m • F)
  have hsnd := map_mulLinear_divisorSections_top k
    (f := ((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField))
    (Units.ne_zero (u⁻¹)) (m • F)
  have hmk1 : Units.mk0 (1 : C.left.functionField) one_ne_zero = 1 :=
    Units.ext rfl
  have hmk : Units.mk0 ((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField)
      (Units.ne_zero (u⁻¹)) = u⁻¹ := Units.ext rfl
  rw [hfst, hsnd, hmk1, Scheme.divOf_one, sub_zero, hmk]
  calc
    divisorSections k (m • F) ⊤ ⊔
        divisorSections k (thetaCoordinateSndDivisor (C := C) pi m) ⊤ =
      divisorSections k ((m • F) ⊔
        thetaCoordinateSndDivisor (C := C) pi m) ⊤ :=
      divisorSections_sup k (m • F)
        (thetaCoordinateSndDivisor (C := C) pi m)
        hwin.1 hwin.2.1 hwin.2.2.1 hwin.2.2.2
    _ = divisorSections k ((1 + m) • F) ⊤ := by
      rw [thetaCoordinate_sup]

theorem exists_thetaCoordinate_decomposition (g m : Nat)
    (hm : windowS_choice pi hpi g ≤ m) (h : H(1 + m)) :
    ∃ z₀ z₁ : H m,
      h = thetaWindowMul (C := C) (pi := pi) 1 m
          (thetaCoordinateFstOne (C := C) pi hpi) z₀ +
        thetaWindowMul (C := C) (pi := pi) 1 m
          (thetaCoordinateSndOne (C := C) pi hpi) z₁ := by
  have hspan := thetaCoordinate_window_span (C := C) pi hpi g m hm
  have hh : (h : C.left.functionField) ∈
      Submodule.map (Scheme.mulLinear k (1 : C.left.functionField))
          (divisorSections k (m • F) ⊤) ⊔
        Submodule.map (Scheme.mulLinear k
          ((u⁻¹ : C.left.functionFieldˣ) : C.left.functionField))
          (divisorSections k (m • F) ⊤) := by
    rw [hspan]
    exact h.property
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hh
  rcases ha with ⟨a, ha, rfl⟩
  rcases hb with ⟨b, hb, rfl⟩
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_add, thetaWindowMul_coe, thetaWindowMul_coe,
    thetaCoordinateFstOne_coe, thetaCoordinateSndOne_coe, one_mul]
  simpa only [Scheme.mulLinear_apply, one_mul] using hab.symm

/-! ## The same recurrence through the field theta pair -/

/-- Componentwise multiplication of field theta pairs. -/
noncomputable def thetaSectionPairMul (a b : Nat)
    (x : ↥(twistSubmodule k (fiberChart₀ pi) (fiberChart₁ pi)
      (thetaUnit pi ^ a) ⊤))
    (y : ↥(twistSubmodule k (fiberChart₀ pi) (fiberChart₁ pi)
      (thetaUnit pi ^ b) ⊤)) :
    ↥(twistSubmodule k (fiberChart₀ pi) (fiberChart₁ pi)
      (thetaUnit pi ^ (a + b)) ⊤) := by
  refine ⟨(x.1.1 * y.1.1, x.1.2 * y.1.2), ?_⟩
  rw [mem_twistSubmodule_iff]
  have hx := (mem_twistSubmodule_iff k (fiberChart₀ pi) (fiberChart₁ pi)
    (thetaUnit pi ^ a) x.1).mp x.2
  have hy := (mem_twistSubmodule_iff k (fiberChart₀ pi) (fiberChart₁ pi)
    (thetaUnit pi ^ b) y.1).mp y.2
  rw [map_mul, map_mul, pow_add, Units.val_mul, map_mul, hx, hy]
  ring

theorem thetaSectionPair_thetaWindowMul (p q : Nat)
    (a : ↥(divisorSections k (p • F) ⊤))
    (m : ↥(divisorSections k (q • F) ⊤)) :
    thetaSectionPair C pi (p + q)
        (thetaWindowMul (C := C) (pi := pi) p q a m) =
      thetaSectionPairMul (C := C) pi p q
        (thetaSectionPair C pi p a) (thetaSectionPair C pi q m) := by
  apply Subtype.ext
  apply Prod.ext
  · simpa [thetaSectionPairMul] using
      (thetaSectionPair_thetaWindowMul_fst C pi p q a m)
  · simpa [thetaSectionPairMul] using
      (thetaSectionPair_thetaWindowMul_snd C pi p q a m)

@[simp]
theorem thetaSectionPair_add (n : Nat)
    (a b : ↥(divisorSections k (n • F) ⊤)) :
    thetaSectionPair C pi n (a + b) =
      thetaSectionPair C pi n a + thetaSectionPair C pi n b := by
  simp [thetaSectionPair]

theorem exists_thetaSectionPair_coordinate_decomposition (g m : Nat)
    (hm : windowS_choice pi hpi g ≤ m) (h : H(1 + m)) :
    ∃ z₀ z₁ : H m,
      thetaSectionPair C pi (1 + m) h =
        thetaSectionPairMul (C := C) pi 1 m
          (thetaSectionPair C pi 1 (thetaCoordinateFstOne (C := C) pi hpi))
          (thetaSectionPair C pi m z₀) +
        thetaSectionPairMul (C := C) pi 1 m
          (thetaSectionPair C pi 1 (thetaCoordinateSndOne (C := C) pi hpi))
          (thetaSectionPair C pi m z₁) := by
  obtain ⟨z₀, z₁, hz⟩ := exists_thetaCoordinate_decomposition
    (C := C) pi hpi g m hm h
  refine ⟨z₀, z₁, ?_⟩
  rw [hz, thetaSectionPair_add,
    thetaSectionPair_thetaWindowMul, thetaSectionPair_thetaWindowMul]

end CoordinateRecurrence

end AlgebraicGeometry
