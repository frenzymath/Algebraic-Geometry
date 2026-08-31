/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivSchemeThetaCoordinateRecurrence
import AlgebraicJacobian.Picard.DivSchemeMulSpanMap

/-!
# Pure high-window multiplication spans

Write `F = fiberWeilDivisor pi` and `S = windowS_choice pi hpi g`.  The
two-coordinate recurrence gives

`H^0((m+1)F) = H^0(mF) + u^-1 H^0(mF)`

for `m >= S`.  Iterating this recurrence shows that every section in
`H^0((q+m)F)` is a sum of products of a section in `H^0(qF)` and a section in
`H^0(mF)`.  In particular, multiplication by the full `S`-window carries the
pure arithmetic progression `S + n*S` onto its successor.

This is the field-level normal-generation input for eventual closure of the
recursive relation readings under arbitrary pinned-chart coefficients.  It
makes no assertion over the nonreduced carve-chart ring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

section PureWindowH1

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (pi : C.left ⟶ P1 k) [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftThetaCoordinateMulSpanH1 :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- Every positive pure multiplier progression has vanishing `H^1`:
`H^1(O((S + n*S)F)) = 0`. -/
theorem window_embedding_pure_mul_iter (g n : Nat) :
    Subsingleton (Sheaf.HModule (C.left.divisorSheaf k
      ((windowS_choice pi hpi g + n * windowS_choice pi hpi g) •
        fiberWeilDivisor pi)) 1) := by
  refine windowBound_spec pi hpi _ ?_
  rw [Scheme.CurveDivisor.deg_nsmul' k, deg_fiberWeilDivisor_windowδ]
  have hS := windowBound_le_S_mul pi hpi g
  have hS0 := windowS_mul_windowδ_nonneg pi hpi g
  have hnS : 0 ≤ (n : Int) *
      ((windowS_choice pi hpi g : Int) * windowδ pi) :=
    mul_nonneg (Int.natCast_nonneg n) hS0
  calc
    windowBound pi hpi ≤
        (windowS_choice pi hpi g : Int) * windowδ pi := hS
    _ ≤ ((windowS_choice pi hpi g + n * windowS_choice pi hpi g : Nat) : Int) *
        windowδ pi := by
      push_cast
      nlinarith

/-- Relative-theta form of `window_embedding_pure_mul_iter`, supplying the
window equivalence on the pure progression `S + n*S`. -/
theorem relThetaPairH1_windowS_add_mulS (g n : Nat) :
    Subsingleton (relTwistPair C k pi (relThetaCocycle C k pi
      (windowS_choice pi hpi g + n * windowS_choice pi hpi g))).H1 :=
  subsingleton_relThetaPairH1 C pi _
    ((subsingleton_hModule_thetaTwistSheaf_one_iff k pi _).mpr
      (window_embedding_pure_mul_iter (C := C) pi hpi g n))

end PureWindowH1

section PureWindowMulSpan

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (pi : C.left ⟶ P1 k) [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftThetaCoordinateMulSpan :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

local notation "F" => fiberWeilDivisor pi
local notation "H" n => divisorSections k (n • F) ⊤

/-- Multiplying an element of `span(H_q H_m)` by a degree-one theta coordinate
lands in `span(H_(q+1) H_m)`. -/
private theorem thetaCoordinate_mul_mulSpan_mem (m q : Nat)
    (e : ↥(H 1)) (z : C.left.functionField)
    (hz : z ∈ Scheme.mulSpan k (H q) (H m)) :
    (e : C.left.functionField) * z ∈
      Scheme.mulSpan k (H(q + 1)) (H m) := by
  change z ∈ Submodule.span k
    {w : C.left.functionField | ∃ a ∈ H q, ∃ b ∈ H m, w = a * b} at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      have hea0 := mul_mem_divisorSections_top k e.property ha
      have hea : (e : C.left.functionField) * a ∈ H(q + 1) := by
        have heq : (1 • F) + (q • F) = (q + 1) • F := by
          rw [← add_nsmul]
          congr 1
          omega
        rwa [heq] at hea0
      rw [← mul_assoc]
      exact Scheme.mul_mem_mulSpan k hea hb
  | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      have hmem := (Scheme.mulSpan k (H(q + 1)) (H m)).smul_mem c hx
      convert hmem using 1
      rw [Scheme.functionFieldOverModule_smul_def,
        Scheme.functionFieldOverModule_smul_def]
      ring

/-- Once `m` is in the recurrence range, every section of `(q+m)F` belongs to
the multiplication span of the `qF` and `mF` windows. -/
theorem divisorSections_le_thetaCoordinate_mulSpan (g m q : Nat)
    (hm : windowS_choice pi hpi g ≤ m) :
    divisorSections k ((q + m) • F) ⊤ ≤ Scheme.mulSpan k (H q) (H m) := by
  induction q with
  | zero =>
      intro z hz
      have hOne : (1 : C.left.functionField) ∈ H 0 :=
        Scheme.one_mem_divisorSections_top k (by simp)
      simpa only [zero_add, one_mul] using
        (Scheme.mul_mem_mulSpan k hOne hz)
  | succ q ih =>
      intro z hz
      have hexp : q.succ + m = 1 + (q + m) := by omega
      have hz' : z ∈ H(1 + (q + m)) := by
        simpa only [hexp] using hz
      let z' : ↥(H(1 + (q + m))) := ⟨z, hz'⟩
      have hqm : windowS_choice pi hpi g ≤ q + m :=
        hm.trans (Nat.le_add_left m q)
      obtain ⟨z₀, z₁, hzdecomp⟩ :=
        exists_thetaCoordinate_decomposition (C := C) pi hpi g (q + m) hqm z'
      have hz₀ : (z₀ : C.left.functionField) ∈
          Scheme.mulSpan k (H q) (H m) := ih z₀.property
      have hz₁ : (z₁ : C.left.functionField) ∈
          Scheme.mulSpan k (H q) (H m) := ih z₁.property
      have hmul₀ := thetaCoordinate_mul_mulSpan_mem (C := C) pi m q
        (thetaCoordinateFstOne (C := C) pi hpi) z₀ hz₀
      have hmul₁ := thetaCoordinate_mul_mulSpan_mem (C := C) pi m q
        (thetaCoordinateSndOne (C := C) pi hpi) z₁ hz₁
      have hzval : z =
          (thetaCoordinateFstOne (C := C) pi hpi : C.left.functionField) * z₀ +
          (thetaCoordinateSndOne (C := C) pi hpi : C.left.functionField) * z₁ := by
        have h := congrArg Subtype.val hzdecomp
        simpa only [z', thetaWindowMul_coe, Submodule.coe_add] using h
      rw [hzval]
      exact Submodule.add_mem _ hmul₀ hmul₁

/-- Field normal generation from the two-coordinate recurrence: when `m >= S`,
the products of the full `q`-window and `m`-window span the full `(q+m)`-window. -/
theorem thetaCoordinate_mulSpan_eq (g m q : Nat)
    (hm : windowS_choice pi hpi g ≤ m) :
    Scheme.mulSpan k (H q) (H m) = divisorSections k ((q + m) • F) ⊤ := by
  apply le_antisymm
  · refine Scheme.mulSpan_le k (fun a ha b hb => ?_)
    have hab := mul_mem_divisorSections_top k ha hb
    have heq : (q • F) + (m • F) = (q + m) • F := (add_nsmul F q m).symm
    rwa [heq] at hab
  · exact divisorSections_le_thetaCoordinate_mulSpan
      (C := C) pi hpi g m q hm

/-- The finite basis-indexed multiplication presentation of a generated
`(q+m)`-window. -/
noncomputable def thetaCoordinateFiniteMulMap (g m q : Nat)
    (hm : windowS_choice pi hpi g ≤ m) :
    (Fin (Module.finrank k ↥(H q)) → ↥(H m)) →ₗ[k] ↥(H(q + m)) :=
  Scheme.finiteMulMapTo (H q) (H m) (H(q + m))
    (Module.finBasis k ↥(H q))
    (thetaCoordinate_mulSpan_eq (C := C) pi hpi g m q hm)

@[simp]
theorem thetaCoordinateFiniteMulMap_coe (g m q : Nat)
    (hm : windowS_choice pi hpi g ≤ m)
    (x : Fin (Module.finrank k ↥(H q)) → ↥(H m)) :
    ((thetaCoordinateFiniteMulMap (C := C) pi hpi g m q hm x :
        ↥(H(q + m))) : C.left.functionField) =
      ∑ t, ((Module.finBasis k ↥(H q)) t : C.left.functionField) *
        (x t : C.left.functionField) := by
  change Scheme.finiteMulMap (H q) (H m)
    (Module.finBasis k ↥(H q)) x = _
  rw [Scheme.finiteMulMap_apply]

/-- The finite multiplication presentation is onto whenever the second
window lies in the two-coordinate recurrence range. -/
theorem thetaCoordinateFiniteMulMap_surjective (g m q : Nat)
    (hm : windowS_choice pi hpi g ≤ m) :
    Function.Surjective
      (thetaCoordinateFiniteMulMap (C := C) pi hpi g m q hm) :=
  Scheme.finiteMulMapTo_surjective (H q) (H m) (H(q + m))
    (Module.finBasis k ↥(H q))
    (thetaCoordinate_mulSpan_eq (C := C) pi hpi g m q hm)

/-- Surjectivity persists after extension to an arbitrary coefficient ring. -/
theorem thetaCoordinateFiniteMulMap_baseChange_surjective
    (R : Type u) [CommRing R] [Algebra k R]
    (g m q : Nat) (hm : windowS_choice pi hpi g ≤ m) :
    Function.Surjective
      (LinearMap.baseChange R
        (thetaCoordinateFiniteMulMap (C := C) pi hpi g m q hm)) :=
  LinearMap.baseChange_surjective R
    (thetaCoordinateFiniteMulMap_surjective (C := C) pi hpi g m q hm)

/-- Successor form on the pure arithmetic progression.  This is the exact
field theorem needed to factor arbitrary pure-window coefficients into repeated
`S`-window multipliers. -/
theorem thetaCoordinate_windowS_mulSpan_eq (g n : Nat) :
    Scheme.mulSpan k
        (H(windowS_choice pi hpi g))
        (H(windowS_choice pi hpi g + n * windowS_choice pi hpi g)) =
      H(windowS_choice pi hpi g + (n + 1) * windowS_choice pi hpi g) := by
  have hm : windowS_choice pi hpi g ≤
      windowS_choice pi hpi g + n * windowS_choice pi hpi g :=
    Nat.le_add_right _ _
  have h := thetaCoordinate_mulSpan_eq (C := C) pi hpi g
    (windowS_choice pi hpi g + n * windowS_choice pi hpi g)
    (windowS_choice pi hpi g) hm
  have heq : windowS_choice pi hpi g +
      (windowS_choice pi hpi g + n * windowS_choice pi hpi g) =
      windowS_choice pi hpi g + (n + 1) * windowS_choice pi hpi g := by
    ring
  simpa only [heq] using h

end PureWindowMulSpan

end AlgebraicGeometry
