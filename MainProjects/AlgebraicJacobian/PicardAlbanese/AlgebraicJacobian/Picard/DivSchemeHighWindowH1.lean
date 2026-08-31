/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/

import AlgebraicJacobian.Picard.DivisorFamilyWindow

/-!
# Vanishing for every high divisor-scheme window

The divisor-scheme construction starts with the two windows `M` and `M + s`.  Its
eventual saturation argument also needs every later window `M + n * s`.  The uniform
window ledger already gives their `H^1`-vanishing: adding a nonnegative multiple of
the multiplier window can only increase the degree.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

section DivisorWindow

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (Y.moduleKSheaf K) 1)]
  (pi : Y ⟶ P1 K) [IsFinite pi] [IsDominant pi]
  (hpi : pi ≫ P1.structureMap K = Y ↘ Spec (CommRingCat.of K))

/-- Every iterated embedding window has vanishing `H^1`:
`H^1(O((M + n * s) F)) = 0`. -/
theorem window_embedding_iter (g n : Nat) :
    Subsingleton (Sheaf.HModule (Y.divisorSheaf K
      ((windowM_choice pi hpi g + n * windowS_choice pi hpi g) •
        fiberWeilDivisor pi)) 1) := by
  refine windowBound_spec pi hpi _ ?_
  rw [Scheme.CurveDivisor.deg_nsmul', deg_fiberWeilDivisor_windowδ]
  have hM := windowBound_le_M_mul pi hpi g
  have hS := windowS_mul_windowδ_nonneg pi hpi g
  have hnS : 0 ≤ (n : Int) *
      ((windowS_choice pi hpi g : Int) * windowδ pi) :=
    mul_nonneg (Int.natCast_nonneg n) hS
  calc
    windowBound pi hpi ≤
        (windowM_choice pi hpi g : Int) * windowδ pi := hM
    _ ≤ ((windowM_choice pi hpi g + n * windowS_choice pi hpi g : Nat) : Int) *
        windowδ pi := by
      push_cast
      nlinarith

end DivisorWindow

section RelativeThetaWindow

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable (pi : C.left ⟶ P1 k) [IsFinite pi]

noncomputable local instance instOverCleftHighWindowH1 :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))] [IsDominant pi]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))

/-- Relative-theta form of `window_embedding_iter`, supplying the `H^1` input to
`relThetaWindowEquiv` at every high window `M + n * s`. -/
theorem relThetaPairH1_windowM_add_mulS (g n : Nat) :
    Subsingleton (relTwistPair C k pi (relThetaCocycle C k pi
      (windowM_choice pi hpi g + n * windowS_choice pi hpi g))).H1 :=
  subsingleton_relThetaPairH1 C pi _
    ((subsingleton_hModule_thetaTwistSheaf_one_iff k pi _).mpr
      (window_embedding_iter pi hpi g n))

end RelativeThetaWindow

end AlgebraicGeometry
