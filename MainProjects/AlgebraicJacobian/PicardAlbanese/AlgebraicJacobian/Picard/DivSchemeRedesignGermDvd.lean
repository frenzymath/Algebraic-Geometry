/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivSchemeUnivFibreHdiv
import AlgebraicJacobian.RiemannRoch.BaseDivisorSpan

/-!
# DD-4 redesign — the fibre-order germ divisibility from the achiever (I-0287 §hle WALL)

Over a fibre curve `relCurve C K` (`K` a field), this file discharges the **single-point order
comparison** that I-0287 isolated as the remaining honest content of the germ-divisibility
`hdiv` (the "`hle` WALL"): if the reading of an *achiever* window section `sec = Θ(v_sec)`
attains the base multiplicity `bd(T)` at a closed point `z` (relative to a pole bound `A`, with
`T` the fibre window `⊆ H⁰(𝒪(A))`), then at `z` its germ divides the germ of the reading of
*every* window section `ψ = Θ(v_ψ)` whose `Φ`-reading lies in `T`.

This is exactly the input the total-space germ divisibility (I-0306 residual 1, step 2 — the
`𝒪_z` ↔ `κ(p)` base change) consumes on the fibre: at the fibre point `z` over `κ(p)`,
`germ_z (read sec) ∣ germ_z (read ψ)`.

The proof is pure `coeffAt`/`divOf`/`ord` calculus threaded through two landed bridges:

* the base-divisor lower bound `Scheme.baseDivisorAt_le_coeffAt` (every window element has
  `bd(T) ≤ (A + div ·)_z`) plus the achiever equality gives the `coeffAt` comparison
  `(A + div Φ_sec)_z ≤ (A + div Φ_ψ)_z`;
* the dictionary `divFamPhi = mulLinear (thetaFieldShiftUnit) ∘ thetaFieldRead ∘
  relThetaWindowEquiv` (`DivisorFamilyFieldDictionary`) turns that into an order comparison of
  the `thetaFieldRead`s — the shift unit `thetaFieldShiftUnit` cancels;
* the germ bridge `germ_relThetaResSide_dvd_iff_ord_le` (`DivSchemeUnivFibreHdiv`, I-0287) then
  reads that order comparison as germ divisibility of the piece side components.

General field `K` (no `κ(p)` residue-field tower), so it stays outside the residue-field
instance minefield.  Certificate-free, `IsGenerator`-free.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

/-! ## The `ord ↔ coeffAt(divOf)` anti-monotone bridge -/

variable (K : Type u) [Field K]

/-- **Order comparison from `coeffAt(divOf)` comparison** (anti-monotone): for function-field
units `a b` at a closed point `z`, `ordₓ a ≤ ordₓ b` exactly follows from
`(div b)ₓ ≤ (div a)ₓ`.  Reads `Scheme.ord = divisorBound (-div ·)` (`Scheme.ord_val_eq`)
through `divisorBound_le_divisorBound_iff`; the two sign reversals of `-div` and the
valuation convention cancel. -/
private lemma ord_le_ord_of_coeffAt_divOf_le {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    (a b : X.functionFieldˣ) {z : X} (hzg : z ≠ genericPoint X)
    (hcoeff : coeffAt hzg (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) b)
        ≤ coeffAt hzg (Scheme.divOf (X ↘ Spec (CommRingCat.of K)) a)) :
    Scheme.ord (X ↘ Spec (CommRingCat.of K)) hzg (a : X.functionField)
      ≤ Scheme.ord (X ↘ Spec (CommRingCat.of K)) hzg (b : X.functionField) := by
  rw [Scheme.ord_val_eq K a hzg, Scheme.ord_val_eq K b hzg,
    divisorBound_le_divisorBound_iff hzg, CurveDivisor.coeffAt_neg,
    CurveDivisor.coeffAt_neg]
  omega

/-! ## The fibre-order germ divisibility -/

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
variable [Algebra k K]
variable (π : C.left ⟶ P1 k) [IsFinite π]

noncomputable local instance instOverCleftGermDvd : C.left.Over (Spec (.of k)) :=
  ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]
variable (a : ℕ)
variable [IsIntegral (relCurve C K)]
  [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (relCurve C K ↘ Spec (CommRingCat.of K))]

set_option maxHeartbeats 800000 in
-- the `divFamPhi`/`relThetaWindowEquiv` window readings and the piece germ bridge over the
-- fibre curve re-elaborate the section/function-field defeq past the defaults
set_option synthInstance.maxHeartbeats 400000 in
set_option linter.unusedSectionVars false in
/-- **The fibre-order germ divisibility from an achiever** (I-0287 §hle WALL, single point):
on the fibre curve `relCurve C K` (`K` a field), let `T ≤ H⁰(𝒪(A))` be a window and
`z` a closed point.  If the reading `Φ(v_sec)` of a window section attains the base
multiplicity `bd(T)` at `z` (`hach`), then the germ at `z` of the piece side component of the
achiever section `relThetaWindowEquiv v_sec` divides that of every window section
`relThetaWindowEquiv v_ψ` whose `Φ`-reading `Φ(v_ψ)` lies in `T`.

This discharges I-0287's remaining `hle` order comparison at the single point `z`: the achiever
has minimal order there, so `ord(read ψ) ≤ ord(read sec)`, and the germ bridge
`germ_relThetaResSide_dvd_iff_ord_le` reads that as germ divisibility.  The shift unit
`thetaFieldShiftUnit` of the dictionary `Φ = mulLinear(shiftUnit) ∘ thetaFieldRead ∘
relThetaWindowEquiv` cancels in the order comparison. -/
theorem germ_relThetaResSide_windowEquiv_dvd_of_achiever
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    {A : (relCurve C K).CurveDivisor}
    {T : Submodule K (relCurve C K).functionField}
    (hTA : T ≤ Scheme.divisorSections K A ⊤)
    (v_sec v_ψ : K ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤))
    (hsec_ne : divFamPhi C K π a hH1 v_sec ≠ 0)
    (hψ_ne : divFamPhi C K π a hH1 v_ψ ≠ 0)
    (hψ_mem : divFamPhi C K π a hH1 v_ψ ∈ T)
    (b : Bool) {V : (relCurve C K).Opens} (hV : V ≤ relPinnedChart C K π b)
    {z : relCurve C K} (hzV : z ∈ V) (hzg : z ≠ genericPoint (relCurve C K))
    (hach : coeffAt hzg (A + Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0 (divFamPhi C K π a hH1 v_sec) hsec_ne))
        = (Scheme.baseDivisorAt K T A ⟨z, hzg⟩ : ℤ)) :
    ((relCurve C K).presheaf.germ V z hzV).hom
          (relThetaResSide a b hV (relThetaWindowEquiv C K π a hH1 v_sec))
      ∣ ((relCurve C K).presheaf.germ V z hzV).hom
          (relThetaResSide a b hV (relThetaWindowEquiv C K π a hH1 v_ψ)) := by
  -- abbreviations for the two `thetaFieldRead`s and the shift unit
  set tsec := thetaFieldRead C K π a (relThetaWindowEquiv C K π a hH1 v_sec) with htsec_def
  set tψ := thetaFieldRead C K π a (relThetaWindowEquiv C K π a hH1 v_ψ) with htψ_def
  set S := thetaFieldShiftUnit C K π a with hS_def
  -- the dictionary: `Φ(v) = S · thetaFieldRead (Θ v)`
  have hdict_sec : divFamPhi C K π a hH1 v_sec = (S : (relCurve C K).functionField) * tsec := by
    simp only [htsec_def, hS_def, divFamPhi, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Scheme.mulLinear_apply]
  have hdict_ψ : divFamPhi C K π a hH1 v_ψ = (S : (relCurve C K).functionField) * tψ := by
    simp only [htψ_def, hS_def, divFamPhi, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Scheme.mulLinear_apply]
  -- the two readings are nonzero (the shift unit is a unit)
  have htsec_ne : tsec ≠ 0 := fun h0 => hsec_ne (by rw [hdict_sec, h0, mul_zero])
  have htψ_ne : tψ ≠ 0 := fun h0 => hψ_ne (by rw [hdict_ψ, h0, mul_zero])
  -- STEP 1: the `coeffAt` comparison, `(A + div Φ_sec)_z ≤ (A + div Φ_ψ)_z`
  have hlow := Scheme.baseDivisorAt_le_coeffAt K hTA hψ_mem hψ_ne hzg
  rw [← hach] at hlow
  rw [CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_add] at hlow
  have hcoeffΦ :
      coeffAt hzg (Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0 (divFamPhi C K π a hH1 v_sec) hsec_ne))
        ≤ coeffAt hzg (Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0 (divFamPhi C K π a hH1 v_ψ) hψ_ne)) := by omega
  -- STEP 2: split off the shift unit, leaving the reading comparison
  have hunit_sec : Units.mk0 (divFamPhi C K π a hH1 v_sec) hsec_ne
      = S * Units.mk0 tsec htsec_ne :=
    Units.ext (by simp only [Units.val_mul, Units.val_mk0, hdict_sec])
  have hunit_ψ : Units.mk0 (divFamPhi C K π a hH1 v_ψ) hψ_ne
      = S * Units.mk0 tψ htψ_ne :=
    Units.ext (by simp only [Units.val_mul, Units.val_mk0, hdict_ψ])
  rw [hunit_sec, hunit_ψ, Scheme.divOf_mul, Scheme.divOf_mul,
    CurveDivisor.coeffAt_add, CurveDivisor.coeffAt_add] at hcoeffΦ
  have hcoeff_read :
      coeffAt hzg (Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0 tsec htsec_ne))
        ≤ coeffAt hzg (Scheme.divOf (relCurve C K ↘ Spec (CommRingCat.of K))
          (Units.mk0 tψ htψ_ne)) := by omega
  -- STEP 3: order comparison of the readings, then the germ bridge
  have hord : Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hzg tψ
      ≤ Scheme.ord (relCurve C K ↘ Spec (CommRingCat.of K)) hzg tsec := by
    have h := ord_le_ord_of_coeffAt_divOf_le K (Units.mk0 tψ htψ_ne)
      (Units.mk0 tsec htsec_ne) hzg hcoeff_read
    simpa only [Units.val_mk0] using h
  exact (germ_relThetaResSide_dvd_iff_ord_le C K π a
      (relThetaWindowEquiv C K π a hH1 v_ψ) (relThetaWindowEquiv C K π a hH1 v_sec)
      b hV hzV hzg).mpr hord

end AlgebraicGeometry
