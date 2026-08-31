/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorDatumRankOne
import AlgebraicJacobian.RiemannRoch.FLVClass
import AlgebraicJacobian.RiemannRoch.Degree

/-!
# DAT-J's Riemann–Roch half: an effective representative **of degree `g`**

`Picard/JacobianDataAbelSquare.lean` splits DAT-J step 3 into a compatibility square and
an effectivity input `heff`, and names the spelling the effectivity half must use
(`exists_effective_of_picClass` / `riemann_inequality`, never `riemann_inequality_curve`,
which imports `Challenge.lean`).  This file discharges that half, and it is **free of the
divisor-representability chain**: nothing below mentions `divFunctor`, `DivFamZar`, a
certificate, a chart or a universal family.

## The gap this closes, and why it was not already closed

Every effectivity lemma in the tree stops one conjunct short of what DAT-J consumes:

* `exists_effective_of_picClass` (`RiemannRoch/FLVClass.lean:208`) and
  `exists_effective_of_h0_pos` (`RiemannRoch/SectionBound.lean:175`) both conclude
  `0 ≤ E ∧ picClass E = picClass W` — **no statement about `deg E`**.
* `DivFamZar.exists_effective_witness` (`Picard/DivisorFamilyH1Locus.lean:123`) *does*
  carry the degree conjunct, but only for a divisor already presented by a locally
  certified family, i.e. behind the whole gated carrier.

`effectiveDivisorClassifyZar` (`Picard/DivisorFamilyFieldSurj.lean:217`) demands
`0 ≤ D` **and** `deg D = g`, so the missing conjunct is exactly what blocked it.  The
conjunct is not extra work: degree is a class invariant (`deg_eq_deg_of_picClass_eq`), so
it comes for free from the class equation — which is why the shape below is a *statement*
gap rather than a mathematical one.

## The degree bookkeeping, stated once

At genus `g` the χ-normalization is `χ(𝒪) = 1 − g`, so the Riemann-inequality entry
condition `1 ≤ deg W + χ(𝒪)` reads `1 ≤ deg W + 1 − g`, i.e. `g ≤ deg W`.  A class of
degree **exactly** `g` therefore sits on the boundary and fires the lemma with no slack —
so no `fiberTwist` shift is needed, contrary to what `Picard/JacobianDataAbelImage.lean`'s
docstring predicts for this brick.  (The shift is what one needs to push a class of
*degree zero* up to the effective range; `pic0` classes reach degree `g` by multiplying by
a fixed degree-`g` class, and that multiplication is the caller's business, not this
file's.)

## Main declarations

* `AlgebraicGeometry.exists_effective_deg_eq_of_classDeg_eq` — over a curve with
  `χ(𝒪) = 1 − g`, every Čech Picard class of degree `g` has an effective representative
  **of degree `g`**.  General: any `X`, no relative curve, no `π`.
* `AlgebraicGeometry.exists_effective_deg_eq_of_classDeg_eq_zero` — **the degree-`0` face, the
  form the campaign uses** (the classes DAT-J holds have degree `0`).  It takes a degree-`g`
  reference divisor `Z` as an *argument*, so it **relocates** the hypothesis rather than
  discharging it — see the retraction at that declaration: a degree-`g` divisor need not exist,
  because `deg` is residue-degree weighted.
* `AlgebraicGeometry.exists_effective_of_classDeg_eq` — the not-silently-stronger probe: the
  landed degree-free conclusion is recovered as a corollary.
* `AlgebraicGeometry.exists_effective_deg_eq_relCurve` — the same at the fibre curve
  `relCurve C K` of the campaign bundle, with the base normalization `hχ` transported by
  `chi_relCurve` and the four fibre instances installed.
* `AlgebraicGeometry.exists_effective_deg_eq_residueField` — the form DAT-J's `heff`
  consumes: at the residue field of a point of an arbitrary scheme `J`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

/-! ## The general statement -/

section General

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
  [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]

/-- **An effective representative of prescribed degree.**  On a curve with
`χ(𝒪) = 1 − g`, a Čech Picard class `L` of degree `g` is the class of an **effective**
divisor `E` with `deg E = g`.

Two landed inputs and no new mathematics: `CurveDivisor.exists_picClass_eq` names some
divisor `W` in the class, `classDeg_picClass` reads `deg W = g` off the class degree, the
Riemann-inequality entry condition `1 ≤ deg W + χ(𝒪)` is then `1 ≤ g + (1 − g)` — an
equality, so the boundary case is the one that matters — and
`exists_effective_of_picClass` produces `E`.  The degree conjunct, which is the whole
reason this statement exists, is `deg_eq_deg_of_picClass_eq` applied to `E`'s class
equation: degree is a class invariant, so it transports for free.

The genus enters only through `hχ`; there is no hypothesis on `X` beyond the curve
package, and in particular no `π` and no rational point. -/
theorem exists_effective_deg_eq_of_classDeg_eq (g : ℕ)
    (hχ : Sheaf.chi (X.moduleKSheaf K) = 1 - (g : ℤ))
    (L : X.CechPic) (hL : classDeg K L = (g : ℤ)) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧ CurveDivisor.picClass K E = L ∧
      CurveDivisor.deg K E = (g : ℤ) := by
  obtain ⟨W, hW⟩ := CurveDivisor.exists_picClass_eq K L
  have hdegW : CurveDivisor.deg K W = (g : ℤ) := by
    rw [← classDeg_picClass K W, hW, hL]
  have hentry : 1 ≤ CurveDivisor.deg K W + Sheaf.chi (X.moduleKSheaf K) := by
    rw [hdegW, hχ]; omega
  obtain ⟨E, hEeff, hEcl⟩ := exists_effective_of_picClass W hentry
  exact ⟨E, hEeff, hEcl.trans hW,
    (deg_eq_deg_of_picClass_eq K hEcl).trans hdegW⟩

/-! ### The two probes this statement owes -/

/-- **THE SATISFIABILITY PROBE, and it is the one that matters here.**  `L` is chosen by the
consumer but *constrained* (`classDeg K L = g`), so the failure mode is not junk-inhabitation:
it is that **no class of degree `g` exists**, in which case the theorem above is a vacuous
truth that every `sorry` census and axiom probe passes.

**RETRACTED 2026-07-29, same session, after a fresh-context audit (`I-0799`).**  The first
draft of this docstring said the probe "comes back positive, and **unconditionally on the
curve**: the degree map hits `g`".  **That is false**, and it is false arithmetically, not
merely unlanded: `CurveDivisor.deg` is weighted by residue degrees
(`deg D = ∑ₓ Dₓ · [κ(x) : K]`, `RiemannRoch/Divisor.lean:61`), so its image is `index · ℤ` for
the index of the curve.  On a curve of index `3` and genus `1` over `ℚ` there is **no** divisor
of degree `1 = g`, and `exists_effective_deg_eq_of_classDeg_eq` is then a vacuous truth.  The
campaign's own reference divisors do not escape this: `deg (m • fiberWeilDivisor π) = m · δ`
(`RiemannRoch/WindowLedger.lean:133`), so `= g` needs `δ ∣ g`.

**So what this lemma does is RELOCATE the hypothesis, not discharge it** — `Z` is an argument.
That is still worth having, because it is the *shape* a `Pic⁰` consumer meets (the classes
DAT-J holds have degree `0`, not `g`, so without this face the degree-`g` statement would be
a theorem nobody could instantiate).  But the honest reading is conditional: **given a
degree-`g` divisor `Z` over the field in question**, every degree-`0` class yields an effective
degree-`g` divisor.  Producing `Z` is a genuine arithmetic hypothesis on the curve, open here.

Given any divisor `Z` of degree `g` (the caller's fixed reference: in the campaign
`m • fiberWeilDivisor π` for suitable `m`, whose degree is positive by
`zero_lt_deg_fiberWeilDivisor`), every degree-`0` class `L₀` yields the degree-`g` class
`L₀ · 𝒪(Z)`, and the theorem above then produces the effective degree-`g` divisor.  So the
hypothesis of `exists_effective_deg_eq_of_classDeg_eq` is inhabited wherever a degree-`g`
divisor exists, and the shift is one `classDeg_mul`. -/
theorem exists_effective_deg_eq_of_classDeg_eq_zero (g : ℕ)
    (hχ : Sheaf.chi (X.moduleKSheaf K) = 1 - (g : ℤ))
    (Z : X.CurveDivisor) (hZ : CurveDivisor.deg K Z = (g : ℤ))
    (L₀ : X.CechPic) (hL₀ : classDeg K L₀ = 0) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧
      CurveDivisor.picClass K E = L₀ * CurveDivisor.picClass K Z ∧
      CurveDivisor.deg K E = (g : ℤ) := by
  refine exists_effective_deg_eq_of_classDeg_eq K g hχ _ ?_
  rw [classDeg_mul, hL₀, classDeg_picClass, hZ, zero_add]

/-- **The not-silently-stronger probe**: the degree-`g` conclusion recovers the landed
degree-free statement, so nothing was smuggled into the hypotheses.  Both directions of the
pair "is it weaker / is it vacuous" are therefore discharged in the file itself, as
`I-0571`'s safeguard asks. -/
theorem exists_effective_of_classDeg_eq (g : ℕ)
    (hχ : Sheaf.chi (X.moduleKSheaf K) = 1 - (g : ℤ))
    (L : X.CechPic) (hL : classDeg K L = (g : ℤ)) :
    ∃ E : X.CurveDivisor, 0 ≤ E ∧ CurveDivisor.picClass K E = L :=
  let ⟨E, hE, hcl, _⟩ := exists_effective_deg_eq_of_classDeg_eq K g hχ L hL
  ⟨E, hE, hcl⟩

end General

/-! ## At the fibre curve of the campaign bundle -/

section FibreCurve

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable local instance instOverCleftAbelEffective :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

-- The fibre-curve package at every field extension (the `DivSchemeMonoBridgeRel` pack:
-- these cannot be synthesized through the `relCurve` `def` barrier).
noncomputable local instance instIsIntegralRelCurveEff (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurveEff (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurveEff (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

noncomputable local instance instFinH0RelCurveEff (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 0) :=
  instModuleFiniteHModuleZeroBaseChange C L

noncomputable local instance instFinH1RelCurveEff (L : Type u) [Field L]
    [Algebra k L] : Module.Finite L (Sheaf.HModule ((relCurve C L).moduleKSheaf L) 1) :=
  instModuleFiniteHModuleOneBaseChange C L

/-- **The fibre form**: at every field `L` over `k`, a class of degree `g` on the fibre
curve `relCurve C L` has an effective representative of degree `g`.

The base normalization `hχ : χ(𝒪_C) = 1 − g` transports to the fibre by `chi_relCurve`
(`Picard/DivisorDatumRankOne.lean:83`, which routes through `genus_baseField`), and the
four fibre instances are installed locally above because they do not synthesize through
the `relCurve` definition barrier. -/
theorem exists_effective_deg_eq_relCurve (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (L : Type u) [Field L] [Algebra k L]
    (cls : (relCurve C L).CechPic) (hcls : classDeg L cls = (g : ℤ)) :
    ∃ E : (relCurve C L).CurveDivisor, 0 ≤ E ∧
      CurveDivisor.picClass L E = cls ∧ CurveDivisor.deg L E = (g : ℤ) :=
  exists_effective_deg_eq_of_classDeg_eq L g (chi_relCurve hχ L) cls hcls

/-- **The fibre form of the shift** — the face a `Pic⁰` consumer actually meets, since the
classes it holds have degree `0` and live on `relCurve C L`.

Same content as `exists_effective_deg_eq_of_classDeg_eq_zero`, stated at the fibre curve so a
caller does not have to re-derive `chi_relCurve` or re-install the fibre instances at the call
site (which is what forces the `(C := …)`-style instance face; measured — supplying the
general lemma directly at a `relCurve` goal fails instance synthesis on all three of
`IsIntegral`, `SmoothOfRelativeDimension` and `QuasiCompact`). -/
theorem exists_effective_deg_eq_relCurve_of_classDeg_eq_zero (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (L : Type u) [Field L] [Algebra k L]
    (Z : (relCurve C L).CurveDivisor) (hZ : CurveDivisor.deg L Z = (g : ℤ))
    (L₀ : (relCurve C L).CechPic) (hL₀ : classDeg L L₀ = 0) :
    ∃ E : (relCurve C L).CurveDivisor, 0 ≤ E ∧
      CurveDivisor.picClass L E = L₀ * CurveDivisor.picClass L Z ∧
      CurveDivisor.deg L E = (g : ℤ) :=
  exists_effective_deg_eq_of_classDeg_eq_zero L g (chi_relCurve hχ L) Z hZ L₀ hL₀

/-- **The `heff` form**: at the residue field of a point `y` of an arbitrary scheme `J`,
a degree-`g` class on the fibre curve has an effective degree-`g` representative.

This is the shape `exists_residueField_lift_of_abelCompatible`
(`Picard/JacobianDataAbelSquare.lean:158`) consumes its divisor in — the residue field of
a point of the Jacobian-to-be, carrying a `k`-algebra structure supplied by the caller.
What is still the caller's business is naming the *class*: which degree-`g` class the
point `y` presents is the content of the Abel-compatibility square, not of this file. -/
theorem exists_effective_deg_eq_residueField (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {J : Scheme.{u}} (y : J) [Algebra k (J.residueField y)]
    (cls : (relCurve C (J.residueField y)).CechPic)
    (hcls : classDeg (J.residueField y) cls = (g : ℤ)) :
    ∃ E : (relCurve C (J.residueField y)).CurveDivisor, 0 ≤ E ∧
      CurveDivisor.picClass (J.residueField y) E = cls ∧
      CurveDivisor.deg (J.residueField y) E = (g : ℤ) :=
  exists_effective_deg_eq_relCurve g hχ (J.residueField y) cls hcls

end FibreCurve

end AlgebraicGeometry
