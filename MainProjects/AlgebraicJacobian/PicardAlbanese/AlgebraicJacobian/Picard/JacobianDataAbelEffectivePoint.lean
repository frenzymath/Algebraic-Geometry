/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataAbelEffective
import AlgebraicJacobian.Picard.Pic0ChartCoverageDegreeStep2
import AlgebraicJacobian.Picard.Pic0ChartSplit

/-!
# DAT-J's effectivity input at a **point of the representing object**

`Picard/JacobianDataAbelEffective.lean` produced an effective divisor of degree `g` from a
class of degree `g`, and its satisfiability face
`exists_effective_deg_eq_of_classDeg_eq_zero` does it from a class of degree **zero** plus a
fixed degree-`g` reference divisor.  This file walks that back one further step, to the datum
DAT-J actually holds: a **point of `J`** together with the `Pic⁰` universal property.

## The chain, and where the divRep-gating actually starts

A point `y : J.left` of the representing object of `pic0TypeFunctor C` gives, with no choices:

1. the affine field test `Over.testPoint y : overSpec k κ(y) ⟶ J`
   (`Picard/Pic0ChartTestPoint.lean:176`) — mathlib's `fromSpecResidueField` read in the
   slice;
2. hence the restricted class `picEtMap C (testPoint y) λ` of any `λ : picEt C J`, and its
   fibre degree is `0` when `λ ∈ pic0Subgroup C J` (`mem_pic0Subgroup_iff`);
3. a finite separable `L/κ(y)` and a presenting Čech class `M` over `L`
   (`exists_splitting_of_picEt`, `Picard/Pic0ChartSplit.lean:143` — **unconditional** on the
   curve, which is what makes this file cheap);
4. `classDeg L M = 0` (`classDeg_presenting_eq_zero`,
   `Picard/Pic0ChartCoverageDegreeStep2.lean:98`);
5. and then this file's `exists_effective_deg_eq_of_classDeg_eq_zero`: an **effective divisor
   of degree `g`** over `L` presenting `M · 𝒪(Z)`.

**Nothing in 1–5 mentions the divisor-representability chain.**  So the "geometric half" of
DAT-J step 3 — the part `Picard/JacobianDataAbelSquare.lean` calls the honest Riemann–Roch
input `heff` — is *not* divRep-gated at all.  What *is* divRep-gated is the other half: that
the resulting `DivScheme`-point sits over `y`, i.e. the Abel-compatibility square, because
naming the Abel map at all requires the representation.

## The honest limit, stated because it is easy to overclaim here

The divisor produced below lives over the **splitting field `L`**, not over `κ(y)` itself, and
DAT-J's `hlift` wants a morphism out of `Spec κ(y)`.  Descending `L ↝ κ(y)` is a genuine
further step (finite separable descent — the `dat-g` lane's business), and this file does not
take it.  What it settles is that the effectivity content is available, unconditionally, at
every point of every `Pic⁰`-representing object.

## TWO FURTHER LIMITS, from a fresh-context audit of this file (`I-0802`, `I-0800`)

**(a) The reference divisor is quantified UNIFORMLY, which is strictly stronger than the
degree-`0` face asks.**  Because the splitting field `L` is produced *existentially inside the
proof*, the caller cannot name it in advance, so the hypothesis had to become
`Zof : ∀ L, (relCurve C L).CurveDivisor` together with `hZ : ∀ L, deg L (Zof L) = g` — a
degree-`g` divisor over **every** field extension at once, including `L = k`.  Compare the
single `Z` of `exists_effective_deg_eq_of_classDeg_eq_zero`.  This has **no producer anywhere
in the tree**, and it is unsatisfiable exactly when the index of the curve does not divide `g`
(`deg` is residue-degree weighted, `RiemannRoch/Divisor.lean:61`).  It is the *binding* limit of
this file — stronger than the descent limit named above, which is the one the first draft
disclosed.

**(b) A `PicRepDatum` face is NOT provided.**  The first draft of this docstring advertised
`PicRepDatum.exists_effective_deg_eq_at_point`, "the degree-zero class supplied by the universal
property rather than assumed".  **No such declaration exists** — it was never written, so the
one face that would consume the `Pic⁰` universal property is absent and `lam`/`hlam` remain
hypotheses the caller supplies.  Recorded rather than quietly deleted, because an advertised
declaration list is unchecked by any build.

**(c) The cone is NOT `Challenge`-free**, and `w4-datj-worksheet.md` §0.5/§3.4 make that
binding for a DAT-J producer.  This file reaches `Challenge.lean` through
`Picard/DivisorDatumRankOne` → `Cohomology/H1BaseFieldInvariance:6`.  Verified by reading the
import lines, not inferred.  §0.5's own claim that `FLVClass.lean` is Challenge-free is *also*
false at HEAD (`RiemannRoch/Degree.lean:7` → `ChiCurve.lean` → `Challenge`), so the standing
"use `exists_effective_of_picClass`, never `riemann_inequality_curve`" rule no longer avoids the
cycle — both are downstream of `Challenge`.  That is a pre-existing tree-wide condition, not
something this file introduced, but it does mean the effectivity content is **not** yet
consumable by the planned DJ-2/DJ-3 discharge.

## Main declarations

* `AlgebraicGeometry.exists_effective_deg_eq_of_pic0_at_point` — from a degree-zero class on
  `J` and a point `y`, an effective degree-`g` divisor over a finite separable extension of
  `κ(y)`, presenting the shifted class.  Conditional on (a) above.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

noncomputable section

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable local instance instOverCleftAbelEffectivePoint :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

-- The fibre-curve package at every field extension.  These do not synthesize through the
-- `relCurve` `def` barrier, so they are installed locally exactly as in
-- `Picard/DivSchemeSeedUnivAssembleKappa.lean` and `Picard/JacobianDataAbelEffective.lean`.
noncomputable local instance instIsIntegralRelCurvePt (L : Type u) [Field L]
    [Algebra k L] : IsIntegral (relCurve C L) := instIsIntegralBaseChange C L

noncomputable local instance instSmoothRelCurvePt (L : Type u) [Field L] [Algebra k L] :
    SmoothOfRelativeDimension 1 (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instSmoothOfRelativeDimensionBaseChange C L

noncomputable local instance instQCRelCurvePt (L : Type u) [Field L] [Algebra k L] :
    QuasiCompact (relCurve C L ↘ Spec (CommRingCat.of L)) :=
  instQuasiCompactBaseChange C L

/-- **The effectivity input of DAT-J at a point of the representing object.**

Given a degree-zero étale Picard class `lam` on a test object `J` and a point `y` of `J.left`,
there is a finite separable extension `L` of the residue field `κ(y)` and an **effective
divisor of degree `g`** on the fibre curve over `L` whose class is the restriction of `lam`
at `y`, shifted by a fixed degree-`g` reference class.

Every step is a landed lemma and none of them is divRep-gated: `Over.testPoint` names the
field test at `y`, `mem_pic0Subgroup_iff` reads off `degAt = 0`, `exists_splitting_of_picEt`
(unconditional) presents the restricted class over a finite separable `L`,
`classDeg_presenting_eq_zero` reads the presenting class's degree as `0`, and
`exists_effective_deg_eq_of_classDeg_eq_zero` shifts by `𝒪(Z)` and produces the divisor.

`Z` is the caller's degree-`g` reference divisor over `L` — in the campaign a multiple of
`fiberWeilDivisor`, whose degree is positive (`zero_lt_deg_fiberWeilDivisor`). -/
theorem exists_effective_deg_eq_of_pic0_at_point (g : ℕ)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    {J : Over (Spec (.of k))} (lam : picEt C J) (hlam : lam ∈ pic0Subgroup C J)
    (y : J.left)
    (Zof : ∀ (L : Type u) [Field L] [Algebra k L], (relCurve C L).CurveDivisor)
    (hZ : ∀ (L : Type u) [Field L] [Algebra k L],
      CurveDivisor.deg L (Zof L) = (g : ℤ)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
        (_ : Algebra (Over.testPointField y) L)
        (_ : IsScalarTower k (Over.testPointField y) L)
        (_ : Module.Finite (Over.testPointField y) L)
        (_ : Algebra.IsSeparable (Over.testPointField y) L)
        (M : (relCurve C L).CechPic) (E : (relCurve C L).CurveDivisor),
      PicEtAff.map C L
          (picEtAffineEquiv C (Over.testPointField y) (picEtMap C (Over.testPoint y) lam))
            = PicEtAff.unit C L (relPicMk C (overSpec k L) M) ∧
        0 ≤ E ∧ CurveDivisor.picClass L E = M * CurveDivisor.picClass L (Zof L) ∧
        CurveDivisor.deg L E = (g : ℤ) := by
  -- (3) the splitting of the restricted class at the field point of `y`
  obtain ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, M, hM⟩ :=
    exists_splitting_of_picEt C (picEtMap C (Over.testPoint y) lam)
  letI := hLfield; letI := hkL; letI := hKL; letI := htow
  -- (2) the fibre degree of the restricted class vanishes, by membership of `pic0Subgroup`
  have hdeg0 : degAt lam (Over.testPoint y) = 0 :=
    mem_pic0Subgroup_iff.mp hlam (Over.testPointField y) (Over.testPoint y)
  -- (4) hence the presenting class has degree zero
  have hM0 : classDeg L M = 0 :=
    classDeg_presenting_eq_zero C lam (Over.testPoint y) hdeg0 L M hM
  -- (5) the shift and the effectivity brick
  obtain ⟨E, hEeff, hEcl, hEdeg⟩ :=
    exists_effective_deg_eq_relCurve_of_classDeg_eq_zero g hχ L (Zof L) (hZ L) M hM0
  exact ⟨L, hLfield, hkL, hKL, htow, hfin, hsep, M, E, hM, hEeff, hEcl, hEdeg⟩

end

end AlgebraicGeometry
