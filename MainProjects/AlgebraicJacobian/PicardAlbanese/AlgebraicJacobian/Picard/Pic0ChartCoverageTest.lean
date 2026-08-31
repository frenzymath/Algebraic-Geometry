/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoverageFibre

/-!
# B-5 assembly: from the fibre step to `chartLocus` membership over a GENERAL test

`Picard/Pic0ChartCoverageFibre.lean` runs `w4-datb` §1.2 steps 4–6 at a splitting field and
produces `IsSplitWitness` of a twisted class over `overSpec k L`.  The coverage theorem
(§1.2's `pic0_chartLocus_cover`) is a statement about a point `t` of a **general test** `T`:

```
∃ c : ChartIndex C, t ∈ chartLocus c lam
```

This file closes the gap between the two, which is one substitution and one collapse:

* the fibre class at `t` is `picEtMap C (Over.testPoint t) lam`, a class over the field
  `κ(t)` — so the fibre step applies at `K := κ(t)` with no change;
* `chartLocus` is *defined* as the split-witness predicate of the twisted class at that field
  point, and the twist commutes with restriction (`picEtMap_chartTwist`), so
  "`IsSplitWitness` of the twisted fibre class" **is** membership, by `Iff.rfl`.

The second point is worth stating as a lemma rather than inlining: `chartTwist` is applied to
`lam` over `T` and then restricted, whereas the fibre step produces the twist of the
*restricted* class over `κ(t)`.  Those are equal, but not syntactically — `picEtMap_chartTwist`
is the law, and `mem_chartLocus_of_isSplitWitness_fibre` is the resulting membership rule.

## What remains of B-5 after this file

**Twice corrected; read the DEFECT section for the full history.**  This header first said the
only residues were the two per-fibre choices; a degree probe added a third (step 6's feedback);
and on 2026-07-28 that third was **removed again** — not by discharging it but by showing
coverage needs no drop, hence no feedback (`Picard/Pic0ChartCoverageNoDrop.lean`).  Step 2 is
likewise landed now (`Picard/Pic0ChartCoverageDegreeStep2.lean`).

The two per-fibre choices, which are residues *of the route through this file*:

* **step 3, the twist exponent `m`.**  Chosen against the fibre's OWN DAT-0a bound `b_L`.  No
  uniform `m₀` exists (§0.2.2, I-0204), so this is a genuine `∃ m` produced inside the
  coverage proof, at the fibre.
* **step 5's oracle instantiation.**  `Curve/SepPointsDense.lean`'s density keystone at
  `P :=` the base-changed `K_s`-points, whose `residueDeg = 1` comes from
  `rationalPointBaseChange_snd`.

Both are `L`-level statements; neither is `divRep`- or certificate-gated.  Everything between
them and `chartLocus` membership is now landed.

## Main declarations

* `AlgebraicGeometry.mem_chartLocus_of_isSplitWitness_fibre` — the membership rule: a split
  witness for the twisted *fibre* class puts `t` in `chartLocus`.
* `AlgebraicGeometry.mem_chartLocus_of_drop` — **the B-5 assembly**: the fibre step's
  hypotheses, at `K := κ(t)`, give `t ∈ chartLocus`.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The membership rule -/

variable (C) in
/-- **A split witness for the twisted FIBRE class puts the point in `chartLocus`.**

`chartLocus` twists over `T` and then restricts to `κ(t)`; the fibre step produces the twist of
the already-restricted class.  `picEtMap_chartTwist` says those agree, and
`chartTwist_eq_mul_thetaFamily_chartTwistClass` puts both in the collapsed spelling the fibre
step uses.

Stated as a named rule because the two sides differ syntactically and a lane that inlines the
substitution will meet the mismatch inside a proof about degrees, where it is least welcome. -/
theorem mem_chartLocus_of_isSplitWitness_fibre (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) {T : Over (Spec (.of k))}
    (lam : picEt C T) (t : T.left)
    (h : IsSplitWitness C
      (picEtMap C (Over.testPoint t) lam
        * thetaFamily C (chartTwistClass C m Z) (overSpec k (Over.testPointField t)))) :
    t ∈ chartLocus C m Z lam := by
  rw [mem_chartLocus_iff, picEtMap_chartTwist,
    chartTwist_eq_mul_thetaFamily_chartTwistClass]
  exact h

/-! ## A DEFECT IN THIS FILE'S OWN COMPOSITION CLAIM — read before using `mem_chartLocus_of_drop`

Found by a degree probe on this file, the same session it was written, and stated here rather
than quietly repaired because the theorems below are **true and correctly proved** — what was
wrong is the account of how they compose.

**The arithmetic.** `hW₀` puts `W₀` in the class `M₀ · (twist class at Z)`.  For a degree-zero
`λ` the presenting class `M₀` has `classDeg = 0`, so

  `deg W₀ = m·d₁ − deg_k Z`,

and `hdeg` demands `deg W₀ = g + e`.  Under the chart-index constraint `deg_k Z = m·d₁ − g`
those force **`e = 0`**: the drop budget is zero and the greedy drop does nothing.  (Verified by
deriving `(e : ℤ) = 0` from exactly this hypothesis pack.)

**What that means.** The pack is *satisfiable* — it instantiates, and at `e = 0` the theorem is
the true statement "a witness of degree `g` gives `chartLocus` membership".  It is not vacuous.
But `w4-datb` §1.2's argument runs the drop at a **different stage** from the chart index:

* the drop runs on `λ·θᵐ` — i.e. at `Z := 0`, where `chartTwistClass C m 0 = θᵐ` and the degree
  is `m·d₁`, so the budget is `e = m·d₁ − g`, nonzero for the `m` step 3 chooses;
* its **output** `Σ` is then the chart index's `Z`, at which the twisted class has degree `g`.

So one `Z` is an input and the other is an output, and this file's headline claim that "steps
4–6 are discharged" conflated them.  Steps 4 and 5 (the vanishing witness and the drop) are
discharged **at `Z := 0`** by `exists_isSplitWitness_of_drop`; step 6 — feeding `Σ` back as the
index and re-reading membership at the *new* `Z` — is **NOT** discharged, and needs the
graph-class transport of `Picard/Pic0ChartRationalGraph.lean` applied to the drop's output.

**Corrected status of B-5, 2026-07-28 — and the correction is a REMOVAL of both residues this
section named.**  The arithmetic above is right and the two-stage reading of `w4-datb` §1.2 is
right; what was wrong is treating the drop as *necessary*.

* the step-6 feedback is not a residue: coverage needs no drop at all, because
  `IsSplitWitness` asks for `h¹ = 0` alone (`Picard/Pic0ChartCoverageNoDrop.lean`).  With the
  drop gone there is one `Z` and nothing to feed back;
* step 2 is landed (`PicEtAff.degAff_map` → `classDeg_presenting_eq_zero`).

What remains of B-5 is step 3's per-fibre `m`.

**RETRACTED 2026-07-29 (I-0660).**  This said "and even that is now *derived* rather than chosen:
`mem_chartLocus_of_vanishing_bound` takes the DAT-0a threshold `b_L` in the shape
`exists_bound_subsingleton_hModule_one_of_isFinite_toP1` produces it, so instantiating DAT-0a at
the base-changed curve is the whole remaining work."  FALSE.  At a chart index legal at parameter
`n` that theorem's `hdeg` **forces** the threshold to equal `n` (`ledger_forces_b_eq_n`), and at
`n = g` the resulting hypothesis says every degree-`g` divisor has `h⁰ = 1`
(`hb_forces_h0_eq_one`) — false on a curve with a moving degree-`g` family, and strictly above
DAT-0a's own bound `n₁·deg F + g`.  See `Picard/Pic0ChartCoverageIndexSlack.lean`; the residue is
reconciling the chart parameter with the threshold, not instantiating DAT-0a.

`mem_chartLocus_of_drop` stays sound and is still the right theorem when the `h⁰ = 1`
normalisation is wanted (DAT-C / GAP-2 need it; membership does not); use it knowing its `Z` is
the drop's input stage. -/

/-! ## The assembly -/

variable (C) in
/-- **THE B-5 ASSEMBLY** (`w4-datb` §1.2, everything except the two per-fibre choices).

For a point `t` of a general test `T` and a plus class `lam` over `T`: given a finite separable
`L/κ(t)` presenting the fibre class, and a divisor `W₀` in the twisted class over `L` of degree
`g + e` with vanishing `H¹`, the point `t` lies in `chartLocus C m Z lam` — and the drop at `L`
additionally yields the `h⁰ = 1` normalisation.

**Reading this against `w4-datb` §1.2 — corrected, and the earlier version of this paragraph
was wrong in two places** (issues I-0614, I-0615).  It said "steps 1, 2, 4, 5, 6 are all
discharged".  Three of those five are; the other two are not:

* **step 1 — discharged.**  The `hM₀` hypothesis, which `exists_splitting_of_picEt` supplies
  unconditionally.
* **step 2 — DISCHARGED 2026-07-28, this line supersedes the "NOT discharged" it replaced.**
  The missing input was base-field invariance of `degAff` under `PicEtAff.map`; it is now
  `PicEtAff.degAff_map` (`Picard/DegreeZeroBaseField.lean`) and holds for an **arbitrary** field
  extension `L/K`, with no finiteness or separability.  Step 2 itself is
  `classDeg_presenting_eq_zero` (`Picard/Pic0ChartCoverageDegreeStep2.lean`), and the whole
  twisted ledger closes to `g + e` there.
* **step 4 — discharged** as an input: `hdeg` + `h1`.
* **step 5 — discharged** by the oracle.
* **step 6 — NOT NEEDED, which supersedes "NOT discharged".**  The feedback is real for the
  route *through the drop*, and the DEFECT section's arithmetic stands.  But coverage does not
  need the drop: `IsSplitWitness` asks for `h¹ = 0` and for **neither** effectivity **nor**
  degree `g`, so a witness of the twisted class suffices and there is only ever one `Z`.  See
  `Picard/Pic0ChartCoverageNoDrop.lean`, whose `mem_chartLocus_of_witness_h1` strictly
  generalises this theorem's membership half — with `g`, `e`, `hχ`, `hdeg` and the whole oracle
  deleted rather than discharged.
* **step 3 — the residue this paragraph originally named**, and still a residue: `m`, `W₀` and
  `hdeg` are *inputs*, because `b_L` is per-fibre and does not transport (I-0204), so no
  formulation of this theorem can produce `m` for the caller.

**Note one conclusion this theorem deliberately drops** — wanted not by coverage (which needs no
drop at all, see the step-6 entry above) but by DAT-C's canonical section and GAP-2 uniqueness:
the fibre step returns `S`'s support clause (`coeffAt hx S ≠ 0 → x ∈ P`), and the `-` pattern below
discards it.  A lane closing step 6 should re-expose it — it is what says `Σ` is supported in
the rational points whose graph classes the index is built from. -/
theorem mem_chartLocus_of_drop {T : Over (Spec (.of k))} (lam : picEt C T) (t : T.left)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    {L : Type u} [Field L] [Algebra k L] [Algebra (Over.testPointField t) L]
    [IsScalarTower k (Over.testPointField t) L]
    [Module.Finite (Over.testPointField t) L] [Algebra.IsSeparable (Over.testPointField t) L]
    (g e : ℕ) (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (M₀ : (relCurve C L).CechPic)
    (hM₀ : PicEtAff.map C L
        (picEtAffineEquiv C (Over.testPointField t) (picEtMap C (Over.testPoint t) lam))
      = PicEtAff.unit C L (relPicMk C (overSpec k L) M₀))
    (W₀ : ((C ⊗ overSpec k L).left).CurveDivisor)
    (hW₀ : Scheme.CurveDivisor.picClass L W₀
      = M₀ * Scheme.CechPic.map (relCurveMap C k L) (chartTwistClass C m Z))
    (hdeg : Scheme.CurveDivisor.deg L W₀ = (g : ℤ) + e)
    (h1 : Subsingleton (Sheaf.HModule ((C ⊗ overSpec k L).left.divisorSheaf L W₀) 1))
    (P : Set ((C ⊗ overSpec k L).left))
    (hdense : ∀ U : ((C ⊗ overSpec k L).left).Opens,
      (U : Set ((C ⊗ overSpec k L).left)).Nonempty → (P ∩ U).Nonempty)
    (hPcl : ∀ x ∈ P, x ≠ genericPoint ((C ⊗ overSpec k L).left))
    (hPdeg : ∀ x ∈ P, ((C ⊗ overSpec k L).left).residueDeg L x = 1) :
    t ∈ chartLocus C m Z lam
      ∧ ∃ S : ((C ⊗ overSpec k L).left).CurveDivisor, 0 ≤ S ∧
        Scheme.CurveDivisor.deg L S = (e : ℤ) ∧
        Sheaf.h0 ((C ⊗ overSpec k L).left.divisorSheaf L (W₀ - S)) = 1 ∧
        Subsingleton (Sheaf.HModule
          ((C ⊗ overSpec k L).left.divisorSheaf L (W₀ - S)) 1) := by
  obtain ⟨hsplit, S, hS0, hSdeg, -, hSh0, hSh1⟩ :=
    exists_isSplitWitness_of_drop C (picEtMap C (Over.testPoint t) lam) m Z g e hχ M₀ hM₀
      W₀ hW₀ hdeg h1 P hdense hPcl hPdeg
  exact ⟨mem_chartLocus_of_isSplitWitness_fibre C m Z lam t hsplit,
    S, hS0, hSdeg, hSh0, hSh1⟩

end

end AlgebraicGeometry
