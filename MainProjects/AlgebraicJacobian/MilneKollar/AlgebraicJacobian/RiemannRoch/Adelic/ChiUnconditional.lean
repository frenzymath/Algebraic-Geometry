/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.LedgerClosure

/-!
# The Čech Euler characteristic is an inclusion–exclusion count — unconditionally

Every χ-statement in this lane so far has been *gated*: `ChiLedger.chi_add` and its
descendants take four exactness hypotheses (`window`, `connect`, `twist`, and the
surjectivity `htwist`) packaging the ledger four-term sequence
`0 → L(D')/L(D) → 𝒜(D')/𝒜(D) → Ȟ¹(D) → Ȟ¹(D') → 0`, whose connecting map and
right-exactness the lane does not construct.  That is why `hbump` — "χ jumps by
`[κ(P):k]` at every one-point bump" — has been carried as an open hypothesis, and why
the audit at inbox `I-0449` was able to *refute* it off the cover overlap.

This file removes the gate for the underlying numerical identity.  The point is that
for a **two-set cover** the Čech Euler characteristic needs no exact sequence at all:

`χ(D) = dim 𝒞⁰(D) − dim 𝒞¹(D)` where `𝒞⁰(D) = Γ(U₀,𝒪(D)) ⊕ Γ(U₁,𝒪(D))`,
`𝒞¹(D) = 𝒜(D) = Γ(U₀ ⊓ U₁, 𝒪(D))`,

and both `ℓ(D) = dim ker` and `h¹(D) = dim coker` are read off the *same* map by
rank–nullity.  Concretely, with `B(D) = Γ(U₀,𝒪(D)) + Γ(U₁,𝒪(D))` the coboundary and
`L(D) = Γ(U₀,𝒪(D)) ⊓ Γ(U₁,𝒪(D))` the global sections (`Substrate.linearSystem_eq_inf`
on a cover), the modular law
`dim(S₀ ⊔ S₁) + dim(S₀ ⊓ S₁) = dim S₀ + dim S₁`
(mathlib's `Submodule.finrank_sup_add_finrank_inf_eq`) *is* the Euler characteristic:

`χ(D) = ℓ(D) − h¹(D) = dim L(D) − (dim 𝒜(D) − dim B(D))`
      `= dim(S₀ ⊓ S₁) + dim(S₀ ⊔ S₁) − dim 𝒜(D) = dim S₀ + dim S₁ − dim 𝒜(D)`.

## What is proved, and what it is worth

* `chi_eq_charts_sub_overlap` — **the unconditional χ formula.**
  `χ(D) = dim Γ(U₀,𝒪(D)) + dim Γ(U₁,𝒪(D)) − dim 𝒜(D)` on a cover `U₀ ⊔ U₁ = ⊤`,
  with **no exactness hypotheses** — only the finiteness of the two chart section
  spaces.  This is strictly stronger than what `chi_add` gives, in the precise sense
  that it has none of `chi_add`'s four gated binders.

* `chi_sub_chi_eq_charts_sub_overlap` — the difference form: the χ-jump between two
  divisors is an alternating sum of three *local step* dimensions, again unconditionally.

* `chi_add_pointDivisor_of_notMem_left` — at a point off one chart the whole χ-jump is the
  *single surviving chart step*, and `bump_iff_chartStep_of_notMem_left` makes the one-step
  bump equivalent to that step being full.  Both ungated.  These are one-step statements and
  must not be read as consistency claims — see the next item.

* `chi_le_finrank_chart_along_tower` and `not_bump_of_notMem_left` (§5) — `hbump` is FALSE
  **under this file's chart-finiteness binders** whenever some prime divisor's point lies off a
  chart.  Along the tower `n·P` both `Γ(U₀,−)` and `𝒜` freeze while `Γ(U₁,−) ⊆ 𝒜` stays
  trapped, so χ is *bounded* — against `hbump`'s linear growth `n·[κ(P):k]`.  **READ THE NEXT
  SECTION BEFORE QUOTING THIS**: those binders are unsatisfiable on a curve, so this refutation
  does not reach a curve.  Earlier versions of this header called it "unconditional"; it is
  unconditional in *exactness data* only, never in the finiteness binders.

* `ledger_refuted_of_notMem_left` (§6) — the same tower refutes the **closed ledger** `hledger`
  on such a cover, under the same binders and with the same caveat.

## The finiteness binders are NOT innocent — and they are UNSATISFIABLE on a curve

`Module.Finite k (sectionSub k U D)` at a **non-total** open `U` is a substantive restriction,
not bookkeeping.  The `ℓ`-level form is `ell_le_finrank_chart_along_tower`:

`ℓ(n·P + E) ≤ dim Γ(U₀,𝒪(E))` for all `n`, whenever `P.point ∉ U₀`

— **it forbids Riemann growth outright**.

**This was originally read as a restriction on the COVER, and that reading is wrong.**
`Adelic/ChartFinitenessRefuted.lean` proves that a *single* instance of the binder, at the zero
divisor alone, forces `K(X)` to be a **finite extension of `k`**
(`module_finite_functionField_of_chart_finite`), and that the binder is *equivalent* to that
statement — one with no cover, no chart and no divisor in it
(`chart_finiteness_iff_module_finite_functionField`).  Mechanism: `Γ(U,𝒪(0))` is a ring
containing `Γ(X,U)`; a `k`-finite domain is a field; a field between `Γ(X,U)` and its own
fraction field is all of `K(X)`.

Consequences, and they are the ones to carry forward:

* On a curve with a nonconstant function the binder holds at **no chart and no cover**.  So
  §5–§6 refute nothing *about a curve*: `hbump` and `hledger` are **open** there, not false.

  **The other refutation route, checked so this claim is not narrower than it sounds.**
  `LedgerClosure.not_bump_of_notMem_overlap` refutes the bump off the *overlap* and carries **no**
  chart-finiteness binder at all, so the argument above does not touch it.  It does not reach a
  curve either, for an independent reason: its hypothesis `hchiAdd` is the conclusion of
  `ChiLedger.chi_add`, whose four exactness data (`window`, `connect`, `twist`, `htwist` — the
  connecting homomorphism and right-exactness of the ledger four-term sequence) are constructed
  **nowhere** in the lane.  So it is conditional on unbuilt data rather than on a false binder.
  Two routes, two different reasons, same conclusion: nothing in AJC currently refutes `hbump` at
  a curve.  This was worth checking rather than asserting, because §2b round 2 of
  `scripts/axiom-frontier.lean` is precisely the error of inferring "not refutable" from "not
  refutable by the route I looked at".
* "Exhibit a cover on which the ledger can hold" — the direction this file's earlier header and
  `WeilDivisor.lean` recommended — is **not** the open problem.  There is no cover to find.
* Prefer stating results at `⊤`, where `Module.Finite` is the honest finiteness of `L(D)`.

This is trap (c) of `scripts/axiom-frontier.lean` applied to a *negative* result, a case the
catalogue did not cover: a refutation whose own hypotheses are unsatisfiable reports clean
axioms exactly like a useful one.

## Provenance

Rederived in AJC's own abstractions (`sectionSub`, `chi`, `H1Mod`).  This is **not** a
port: the sibling project's `RiemannRoch/UniformVanishing.lean` core is a bounded
vanishing statement, not this identity, and nothing of this shape existed in either
project — the lane had only the gated `chi_add`.  The mathlib input is exactly one
lemma, `Submodule.finrank_sup_add_finrank_inf_eq`.

## Correction history

This module shipped, within one session, with docstrings claiming that the audit at inbox
`I-0449` had misfired and that `hbump` was *not* refutable off the overlap.  An adversarial
review (`I-0467`) showed the opposite from this file's own formula, and §5/§6 now carry the
refutations in Lean.  The retracted claim is left described rather than silently deleted, since
it was broadcast to two other teams before being corrected.

**Third correction (task `ajc-rr`, 2026-07-28), and it goes the other way from the second.**
The refutations of §5–§6 were then presented as "unconditional" and as redirecting the route
towards a better cover.  Both readings were wrong, and the second one sent the next session at a
non-problem.  They are unconditional in *exactness data* only; their chart-finiteness binders are
unsatisfiable on a curve (`ChartFinitenessRefuted.lean`), so on a curve the refutations are
vacuous and `hbump`/`hledger` are open rather than false.  The theorems are unchanged and still
true — only their scope was overstated.  Pattern worth naming, since this module has now
produced it twice in opposite directions: "not refutable by this route" does not give "fine",
and "refuted under my binders" does not give "refuted".
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

section ChiCharts

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **`L(D)` is the intersection of the two chart section spaces**, as `k`-submodules.
The `k`-linear form of `Substrate.linearSystem_eq_inf`. -/
theorem sectionSub_top_eq_inf (hcov : U₀ ⊔ U₁ = ⊤) (D : X.WeilDivisor) :
    sectionSub k ⊤ D = sectionSub k U₀ D ⊓ sectionSub k U₁ D := by
  apply SetLike.coe_injective
  change (sectionOfDivisor ⊤ D : Set X.functionField) = _
  rw [show sectionOfDivisor (X := X) ⊤ D = linearSystem D from rfl,
    linearSystem_eq_inf hcov D]
  rfl

/-- **The unconditional Čech Euler characteristic.**  On a two-set cover `U₀ ⊔ U₁ = ⊤`,

`χ(D) = dim_k Γ(U₀,𝒪(D)) + dim_k Γ(U₁,𝒪(D)) − dim_k 𝒜(D)`.

**No exactness hypotheses.**  The only inputs are the cover and the finiteness of the two
chart section spaces; `𝒜(D)`'s finiteness follows, since `𝒜(D) ⊇ B(D)` is not needed —
what is needed is that `Ȟ¹(D) = 𝒜(D)/B(D)` is finite-dimensional, which is the binder
`Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)`.

Proof: `ℓ(D) = dim(S₀ ⊓ S₁)` (the cover, `sectionSub_top_eq_inf`) and
`h¹(D) = dim 𝒜(D) − dim(S₀ ⊔ S₁)` (rank–nullity for the quotient `𝒜(D)/B(D)`), so
`χ(D) = dim(S₀ ⊓ S₁) + dim(S₀ ⊔ S₁) − dim 𝒜(D)`, and the modular law
`Submodule.finrank_sup_add_finrank_inf_eq` replaces the first two terms by
`dim S₀ + dim S₁`. -/
theorem chi_eq_charts_sub_overlap (hcov : U₀ ⊔ U₁ = ⊤) (D : X.WeilDivisor)
    [Module.Finite k (sectionSub k U₀ D)] [Module.Finite k (sectionSub k U₁ D)]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)] :
    chi k U₀ U₁ D = (Module.finrank k (sectionSub k U₀ D) : ℤ)
      + Module.finrank k (sectionSub k U₁ D)
      - Module.finrank k (sectionSub k (U₀ ⊓ U₁) D) := by
  classical
  -- `h¹(D) + dim B(D) = dim 𝒜(D)`: rank–nullity for `Ȟ¹(D) = 𝒜(D) / B(D)`.
  have hcob : Module.finrank k (H1Mod k U₀ U₁ D)
      + Module.finrank k (Submodule.comap (sectionSub k (U₀ ⊓ U₁) D).subtype
          (coboundarySub k U₀ U₁ D))
        = Module.finrank k (sectionSub k (U₀ ⊓ U₁) D) :=
    Submodule.finrank_quotient_add_finrank _
  -- The comap of `B(D)` into `𝒜(D)` has the same dimension as `B(D)` itself,
  -- because `B(D) ≤ 𝒜(D)`.
  have hBeq : Module.finrank k (Submodule.comap (sectionSub k (U₀ ⊓ U₁) D).subtype
      (coboundarySub k U₀ U₁ D)) = Module.finrank k (coboundarySub k U₀ U₁ D) :=
    (Submodule.comapSubtypeEquivOfLe (coboundarySub_le_overlap k U₀ U₁ D)).finrank_eq
  -- The modular law for the two chart subspaces.
  have hmod : Module.finrank k (coboundarySub k U₀ U₁ D)
      + Module.finrank k (sectionSub k U₀ D ⊓ sectionSub k U₁ D : Submodule k X.functionField)
        = Module.finrank k (sectionSub k U₀ D) + Module.finrank k (sectionSub k U₁ D) :=
    Submodule.finrank_sup_add_finrank_inf_eq _ _
  -- `ℓ(D) = dim (S₀ ⊓ S₁)` by the cover.
  have hell : ell k D
      = Module.finrank k (sectionSub k U₀ D ⊓ sectionSub k U₁ D : Submodule k X.functionField) := by
    rw [ell, sectionSub_top_eq_inf k U₀ U₁ hcov D]
  rw [hBeq] at hcob
  simp only [chi, h1dim, hell]
  omega

/-- **The unconditional χ-difference formula.**  The χ-jump between any two divisors is
the alternating sum of the two chart steps and the overlap step:

`χ(D') − χ(D) = ΔS₀ + ΔS₁ − Δ𝒜`

where each `Δ` is the difference of the corresponding dimensions.  Again no exactness
hypotheses.  This is the honest replacement for `ChiLedger.chi_add`. -/
theorem chi_sub_chi_eq_charts_sub_overlap (hcov : U₀ ⊔ U₁ = ⊤) (D D' : X.WeilDivisor)
    [Module.Finite k (sectionSub k U₀ D)] [Module.Finite k (sectionSub k U₁ D)]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)]
    [Module.Finite k (sectionSub k U₀ D')] [Module.Finite k (sectionSub k U₁ D')]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) D')] :
    chi k U₀ U₁ D' - chi k U₀ U₁ D =
      ((Module.finrank k (sectionSub k U₀ D') : ℤ) - Module.finrank k (sectionSub k U₀ D))
      + ((Module.finrank k (sectionSub k U₁ D') : ℤ) - Module.finrank k (sectionSub k U₁ D))
      - ((Module.finrank k (sectionSub k (U₀ ⊓ U₁) D') : ℤ)
          - Module.finrank k (sectionSub k (U₀ ⊓ U₁) D)) := by
  rw [chi_eq_charts_sub_overlap k U₀ U₁ hcov D, chi_eq_charts_sub_overlap k U₀ U₁ hcov D']
  ring

/-- **A one-point bump does not change the sections over an open missing that point.**
`Γ(U, 𝒪(1·P + E)) = Γ(U, 𝒪(E))` when `P.point ∉ U`, because `Γ(U, −)` reads the divisor
only at primes meeting `U`.

This is `LedgerClosure.sectionSub_add_pointDivisor_of_notMem_overlap` with the overlap
`U₀ ⊓ U₁` generalised to an arbitrary open — the generalisation is what lets the same
computation be run at *all three* terms of the Čech count below. -/
theorem sectionSub_add_pointDivisor_of_notMem (U : X.Opens)
    {P : X.PrimeDivisor} (hP : P.point ∉ U) (E : X.WeilDivisor) :
    sectionSub k U (pointDivisor P + E) = sectionSub k U E := by
  apply le_antisymm
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    refine Or.inr fun Q hQ => ?_
    have hQP : Q ≠ P := fun h => hP (h ▸ hQ)
    rw [← add_pointDivisor_apply_of_ne E hQP]
    exact ((mem_sectionOfDivisor_of_ne_zero hx0).mp hx) Q hQ
  · exact sectionSub_mono k U (le_add_pointDivisor E P)

/-- **The off-overlap χ-jump is exactly the ONE surviving chart step** — unconditionally.

Let `P.point ∉ U₀`.  Then the bump `E ↦ 1·P + E` leaves both the `U₀` term and the
overlap term of `chi_eq_charts_sub_overlap` untouched (`P.point ∉ U₀` and
`P.point ∉ U₀ ⊓ U₁`), so the entire χ-jump is carried by the `U₁` chart:

`χ(1·P + E) − χ(E) = dim Γ(U₁, 𝒪(1·P+E)) − dim Γ(U₁, 𝒪(E))`.

**Do NOT read this as rescuing `hbump`.**  An earlier version of this docstring did exactly
that: it noted that the surviving chart step is `≥ 0` rather than provably `0`, and concluded
that inbox `I-0449`'s refutation of `hbump` off the overlap had misfired — that the argument
measured `chi_add`'s hypotheses rather than `hbump`.  **That was wrong**, and §5 below proves
the opposite from this file's own formula: `hbump` is refuted off a chart *unconditionally*,
with no `chi_add` and no exactness hypothesis anywhere.  `I-0449` was right, and is now
strengthened from a conditional to an unconditional refutation.

The error is worth naming because it is a general one.  A **one-step** identity constrains
nothing by itself.  The refutation lives in the **tower** `n·P`: iterating this same bump
freezes both `Γ(U₀,−)` (the point is off `U₀`) and `𝒜` (off the overlap), while
`Γ(U₁,−) ⊆ 𝒜` is trapped — so χ is *bounded* along the tower, whereas `hbump` demands growth
`n·[κ(P):k]`.  See `chi_le_finrank_chart_along_tower` and `not_bump_of_notMem_left`. -/
theorem chi_add_pointDivisor_of_notMem_left (hcov : U₀ ⊔ U₁ = ⊤)
    {P : X.PrimeDivisor} (hP : P.point ∉ U₀) (E : X.WeilDivisor)
    [Module.Finite k (sectionSub k U₀ E)] [Module.Finite k (sectionSub k U₁ E)]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) E)]
    [Module.Finite k (sectionSub k U₀ (pointDivisor P + E))]
    [Module.Finite k (sectionSub k U₁ (pointDivisor P + E))]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) (pointDivisor P + E))] :
    chi k U₀ U₁ (pointDivisor P + E) - chi k U₀ U₁ E =
      (Module.finrank k (sectionSub k U₁ (pointDivisor P + E)) : ℤ)
        - Module.finrank k (sectionSub k U₁ E) := by
  have hPinf : P.point ∉ (U₀ ⊓ U₁ : X.Opens) := fun h => hP h.1
  rw [chi_sub_chi_eq_charts_sub_overlap k U₀ U₁ hcov E (pointDivisor P + E),
    sectionSub_add_pointDivisor_of_notMem k U₀ hP E,
    sectionSub_add_pointDivisor_of_notMem k (U₀ ⊓ U₁) hPinf E]
  ring

/-- **Off the overlap, the bump at one step is equivalent to the one-chart step being full.**

For `P.point ∉ U₀`, the bump statement `χ(1·P+E) = χ(E) + [κ(P):k]` holds if and only if
the `U₁`-chart section space grows by exactly `[κ(P):k]`.  Neither direction needs an
exactness hypothesis.

**Read the quantifiers.**  This is an equivalence at a *single* `(P, E)`.  It does **not** say
`hbump` is consistent: `hbump` asserts the left side for *all* `E`, hence at every stage of the
tower `n·P`, and §5 shows the right side must fail for large `n` because `Γ(U₁,−) ⊆ 𝒜` is
frozen there.  An earlier docstring here drew the consistency conclusion from this iff; that
inference is invalid, and `not_bump_of_notMem_left` is the correction. -/
theorem bump_iff_chartStep_of_notMem_left (hcov : U₀ ⊔ U₁ = ⊤)
    {P : X.PrimeDivisor} (hP : P.point ∉ U₀) (E : X.WeilDivisor)
    [Module.Finite k (sectionSub k U₀ E)] [Module.Finite k (sectionSub k U₁ E)]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) E)]
    [Module.Finite k (sectionSub k U₀ (pointDivisor P + E))]
    [Module.Finite k (sectionSub k U₁ (pointDivisor P + E))]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) (pointDivisor P + E))] :
    chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P ↔
      (Module.finrank k (sectionSub k U₁ (pointDivisor P + E)) : ℤ)
        - Module.finrank k (sectionSub k U₁ E) = residueDeg k P := by
  have h := chi_add_pointDivisor_of_notMem_left k U₀ U₁ hcov hP E
  omega

/-! ## §5. `hbump` is refuted off a chart — unconditionally

This section supersedes the reading this file shipped with, and it is the sharp answer to the
question inbox `I-0456` posed ("*where* is the hypothesis false?").

The mechanism is the **tower** `n·P`.  Fix `P.point ∉ U₀`.  Then along `E ↦ n·P + E`:

* `Γ(U₀, −)` is frozen — the point is off `U₀` (`sectionSub_add_pointDivisor_of_notMem`);
* `𝒜 = Γ(U₀ ⊓ U₁, −)` is frozen — the point is off the overlap too;
* `Γ(U₁, −) ⊆ 𝒜` always, since `sectionSub` is antitone in the open.

So all three terms of `chi_eq_charts_sub_overlap` are bounded, giving `χ(n·P + E) ≤ dim Γ(U₀,𝒪(E))`
for **every** `n`.  But `hbump` forces `χ(n·P) = χ(0) + n·[κ(P):k]`, and `[κ(P):k] ≥ 1`
(`one_le_residueDeg`).  Linear growth against a fixed bound is a contradiction.

Credit: found by an adversarial `work-reviewer` audit of this module (inbox `I-0467`/`I-0468`),
which caught this file's own docstrings claiming the opposite.  I verified the argument
independently before landing it. -/

section BumpRefutedOffChart

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X]

/-- **An open missing `P` sees no change along the whole tower `n·P`.**  Iterate
`sectionSub_add_pointDivisor_of_notMem`. -/
theorem sectionSub_divisorOfList_replicate_of_notMem (U : X.Opens)
    {P : X.PrimeDivisor} (hP : P.point ∉ U) (E : X.WeilDivisor) (n : ℕ) :
    sectionSub k U (divisorOfList (List.replicate n P) + E) = sectionSub k U E := by
  induction n with
  | zero => simp only [List.replicate_zero, divisorOfList, zero_add]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [divisorOfList]
    rw [show pointDivisor P + divisorOfList (List.replicate m P) + E
          = pointDivisor P + (divisorOfList (List.replicate m P) + E) by abel,
      sectionSub_add_pointDivisor_of_notMem k U hP, ih]

variable (U₀ U₁ : X.Opens)

/-- **χ is BOUNDED along a tower at a point off one chart.**  `χ(n·P + E) ≤ dim Γ(U₀,𝒪(E))`
for every `n`, when `P.point ∉ U₀`.

Two of the three Čech terms are frozen by the tower and the third is trapped under the
overlap term (`Γ(U₁,−) ⊆ 𝒜`, antitonicity in the open).  No exactness hypothesis. -/
theorem chi_le_finrank_chart_along_tower (hcov : U₀ ⊔ U₁ = ⊤)
    {P : X.PrimeDivisor} (hP : P.point ∉ U₀) (E : X.WeilDivisor)
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₀ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₁ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)]
    (n : ℕ) :
    chi k U₀ U₁ (divisorOfList (List.replicate n P) + E)
      ≤ (Module.finrank k (sectionSub k U₀ E) : ℤ) := by
  have hPinf : P.point ∉ (U₀ ⊓ U₁ : X.Opens) := fun h => hP h.1
  set D := divisorOfList (List.replicate n P) + E with hD
  have h := chi_eq_charts_sub_overlap k U₀ U₁ hcov D
  have hle : Module.finrank k (sectionSub k U₁ D)
      ≤ Module.finrank k (sectionSub k (U₀ ⊓ U₁) D) :=
    Submodule.finrank_mono (sectionSub_antitone_open k inf_le_right D)
  have h0 : sectionSub k U₀ D = sectionSub k U₀ E := by
    rw [hD]; exact sectionSub_divisorOfList_replicate_of_notMem k U₀ hP E n
  rw [h0] at h
  omega

/-- **Chart-level finiteness alone forbids Riemann growth: `ℓ` is BOUNDED along a tower.**

`ℓ(n·P + E) ≤ dim Γ(U₀, 𝒪(E))` for every `n`, whenever `P.point ∉ U₀` and the `U₀`-chart
section spaces are finite-dimensional.  No cover hypothesis, no χ, no exactness datum: it is
`sectionSub k ⊤ D ≤ sectionSub k U₀ D` (antitonicity in the open) composed with the freeze.

**This is the root cause of everything in §5–§6, and it is worth stating separately because it is
stronger and simpler than the χ-level statements.**  Riemann–Roch says `ℓ(D)` grows like
`deg D`; this says it *cannot*, along any tower at a point missing a chart whose sections are
finite-dimensional.  So `Module.Finite k (sectionSub k U D)` at a **non-total** `U` is not
bookkeeping — it is a substantive geometric restriction, and any theorem assuming it over all
divisors has already excluded the curves Riemann–Roch is about.

**How substantive was underestimated here, and the sharp form is not about towers at all.**  This
docstring says the binder "excludes the curves Riemann–Roch is about"; in fact it excludes *every*
curve with a nonconstant function, and needs neither a tower nor a cover to see it.  A single
instance at `D = 0` forces `K(X)/k` finite — `Γ(U,𝒪(0))` is a ring containing `Γ(X,U)`, a
`k`-finite domain is a field, and a field between `Γ(X,U)` and its own fraction field is all of
`K(X)`.  See `ChartFinitenessRefuted.module_finite_functionField_of_chart_finite`, and
`chart_finiteness_iff_module_finite_functionField` for the equivalence.

Consequence for reading this whole module: the `[∀ D, Module.Finite k (sectionSub k Uᵢ D)]`
binders on §5–§6 are what make the refutations available, and a consumer who supplies them has not
merely "chosen the geometry" — it has assumed something false of any curve, so the §5–§6
conclusions do not transfer to a curve.  Tower form found by a fresh-context review of this
module; the field-theoretic sharpening by task `ajc-rr`. -/
theorem ell_le_finrank_chart_along_tower (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ : X.Opens)
    {P : X.PrimeDivisor} (hP : P.point ∉ U₀) (E : X.WeilDivisor)
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₀ D)] (n : ℕ) :
    ell k (divisorOfList (List.replicate n P) + E)
      ≤ Module.finrank k (sectionSub k U₀ E) := by
  have hsub : sectionSub k ⊤ (divisorOfList (List.replicate n P) + E)
      ≤ sectionSub k U₀ (divisorOfList (List.replicate n P) + E) :=
    sectionSub_antitone_open k le_top _
  rw [sectionSub_divisorOfList_replicate_of_notMem k U₀ hP E n] at hsub
  exact Submodule.finrank_mono hsub

/-- **`hbump` is FALSE under this file's chart-finiteness binders**, whenever some prime divisor
sits off one chart of the cover.

No `chi_add`, no exactness hypothesis, no approximation input: `hbump` forces `χ` to grow
linearly along the tower `n·P` while `chi_le_finrank_chart_along_tower` bounds it.

**DO NOT QUOTE THIS AS A REFUTATION AT A CURVE.**  The three
`[∀ D, Module.Finite k (sectionSub k Uᵢ D)]` binders are unsatisfiable there:
`ChartFinitenessRefuted.module_finite_functionField_of_chart_finite` shows one instance of them,
at `D = 0` alone, already forces `K(X)/k` finite.  So on a curve with a nonconstant function this
theorem has no instances and `hbump` is **open**, not false.  What is genuinely refuted is
`hbump` *together with* chart finiteness — and it is the finiteness half that fails.

**This is inbox `I-0449`'s conclusion, strengthened.**  That audit derived the same
incompatibility *conditionally*, from `ChiLedger.chi_add`'s conclusion; an earlier version of
this module claimed on that basis that the audit had measured `chi_add` rather than `hbump`.
The claim was false and is retracted here in Lean rather than only in prose.

Note the reach: `P.point ∉ U₀` (or symmetrically `∉ U₁`) is far weaker than `P.point ∉ U₀ ⊓ U₁`,
so this refutes `hbump` on a *larger* set of primes than `I-0449` addressed.  Together with
`LedgerClosure.chi_eq_of_bump` — which derives the closed ledger *from* `hbump` — the honest
consequence is that the bump route to the ledger is dead for any cover having such a prime,
and consumers must not be pointed at it. -/
theorem not_bump_of_notMem_left (hcov : U₀ ⊔ U₁ = ⊤)
    {P : X.PrimeDivisor} (hP : P.point ∉ U₀)
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₀ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₁ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)]
    [Module.Finite k (localStepTgt k P 1)] :
    ¬ (∀ (Q : X.PrimeDivisor) (E : X.WeilDivisor),
        chi k U₀ U₁ (pointDivisor Q + E) = chi k U₀ U₁ E + residueDeg k Q) := by
  intro hbump
  have hgrow : ∀ n : ℕ,
      chi k U₀ U₁ (divisorOfList (List.replicate n P) + (0 : X.WeilDivisor))
        = chi k U₀ U₁ (0 : X.WeilDivisor) + n * residueDeg k P := by
    intro n
    induction n with
    | zero => simp only [List.replicate_zero, divisorOfList]; ring_nf; rfl
    | succ m ih =>
      rw [List.replicate_succ]
      simp only [divisorOfList]
      rw [show pointDivisor P + divisorOfList (List.replicate m P) + (0 : X.WeilDivisor)
            = pointDivisor P + (divisorOfList (List.replicate m P) + (0 : X.WeilDivisor)) by abel,
        hbump P, ih]
      push_cast; ring
  obtain ⟨n, hn⟩ := exists_nat_gt
    ((Module.finrank k (sectionSub k U₀ (0 : X.WeilDivisor)) : ℤ)
      - chi k U₀ U₁ (0 : X.WeilDivisor))
  have hb := chi_le_finrank_chart_along_tower k U₀ U₁ hcov hP (0 : X.WeilDivisor) n
  rw [hgrow n] at hb
  have hr : (1 : ℤ) ≤ (residueDeg k P : ℤ) := by exact_mod_cast one_le_residueDeg k P
  have hnn : (n : ℤ) ≤ n * residueDeg k P := by nlinarith [Int.natCast_nonneg n]
  omega

end BumpRefutedOffChart

/-! ## §3. Cluster-P consequences that no longer need the ledger

The two statements cluster P actually wants downstream are a **section lower bound**
(Riemann inequality) and an **H¹ vanishing criterion**.  Both follow from the ungated χ
formula without `hledger`, `hbump`, or any exactness hypothesis.  What they still need is
the *geometric* input relating the chart dimensions to `deg D`; that input is isolated as
an explicit hypothesis rather than hidden, and it is the honest residual leaf. -/

/-- **Riemann inequality, gate-free.**  `ℓ(D) ≥ χ(D)` is elementary (`chi_le_ell`), so the
ungated χ formula turns any lower bound on the Čech count into a lower bound on `ℓ(D)`:

`dim Γ(U₀,𝒪(D)) + dim Γ(U₁,𝒪(D)) − dim 𝒜(D) ≤ ℓ(D)`.

Compare `SectionBounds.degK_add_chi_zero_le_ell` and
`BoundedVanishing.exists_bound_ell_eq`, which reach comparable conclusions only under
`hledger`.  Here there is no ledger hypothesis at all; the content has moved into the
computable left-hand side. -/
theorem charts_sub_overlap_le_ell (hcov : U₀ ⊔ U₁ = ⊤) (D : X.WeilDivisor)
    [Module.Finite k (sectionSub k U₀ D)] [Module.Finite k (sectionSub k U₁ D)]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)] :
    (Module.finrank k (sectionSub k U₀ D) : ℤ)
      + Module.finrank k (sectionSub k U₁ D)
      - Module.finrank k (sectionSub k (U₀ ⊓ U₁) D) ≤ (ell k D : ℤ) := by
  rw [← chi_eq_charts_sub_overlap k U₀ U₁ hcov D]
  exact chi_le_ell k U₀ U₁ D

/-- **H¹ vanishing is equivalent to the Čech count being exact** — no gate.

`Ȟ¹(D) = 0` iff `dim Γ(U₀,𝒪(D)) + dim Γ(U₁,𝒪(D)) − dim 𝒜(D) = ℓ(D)`, i.e. iff the
inclusion–exclusion count computes `ℓ(D)` on the nose.

This is the vanishing criterion cluster P needs, and unlike
`BoundedVanishing.subsingleton_h1Mod_iff` (a restatement of `𝒜(D) ⊆ B(D)`) it is a
**numerical** criterion: it can be certified by counting dimensions on the two charts,
which is what an explicit cover computation actually produces.  Note it is a genuine
two-way reduction, not a reformulation of `h1dim = 0` — the right-hand side mentions only
the three chart dimensions and `ℓ`.

**Caveat.**  This is a criterion, not a vanishing theorem: nothing here or elsewhere in AJC
proves its right-hand side at any curve.  Do not read it as closing single-field vanishing.

It is *not*, however, damaged by §5–§6: this statement assumes finiteness at the single divisor
`D` only, and its right-hand side compares the count with `ℓ(D)` rather than with `deg_k D`, so
the tower argument does not touch it (see the discussion at
`exists_bound_h1dim_eq_zero_of_charts`).  Vanishing content survives; it is the ledger's *growth*
claim that the chart-finiteness binders refute. -/
theorem h1dim_eq_zero_iff_charts (hcov : U₀ ⊔ U₁ = ⊤) (D : X.WeilDivisor)
    [Module.Finite k (sectionSub k U₀ D)] [Module.Finite k (sectionSub k U₁ D)]
    [Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)] :
    h1dim k U₀ U₁ D = 0 ↔
      (Module.finrank k (sectionSub k U₀ D) : ℤ)
        + Module.finrank k (sectionSub k U₁ D)
        - Module.finrank k (sectionSub k (U₀ ⊓ U₁) D) = (ell k D : ℤ) := by
  have h := chi_eq_charts_sub_overlap k U₀ U₁ hcov D
  rw [chi] at h
  omega

/-- **Uniform vanishing from a uniform chart count.**  If above some weighted-degree
threshold `b` the Čech count is exact at every divisor, then `h¹` vanishes uniformly above
`b`.  The quantifier structure is the one cluster P's consumers take, and the hypothesis is
now a statement about chart dimensions rather than about a connecting homomorphism.

This is deliberately stated with the finiteness binders as an instance-quantified
hypothesis, matching `ResidueField.UniformlyBoundedVanishing`'s shape, so that a consumer
proving the chart count over a family of divisors gets uniform vanishing directly.

**Is `hcount` refutable by the §5–§6 tower argument?  No — and the reason is the useful part.**
This hypothesis equates the chart count with `ℓ(D)`, and `ell_le_finrank_chart_along_tower` says
`ℓ` is *also* bounded along the tower under these binders.  Bounded = bounded is no
contradiction, so unlike `hledger` — which equates χ with the **unbounded** `deg_k D` — `hcount`
survives the tower.

That contrast is the sharpest available statement of what went wrong with the lane's ledger:
`hcount` and `hledger` both look like "the Čech count is exact", but only the ledger asserts
*growth*.  The vanishing content is safe from the *tower*; the Riemann-growth content is what
these binders forbid.

**BUT THIS THEOREM IS STILL EMPTY AT A CURVE, for the other reason, and the distinction is
worth keeping straight.**  Surviving the tower argument is not the same as being instantiable.
The three `∀ D` chart-finiteness binders it carries are unsatisfiable on a curve outright
(`ChartFinitenessRefuted.not_chart_finite_of_primeDivisor`), so no curve supplies them and this
theorem has no instances there either.  The difference from `hledger` is real but narrower than
it looks: `hledger` is *inconsistent with* the binders, while `hcount` is merely *unavailable
because of* them.  Neither reaches a curve.

**A DEAD END worth recording, because it is the obvious escape and it does not work.**
`h1dim_eq_zero_iff_charts` and `charts_sub_overlap_le_ell` assume finiteness at a *single*
divisor rather than over the family, so they look salvageable by instantiating at
`U₀ = U₁ = ⊤`, where `Module.Finite` is the honest finiteness of `L(D)`.  They are not: at that
cover `𝒜(D) = Γ(⊤,𝒪(D))` too, the count `dim + dim − dim` collapses to `ℓ(D)`, and the
criterion's right-hand side becomes `ℓ(D) = ℓ(D)`.  So `h1dim k ⊤ ⊤ D = 0` follows
*unconditionally* — which is correct (the Čech `H¹` of a one-set cover vanishes) and useless.
Machine-checked, not argued: the proof is `rw [h1dim_eq_zero_iff_charts, ell, inf_idem]; ring`.

So the §3 criteria face a genuine squeeze rather than a fixable defect: at a two-chart cover
their binders are unsatisfiable, and at the degenerate cover their conclusion is vacuous.  What
they need is finiteness of the three chart section spaces at *some* cover that is neither — which
is exactly what `ChartFinitenessRefuted` shows no curve provides at an affine chart.  Anyone
picking this up should treat the two-chart adelic count as the thing to replace, not the
hypothesis to weaken. -/
theorem exists_bound_h1dim_eq_zero_of_charts (hcov : U₀ ⊔ U₁ = ⊤) (b : ℤ)
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₀ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₁ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)]
    (hcount : ∀ D : X.WeilDivisor, b ≤ degK k D →
      (Module.finrank k (sectionSub k U₀ D) : ℤ)
        + Module.finrank k (sectionSub k U₁ D)
        - Module.finrank k (sectionSub k (U₀ ⊓ U₁) D) = (ell k D : ℤ)) :
    ∀ D : X.WeilDivisor, b ≤ degK k D → h1dim k U₀ U₁ D = 0 :=
  fun D hD => (h1dim_eq_zero_iff_charts k U₀ U₁ hcov D).mpr (hcount D hD)

end ChiCharts

/-! ## §6. The closed ledger itself is refuted on such a cover — so the leaf needs a better cover

An earlier §4 of this module defined `ChartCountsDegree` (verbatim the closed ledger) and
derived `deg_k(div g) = 0` from it, advertised as "the principal-divisor leaf with the ledger
removed".  **Both the framing and the theorem have been deleted**, for two independent reasons
found by the audit at inbox `I-0467`:

1. It was a *duplicate*, not a reduction.  `ChartCountsDegree` was `Iff.rfl` to `hledger`, and
   `SectionBounds.degK_principal_eq_zero` already accepts that hypothesis verbatim — so the new
   theorem was the old one with a renamed hypothesis.  Admitting in a docstring that a
   restatement is a restatement does not make it worth adding; `I-0456`'s lesson is to delete or
   fold, not to relabel.
2. It was *vacuous on the covers this file is about*.  `ledger_refuted_of_notMem_left` below
   shows the ledger is false whenever a prime divisor lies off one chart **and the chart section
   spaces are finite-dimensional** — the same tower argument as §5, since `deg_k` grows linearly
   along `n·P` while χ stays bounded.  (Reason 1 is unaffected by the 2026-07-28 correction and
   is by itself sufficient for the deletion.  Reason 2 is weaker than it reads: those covers do
   not exist on a curve — see the module header and `ChartFinitenessRefuted.lean`.)

What survives is sharper than what was deleted, and it is a genuine constraint on the route
rather than a theorem about it. -/

section LedgerRefuted

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **The closed ledger is FALSE if any prime divisor lies off one chart of the cover.**

`deg_k` grows linearly along the tower `n·P` (it is additive with
`deg_k P = [κ(P):k] ≥ 1`), while `chi_le_finrank_chart_along_tower` bounds χ there.  So
`χ(D) = χ(0) + deg_k D` cannot hold at every `D`.

**Consequence for the lane — with the quantifiers stated exactly, because they matter.**  Every
conditional statement in `SectionBounds.lean` §3, `BoundedVanishing.lean` and
`GlobalGeneration.lean` takes this same `hledger`.  Where those consumers *also* satisfy this
theorem's two extra hypotheses, their `hledger` is unsatisfiable and they are vacuous.

The two extra hypotheses are **not** automatic, and it would be an overclaim to drop them:

* `hcov : U₀ ⊔ U₁ = ⊤`.  The consumers do **not** assume it — they are stated for arbitrary
  `U₀ U₁`.  Without a cover, `chi` is not computing a Čech Euler characteristic and this
  argument says nothing.
* the three `∀ D, Module.Finite k (sectionSub k · D)` instances.  The consumers assume finiteness
  only at `⊤` (`Module.Finite k (sectionSub k ⊤ D)`), never at the charts.  As the module header
  notes, chart-level finiteness at a non-total open is a real restriction — it is what forbids
  Riemann growth along the tower.

So the honest statement is: **on a genuine two-chart cover whose chart section spaces are all
finite-dimensional, and which has a prime divisor off a chart, the ledger is false and the lane's
conditional results are vacuous.**

**AND NO CURVE MEETS THAT DESCRIPTION** — settled after this docstring was written, by
`Adelic/ChartFinitenessRefuted.lean`.  The sentence above asked "whether a given curve's cover
meets that description is not settled here"; the answer is *none does*, for a reason having
nothing to do with covers.  One instance of the chart-finiteness binder, at `D = 0` alone, forces
`K(X)/k` finite (`module_finite_functionField_of_chart_finite`), and the binder is *equivalent* to
that (`chart_finiteness_iff_module_finite_functionField`).  So on a curve with a nonconstant
function this theorem is instance-free and refutes nothing there: `hledger` is **open** at a
curve, and the lane's `hledger`-conditional results are **not** shown vacuous.

The last two sentences of the previous paragraph were the actively misleading part and are
withdrawn: "the fix is a different cover hypothesis, or more charts" pointed the next session at a
non-problem.  There is no cover to find.  The genuine open question is the ledger itself, and the
route with real evidence behind it is the sibling project's dévissage-over-closed-points proof
(`Algebraic-Jacobian-Challenge-Rebuild`, `RiemannRoch/ChiLedger.lean`, sorry-free), which uses no
chart-finiteness binder at all. -/
theorem ledger_refuted_of_notMem_left (hcov : U₀ ⊔ U₁ = ⊤)
    {P : X.PrimeDivisor} (hP : P.point ∉ U₀)
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₀ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₁ D)]
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k (U₀ ⊓ U₁) D)]
    [Module.Finite k (localStepTgt k P 1)] :
    ¬ (∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D) := by
  intro hledger
  have hdeg : ∀ n : ℕ, degK k (divisorOfList (List.replicate n P) + (0 : X.WeilDivisor))
      = n * residueDeg k P := by
    intro n
    rw [add_zero, degK_divisorOfList]
    simp [List.map_replicate, List.sum_replicate]
  obtain ⟨n, hn⟩ := exists_nat_gt
    ((Module.finrank k (sectionSub k U₀ (0 : X.WeilDivisor)) : ℤ)
      - chi k U₀ U₁ (0 : X.WeilDivisor))
  have hb := chi_le_finrank_chart_along_tower k U₀ U₁ hcov hP (0 : X.WeilDivisor) n
  rw [hledger (divisorOfList (List.replicate n P) + (0 : X.WeilDivisor)), hdeg n] at hb
  have hr : (1 : ℤ) ≤ (residueDeg k P : ℤ) := by exact_mod_cast one_le_residueDeg k P
  have hnn : (n : ℤ) ≤ n * residueDeg k P := by nlinarith [Int.natCast_nonneg n]
  omega

end LedgerRefuted

end Adelic
end AlgebraicGeometry
