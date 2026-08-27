/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.ChiUnconditional

/-!
# Chart finiteness is not a restriction — it is UNSATISFIABLE on a curve

`ChiUnconditional.lean` refutes the one-point bump `hbump` and the closed χ-ledger `hledger`
on any two-set cover having a prime divisor off one chart.  Both refutations carry the binder

`[∀ D : X.WeilDivisor, Module.Finite k (sectionSub k U₀ D)]`

at a **non-total** open `U₀`, and that file's `ell_le_finrank_chart_along_tower` describes it
as "a substantive geometric restriction" which "has already excluded the curves
Riemann–Roch is about".  `WeilDivisor.lean:1271-1280` reads the same binder as ruling out
"a class of covers, not the ledger", and concludes the open work is to *exhibit a cover on
which the ledger can hold*.

**This file shows there is no such cover, and the reason is one step of commutative algebra
rather than anything about covers.**  A single instance of the binder — at the zero divisor
alone, not the whole family — already forces `K(X)` to be a finite extension of `k`:

`Adelic.module_finite_functionField_of_chart_finite`:
  `Module.Finite k (sectionSub k U 0) → Module.Finite k K(X)`, for a nonempty affine `U`.

The mechanism: `sectionSub k U 0` is exactly the set of rational functions with
`ord_P ≥ 0` at every prime divisor meeting `U`.  That set is a **subring** (orders add under
multiplication, `sectionSub_mul_mem_zero`) and it **contains the chart ring** `Γ(X, U)`
(chart-integral elements have nonnegative order, `order_algebraMap_chart_nonneg`).  A
`k`-finite domain is a field (`fieldOfFiniteDimensional`), and a subfield of `K(X)`
containing `Γ(X, U)` — whose fraction field is `K(X)` (`chartRing_isFractionRing`) — is all
of `K(X)`.

## Why this sharpens the refutations rather than weakening them

The refutations of `hbump`/`hledger` remain true and remain proved.  What changes is their
**reading**.  They were presented as "the ledger is false on covers of this kind, so look for
a better cover".  The honest reading is stronger and simpler:

* On a curve with a nonconstant function, `K(X)/k` is *not* finite (a nonconstant function is
  transcendental over the constants), so the chart-finiteness binder is **satisfied at no
  such curve, on any cover, with any charts**.  Hence the §5–§6 refutations of
  `ChiUnconditional.lean` are — on a curve — refutations with unsatisfiable hypotheses.
* So the bump route is not "dead on bad covers"; the *refutation* of it is vacuous on curves.
  Neither `hbump` nor `hledger` has been shown false at a curve. They are **open**, not
  refuted, and the search for "a cover on which the ledger can hold" is not the open problem.

This is trap (c) of `scripts/axiom-frontier.lean` applied to a *negative* result, which is the
case the trap catalogue did not cover: a refutation whose own hypotheses are unsatisfiable
tells you nothing about the statement it refutes.  Both the refutation and its retraction
report clean axioms.

`chart_finiteness_iff_module_finite_functionField` states the equivalence, so the binder is
visibly interchangeable with a hypothesis about `k ⊆ K(X)` alone — no cover, no charts, no
divisors.

## The `⊤` binders used everywhere else in the lane are NOT affected — and here is why

This matters more than the negative result itself, because if the argument reached `⊤` it would
demolish `GlobalGeneration.lean`, `LedgerClosure.lean` and `SectionBounds.lean` as well, all of
which assume `Module.Finite k (sectionSub k ⊤ D)`.  The dividing line is visible in the
signature: **`IsAffineOpen U` is load-bearing**, used exactly once, for
`chartRing_isFractionRing` — the step that identifies `K(X)` as the fraction field of the chart
ring.

**The precise statement, and it is NOT "⊤ is safe".**  What decides the matter is whether `⊤` is
affine, i.e. whether `X` is affine — *not* whether `U` is written `⊤`:

* On a **proper** curve `⊤` is not affine, so `chartRing_isFractionRing` is unavailable and **this
  derivation** does not run.  Stated carefully, because the careless version is the error this
  whole module is about: what is established there is the *absence of this route*, not the
  satisfiability of the binder.  Nothing here proves `Module.Finite k (sectionSub k ⊤ D)` holds at
  a proper curve — that is finiteness of `L(D)`, which is Riemann–Roch's own content and is open
  in AJC.  So the honest statement is "not refuted by this argument", not "survives".
* On an **affine** `X` with a prime divisor, `isAffineOpen_top` applies and
  `not_chart_finite_of_primeDivisor` kills the `⊤` binder as well.  Machine-checked, not
  reasoned: `not_chart_finite_of_primeDivisor k (isAffineOpen_top X) P` elaborates.

That second bullet is a real caveat rather than a curiosity, because the consumers in
`GlobalGeneration.lean`, `LedgerClosure.lean` and `SectionBounds.lean` are stated for a **bare
`Scheme X`** with no `IsProper` binder anywhere.  So their `⊤` binders are unsatisfiable on the
affine members of the family they quantify over, and no docstring in that lane says so.

**What is proved and what is not, kept apart — a fresh-context review caught an earlier version
of this section presenting the second as the first.**

* PROVED: on an affine `X` with a prime divisor, the `⊤` binder fails
  (`not_chart_finite_top_of_isAffine`).
* NOT PROVED, and not provable here: that the `⊤` binder *holds* at a proper curve.  That is
  finiteness of `L(D)` — Riemann–Roch's own content, and open in AJC.  All this module gives at a
  proper curve is that *its* argument does not apply.  "Not refuted by this route" is the claim;
  "survives", "is fine", or "is safe" would all be stronger than anything checked.

The asymmetry worth carrying, stated at that strength: `Module.Finite k (sectionSub k U D)` at an
affine chart is a **disguised finiteness of `K(X)/k`**, which is false — that is a theorem.
`Module.Finite k (sectionSub k ⊤ D)` at a proper curve is finiteness of `L(D)`, which is what one
wants to be true and which this module says nothing about either way.

`ell_le_finrank_chart_along_tower` is the one to compare: it needs no cover and no affineness, so
it applies at any `U`, but its *conclusion* is vacuous when `U = ⊤` (`ℓ(D) ≤ ℓ(E)` with the tower
frozen is then no restriction at all). The bite comes only from a non-total open, which is
precisely where affineness is available and the binder collapses.

## What this file does NOT claim

It does not prove `hbump` or `hledger` — those are now *open* at a curve rather than refuted,
which is a statement about the state of knowledge, not a proof of either.

**The residual input IS discharged, and more cheaply than first expected.**  An earlier
version of this header said proving `K(X)/k` infinite "needs a nonconstant rational function,
which is `NonconstantToP1.lean` territory and is not wired in here".  That turned out to be
unnecessary: `not_module_finite_functionField_of_primeDivisor` gets it from the existence of a
**single prime divisor**, with no polynomial argument and no morphism to `ℙ¹`.  The DVR stalk
`𝒪_P` sits between `k` and `K(X)`; finiteness would make it a `k`-finite domain, hence a field,
and `exists_order_eq` produces an element of order `1` whose inverse has order `-1` and so
cannot lie in it.  A discrete valuation ring is not a field.

So `not_chart_finite_of_primeDivisor` is the unconditional statement: on a curve with a prime
divisor and a nonempty affine chart, the binder holds nowhere.  The
`_of_transcendental` variants are kept as the general field-theoretic form.

## The three cluster-P gaps, kept apart

Unchanged by this file, and this file touches only the first:

* **Single-field vanishing** — open. This file removes a *false lead* (repairing the cover)
  rather than supplying vanishing.
* **Extension uniformity** — untouched. Still `UniformChartVanishing.UniformChartCount`,
  proved at no curve, strictly stronger than the single-field count.
* **Global generation** — untouched. Still ledger-conditional in `GlobalGeneration.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

section ChartFiniteness

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X]

/-- **A stalk-integral rational function has nonnegative order.**  The converse of
`ChiLedger.exists_stalk_lift_of_order_nonneg`: mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation_le_one` says the adic valuation of an element of
the ring is `≤ 1`, and `ord_P = -log ∘ v_P` (`order_eq_neg_log_pointValuation`) turns that into
`ord_P ≥ 0`. -/
theorem order_algebraMap_stalk_nonneg {P : X.PrimeDivisor}
    (a : X.presheaf.stalk P.point) :
    0 ≤ Scheme.RationalMap.order P
      (algebraMap (X.presheaf.stalk P.point) X.functionField a) := by
  set f := algebraMap (X.presheaf.stalk P.point) X.functionField a with hfdef
  have hle1 : pointValuation P f ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  rw [order_eq_neg_log_pointValuation]
  rcases eq_or_ne (pointValuation P f) 0 with h0 | h0
  · rw [h0]; simp
  · have hlog : WithZero.log (pointValuation P f) ≤ WithZero.log (1 : ℤᵐ⁰) :=
      (WithZero.log_le_log h0 one_ne_zero).mpr hle1
    rw [WithZero.log_one] at hlog
    linarith

/-- **A chart section has nonnegative order at every prime divisor meeting the chart.**
Factor `algebraMap Γ(X, U) K(X)` through the stalk at `Y.point` (`functionField_isScalarTower`)
and apply `order_algebraMap_stalk_nonneg`.  Note no affineness hypothesis is needed: the
scalar tower through the stalk exists for any open containing the point. -/
theorem order_algebraMap_chart_nonneg {U : X.Opens} [Nonempty U]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U) (r : Γ(X, U)) :
    0 ≤ Scheme.RationalMap.order Y (algebraMap Γ(X, U) X.functionField r) := by
  letI algSt : Algebra Γ(X, U) (X.presheaf.stalk Y.point) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨Y.point, hYU⟩
  haveI hst : IsScalarTower Γ(X, U) (X.presheaf.stalk Y.point) X.functionField :=
    AlgebraicGeometry.functionField_isScalarTower X U ⟨Y.point, hYU⟩
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk Y.point) X.functionField r]
  exact order_algebraMap_stalk_nonneg _

/-- **The chart ring lands in `Γ(U, 𝒪(0))`.**  Immediate from
`order_algebraMap_chart_nonneg`: membership in `sectionSub k U 0` asks for
`-0 ≤ ord_P` at each prime meeting `U`. -/
theorem algebraMap_chart_mem_sectionSub_zero {U : X.Opens} [Nonempty U] (r : Γ(X, U)) :
    algebraMap Γ(X, U) X.functionField r ∈ sectionSub k U (0 : X.WeilDivisor) := by
  rcases eq_or_ne (algebraMap Γ(X, U) X.functionField r) 0 with h0 | h0
  · rw [h0]; exact Submodule.zero_mem _
  refine Or.inr fun P hP => ?_
  change -((0 : X.PrimeDivisor →₀ ℤ) P) ≤ _
  simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
  exact order_algebraMap_chart_nonneg P hP r

/-- **`Γ(U, 𝒪(0))` is closed under multiplication.**  Orders add
(`order_mul_of_ne_zero`), so two functions with nonnegative order at each prime meeting `U`
have a product with the same property.  This is what makes the section space at the *zero*
divisor a ring, and it is the step that turns a finiteness binder into a field. -/
theorem sectionSub_mul_mem_zero (U : X.Opens) {f g : X.functionField}
    (hf : f ∈ sectionSub k U (0 : X.WeilDivisor))
    (hg : g ∈ sectionSub k U (0 : X.WeilDivisor)) :
    f * g ∈ sectionSub k U (0 : X.WeilDivisor) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp only [zero_mul]; exact Submodule.zero_mem _
  rcases eq_or_ne g 0 with rfl | hg0
  · simp only [mul_zero]; exact Submodule.zero_mem _
  refine Or.inr fun P hP => ?_
  rw [Scheme.RationalMap.order_mul_of_ne_zero P hf0 hg0]
  have h1 := (mem_sectionOfDivisor_of_ne_zero hf0).mp hf P hP
  have h2 := (mem_sectionOfDivisor_of_ne_zero hg0).mp hg P hP
  change -((0 : X.PrimeDivisor →₀ ℤ) P) ≤ _ at h1 h2
  change -((0 : X.PrimeDivisor →₀ ℤ) P) ≤ _
  simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at h1 h2 ⊢
  linarith

/-- **`Γ(U, 𝒪(0))` as a `k`-subalgebra of the function field.**  The multiplicative closure
`sectionSub_mul_mem_zero` plus `1 ∈ Γ(U, 𝒪(0))` upgrade the `k`-submodule to a subalgebra.
Its being a *ring* is what converts a finiteness binder into a field, which is the whole
mechanism of this file. -/
def chartAlg (U : X.Opens) : Subalgebra k X.functionField where
  carrier := sectionSub k U (0 : X.WeilDivisor)
  mul_mem' := sectionSub_mul_mem_zero k U
  one_mem' := one_mem_sectionOfDivisor_zero U
  add_mem' := (sectionSub k U (0 : X.WeilDivisor)).add_mem
  zero_mem' := (sectionSub k U (0 : X.WeilDivisor)).zero_mem
  algebraMap_mem' := fun c => by
    have h1 : (1 : X.functionField) ∈ sectionSub k U (0 : X.WeilDivisor) :=
      one_mem_sectionOfDivisor_zero U
    have := (sectionSub k U (0 : X.WeilDivisor)).smul_mem c h1
    rwa [Algebra.smul_def, mul_one] at this

@[simp] theorem mem_chartAlg {U : X.Opens} {f : X.functionField} :
    f ∈ chartAlg k U ↔ f ∈ sectionSub k U (0 : X.WeilDivisor) := Iff.rfl

/-- **If `Γ(U, 𝒪(0))` is a field, it is the whole function field.**  On a nonempty affine
chart, `K(X) = Frac Γ(X, U)` (`chartRing_isFractionRing`), so every `f : K(X)` is `a/b` with
`a, b ∈ Γ(X, U) ⊆ chartAlg`.  Inside a field, `b⁻¹` is available, so `f = a·b⁻¹` lies in
`chartAlg` too. -/
theorem chartAlg_eq_top_of_isField {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (hfield : IsField (chartAlg k U)) : chartAlg k U = ⊤ := by
  haveI hfr : IsFractionRing Γ(X, U) X.functionField := chartRing_isFractionRing hU
  refine Algebra.eq_top_iff.mpr fun f => ?_
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) f
  have ha' : algebraMap Γ(X, U) X.functionField a ∈ chartAlg k U :=
    algebraMap_chart_mem_sectionSub_zero k a
  have hb' : algebraMap Γ(X, U) X.functionField b ∈ chartAlg k U :=
    algebraMap_chart_mem_sectionSub_zero k b
  have hbne : algebraMap Γ(X, U) X.functionField b ≠ 0 := fun h =>
    (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩) (IsFractionRing.to_map_eq_zero_iff.mp h)
  obtain ⟨c, hc⟩ := hfield.mul_inv_cancel (a := (⟨_, hb'⟩ : chartAlg k U))
    (by simpa [Subtype.ext_iff] using hbne)
  have hbinv : (algebraMap Γ(X, U) X.functionField b)⁻¹ ∈ chartAlg k U := by
    have hval : algebraMap Γ(X, U) X.functionField b * (c : X.functionField) = 1 := by
      have := congrArg (fun z : chartAlg k U => (z : X.functionField)) hc
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hval]; exact c.2
  rw [← hab, div_eq_mul_inv]
  exact Subalgebra.mul_mem _ ha' hbinv

/-- **THE MAIN RESULT — chart finiteness at the ZERO divisor already forces `K(X)/k` finite.**

One instance of the binder that `ChiUnconditional.lean`'s refutations quantify over the whole
divisor family — `Module.Finite k (sectionSub k U 0)` at a single nonempty affine chart — is
enough to collapse the function field onto a finite extension of `k`.

Chain: `Γ(U, 𝒪(0))` is a `k`-finite domain (`chartAlg`), hence a field
(`fieldOfFiniteDimensional`); a field between `Γ(X, U)` and its own fraction field is
everything (`chartAlg_eq_top_of_isField`); so `K(X)` *is* that finite `k`-module.

**Why this is the sharp statement.** `ell_le_finrank_chart_along_tower` says chart finiteness
bounds `ℓ` along a tower and calls that "a substantive geometric restriction". It is not a
restriction on the *cover* at all — no cover appears in this statement. It is a restriction on
`k ⊆ K(X)`, which no choice of charts can change. -/
theorem module_finite_functionField_of_chart_finite {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] (hfin : Module.Finite k (sectionSub k U (0 : X.WeilDivisor))) :
    Module.Finite k X.functionField := by
  haveI hfd : FiniteDimensional k (chartAlg k U) := hfin
  have htop : chartAlg k U = ⊤ :=
    chartAlg_eq_top_of_isField k hU (fieldOfFiniteDimensional k (chartAlg k U)).toIsField
  exact Module.Finite.equiv
    ((Subalgebra.equivOfEq _ _ htop).toLinearEquiv.trans
      (Subalgebra.topEquiv (R := k) (A := X.functionField)).toLinearEquiv)

/-- **The binder is EQUIVALENT to a statement with no cover, no chart and no divisor in it.**
Forward is `module_finite_functionField_of_chart_finite`; backward, a `k`-submodule of a
`k`-finite space is `k`-finite.  Stating the equivalence is the point: it makes visible that
supplying the chart-finiteness binder is *exactly* assuming `K(X)/k` finite, and therefore that
no cleverness about covers or charts can ever satisfy it on a curve. -/
theorem chart_finiteness_iff_module_finite_functionField {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    Module.Finite k (sectionSub k U (0 : X.WeilDivisor)) ↔ Module.Finite k X.functionField := by
  refine ⟨fun h => module_finite_functionField_of_chart_finite k hU h, fun h => ?_⟩
  exact Module.Finite.of_injective (sectionSub k U (0 : X.WeilDivisor)).subtype
    Subtype.val_injective

omit [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X] [IsConstantField k X] in
/-- **What closing this costs, as one hypothesis.**  If some `f : K(X)` is transcendental over
`k` then `K(X)/k` is not finite, so — by
`chart_finiteness_iff_module_finite_functionField` — the chart-finiteness binder fails at
*every* nonempty affine chart, and with it every §5–§6 refutation of `ChiUnconditional.lean`.

The hypothesis is exactly "the curve has a nonconstant function". AJC constructs such a
function in `NonconstantToP1.lean` for its own curve; wiring that in is downstream of this
module and is deliberately left as this named input rather than assumed here.

Pure field theory — no geometry is used, hence the `omit`. -/
theorem not_module_finite_functionField_of_transcendental
    (f : X.functionField) (hf : ¬ IsAlgebraic k f) :
    ¬ Module.Finite k X.functionField := fun hfin => by
  haveI : FiniteDimensional k X.functionField := hfin
  exact hf (Algebra.IsIntegral.isIntegral f).isAlgebraic

/-- **The order-nonnegative subring at a prime divisor `P`, as a `k`-subalgebra of `K(X)`.**
This is the DVR stalk `𝒪_P` seen inside the function field. `sectionSub k U 0` is the
intersection of these over the primes meeting `U`; this is the single-prime version, and it is
what makes the residual input of this file discharge with no transcendence hypothesis. -/
def valSubalg (P : X.PrimeDivisor) : Subalgebra k X.functionField where
  carrier := orderGeSub k P 0
  mul_mem' := by
    intro f g hf hg
    rcases eq_or_ne f 0 with rfl | hf0
    · simp only [zero_mul]; exact Submodule.zero_mem _
    rcases eq_or_ne g 0 with rfl | hg0
    · simp only [mul_zero]; exact Submodule.zero_mem _
    refine Or.inr ?_
    rw [Scheme.RationalMap.order_mul_of_ne_zero P hf0 hg0]
    have h1 := (mem_orderGe_of_ne_zero hf0).mp hf
    have h2 := (mem_orderGe_of_ne_zero hg0).mp hg
    linarith
  one_mem' := Or.inr (by rw [Scheme.RationalMap.order_one])
  add_mem' := (orderGeSub k P 0).add_mem
  zero_mem' := (orderGeSub k P 0).zero_mem
  algebraMap_mem' := fun c => by
    have h1 : (1 : X.functionField) ∈ orderGeSub k P 0 :=
      Or.inr (by rw [Scheme.RationalMap.order_one])
    have := (orderGeSub k P 0).smul_mem c h1
    rwa [Algebra.smul_def, mul_one] at this

/-- **`K(X)/k` IS NOT FINITE as soon as ONE prime divisor exists — no transcendence
hypothesis needed.**

This discharges the residual input of this module outright.  The argument needs no polynomial
and no nonconstant morphism: if `K(X)/k` were finite then the order-nonnegative subring `𝒪_P`
(`valSubalg`) would be a `k`-finite domain, hence a **field** — but `exists_order_eq` supplies
`t` with `ord_P t = 1`, and `t · u = 1` forces `ord_P u = -1 < 0`, contradicting membership in
`𝒪_P`.  In one line: *a discrete valuation ring is not a field, and finiteness over `k` would
make it one.*

The hypothesis "some prime divisor exists" is exactly what
`Scheme.IsRegularInCodimensionOne` is about, and it is far weaker than a nonconstant map to
`ℙ¹`: a curve without prime divisors has nothing for `sectionSub` to read. -/
theorem not_module_finite_functionField_of_primeDivisor (P : X.PrimeDivisor) :
    ¬ Module.Finite k X.functionField := by
  intro hfin
  haveI : FiniteDimensional k X.functionField := hfin
  haveI : FiniteDimensional k (valSubalg k P) :=
    Module.Finite.of_injective (valSubalg k P).toSubmodule.subtype Subtype.val_injective
  have hfield : IsField (valSubalg k P) := (fieldOfFiniteDimensional k (valSubalg k P)).toIsField
  obtain ⟨t, ht0, ht⟩ := exists_order_eq P 1
  have htmem : t ∈ valSubalg k P := Or.inr (by rw [ht]; norm_num)
  obtain ⟨u, hu⟩ := hfield.mul_inv_cancel (a := (⟨t, htmem⟩ : valSubalg k P))
    (by simp only [ne_eq, Subtype.ext_iff]; exact ht0)
  have hval : t * (u : X.functionField) = 1 := by
    have := congrArg (fun z : valSubalg k P => (z : X.functionField)) hu
    simpa using this
  have hu0 : (u : X.functionField) ≠ 0 := by
    intro h; rw [h, mul_zero] at hval; exact one_ne_zero hval.symm
  have hsum : Scheme.RationalMap.order P t
      + Scheme.RationalMap.order P (u : X.functionField) = 0 := by
    rw [← Scheme.RationalMap.order_mul_of_ne_zero P ht0 hu0, hval,
      Scheme.RationalMap.order_one]
  have huge : 0 ≤ Scheme.RationalMap.order P (u : X.functionField) :=
    (mem_orderGe_of_ne_zero hu0).mp u.2
  rw [ht] at hsum
  omega

/-- **THE UNCONDITIONAL FORM: the refutations' binder is satisfiable at NO curve with a prime
divisor.**  No transcendence hypothesis, no nonconstant map, no cover condition — a single
prime divisor plus a nonempty affine chart is enough.

Combined with `ChiUnconditional.not_bump_of_notMem_left` and `ledger_refuted_of_notMem_left`
— whose hypotheses this contradicts — the conclusion is that those two theorems have **no
instances** on such a curve.  `hbump` and the closed χ-ledger are therefore **open** there,
not false, and the "find a better cover" reading of them is void. -/
theorem not_chart_finite_of_primeDivisor {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (P : X.PrimeDivisor) :
    ¬ Module.Finite k (sectionSub k U (0 : X.WeilDivisor)) := fun hfin =>
  not_module_finite_functionField_of_primeDivisor k P
    (module_finite_functionField_of_chart_finite k hU hfin)

/-- **On an AFFINE `X`, even the `⊤` binder collapses** — so "state it at `⊤`" is only safe when
`⊤` fails to be affine, i.e. when `X` is non-affine (in the intended application, proper).

This is the sharp form of the scope caveat in the module docstring, and it is stated as a theorem
because the prose version invites exactly the wrong summary ("`⊤` is safe").  What is safe is
*non-affineness*, not the symbol `⊤`.

Consequence a consumer should know: `GlobalGeneration.lean`, `LedgerClosure.lean` and
`SectionBounds.lean` assume `Module.Finite k (sectionSub k ⊤ D)` over a **bare `Scheme X`** with
no `IsProper` binder, so at the affine members of that family their hypotheses are unsatisfiable
and their conclusions vacuous.  At a proper curve this argument does not apply — which is *not*
the same as the binder holding there; that is finiteness of `L(D)`, open in AJC. -/
theorem not_chart_finite_top_of_isAffine [IsAffine X] [Nonempty (X : Type u)]
    (P : X.PrimeDivisor) :
    ¬ Module.Finite k (sectionSub k (⊤ : X.Opens) (0 : X.WeilDivisor)) := by
  haveI : Nonempty ((⊤ : X.Opens) : Type u) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (X : Type u)); exact ⟨⟨x, trivial⟩⟩
  exact not_chart_finite_of_primeDivisor k (isAffineOpen_top X) P

/-- **The refutations' binder is unsatisfiable on a curve with a nonconstant function.**  The
contrapositive form a consumer wants: no nonempty affine chart of such a curve has
finite-dimensional `Γ(U, 𝒪(0))`, so `ChiUnconditional.not_bump_of_notMem_left` and
`ledger_refuted_of_notMem_left` have unsatisfiable hypotheses there and refute nothing about a
curve. `hbump` and the closed ledger are **open** at a curve, not false. -/
theorem not_chart_finite_of_transcendental {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) (hf : ¬ IsAlgebraic k f) :
    ¬ Module.Finite k (sectionSub k U (0 : X.WeilDivisor)) := fun hfin =>
  not_module_finite_functionField_of_transcendental k f hf
    (module_finite_functionField_of_chart_finite k hU hfin)

end ChartFiniteness

end Adelic
end AlgebraicGeometry
