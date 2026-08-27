/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.GlobalGeneration

/-!
# Adelic Riemann–Roch — closing the ledger from the one-point bump

Every conditional statement of the vanishing and generation lane
(`Adelic/SectionBounds.lean` §3, `Adelic/BoundedVanishing.lean`,
`Adelic/GlobalGeneration.lean`) takes the **closed ledger**

`hledger : ∀ D : X.WeilDivisor, χ(D) = χ(0) + deg_k D`

as a hypothesis quantified over **all** Weil divisors.  `chi_telescope_list` establishes
it for *effective* divisors from the one-point bump, and the sibling docstrings recorded
"extending from list-effective divisors to all divisors additionally needs the negative
part" as an open item.

**This file closes that extension.**  `chi_eq_of_bump` proves the ledger at every Weil
divisor from the one-point bump alone, so `hledger` is not an independent open input of the
lane: every consumer that takes it can instead take `hbump`.  But `hbump` is
NOT merely one application of `chi_add_eq_residueDeg` per step: that theorem
requires `P.point ∈ U₀ ⊓ U₁`, so **off the overlap it supplies no route to the bump at
all**.  See §5.

**`hbump` IS FALSE, and so is the ledger it yields (later session).**  §5 below records the
refutation conditionally; `Adelic/ChiUnconditional.lean` §5–§6 now prove it **unconditionally**:

* `ChiUnconditional.not_bump_of_notMem_left` — `hbump` is false whenever some prime divisor's
  point lies off a chart (weaker, hence more often applicable, than off the *overlap*);
* `ChiUnconditional.ledger_refuted_of_notMem_left` — the closed ledger `hledger` is itself
  false there.

Both carry two side conditions this file does not assume: a genuine cover `U₀ ⊔ U₁ = ⊤`, and
finite-dimensionality of all three *chart* section spaces (not merely at `⊤`).  So they say which
covers are unusable rather than refuting the hypotheses outright for arbitrary `U₀ U₁`.

The mechanism is the tower `n·P`: `Γ(U₀,−)` and `𝒜` freeze while `Γ(U₁,−) ⊆ 𝒜` is trapped, so
χ is *bounded*, against the linear growth `hbump`/`hledger` demand.

**So `chi_eq_of_bump` below, while correct, must not be advertised as a route to the ledger.**
It derives a false conclusion from a false hypothesis on any such cover.  What the lane needs
is a cover hypothesis excluding those primes (or more charts) — not further work on the bump.
(An intermediate version of this note claimed the opposite, that `hbump` was *not* refutable
off the overlap; that was this session's own error, retracted.)

## What is proved

* `chi_eq_of_bump_of_nonneg` — the ledger at **every effective divisor**, with the list
  eliminated from the statement (every effective divisor is list-effective,
  `exists_divisorOfList_of_nonneg`, so a consumer no longer has to produce a list).
* `chi_telescope_list_add` — the telescope run from an **arbitrary base divisor**, not
  only from `0`.
* `chi_eq_of_bump` — **the closed ledger, at every Weil divisor**, from the bump alone.

## The negative part costs nothing, and why this file previously said otherwise

An earlier version of this module — and the sibling docstrings in `SectionBounds.lean`,
`BoundedVanishing.lean` and `ResidueField.lean` — recorded the extension from the effective
cone to all divisors as **open**, "needing an input the lane does not have".  That was
false, and the error is worth stating precisely, because it survived three sessions and
shaped their plans.

The reasoning was: write `D = D⁺ − (−D)⁺` as a difference of effective divisors; the
effective case handles each piece; but `χ` is **not additive** in the divisor, and `D` is
**not linearly equivalent** to `D⁺` in general, so neither of the lane's two transport
mechanisms moves `χ` across the decomposition.  Every clause of that is true — and
irrelevant, because no transport is needed.  `hbump` is quantified over **every** base
divisor `E`, not only over effective ones, so the telescope is not confined to the effective
cone: read the same identity as `D⁺ = (−D)⁺ + D`, i.e. the effective divisor `(−D)⁺`
telescoped **onto the base `D`**, and `chi_telescope_list_add` computes `χ(D⁺)` from `χ(D)`
in one induction.  Comparing with the effective-cone value of `χ(D⁺)` gives the ledger at
`D`.

The generalisable lesson: the obstruction was sought among the *transports* the lane owns,
when what mattered was the *quantifier* of a hypothesis the lane already had.

`chi_eq_iff_step_of_bump` is kept with its statement unchanged and its reading corrected:
given `hbump`, both sides of that `iff` are now theorems, so it records an identity rather
than a gap.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

section Positive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]

omit [IsIntegral X] [IsLocallyNoetherian X] [X.IsRegularInCodimensionOne] in
/-- **The coefficients of the positive part.** -/
theorem positivePart_apply (D : X.WeilDivisor) (P : X.PrimeDivisor) :
    (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.positivePart D) P =
      max ((show X.PrimeDivisor →₀ ℤ from D) P) 0 := by
  change (Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)
    (show X.PrimeDivisor →₀ ℤ from D)) P = _
  rw [Finsupp.mapRange_apply]

omit [IsIntegral X] [IsLocallyNoetherian X] [X.IsRegularInCodimensionOne] in
/-- **The positive part is effective.** -/
theorem positivePart_nonneg (D : X.WeilDivisor) (P : X.PrimeDivisor) :
    0 ≤ (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.positivePart D) P := by
  rw [positivePart_apply]; omega

omit [IsIntegral X] [IsLocallyNoetherian X] [X.IsRegularInCodimensionOne] in
/-- **The canonical decomposition `D = D⁺ − (−D)⁺`.**  Pointwise
`n = max(n,0) − max(−n,0)`, the integer fact behind the decomposition of a Weil divisor
into a difference of effective divisors. -/
theorem eq_positivePart_sub_negativePart (D : X.WeilDivisor) :
    D = Scheme.WeilDivisor.positivePart D -
      Scheme.WeilDivisor.positivePart (-D) := by
  apply Finsupp.ext
  intro P
  rw [show (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.positivePart D -
        Scheme.WeilDivisor.positivePart (-D)) P =
      (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.positivePart D) P -
        (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.positivePart (-D)) P from
    Finsupp.sub_apply _ _ _, positivePart_apply, positivePart_apply]
  rw [show (show X.PrimeDivisor →₀ ℤ from -D) P =
      -(show X.PrimeDivisor →₀ ℤ from D) P from Finsupp.neg_apply _ _]
  -- `omega` treats `(show _ from D) P` and `D P` as distinct atoms, so name the value
  set n : ℤ := (show X.PrimeDivisor →₀ ℤ from D) P with hn
  omega

end Positive

section LedgerFromBump

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **The ledger holds on every effective divisor, from the one-point bump.**
`chi_telescope_list` gives it on list-effective divisors and
`exists_divisorOfList_of_nonneg` says every effective divisor is list-effective, so the
two combine to remove the list from the statement.

This is the first half of closing the ledger: the effective cone is done, with no
hypothesis beyond the bump. -/
theorem chi_eq_of_bump_of_nonneg
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    {D : X.WeilDivisor}
    (hD : ∀ P : X.PrimeDivisor, 0 ≤ (show X.PrimeDivisor →₀ ℤ from D) P) :
    chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D := by
  obtain ⟨L, rfl⟩ := exists_divisorOfList_of_nonneg D hD
  exact chi_divisorOfList_eq_degK k U₀ U₁ L hbump

/-- **The ledger at `D` is equivalent to the single step identity `χ(D⁺) − χ(D) = deg_k (−D)⁺`.**

Given the bump, the ledger at an arbitrary `D` holds exactly when `χ` drops by the weighted
degree of the removed negative part.  Both directions are proved.

**Its status has changed, and the statement has not.**  This theorem was written to record
what extending the ledger past the effective cone was thought to cost, with the `iff` chosen
deliberately over a `←`-only "reduction" that would have re-indexed its own conclusion
(inbox memory I-0399).  Both sides are now *theorems* given `hbump` — the right-hand
identity is `chi_telescope_list_add` at `D`, and the left is `chi_eq_of_bump` — so what this
records is an identity between two proved facts, not a gap.  It is kept because the
equivalence is still the sharpest description of how the negative part enters, and because
the diagnosis it encoded is exactly the one that turned out to be wrong: the missing
ingredient was never a transport for `χ`, it was noticing that `hbump` admits an arbitrary
base divisor. -/
theorem chi_eq_iff_step_of_bump
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D : X.WeilDivisor) :
    chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D ↔
      chi k U₀ U₁ (Scheme.WeilDivisor.positivePart D) - chi k U₀ U₁ D =
        degK k (Scheme.WeilDivisor.positivePart (-D)) := by
  have hpos := chi_eq_of_bump_of_nonneg k U₀ U₁ hbump (positivePart_nonneg D)
  have hdec : degK k D = degK k (Scheme.WeilDivisor.positivePart D) -
      degK k (Scheme.WeilDivisor.positivePart (-D)) := by
    rw [← degK_sub, ← eq_positivePart_sub_negativePart D]
  constructor
  · intro h; omega
  · intro h; omega

/-- **The telescope, started at an arbitrary base divisor.**  `chi_telescope_list` runs the
one-point bump from `0`; the same induction runs from any `E`, because `hbump` is quantified
over **all** base divisors and not only over effective ones. -/
theorem chi_telescope_list_add (L : List X.PrimeDivisor)
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (E : X.WeilDivisor) :
    chi k U₀ U₁ (divisorOfList L + E) =
      chi k U₀ U₁ E + ((L.map (residueDeg k)).sum : ℤ) := by
  induction L with
  | nil => rw [divisorOfList, zero_add]; simp
  | cons P L ih =>
    have hassoc : divisorOfList (P :: L) + E = pointDivisor P + (divisorOfList L + E) := by
      rw [divisorOfList]; abel
    rw [hassoc, hbump, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

/-- **The ledger on ALL divisors, from the one-point bump.**  This closes the extension that
the file's original docstring called open.

The argument the naive route missed: `hbump` is quantified over **every** base divisor `E`,
not only over effective ones, so the telescope is not confined to the effective cone.  Write
`D⁺ = (−D)⁺ + D` — the pointwise identity `max(n,0) = max(−n,0) + n` — and read it as "the
effective divisor `(−D)⁺` telescoped **onto the base `D`**".  Then
`chi_telescope_list_add` computes `χ(D⁺)` from `χ(D)`, and `chi_eq_of_bump_of_nonneg`
computes `χ(D⁺)` from `χ(0)` since `D⁺` is effective.  Equating the two and using
additivity of `deg_k` gives the ledger at `D`.

So the negative part costs nothing beyond the bump: it is the *base* of a second telescope
rather than a term that has to be transported.  `chi_eq_iff_step_of_bump` below identified
the remaining content as the single identity `χ(D⁺) − χ(D) = deg_k (−D)⁺`; that identity is
exactly what `chi_telescope_list_add` supplies, which is why the two together close the
ledger. -/
theorem chi_eq_of_bump (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D : X.WeilDivisor) :
    chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D := by
  -- `D⁺ = (−D)⁺ + D`, with `(−D)⁺` effective
  have hdecomp : Scheme.WeilDivisor.positivePart D =
      Scheme.WeilDivisor.positivePart (-D) + D := by
    -- pointwise `max(n,0) = max(−n,0) + n`; `abel` cannot be used, since `positivePart`
    -- is not a group operation and normalising inside it is not sound
    apply Finsupp.ext
    intro P
    rw [positivePart_apply, show (show X.PrimeDivisor →₀ ℤ from
          Scheme.WeilDivisor.positivePart (-D) + D) P =
        (show X.PrimeDivisor →₀ ℤ from Scheme.WeilDivisor.positivePart (-D)) P +
          (show X.PrimeDivisor →₀ ℤ from D) P from Finsupp.add_apply _ _ _,
      positivePart_apply,
      show (show X.PrimeDivisor →₀ ℤ from -D) P =
        -(show X.PrimeDivisor →₀ ℤ from D) P from Finsupp.neg_apply _ _]
    set n : ℤ := (show X.PrimeDivisor →₀ ℤ from D) P with hn
    omega
  obtain ⟨L, hL⟩ :=
    exists_divisorOfList_of_nonneg (Scheme.WeilDivisor.positivePart (-D))
      (positivePart_nonneg (-D))
  -- route 1: telescope `(−D)⁺` onto the base `D`
  have h1 : chi k U₀ U₁ (Scheme.WeilDivisor.positivePart D) =
      chi k U₀ U₁ D + degK k (Scheme.WeilDivisor.positivePart (-D)) := by
    rw [hdecomp, hL, chi_telescope_list_add k U₀ U₁ L hbump D, ← degK_divisorOfList k L]
  -- route 2: `D⁺` is effective, so the effective-cone ledger applies
  have h2 : chi k U₀ U₁ (Scheme.WeilDivisor.positivePart D) =
      chi k U₀ U₁ 0 + degK k (Scheme.WeilDivisor.positivePart D) :=
    chi_eq_of_bump_of_nonneg k U₀ U₁ hbump (positivePart_nonneg D)
  -- and `deg_k` is additive across the decomposition
  have hdeg : degK k (Scheme.WeilDivisor.positivePart D) =
      degK k (Scheme.WeilDivisor.positivePart (-D)) + degK k D := by
    rw [hdecomp, degK_add]
  omega

end LedgerFromBump

/-! ## §2. The lane's conclusions with the ledger eliminated

`chi_eq_of_bump` removes `hledger` from every conditional statement of the lane by
substituting the bump for it.  The restatements below are mechanical, and they matter for
exactly one reason: they change the lane's open-input count from three to two, and they make
the two remaining inputs *homogeneous* — both are now one-point statements about the local
step at a single prime divisor, rather than one one-point statement plus a global identity
over all divisors.

A caveat this section does **not** claim away.  The bump is not cheap: each instance is one
application of `chi_add_eq_residueDeg`, which consumes the ledger exact sequence's
connecting and surjectivity data plus the strong-approximation input `hsurj`.  What has been
removed is the *separate* quantified-over-all-divisors hypothesis, not the mathematics
underneath the bump. -/

section LedgerEliminated

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **The Riemann inequality from the bump.**  `deg_k D + χ(0) ≤ ℓ(D)`, with the ledger
eliminated (`degK_add_chi_zero_le_ell` is the form that takes it). -/
theorem degK_add_chi_zero_le_ell_of_bump
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D : X.WeilDivisor) :
    degK k D + chi k U₀ U₁ 0 ≤ (ell k D : ℤ) :=
  degK_add_chi_zero_le_ell k U₀ U₁ (chi_eq_of_bump k U₀ U₁ hbump) D

/-- **Principal divisors have weighted degree zero, from the bump.**  `deg_k (div g) = 0`
with the ledger eliminated; `degK_principal_eq_zero` is the form that takes it. -/
theorem degK_principal_eq_zero_of_bump
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    {g : X.functionField} (hg : g ≠ 0) :
    degK k (Scheme.WeilDivisor.principal g hg) = 0 :=
  degK_principal_eq_zero k U₀ U₁ (chi_eq_of_bump k U₀ U₁ hbump) hg

/-- **`deg_k` descends to linear-equivalence classes, from the bump.** -/
theorem degK_eq_of_linearEquivalence_of_bump
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    {D D' : X.WeilDivisor} (h : Scheme.WeilDivisor.LinearEquivalence D D') :
    degK k D = degK k D' :=
  degK_eq_of_linearEquivalence k U₀ U₁ (chi_eq_of_bump k U₀ U₁ hbump) h

/-- **Bounded `H¹` vanishing from two one-point inputs.**  The lane's headline vanishing
statement with `hledger` eliminated: the remaining inputs are the base vanishing at one
divisor and the two one-point local statements (`hbump` and the one-point peel).

This is the form to quote for the single-field clause of cluster P.  Compare
`exists_bound_subsingleton_h1Mod_of_pointPeel`, which is this statement plus a separate
ledger hypothesis. -/
theorem exists_bound_subsingleton_h1Mod_of_bump_of_pointPeel
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hstep : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      Peel k U₀ U₁ E (pointDivisor P + E)) :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      Subsingleton (H1Mod k U₀ U₁ D) :=
  exists_bound_subsingleton_h1Mod_of_pointPeel k U₀ U₁
    (chi_eq_of_bump k U₀ U₁ hbump) D₀ hbase hstep

/-- **Riemann–Roch in the vanishing range from the bump**: a threshold past which
`ℓ(D) = χ(0) + deg_k D` exactly.  With `χ(0) = 1 − g` this is `ℓ(D) = deg_k D + 1 − g` for
`deg_k D` large, on two one-point inputs plus one base vanishing. -/
theorem exists_bound_ell_eq_of_bump_of_pointPeel
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hstep : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      Peel k U₀ U₁ E (pointDivisor P + E)) :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      (ell k D : ℤ) = chi k U₀ U₁ 0 + degK k D := by
  obtain ⟨b, hb⟩ :=
    exists_bound_subsingleton_h1Mod_of_bump_of_pointPeel k U₀ U₁ hbump D₀ hbase hstep
  exact ⟨b, fun D hD =>
    ell_eq_of_bound k U₀ U₁ (chi_eq_of_bump k U₀ U₁ hbump) (hb D hD)⟩

/-- **Global generation from the bump**, uniformly in the point given a residue-degree
bound `r`.  The ledger is eliminated; the open inputs are the base vanishing and the two
one-point statements. -/
theorem exists_bound_forall_generatedAt_of_bump
    (hbump : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show X.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D')
    (r : ℕ) (hr : ∀ P : X.PrimeDivisor, residueDeg k P ≤ r)
    [∀ D : X.WeilDivisor, Module.Finite k (sectionSub k ⊤ D)]
    [∀ P : X.PrimeDivisor, Module.Finite k (localStepTgt k P 1)] :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      ∀ P : X.PrimeDivisor, GeneratedAt k D P :=
  exists_bound_forall_generatedAt k U₀ U₁ (chi_eq_of_bump k U₀ U₁ hbump)
    D₀ hbase hpeel r hr

end LedgerEliminated

/-! ## §3. The one-point peel has content only on the overlap

With the ledger closed, the one-point peel `Peel E (1·P + E)` is one of the lane's two
remaining open inputs.  This section localises it: **the peel is free at every prime divisor
whose point lies outside the overlap `U₀ ⊓ U₁`**, so its whole content sits at points of the
overlap.

The reason is that `𝒜(D) = Γ(U₀ ⊓ U₁, 𝒪(D))` constrains orders only at primes meeting the
overlap.  If `P.point ∉ U₀ ⊓ U₁` then `1·P + E` and `E` impose the *same* conditions there —
they differ only at `P` — so `𝒜(1·P + E) = 𝒜(E)` and one may take `y = x`, with
`x − y = 0` a coboundary for free.

**What this is actually worth — and the first answer here was wrong about it.**

As a *reduction of the peel*, it is small.  On the covers this lane uses (two nonempty affine
opens of an irreducible curve) the overlap should be a dense open omitting only finitely many
closed points, so the primes disposed of are the few, not the many.  (That estimate is a
mathematical expectation about the intended covers, **not** a theorem in this file: the lemmas
below hold for arbitrary `U₀ U₁`, where the exceptional set may be large or everything.)

But the identity `𝒜(1·P + E) = 𝒜(E)` that makes the peel free off the overlap is the *same*
computation that shows the ledger exact sequence gives a `χ`-jump of `0` there, rather than
`[κ(P):k]`.  So §3's real content is not modesty about a count: it is the evidence that
**`chi_add`'s exactness hypotheses cannot hold at off-overlap primes** — see §5
(`not_bump_of_notMem_overlap`), which turns this observation into a theorem.

(An earlier version of this paragraph read that same computation as evidence that *`hbump`*
is refutable off the overlap.  It is not: `ChiUnconditional.chi_eq_charts_sub_overlap` computes
χ off the overlap without any exactness hypothesis and finds the jump equal to the surviving
one-chart step, so what fails there is `chi_add`'s hypotheses, not the bump.)

An earlier version of this paragraph offered the diagnosis "one
cannot shrink the exceptional set by choosing a better cover, because it is already nearly
empty", which is true and points away from that.  Credit for the re-reading: an independent
`work-reviewer` audit (inbox I-0450).

What remains at an overlap point is the substantive input: the
Mittag-Leffler/strong-approximation statement that a section with a first-order pole at `P`
can be corrected, modulo the coboundary, by an overlap section without it.  Nothing here
supplies that, and it is the same datum `ChiLedger.localStepMapₖ_surjective` takes as
`hsurj`.  The value of the section is that the residual leaf now has an explicitly bounded
domain of quantification rather than being stated at all primes, and that the two easy cases
are no longer mixed with the hard one.

(These lemmas are about `Peel`, defined in `BoundedVanishing.lean`; they live here because
this file is where the ledger closure makes the peel the residual input.) -/

section PeelOffOverlap

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **Off the overlap, a one-point bump does not change the overlap sections.**
`𝒜(1·P + E) = 𝒜(E)` when `P.point ∉ U₀ ⊓ U₁`, because the two divisors differ only at `P`
and `𝒜` reads the divisor only at primes meeting the overlap. -/
theorem sectionSub_add_pointDivisor_of_notMem_overlap
    {P : X.PrimeDivisor} (hP : P.point ∉ (U₀ ⊓ U₁ : X.Opens)) (E : X.WeilDivisor) :
    sectionSub k (U₀ ⊓ U₁) (pointDivisor P + E) = sectionSub k (U₀ ⊓ U₁) E := by
  apply le_antisymm
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    refine Or.inr fun Q hQ => ?_
    have hQP : Q ≠ P := fun h => hP (h ▸ hQ)
    rw [← add_pointDivisor_apply_of_ne E hQP]
    exact ((mem_sectionOfDivisor_of_ne_zero hx0).mp hx) Q hQ
  · exact sectionSub_mono k (U₀ ⊓ U₁) (le_add_pointDivisor E P)

/-- **The one-point peel is free off the overlap.**  For a prime divisor `P` with
`P.point ∉ U₀ ⊓ U₁`, `Peel E (1·P + E)` holds for every `E`, with no approximation input:
take `y = x`, legitimate because the bump did not change the overlap sections
(`sectionSub_add_pointDivisor_of_notMem_overlap`).

So the one-point peel — one of the lane's two residual open inputs — has content **only** at
primes whose point lies in the overlap. -/
theorem peel_pointDivisor_of_notMem_overlap
    {P : X.PrimeDivisor} (hP : P.point ∉ (U₀ ⊓ U₁ : X.Opens)) (E : X.WeilDivisor) :
    Peel k U₀ U₁ E (pointDivisor P + E) := by
  intro x hx
  refine ⟨x, ?_, by simp⟩
  rwa [sectionSub_add_pointDivisor_of_notMem_overlap k U₀ U₁ hP E] at hx

/-- **The one-point peel, reduced to the overlap.**  To have the one-point peel at *every*
prime divisor and every base divisor, it suffices to have it at the primes meeting the
overlap `U₀ ⊓ U₁`.  Off the overlap it is `peel_pointDivisor_of_notMem_overlap`.

This is the precise form of the residual leaf.  Combined with `Peel.of_list` and
`exists_bound_subsingleton_h1Mod_of_bump_of_pointPeel`, the single-field vanishing lane rests
on: the bump, one base vanishing, and the peel **at overlap points only**. -/
theorem pointPeel_of_pointPeel_on_overlap
    (hover : ∀ (P : X.PrimeDivisor), P.point ∈ (U₀ ⊓ U₁ : X.Opens) →
      ∀ E : X.WeilDivisor, Peel k U₀ U₁ E (pointDivisor P + E))
    (P : X.PrimeDivisor) (E : X.WeilDivisor) :
    Peel k U₀ U₁ E (pointDivisor P + E) := by
  by_cases hP : P.point ∈ (U₀ ⊓ U₁ : X.Opens)
  · exact hover P hP E
  · exact peel_pointDivisor_of_notMem_overlap k U₀ U₁ hP E

end PeelOffOverlap

/-! ## §4. `hbump` is a satisfiable hypothesis

`chi_eq_of_bump` is worth its statement only if `hbump` can hold.  A theorem whose hypothesis
is contradictory is true, axiom-clean, instantiable, and worthless — and no axiom check or
elaboration probe detects it.  This section rules that out.

Two facts, and it is worth being exact about how little each one gives:

* `bump_of_isEmpty_primeDivisor` — `hbump` is **consistent**: it holds vacuously when there are
  no prime divisors.  That is all it shows.  A first draft of this section also contained a
  "reduction" of `hbump` to the conclusion of `chi_add_eq_residueDeg`; it was deleted, because
  the two statements are *literally the same proposition*, so the lemma was `Iff.rfl` dressed
  as content — the re-indexing failure mode that inbox memory I-0399 records for this task.
* Each instance of `hbump` is, syntactically, the conclusion of
  `ChiLedger.chi_add_eq_residueDeg` at the one-point twist `E ↦ 1·P + E`.  That is a remark
  about where to look, not a theorem, and it is recorded here as prose for exactly that reason.

What this section does **not** claim: that `hbump` *holds* at any particular curve.  Exhibiting
one needs the strong-approximation input `hsurj`, which is the lane's residual open leaf.  The
distinction between "consistent" and "satisfied somewhere interesting" is the kind this task's
predecessors got wrong in the other direction, so it is stated rather than left to the reader.
The non-degenerate half of the picture is that `ResidueField.primeDivisorOfNotGeneric` produces
an actual prime divisor on a curve, so the vacuous witness does not apply there. -/

section BumpRefuted

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **Off the overlap the local step is trivial.**  `𝒜(1·P + E) = 𝒜(E)` for `P.point ∉ U₀ ⊓ U₁`
(`sectionSub_add_pointDivisor_of_notMem_overlap`), so the local step space is a subsingleton and
its `k`-dimension is `0`. -/
theorem finrank_localStepDom_eq_zero_of_notMem_overlap
    {P : X.PrimeDivisor} (hP : P.point ∉ (U₀ ⊓ U₁ : X.Opens)) (E : X.WeilDivisor) :
    Module.finrank k (localStepDom k (U₀ ⊓ U₁) E (pointDivisor P + E)) = 0 := by
  have h := sectionSub_add_pointDivisor_of_notMem_overlap k U₀ U₁ hP E
  haveI : Subsingleton (localStepDom k (U₀ ⊓ U₁) E (pointDivisor P + E)) := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply]
    exact Submodule.sub_mem _ (h ▸ x.2) (h ▸ y.2)
  exact Module.finrank_zero_of_subsingleton

/-- **`hbump` fails at an off-overlap prime, given `chi_add`'s conclusion there.**  The
*conditional* form of the refutation; the unconditional one is
`ChiUnconditional.not_bump_of_notMem_left`.

The incompatibility is real: `chi_add` concludes
`χ(1·P + E) = χ(E) + dim_k(𝒜(1·P+E)/𝒜(E))`, off the overlap that dimension is `0`
(`finrank_localStepDom_eq_zero_of_notMem_overlap`), while `hbump` asserts a jump of
`[κ(P):k] ≥ 1` (`one_le_residueDeg`).  The two cannot both hold.

**Which one gives way: `hbump`.**  `ChiUnconditional` §5–§6 settle it, and the answer is *not*
the one an intermediate version of this docstring gave.  On a genuine cover with
finite-dimensional chart sections, `ChiUnconditional.ell_le_finrank_chart_along_tower` bounds `ℓ`
— and hence χ — along the tower `n·P` at any `P` off a chart, while `hbump` demands growth
`n·[κ(P):k]`.  So `hbump` is false there outright, and the closed ledger with it
(`ledger_refuted_of_notMem_left`).

**What this does and does not do to `chi_eq_of_bump`.**  It does not touch its proof, which is
correct: from `hbump` the ledger follows at every divisor.  What it means is that `chi_eq_of_bump`
derives a false conclusion from a false hypothesis on such a cover, so it must **not** be
advertised as a route to the ledger.  A consumer intending to discharge `hbump` from
`chi_add_eq_residueDeg` cannot — that producer requires `P.point ∈ U₀ ⊓ U₁` and is unavailable off
the overlap.

**Correction history.**  This docstring was twice wrong in opposite directions.  It first
advertised itself as showing "`hbump` is REFUTED at every off-overlap prime" — too strong for what
the *statement* says, since the hypothesis `hchiAdd` is doing work.  It was then rewritten to say
that `chi_add`'s hypotheses are what fail and that `hbump` "is not false anywhere" — which was
false.  The stable position is above: the statement here is conditional, and the unconditional
refutation of `hbump` exists in `ChiUnconditional`.  What was correct throughout: the cost
accounting five docstrings in this lane carried ("one application of
`ChiLedger.chi_add_eq_residueDeg`" per bump instance) *was* false off the overlap.

Credit: the conditional refutation was found by an independent `work-reviewer` audit (inbox
I-0449 / I-0451); the unconditional one, and the correction of the middle position above, by a
second such audit (I-0467 / I-0468).  Both machine-checked rather than left as prose. -/
theorem not_bump_of_notMem_overlap
    {P : X.PrimeDivisor} (hP : P.point ∉ (U₀ ⊓ U₁ : X.Opens)) (E : X.WeilDivisor)
    [Module.Finite k (localStepTgt k P 1)]
    (hchiAdd : chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E
      + Module.finrank k (localStepDom k (U₀ ⊓ U₁) E (pointDivisor P + E))) :
    chi k U₀ U₁ (pointDivisor P + E) ≠ chi k U₀ U₁ E + residueDeg k P := by
  rw [finrank_localStepDom_eq_zero_of_notMem_overlap k U₀ U₁ hP E] at hchiAdd
  have h1 : 1 ≤ residueDeg k P := one_le_residueDeg k P
  omega

end BumpRefuted

section BumpSatisfiable

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **`hbump` holds vacuously on a scheme with no prime divisors** — the cheap witness that it
is not a contradictory hypothesis.

This is a *degenerate* witness and is labelled as one: on such a scheme every `∀ P` statement
in the lane is vacuous, and `degK` is identically `0`, so the ledger it yields is the trivial
`χ(D) = χ(0)`.  It establishes exactly one thing — that `hbump` is consistent — and nothing
about the lane's content.

The non-degenerate direction is the other one, and this project has it: `ResidueField`'s
`primeDivisorOfNotGeneric` produces an actual prime divisor on a curve, so on a curve the `∀ P`
quantifier ranges over a nonempty family and the degenerate witness does not apply.  Both facts
together are what "satisfiable and not idle" means. -/
theorem bump_of_isEmpty_primeDivisor [IsEmpty X.PrimeDivisor] :
    ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      chi k U₀ U₁ (pointDivisor P + E) = chi k U₀ U₁ E + residueDeg k P :=
  fun P _ => isEmptyElim P

end BumpSatisfiable

end Adelic
end AlgebraicGeometry
