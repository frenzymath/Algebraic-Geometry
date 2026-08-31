/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.Adelic.SectionBounds

/-!
# Adelic Riemann–Roch — bounded `H¹` vanishing over a single base field

This file assembles the **single-field bounded vanishing** statement of the
campaign's cluster P (P5, primary clause):

`∃ b : ℤ, ∀ D, b ≤ deg_k D → Subsingleton (Ȟ¹(D))`

from three inputs that are named explicitly in every statement:

1. **a base vanishing** `Subsingleton (Ȟ¹(D₀))` at one divisor `D₀`;
2. **the peel input** — surjectivity of the twist `Ȟ¹(D) ↠ Ȟ¹(D')` for `D ≤ D'`,
   in the concrete form `𝒜(D') = 𝒜(D) + B(D')`.  This is exactly the `htwist`
   datum of the χ-ledger (`chi_add`), unwound;
3. **the closed ledger** `χ(D) = χ(0) + deg_k D`, used only to produce an
   effective witness in the class of `D − D₀`.

**Input 3 is no longer open.**  `Adelic/LedgerClosure.chi_eq_of_bump` proves the closed
ledger at every Weil divisor from the one-point bump `hbump`, so the statements below can be
read with `hledger` discharged; the ledger-free forms are in `LedgerClosure.lean` §2.  The
theorems here keep the `hledger` binder because it is strictly more general.  Note this does
**not** make the lane unconditional, and the bump is *not* merely one application of
`chi_add_eq_residueDeg` per step: off the overlap that theorem does not apply.  **Stronger, and
it bears on every theorem in this file:** on a *genuine* cover (`U₀ ⊔ U₁ = ⊤`) whose three chart
section spaces are finite-dimensional and which has a prime divisor off a chart, both `hbump` and
`hledger` are FALSE (`ChiUnconditional.not_bump_of_notMem_left`,
`ChiUnconditional.ledger_refuted_of_notMem_left`) — χ is bounded along the tower `n·P` while both
demand linear growth — so this file's `hledger`-conditional results are **vacuous** there.  Those
side conditions are extra (this file assumes neither a cover nor chart-level finiteness), so the
claim is about which covers are usable rather than a blanket vacuity.  The mathematics moved
under the bump rather than away, and there is more of it there than this file used to say.
Input 2 is also
localised — `LedgerClosure.peel_pointDivisor_of_notMem_overlap` discharges the one-point peel
at every prime divisor off the overlap `U₀ ⊓ U₁`, leaving its content at overlap points.

Inputs 1 and 2 are individually load-bearing, but they are **not** two independent
facts: `coneVanishing_iff_base_and_peel` proves their conjunction equivalent to
vanishing on the whole cone `{D' ≥ D₀}`.  So the theorem's real content is
*cone-vanishing (pointwise condition) + ledger ⟹ degree-vanishing (numerical
condition)*, which is a genuine reduction — a divisor of large weighted degree need
not dominate `D₀` — but the input is a vanishing statement on an infinite family,
not one base vanishing plus a soft surjectivity.  The `_of_pointPeel` corollary is
the form that actually reduces the burden, to a one-point bump.

Nothing here is a `sorry` and nothing here is a new gate class: each theorem is of
the form "given (1)–(3), the bound exists", with `b` computed explicitly as
`b = deg_k D₀ + 1 − χ(0)`.

## Vanishing as `Subsingleton`, not as `h¹ = 0`

Vanishing is stated as `Subsingleton (H1Mod k U₀ U₁ D)` rather than
`h1dim k U₀ U₁ D = 0`.  The two agree when `Ȟ¹(D)` is finite-dimensional, but the
`Subsingleton` form needs **no finiteness instance**, so §1 stays independent of the
finiteness gates.  `h1dim_eq_zero_of_subsingleton` converts.

**Do not over-read that.**  It is a claim about *instance arguments* in §1 only.
Every theorem taking the closed ledger `hledger` is a different matter: since
`Module.finrank` of an infinite-dimensional space is `0`, an identity
`∀ D, χ(D) = χ(0) + deg_k D` silently forces finite-dimensionality wherever it
forces a nonzero rank.  So the ledger hypothesis carries finiteness content even
though no `Module.Finite` binder appears next to it.

## Main declarations

* `subsingleton_h1Mod_iff` — `Ȟ¹(D) = 0 ⟺ 𝒜(D) ⊆ B(D)`: the concrete criterion
  everything below runs on.
* `subsingleton_h1Mod_peel` — the **peel step**: base vanishing at `D` plus the
  peel input transports vanishing to any `D' ≥ D`.
* `subsingleton_h1Mod_of_linearEquivalence` — vanishing is a class invariant
  (from `ClassInvariance.lean`, finiteness-free).
* `exists_bound_subsingleton_h1Mod_of_residualLedger` — the assembled bound, taking the
  ledger only at the **residuals** `D − D₀`, which is where the proof uses it (inbox I-0394).
* `exists_bound_subsingleton_h1Mod` — the same with the universal ledger binder, a one-line
  corollary of the previous, kept for existing consumers.

## Relation to the sibling project's `UniformVanishing.lean`

`AJCR RiemannRoch/UniformVanishing.lean` proves a statement of exactly this
shape, `∃ b, ∀ D, b ≤ deg D → Subsingleton H¹(𝒪(D))`, and its proof has the same
skeleton: fix a base twist, produce an effective witness of the residual class,
peel it, transport along the class.  **This file is not a port of it.**  AJCR's
version obtains its base vanishing from the FLV-class machine
(`RiemannRoch/FLVClass.lean`, via a finite dominant `π : Y → ℙ¹` and the fiber
divisor) and its peel step from `peel_effective` on `divisorSheaf`; neither the
FLV machinery nor `divisorSheaf` exists in AJC.  So here (1) and (2) are named
hypotheses rather than discharged lemmas, and the file is honest about that: what
is *new* relative to AJC is the assembly and the class-transport, and those are
now proved.

## The three gaps, kept apart

`exists_bound_subsingleton_h1Mod` is **single-field**: `k`, the cover `U₀, U₁` and
the base divisor `D₀` are all fixed.  It is therefore strictly weaker than the two
things downstream consumers eventually want.  Of those two, the first is still open
anywhere in this project and the second is now proved elsewhere in the lane:

* **extension uniformity** — the *same* `b` for every field extension `κ/k`.  Needs flat base
  change of the bound along `k → κ`; nothing here quantifies over extensions.

  An earlier version of this paragraph added that even the *statement* was unavailable, for
  want of transported cover data.  **That was wrong**: `CurveBaseChange.lean` §3's
  `AffineCoverMVSquare.baseChangeField` does transport a 2-affine cover to `C_κ`, and its
  opens are what `Ȟ¹` consumes.  The predicate is written down as
  `Adelic.UniformlyBoundedVanishing` (`Adelic/ResidueField.lean` §5).  It is **statable and
  open** — the two genuinely missing inputs are flat base change for the section spaces
  (`Γ(C_κ, 𝒪(D_κ)) ≃ Γ(C,𝒪(D)) ⊗_k κ`) and a `WeilDivisor` pullback along `C_κ ⟶ C`, neither
  of which is a cover-transport problem.
* **global generation** above the bound.  Needs `Ȟ¹(D − x) = 0` at every closed
  point `x`, i.e. the bound raised by the maximal residue degree, plus the
  evaluation-surjectivity argument.  **Now proved**, in
  `Adelic/GlobalGeneration.lean`, from *this file's* three inputs and nothing more:
  the evaluation map is onto exactly when the section drop is maximal, which the
  ledger converts into the pair of vanishings at `D` and `D − x`
  (`evalMap_surjective`, `exists_bound_generatedAt`).  The uniform-over-points form
  additionally needs a bound on residue degrees, which is `1` over an algebraically
  closed base — and that residue fact is now **proved**, in `Adelic/ResidueField.lean`
  (`residueDeg_eq_one_of_isAlgClosed_curve`), on the curve hypotheses the project's
  headline already carries.  So the uniform form
  `exists_bound_forall_generatedAt_of_isAlgClosed_curve` is conditional on *this* file's
  three inputs and nothing else.  (`GlobalGeneration.lean` §7's own
  `hasRationalResidues_of_isAlgClosed` is a *reformulation* onto three stalk-level binders
  and is **not** the discharge — cite the `ResidueField.lean` form, and read the warning in
  §7 before citing that one.)

`ajc-gate` should therefore not read this file as discharging an extension-uniform
hypothesis; it discharges the single-field bounded-vanishing shape only, and only
relative to (1)–(3).  For global generation, cite `Adelic/GlobalGeneration.lean`,
which is conditional on the same (1)–(3).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits IsDedekindDomain
open scoped WithZero

namespace AlgebraicGeometry
namespace Adelic

section Vanishing

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **The concrete vanishing criterion.**  `Ȟ¹(D) = 𝒜(D)/B(D)` is trivial exactly
when the overlap sections are already coboundaries: `𝒜(D) ⊆ B(D)`.  (The reverse
inclusion always holds, `coboundarySub_le_overlap`, so the condition really is
equality.) -/
theorem subsingleton_h1Mod_iff (D : X.WeilDivisor) :
    Subsingleton (H1Mod k U₀ U₁ D) ↔
      sectionSub k (U₀ ⊓ U₁) D ≤ coboundarySub k U₀ U₁ D := by
  constructor
  · intro hsub x hx
    have hzero : Submodule.Quotient.mk (p := Submodule.comap
        (sectionSub k (U₀ ⊓ U₁) D).subtype (coboundarySub k U₀ U₁ D))
        (⟨x, hx⟩ : sectionSub k (U₀ ⊓ U₁) D) = 0 := Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply] at hzero
    exact hzero
  · intro hle
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply]
    exact hle ((sectionSub k (U₀ ⊓ U₁) D).sub_mem x.2 y.2)

/-- **The peel step.**  Suppose `Ȟ¹(D)` vanishes and the twist `Ȟ¹(D) → Ȟ¹(D')`
is surjective — concretely, every overlap section of `𝒪(D')` agrees, modulo the
coboundary `B(D')`, with an overlap section of `𝒪(D)`.  Then `Ȟ¹(D')` vanishes.

`D'` is typically `D + E` with `E ≥ 0`: this is "peel off an effective divisor",
the step that turns one base vanishing into vanishing on a whole cone.  The
`hpeel` hypothesis is the ledger's surjectivity datum `htwist`, unwound; it is
supplied here as a hypothesis because AJC has no unconditional source for it. -/
theorem subsingleton_h1Mod_peel {D D' : X.WeilDivisor}
    (hbase : Subsingleton (H1Mod k U₀ U₁ D))
    (hpeel : ∀ x ∈ sectionSub k (U₀ ⊓ U₁) D', ∃ y ∈ sectionSub k (U₀ ⊓ U₁) D,
      x - y ∈ coboundarySub k U₀ U₁ D')
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P ≤
      (show X.PrimeDivisor →₀ ℤ from D') P) :
    Subsingleton (H1Mod k U₀ U₁ D') := by
  rw [subsingleton_h1Mod_iff] at hbase ⊢
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hpeel x hx
  have hyB : y ∈ coboundarySub k U₀ U₁ D' := by
    have : y ∈ coboundarySub k U₀ U₁ D := hbase hy
    exact coboundarySub_mono k U₀ U₁ hle this
  have : x = (x - y) + y := by abel
  rw [this]
  exact (coboundarySub k U₀ U₁ D').add_mem hxy hyB

/-- **The peel relation `Peel D D'`.**  "Every overlap section of `𝒪(D')` agrees,
modulo the coboundary `B(D')`, with an overlap section of `𝒪(D)`" — equivalently,
the twist `Ȟ¹(D) → Ȟ¹(D')` is surjective.  Named so that it can be composed
(`Peel.trans`) and so that consumers can discharge it one point at a time rather
than in one step. -/
def Peel (D D' : X.WeilDivisor) : Prop :=
  ∀ x ∈ sectionSub k (U₀ ⊓ U₁) D', ∃ y ∈ sectionSub k (U₀ ⊓ U₁) D,
    x - y ∈ coboundarySub k U₀ U₁ D'

/-- **The peel relation is reflexive** (take `y = x`). -/
theorem Peel.refl (D : X.WeilDivisor) : Peel k U₀ U₁ D D :=
  fun x hx => ⟨x, hx, by simp⟩

/-- **The peel relation composes.**  `Peel D₀ D₁` and `Peel D₁ D₂` give
`Peel D₀ D₂`, provided `D₁ ≤ D₂` (so that `B(D₁) ⊆ B(D₂)`).

This is what makes the peel hypothesis of `exists_bound_subsingleton_h1Mod`
tractable: it need only be established for **one-point** bumps `E ↦ E + P`, then
chained along an effective divisor.  Chaining one-point peels is the adelic
analogue of AJCR's `peel_effective`, which peels a whole effective divisor in one
sheaf-level step. -/
theorem Peel.trans {D₀ D₁ D₂ : X.WeilDivisor}
    (h₀₁ : Peel k U₀ U₁ D₀ D₁) (h₁₂ : Peel k U₀ U₁ D₁ D₂)
    (hle : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₁) P ≤
      (show X.PrimeDivisor →₀ ℤ from D₂) P) :
    Peel k U₀ U₁ D₀ D₂ := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h₁₂ x hx
  obtain ⟨z, hz, hyz⟩ := h₀₁ y hy
  refine ⟨z, hz, ?_⟩
  have : x - z = (x - y) + (y - z) := by abel
  rw [this]
  exact (coboundarySub k U₀ U₁ D₂).add_mem hxy
    (coboundarySub_mono k U₀ U₁ hle hyz)

/-- **Chaining one-point peels along a list.**  If every one-point bump peels —
`Peel E (1·P + E)` for every prime divisor `P` and every `E` — then `D₀` peels to
`divisorOfList L + D₀` for every list `L`, i.e. to `D₀` plus an arbitrary effective
divisor.  Induction on `L` with `Peel.trans`. -/
theorem Peel.of_list (hstep : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      Peel k U₀ U₁ E (pointDivisor P + E))
    (D₀ : X.WeilDivisor) (L : List X.PrimeDivisor) :
    Peel k U₀ U₁ D₀ (divisorOfList L + D₀) := by
  induction L with
  | nil =>
    have h0 : divisorOfList ([] : List X.PrimeDivisor) + D₀ = D₀ := by
      rw [divisorOfList, zero_add]
    rw [h0]
    exact Peel.refl k U₀ U₁ D₀
  | cons P L ih =>
    have hassoc : divisorOfList (P :: L) + D₀ =
        pointDivisor P + (divisorOfList L + D₀) := by
      rw [divisorOfList]; abel
    rw [hassoc]
    refine ih.trans k U₀ U₁ (hstep P (divisorOfList L + D₀)) fun Q => ?_
    exact le_add_pointDivisor (divisorOfList L + D₀) P Q

/-- **Vanishing is a linear-equivalence invariant** (finiteness-free).  The
multiplication isomorphism of `ClassInvariance.lean` is a `k`-linear isomorphism
`Ȟ¹(D) ≃ₗ[k] Ȟ¹(D')` whenever `D' = D − div g`, and `Subsingleton` transports
along any equivalence. -/
theorem subsingleton_h1Mod_of_shift {D D' : X.WeilDivisor} {g : X.functionField}
    (hg : g ≠ 0)
    (hD' : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D') P =
      (show X.PrimeDivisor →₀ ℤ from D) P - Scheme.RationalMap.order P g)
    (h : Subsingleton (H1Mod k U₀ U₁ D)) :
    Subsingleton (H1Mod k U₀ U₁ D') :=
  (h1ModMulEquiv k U₀ U₁ hg hD').symm.toEquiv.subsingleton

/-- **`h¹ = 0` from vanishing**, for consumers phrased on the numerical
invariant. -/
theorem h1dim_eq_zero_of_subsingleton {D : X.WeilDivisor}
    (h : Subsingleton (H1Mod k U₀ U₁ D)) : h1dim k U₀ U₁ D = 0 := by
  rw [h1dim]
  exact Module.finrank_zero_of_subsingleton

end Vanishing

/-! ## §2. The assembled single-field bound

The assembly.  Fix a base divisor `D₀` with `Ȟ¹(D₀) = 0`.  For `D` of large
weighted degree the residual class `D − D₀` has `χ ≥ 1`, hence a nonzero global
section, hence an **effective** representative `E ~ D − D₀` (the effective-witness
dictionary of `ClassInvariance.lean`).  Then `D₀ + E ≥ D₀`, so peeling `E` off the
base vanishing kills `Ȟ¹(D₀ + E)`, and `D₀ + E ~ D` transports it to `Ȟ¹(D)`.

The threshold that makes the residual class have a section is
`b := deg_k D₀ + 1 − χ(0)`: for `deg_k D ≥ b` the ledger gives
`χ(D − D₀) = χ(0) + deg_k D − deg_k D₀ ≥ 1`, and `χ ≤ ℓ` does the rest.
-/

section Bound

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    [Algebra k X.functionField] [IsConstantField k X] (U₀ U₁ : X.Opens)

/-- **A class of positive `χ` has a nonzero global section.**  From `χ ≤ ℓ`
(`chi_le_ell`, i.e. `h¹ ≥ 0`): if `1 ≤ χ(D)` then `1 ≤ ℓ(D)`, so
`Γ(⊤, 𝒪(D)) ≠ 0`. -/
theorem exists_ne_zero_mem_of_one_le_chi {D : X.WeilDivisor}
    (hchi : 1 ≤ chi k U₀ U₁ D) :
    ∃ f : X.functionField, f ∈ sectionSub k ⊤ D ∧ f ≠ 0 := by
  have hell : 1 ≤ (ell k D : ℤ) := le_trans hchi (chi_le_ell k U₀ U₁ D)
  by_contra hno
  have hbot : sectionSub k ⊤ D = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    · exact absurd ⟨x, hx, hx0⟩ hno
  rw [ell, hbot] at hell
  simp at hell

/-- **The effective representative, from the ledger at the one divisor it is needed at.**
If `deg_k D ≥ 1 − χ(0)` and the ledger holds **at `D`**, then `D` is linearly equivalent to an
effective divisor.  This is the adelic counterpart of AJCR's `exists_effective_of_picClass`,
proved here from `χ ≤ ℓ` plus the effective-witness dictionary.

Stated at a single divisor so that the universal ledger binder does not propagate into
consumers that only have the identity at one place (inbox I-0394). -/
theorem exists_effective_linearEquiv_of_le_degK_at
    {D : X.WeilDivisor}
    (hledgerD : chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (hdeg : 1 - chi k U₀ U₁ 0 ≤ degK k D) :
    ∃ E : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, 0 ≤ (show X.PrimeDivisor →₀ ℤ from E) P) ∧
        Scheme.WeilDivisor.LinearEquivalence E D := by
  have hchi : 1 ≤ chi k U₀ U₁ D := by rw [hledgerD]; omega
  obtain ⟨f, hfmem, hfne⟩ := exists_ne_zero_mem_of_one_le_chi k U₀ U₁ hchi
  exact exists_effective_linearEquiv_of_ne_zero_mem hfne hfmem

/-- **An effective representative of a class of large weighted degree.**  The universal-ledger
form of `exists_effective_linearEquiv_of_le_degK_at`, kept for existing consumers. -/
theorem exists_effective_linearEquiv_of_le_degK
    (hledger : ∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    {D : X.WeilDivisor} (hdeg : 1 - chi k U₀ U₁ 0 ≤ degK k D) :
    ∃ E : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, 0 ≤ (show X.PrimeDivisor →₀ ℤ from E) P) ∧
        Scheme.WeilDivisor.LinearEquivalence E D :=
  exists_effective_linearEquiv_of_le_degK_at k U₀ U₁ (hledger D) hdeg

/-- **The bound, with the ledger taken only where the proof uses it** — the sharpened form
requested by inbox item I-0394.

`exists_bound_subsingleton_h1Mod` below takes the ledger at **every** divisor.  The proof
uses it at exactly one divisor per `D`, namely the **residual** `D − D₀`, and only for `D`
above the bound.  This version asks for precisely that, as `hledgerRes`.

Why this was worth stating separately.  I-0394 observes that the universal form silently
carries finiteness content (`Module.finrank` of an infinite-dimensional space is `0`, so the
identity forces finite-dimensionality wherever it forces a nonzero rank).  Restricting to the
residuals makes the requirement **stated at the divisors that matter**, so a caller who has
the ledger only on a set containing `{D − D₀ | deg_k D ≥ b}` can still use the theorem, and a
reader can see which instances are load-bearing without auditing the proof.

**What has changed since.**  This docstring used to add that "nothing in the project can
discharge it — `chi_telescope_list` and `LedgerClosure.chi_eq_of_bump_of_nonneg` reach the
*effective* cone only", the point being that a residual `D − D₀` is a difference and need not
be effective.  The premise is now false: `LedgerClosure.chi_eq_of_bump` proves the ledger at
**every** Weil divisor from the one-point bump, differences included, because `hbump` admits
an arbitrary base divisor.  So `hledgerRes` *is* dischargeable from the bump, and the
restriction to residuals is now a convenience for callers with partial information rather
than a record of an open gap.

The finiteness observation of I-0394 survives unchanged, and **transfers to the bump** — this is
machine-checked, not inferred.  From `hbump` alone, via `LedgerClosure.chi_eq_of_bump` and
`chi_le_ell`, one derives `0 < χ(0) + deg_k D → 0 < finrank k Γ(⊤,𝒪(D))`; since `Module.finrank`
of an infinite-dimensional space is `0`, that is finite-dimensionality forced by the hypothesis
with no `Module.Finite` binder in sight.

So "the ledger is now a theorem" must **not** be read as "the finiteness worry is gone".  The
worry attaches to whichever hypothesis carries the identity, and that is now `hbump`. -/
theorem exists_bound_subsingleton_h1Mod_of_residualLedger
    (hledgerRes : ∀ D : X.WeilDivisor, 1 - chi k U₀ U₁ 0 ≤ degK k D →
      chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show X.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      Subsingleton (H1Mod k U₀ U₁ D) := by
  refine ⟨degK k D₀ + 1 - chi k U₀ U₁ 0, fun D hD => ?_⟩
  -- the residual class `D - D₀` has weighted degree ≥ 1 - χ(0), so it is effective
  have hres : 1 - chi k U₀ U₁ 0 ≤ degK k (D - D₀) := by rw [degK_sub]; omega
  obtain ⟨E, hEnonneg, hEclass⟩ :=
    exists_effective_linearEquiv_of_le_degK_at k U₀ U₁ (hledgerRes (D - D₀) hres) hres
  -- `D₀ + E ≥ D₀`, so peeling `E` off the base vanishing kills `Ȟ¹(D₀ + E)`
  have hmono : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
      (show X.PrimeDivisor →₀ ℤ from D₀ + E) P := by
    intro P
    rw [show (show X.PrimeDivisor →₀ ℤ from D₀ + E) P =
          (show X.PrimeDivisor →₀ ℤ from D₀) P +
            (show X.PrimeDivisor →₀ ℤ from E) P from Finsupp.add_apply _ _ _]
    have := hEnonneg P
    linarith
  have hpeeled : Subsingleton (H1Mod k U₀ U₁ (D₀ + E)) :=
    subsingleton_h1Mod_peel k U₀ U₁ hbase (hpeel (D₀ + E) hmono) hmono
  -- `D₀ + E ~ D₀ + (D - D₀) = D`, so transport along the class
  obtain ⟨g, hg, hgE⟩ := hEclass
  have hshift : ∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D) P =
      (show X.PrimeDivisor →₀ ℤ from D₀ + E) P - Scheme.RationalMap.order P g := by
    intro P
    have hDsub : D = (D₀ + E) - Scheme.WeilDivisor.principal g hg := by
      have : E = (D - D₀) + Scheme.WeilDivisor.principal g hg := by
        rw [← hgE]; abel
      rw [this]; abel
    rw [hDsub]
    exact sub_principal_apply hg P
  exact subsingleton_h1Mod_of_shift k U₀ U₁ hg hshift hpeeled

/-- **Single-field bounded `H¹` vanishing** (campaign P5, primary clause; the
strongest form reachable in AJC today).

Given
* a base divisor `D₀` with `Ȟ¹(D₀) = 0`,
* the **peel input** at `D₀`: for every `D' ≥ D₀`, each overlap section of
  `𝒪(D')` agrees modulo `B(D')` with an overlap section of `𝒪(D₀)` — i.e. the
  twist `Ȟ¹(D₀) → Ȟ¹(D')` is surjective (the ledger's `htwist` datum, unwound),
* the closed ledger,

there is a single threshold `b = deg_k D₀ + 1 − χ(0)` past which `Ȟ¹(D)` vanishes
for **every** Weil divisor `D` of weighted degree `≥ b`.

The bound depends only on `(k, U₀, U₁, D₀)`.  It is **not** uniform over field
extensions and says **nothing** about global generation — see the module
docstring.

This is the universal-ledger form, kept for existing consumers; the ledger is actually needed
only at the residuals `D − D₀`, which is
`exists_bound_subsingleton_h1Mod_of_residualLedger` above. -/
theorem exists_bound_subsingleton_h1Mod
    (hledger : ∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show X.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      Subsingleton (H1Mod k U₀ U₁ D) :=
  exists_bound_subsingleton_h1Mod_of_residualLedger k U₀ U₁
    (fun D _ => hledger D) D₀ hbase hpeel

omit [IsIntegral X] [IsNoetherian X] [X.IsRegularInCodimensionOne] in
/-- **Every effective divisor is list-effective.**  An effective `E ≥ 0` is
`Σ_{P ∈ L} 1·P` for some list `L` of prime divisors, multiplicity encoded by
repetition.  Strong induction on the support: peel one support point `P₀`, replace
`E` by `E − 1·P₀` (whose support is contained in that of `E`, and strictly smaller
when `E(P₀) = 1`), recurse.

Implemented as induction on `(Σ_P E(P)).toNat`, which strictly decreases at each
peel because `E(P₀) ≥ 1` and every other coefficient is unchanged.  This discharges
the list-effectivity bookkeeping of
`exists_bound_subsingleton_h1Mod_of_pointPeel`.  Pure `Finsupp` combinatorics — the
geometric instances play no role, hence the `omit`. -/
theorem exists_divisorOfList_of_nonneg (E : X.WeilDivisor)
    (hE : ∀ P : X.PrimeDivisor, 0 ≤ (show X.PrimeDivisor →₀ ℤ from E) P) :
    ∃ L : List X.PrimeDivisor, E = divisorOfList L := by
  classical
  -- induct on the total (unweighted) mass of `E`
  generalize hn : (Scheme.WeilDivisor.degree E).toNat = n
  induction n generalizing E with
  | zero =>
    -- total mass 0 with all coefficients ≥ 0 forces `E = 0`
    refine ⟨[], ?_⟩
    rw [divisorOfList]
    have hsum : (show X.PrimeDivisor →₀ ℤ from E).sum (fun _ n => n) = 0 := by
      have hnn : 0 ≤ Scheme.WeilDivisor.degree E :=
        Finset.sum_nonneg fun P _ => hE P
      have hdeg : Scheme.WeilDivisor.degree E
          = (show X.PrimeDivisor →₀ ℤ from E).sum (fun _ n => n) := rfl
      omega
    -- a nonnegative finsupp of total mass 0 is zero
    apply Finsupp.ext
    intro P
    by_cases hP : P ∈ (show X.PrimeDivisor →₀ ℤ from E).support
    · have := Finset.sum_eq_zero_iff_of_nonneg
        (f := fun Q => (show X.PrimeDivisor →₀ ℤ from E) Q)
        (s := (show X.PrimeDivisor →₀ ℤ from E).support)
        (fun Q _ => hE Q)
      have hzero := (this.mp hsum) P hP
      rw [show (show X.PrimeDivisor →₀ ℤ from (0 : X.WeilDivisor)) P = (0 : ℤ) from
        Finsupp.zero_apply]
      exact hzero
    · rw [Finsupp.notMem_support_iff] at hP
      rw [show (show X.PrimeDivisor →₀ ℤ from (0 : X.WeilDivisor)) P = (0 : ℤ) from
        Finsupp.zero_apply]
      exact hP
  | succ n ih =>
    -- positive mass: some coefficient is ≥ 1
    have hdegE : Scheme.WeilDivisor.degree E
        = (show X.PrimeDivisor →₀ ℤ from E).sum (fun _ n => n) := rfl
    have hpos : 0 < (show X.PrimeDivisor →₀ ℤ from E).sum (fun _ n => n) := by omega
    obtain ⟨P₀, hP₀supp, hP₀pos⟩ :
        ∃ P₀ ∈ (show X.PrimeDivisor →₀ ℤ from E).support,
          0 < (show X.PrimeDivisor →₀ ℤ from E) P₀ := by
      by_contra hno
      push Not at hno
      have hle0 : (show X.PrimeDivisor →₀ ℤ from E).sum (fun _ n => n) ≤ 0 :=
        Finset.sum_nonpos fun Q hQ => hno Q hQ
      omega
    -- peel `1·P₀`
    set E' : X.WeilDivisor := E - pointDivisor P₀ with hE'def
    have hE'apply : ∀ P : X.PrimeDivisor,
        (show X.PrimeDivisor →₀ ℤ from E') P =
          (show X.PrimeDivisor →₀ ℤ from E) P -
            (if P = P₀ then 1 else 0) := by
      intro P
      rw [hE'def, show (show X.PrimeDivisor →₀ ℤ from E - pointDivisor P₀) P =
            (show X.PrimeDivisor →₀ ℤ from E) P -
              (show X.PrimeDivisor →₀ ℤ from pointDivisor P₀) P from
          Finsupp.sub_apply _ _ _, pointDivisor]
      by_cases h : P = P₀
      · rw [h, Finsupp.single_eq_same, if_pos rfl]
      · rw [Finsupp.single_eq_of_ne (Ne.symm (Ne.symm h) : P ≠ P₀), if_neg h]
    have hE'nonneg : ∀ P : X.PrimeDivisor,
        0 ≤ (show X.PrimeDivisor →₀ ℤ from E') P := by
      intro P
      rw [hE'apply P]
      by_cases h : P = P₀
      · subst h; rw [if_pos rfl]; omega
      · rw [if_neg h]; have := hE P; omega
    -- the mass drops by exactly one
    have hmass : Scheme.WeilDivisor.degree E'
        = Scheme.WeilDivisor.degree E - 1 := by
      have hEE' : E = E' + pointDivisor P₀ := by rw [hE'def]; abel
      have hadd := Scheme.WeilDivisor.degree_add E' (pointDivisor P₀)
      have hpt : Scheme.WeilDivisor.degree (pointDivisor P₀ : X.WeilDivisor) = 1 := by
        rw [Scheme.WeilDivisor.degree, pointDivisor]
        exact Finsupp.sum_single_index rfl
      rw [hpt, ← hEE'] at hadd
      omega
    obtain ⟨L, hL⟩ := ih E' hE'nonneg (by omega)
    refine ⟨P₀ :: L, ?_⟩
    rw [divisorOfList, ← hL, hE'def]
    abel

/-- **The bound from the one-point peel** — the form a consumer should actually
aim at.  Instead of the peel input for all `D' ≥ D₀` at once, it suffices to have
it for a **single point bump** `E ↦ 1·P + E`, uniformly in `P` and `E`: chaining
along a list (`Peel.of_list`) recovers the general case.

So the hypotheses reduce to exactly three, and only two of them are open
mathematics: the base vanishing, the **one-point** peel, and the closed ledger.
The list-effectivity bookkeeping is discharged internally by
`exists_divisorOfList_of_nonneg`. -/
theorem exists_bound_subsingleton_h1Mod_of_pointPeel
    (hledger : ∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hstep : ∀ (P : X.PrimeDivisor) (E : X.WeilDivisor),
      Peel k U₀ U₁ E (pointDivisor P + E)) :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      Subsingleton (H1Mod k U₀ U₁ D) := by
  refine exists_bound_subsingleton_h1Mod k U₀ U₁ hledger D₀ hbase ?_
  -- the general peel input, recovered from the one-point one
  intro D' hmono
  -- `D' = D₀ + (D' - D₀)` with `D' - D₀` effective, hence list-effective
  have hEnonneg : ∀ P : X.PrimeDivisor,
      0 ≤ (show X.PrimeDivisor →₀ ℤ from D' - D₀) P := by
    intro P
    rw [show (show X.PrimeDivisor →₀ ℤ from D' - D₀) P =
          (show X.PrimeDivisor →₀ ℤ from D') P -
            (show X.PrimeDivisor →₀ ℤ from D₀) P from Finsupp.sub_apply _ _ _]
    have := hmono P
    linarith
  obtain ⟨L, hL⟩ := exists_divisorOfList_of_nonneg (D' - D₀) hEnonneg
  have hD' : D' = divisorOfList L + D₀ := by rw [← hL]; abel
  rw [hD']
  exact Peel.of_list k U₀ U₁ hstep D₀ L

/-! ### What the `hbase ∧ hpeel` pair really is

Both hypotheses of `exists_bound_subsingleton_h1Mod` are individually load-bearing,
but that is **not** enough to call them two independent inputs, and the honest
description is sharper: their conjunction is *equivalent* to vanishing on the whole
cone above `D₀`.

`ConeVanishing_iff_base_and_peel` below proves both directions.  `←` is
`subsingleton_h1Mod_peel`.  `→` is the direction that matters for honesty: given
cone-vanishing, `hpeel` holds by taking `y = 0`, since `x − 0 = x ∈ B(D')` is
exactly the vanishing criterion at `D'`.

So `exists_bound_subsingleton_h1Mod` should be read as: **cone-vanishing above `D₀`
plus the ledger implies degree-vanishing above `b`.**  That is a genuine reduction
and not a re-indexing — the cone condition `D' ≥ D₀` is a *pointwise ordering*,
while the conclusion's condition `b ≤ deg_k D` is *numerical*, and a divisor of
large weighted degree need not dominate `D₀` at all.  Bridging the two is exactly
what the effective-witness/linear-equivalence transport does.  But it does mean the
input is a vanishing statement on an infinite family, not a single base vanishing
plus a soft surjectivity, and the `_of_pointPeel` corollary is the one that actually
reduces the burden (to a one-point bump).

A second caveat, recorded for the same reason: `hledger` is not as
finiteness-innocent as it looks.  `Module.finrank` of an infinite-dimensional space
is `0`, so an identity `∀ D, χ(D) = χ(0) + deg_k D` silently forces
finite-dimensionality wherever it forces a nonzero rank.  The claim that this file's
vanishing lane needs no finiteness instance is a statement about *instance
arguments* only; it does not apply to the theorems that take `hledger`. -/

/-- **`hbase ∧ hpeel` is exactly vanishing on the cone above `D₀`.**  See the
section note: `←` is `subsingleton_h1Mod_peel`, and `→` takes `y = 0`. -/
theorem coneVanishing_iff_base_and_peel (D₀ : X.WeilDivisor) :
    (∀ D' : X.WeilDivisor,
        (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
          (show X.PrimeDivisor →₀ ℤ from D') P) →
        Subsingleton (H1Mod k U₀ U₁ D')) ↔
      (Subsingleton (H1Mod k U₀ U₁ D₀) ∧
        ∀ D' : X.WeilDivisor,
          (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
            (show X.PrimeDivisor →₀ ℤ from D') P) →
          Peel k U₀ U₁ D₀ D') := by
  constructor
  · intro hcone
    refine ⟨hcone D₀ (fun _ => le_rfl), fun D' hmono x hx => ?_⟩
    -- take `y = 0`: `x - 0 = x` is a coboundary by vanishing at `D'`
    refine ⟨0, (sectionSub k (U₀ ⊓ U₁) D₀).zero_mem, ?_⟩
    rw [sub_zero]
    exact (subsingleton_h1Mod_iff k U₀ U₁ D').mp (hcone D' hmono) hx
  · rintro ⟨hbase, hpeel⟩ D' hmono
    exact subsingleton_h1Mod_peel k U₀ U₁ hbase (hpeel D' hmono) hmono

/-- **The bound is not vacuous: divisors above it exist.**  For every threshold `b`
and every prime divisor `P`, some multiple `n·P` has weighted degree `≥ b` — because
`[κ(P):k] ≥ 1` (`one_le_residueDeg`).  So the `∀ D, b ≤ deg_k D → …` conclusion of
`exists_bound_subsingleton_h1Mod` quantifies over a nonempty family, and cannot be
satisfied trivially by there being no divisor of large degree.

(Recorded explicitly because an `∃ b, ∀ D, b ≤ deg D → P D` statement is exactly
the shape that *can* be vacuous, and a reader is entitled to see that ruled out
rather than assumed.  Note the witness needs no rational point: any prime divisor
does, since residue degrees are positive.) -/
theorem exists_degK_ge (b : ℤ) (P : X.PrimeDivisor)
    [Module.Finite k (localStepTgt k P 1)] :
    ∃ n : ℕ, b ≤ degK k ((n : ℤ) • pointDivisor P : X.WeilDivisor) := by
  refine ⟨b.toNat, ?_⟩
  rw [show degK k ((b.toNat : ℤ) • pointDivisor P : X.WeilDivisor)
        = (b.toNat : ℤ) • degK k (pointDivisor P : X.WeilDivisor) from
      map_zsmul (degKHom k) _ _, degK_pointDivisor, smul_eq_mul]
  have h1 : (1 : ℤ) ≤ (residueDeg k P : ℤ) := by
    exact_mod_cast one_le_residueDeg k P
  have hb : b ≤ (b.toNat : ℤ) := Int.self_le_toNat b
  calc b ≤ (b.toNat : ℤ) := hb
    _ = (b.toNat : ℤ) * 1 := by ring
    _ ≤ (b.toNat : ℤ) * (residueDeg k P : ℤ) :=
        mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg _)

/-- **The bound in numerical form.**  Same statement with the conclusion read on
`h¹` rather than on `Subsingleton`; `h1dim` is `0` for a subsingleton without any
finiteness input (`Module.finrank_zero_of_subsingleton`). -/
theorem exists_bound_h1dim_eq_zero
    (hledger : ∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show X.PrimeDivisor →₀ ℤ from D') P) →
      ∀ x ∈ sectionSub k (U₀ ⊓ U₁) D', ∃ y ∈ sectionSub k (U₀ ⊓ U₁) D₀,
        x - y ∈ coboundarySub k U₀ U₁ D') :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D → h1dim k U₀ U₁ D = 0 := by
  obtain ⟨b, hb⟩ :=
    exists_bound_subsingleton_h1Mod k U₀ U₁ hledger D₀ hbase hpeel
  exact ⟨b, fun D hD => h1dim_eq_zero_of_subsingleton k U₀ U₁ (hb D hD)⟩

/-- **Above the bound, `ℓ` is computed exactly by the ledger:**
`ℓ(D) = χ(0) + deg_k D`.  This is the Riemann–Roch conclusion in the vanishing
range — the shape a Grassmannian-embedding or rank-counting consumer wants, since
it turns `ℓ` from an inequality into a formula. -/
theorem ell_eq_of_bound
    (hledger : ∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    {D : X.WeilDivisor} (hvan : Subsingleton (H1Mod k U₀ U₁ D)) :
    (ell k D : ℤ) = chi k U₀ U₁ 0 + degK k D := by
  have hh1 := h1dim_eq_zero_of_subsingleton k U₀ U₁ hvan
  have := hledger D
  rw [chi, hh1] at this
  omega

/-- **Riemann–Roch in the vanishing range, assembled.**  Combining the bound with
`ell_eq_of_bound`: there is a threshold `b` past which `ℓ` is given by the *formula*
`ℓ(D) = χ(0) + deg_k D`, not merely bounded below by it.

This is the single statement a downstream rank-counting consumer should quote: the
Riemann inequality `deg_k D + χ(0) ≤ ℓ(D)` holds always
(`degK_add_chi_zero_le_ell`), and above `b` it is an equality.  With
`χ(0) = 1 − g` for the structure sheaf this is the classical
`ℓ(D) = deg D + 1 − g` for `deg` large.

Conditional on the same three inputs as the bound, and single-field — see the
module docstring for why extension-uniformity and global generation are strictly
more. -/
theorem exists_bound_ell_eq
    (hledger : ∀ D : X.WeilDivisor, chi k U₀ U₁ D = chi k U₀ U₁ 0 + degK k D)
    (D₀ : X.WeilDivisor) (hbase : Subsingleton (H1Mod k U₀ U₁ D₀))
    (hpeel : ∀ D' : X.WeilDivisor,
      (∀ P : X.PrimeDivisor, (show X.PrimeDivisor →₀ ℤ from D₀) P ≤
        (show X.PrimeDivisor →₀ ℤ from D') P) →
      Peel k U₀ U₁ D₀ D') :
    ∃ b : ℤ, ∀ D : X.WeilDivisor, b ≤ degK k D →
      (ell k D : ℤ) = chi k U₀ U₁ 0 + degK k D := by
  obtain ⟨b, hb⟩ :=
    exists_bound_subsingleton_h1Mod k U₀ U₁ hledger D₀ hbase hpeel
  exact ⟨b, fun D hD => ell_eq_of_bound k U₀ U₁ hledger (hb D hD)⟩

end Bound

end Adelic
end AlgebraicGeometry
