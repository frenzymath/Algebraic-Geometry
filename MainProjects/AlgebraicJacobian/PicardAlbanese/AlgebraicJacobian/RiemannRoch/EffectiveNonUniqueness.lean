/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.RiemannRoch.EffectiveUniqueness
import AlgebraicJacobian.RiemannRoch.SectionBound

/-!
# The converse of GAP-2: `h⁰ ≥ 2` gives TWO distinct effective divisors in one class

`RiemannRoch/EffectiveUniqueness.lean` lands the keystone
`Scheme.CurveDivisor.eq_of_picClass_eq_of_h0_one`: at `h⁰ = 1` the effective representative
of a class is unique.  Everything in the chart layer of this project consumes that direction.
**Nothing consumes, and nothing states, the converse** — and the converse is the entire
negative branch of the `abel-noninj` fork.

## Why this file exists rather than an `exists_effective_of_h0_pos` call

`Scheme.exists_effective_of_h0_pos` (`SectionBound.lean:175`) already turns a *positive* `h⁰`
into an effective representative.  It cannot be used twice to get two: its proof picks a
section with `exists_ne (0 : …)` inside the proof term, so it is an existential and not a
function of the section.  Feeding it the same class twice returns the same unspecified
witness, and there is no `divisorOfSection` map in the project to compare two sections
through (measured: no declaration named `divisorOfSection`, `sectionDivisor`, `divOfSection`,
`zerosDivisor` or `toDivisor`-of-a-section exists anywhere in the tree).

So the content here is the *pairing*, and it is exactly the classical statement that a
linear system of dimension `≥ 2` has two distinct members:

* `1 ∈ H⁰(𝒪(A))` when `A` is effective (`one_mem_divisorSections_top`, landed);
* `2 ≤ h⁰` means `H⁰(𝒪(A))` is not the span of `1`, so some `f` lies outside it;
* `A + div f` and `A + div 1 = A` are both effective and in the class of `A`;
* they are **distinct**, because `A + div f = A` gives `div f = 0`, and a rational function
  with trivial principal divisor is a constant *provided `h⁰(𝒪_X) = 1`* — the standing
  normalization `hO` this project threads through every ledger statement.

## The one hypothesis beyond the standing package, and why it is not a new hypothesis

`hO : Sheaf.h0 (X.moduleKSheaf K) = 1`.  It is the `hO` of the window ledger, of
`divFam_divEq_of_eps_eq_total` and of every `IsCertified`-consumer in the project; it holds
for a proper geometrically-integral curve and is the normalization the whole `RiemannRoch`
directory is stated against.  It is *load-bearing here*, not decoration: on a curve with
`h⁰(𝒪) ≥ 2` (a disconnected or non-reduced bundle) a nonconstant function can have trivial
divisor and the two members could coincide.

## What this does NOT claim

It does not exhibit a divisor with `2 ≤ h⁰` — that is supplied elsewhere
(`Picard/Pic0ChartLocusH0Rank.lean` produces one at the admissible coverage parameter, over a
finite separable extension of a test point's residue field).  This file is the bridge from
that hypothesis to a *pair*, and the pair is what the fork's negative branch consumes.

It also does not conclude anything about effectivity of the divisor a chart-locus witness
names: `IsSplitWitness` carries no `0 ≤ W` clause, so a consumer must re-supply effectivity
through the class (`exists_effective_of_h0_pos` does that, and its output is effective by
construction).  `exists_two_effective_picClass_eq_of_two_le_h0` below is stated so that it
takes an *effective* `A`, and `exists_two_effective_of_two_le_h0_of_picClass` handles the
non-effective case by first normalizing.

## Main declarations

* `Scheme.eq_functionFieldOverAlgebraMap_of_divOf_eq_zero` — **the converse of
  `divOf_eq_zero_of_val_eq_functionFieldOverAlgebraMap`**: at `h⁰(𝒪_X) = 1` a unit with
  trivial principal divisor is a constant.
* `Scheme.CurveDivisor.exists_two_effective_picClass_eq_of_two_le_h0` — **the payoff**: from
  `0 ≤ A` and `2 ≤ h⁰(𝒪(A))`, two effective divisors of the class of `A` that are distinct.
* `Scheme.CurveDivisor.not_forall_eq_of_two_le_h0` — the same fact as the **refutation of
  uniqueness**: no effective divisor of the class is the unique one.  This is the exact negation
  of the shape a chart-locus uniqueness statement produces.
* `Scheme.CurveDivisor.two_le_h0_iff_exists_two_effective` — **the equivalence with the landed
  keystone**, so this file is a converse and not a parallel statement: the `←` direction is the
  keystone `eq_of_picClass_eq_of_h0_one` contraposed, through the class-invariance of `h⁰`.

**This list was wrong when the file first landed, and the correction is the reusable part.**  It
advertised three declarations the file did not contain, including the equivalence — the item the
whole "this is a converse" claim rests on.  A "Main declarations" census is prose, so no `sorry`
check, axiom probe or green build says anything about it.  The two names above are now theorems;
a third phantom (`exists_two_effective_of_two_le_h0_of_picClass`, a non-effective-input variant)
is deleted rather than proved, because `exists_effective_of_h0_pos` already normalizes an
arbitrary class to an effective representative and a consumer should call that. -/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.functionFieldOverModule Scheme.overModule

namespace Scheme

variable (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))] [IsIntegral X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]

/-! ## The converse of "constants have trivial divisor" -/

/-- **A unit with trivial principal divisor is a constant, at `h⁰(𝒪_X) = 1`.**

`div g = 0` puts `g` in `H⁰(𝒪(0))`, whose dimension is `h⁰(𝒪(0)) = h⁰(𝒪_X) = 1` by the
anchor isomorphism `divisorSheafZeroIso`.  The constant `1` is a nonzero member of the same
line, so `g` is a scalar multiple of it.

This is the exact converse of
`divOf_eq_zero_of_val_eq_functionFieldOverAlgebraMap`, and the hypothesis `hO` is what makes
it a converse rather than a different statement: on a bundle with `h⁰(𝒪) ≥ 2` it is false. -/
theorem eq_functionFieldOverAlgebraMap_of_divOf_eq_zero
    (hO : Sheaf.h0 (X.moduleKSheaf K) = 1) {g : X.functionFieldˣ}
    (hg : Scheme.divOf (X ↘ Spec (CommRingCat.of K)) g = 0) :
    ∃ c : K, (g : X.functionField) = functionFieldOverAlgebraMap K X c := by
  -- `H⁰(𝒪(0))` is one-dimensional
  have hzero : Module.finrank K ↥(divisorSections K (0 : X.CurveDivisor) ⊤) = 1 := by
    rw [finrank_divisorSections_top, Sheaf.h0_congr (divisorSheafZeroIso K)]
    exact hO
  -- `g` and `1` both lie in it
  have hgmem : (g : X.functionField) ∈ divisorSections K (0 : X.CurveDivisor) ⊤ := by
    rw [mem_divisorSections_top_iff K g.ne_zero]
    have hmk : Units.mk0 (g : X.functionField) g.ne_zero = g := Units.ext rfl
    rw [hmk, hg, add_zero]
  have h1mem : (1 : X.functionField) ∈ divisorSections K (0 : X.CurveDivisor) ⊤ :=
    one_mem_divisorSections_top K le_rfl
  have h1ne : (⟨1, h1mem⟩ : ↥(divisorSections K (0 : X.CurveDivisor) ⊤)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨1, h1mem⟩ :
    ↥(divisorSections K (0 : X.CurveDivisor) ⊤)) h1ne).mp hzero
    ⟨(g : X.functionField), hgmem⟩
  refine ⟨c, ?_⟩
  have h : c • (1 : X.functionField) = (g : X.functionField) := congrArg Subtype.val hc
  rw [← h, functionFieldOverModule_smul_def, mul_one]

/-! ## The pair -/

/-- **THE PAYOFF — a linear system of dimension `≥ 2` has two distinct members.**

From `0 ≤ A` and `2 ≤ h⁰(𝒪(A))`: two effective divisors, both in the class of `A`, distinct.

The pair is `A` itself and `A + div f`, where `f` is a global section of `𝒪(A)` **outside the
line spanned by `1`** — which exists precisely because `h⁰ ≥ 2` (if every section were a
multiple of `1` the dimension would be `1`).  Effectivity of `A + div f` is membership of `f`
in `H⁰(𝒪(A))` read through `mem_divisorSections_top_iff`; the class is unchanged because a
principal divisor has trivial class.

**Distinctness is where the work is, and it is where `hO` is consumed.**  If the two coincided
then `div f = 0`, and `eq_functionFieldOverAlgebraMap_of_divOf_eq_zero` would make `f` a
constant — i.e. a multiple of `1`, contradicting the choice of `f`.  That step is the only use
of `hO` and it is not removable: with `h⁰(𝒪_X) ≥ 2` a nonconstant function can have trivial
divisor and the two members can coincide.

Note the shape: the second member is produced from the *same* section that witnesses
`h⁰ ≥ 2`, which is what `exists_effective_of_h0_pos` cannot do — it quantifies its section
away inside the proof term. -/
theorem CurveDivisor.exists_two_effective_picClass_eq_of_two_le_h0
    (hO : Sheaf.h0 (X.moduleKSheaf K) = 1) {A : X.CurveDivisor} (hA : 0 ≤ A)
    (hh0 : 2 ≤ Sheaf.h0 (X.divisorSheaf K A)) :
    ∃ D D' : X.CurveDivisor, 0 ≤ D ∧ 0 ≤ D' ∧ D ≠ D' ∧
      CurveDivisor.picClass K D = CurveDivisor.picClass K A ∧
      CurveDivisor.picClass K D' = CurveDivisor.picClass K A := by
  classical
  -- `1 ∈ H⁰(𝒪(A))`, and `H⁰(𝒪(A))` is not the line it spans
  have h1mem : (1 : X.functionField) ∈ divisorSections K A ⊤ :=
    one_mem_divisorSections_top K hA
  set one' : ↥(divisorSections K A ⊤) := ⟨1, h1mem⟩ with hone'
  have h1ne : one' ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  -- if every section were a multiple of `1`, the dimension would be `1`, contradicting `2 ≤ h⁰`
  have hnotall : ¬ ∀ w : ↥(divisorSections K A ⊤), ∃ c : K, c • one' = w := by
    intro hall
    have hrank : Module.finrank K ↥(divisorSections K A ⊤) = 1 :=
      (finrank_eq_one_iff_of_nonzero' one' h1ne).mpr hall
    rw [finrank_divisorSections_top] at hrank
    omega
  obtain ⟨w, hw⟩ := not_forall.mp hnotall
  -- the section `f` outside the span of `1`; it is nonzero, since `0 = 0 • 1`
  set f : X.functionField := (w : X.functionField) with hf
  have hfne : f ≠ 0 := by
    intro h0
    refine hw ⟨0, Subtype.ext ?_⟩
    change (0 : K) • (1 : X.functionField) = f
    rw [functionFieldOverModule_smul_def, map_zero, zero_mul]
    exact h0.symm
  set u : X.functionFieldˣ := Units.mk0 f hfne with hu
  -- `A + div f` is effective and in the class of `A`
  have hume : (f : X.functionField) ∈ divisorSections K A ⊤ := w.2
  have hueff : 0 ≤ A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u :=
    (mem_divisorSections_top_iff K hfne).mp hume
  refine ⟨A, A + Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u, hA, hueff, ?_, rfl, ?_⟩
  · -- distinctness: equality forces `div f = 0`, hence `f` constant, hence in the span of `1`
    intro heq
    have hdiv0 : Scheme.divOf (X ↘ Spec (CommRingCat.of K)) u = 0 := by
      have := heq.symm
      rwa [add_eq_left] at this
    obtain ⟨c, hc⟩ := eq_functionFieldOverAlgebraMap_of_divOf_eq_zero K hO hdiv0
    refine hw ⟨c, Subtype.ext ?_⟩
    change c • (1 : X.functionField) = f
    rw [functionFieldOverModule_smul_def, mul_one]
    exact hc.symm
  · -- the class is unchanged by a principal divisor
    rw [CurveDivisor.picClass_add, CurveDivisor.picClass_divOf, mul_one]

/-! ## The two forms the "Main declarations" list advertises -/

/-- **THE REFUTATION OF UNIQUENESS.**  At `2 ≤ h⁰` no effective divisor of the class is *the*
unique effective representative — the exact negation of the shape a chart-locus uniqueness
statement produces.

Stated with the uniqueness clause quantified over the same class rather than over a fixed
divisor, because that is the form the consumers use. -/
theorem CurveDivisor.not_forall_eq_of_two_le_h0
    (hO : Sheaf.h0 (X.moduleKSheaf K) = 1) {A : X.CurveDivisor} (hA : 0 ≤ A)
    (hh0 : 2 ≤ Sheaf.h0 (X.divisorSheaf K A)) :
    ¬ ∃ E : X.CurveDivisor, 0 ≤ E ∧
        CurveDivisor.picClass K E = CurveDivisor.picClass K A ∧
        ∀ E' : X.CurveDivisor, 0 ≤ E' →
          CurveDivisor.picClass K E' = CurveDivisor.picClass K A → E' = E := by
  rintro ⟨E, -, -, hEu⟩
  obtain ⟨D, D', hD, hD', hne, hcl, hcl'⟩ :=
    CurveDivisor.exists_two_effective_picClass_eq_of_two_le_h0 K hO hA hh0
  exact hne ((hEu D hD hcl).trans (hEu D' hD' hcl').symm)

/-- **THE EQUIVALENCE WITH THE LANDED KEYSTONE**, so this file is a converse and not a parallel
statement.

`→` is the payoff above.  `←` is the keystone `eq_of_picClass_eq_of_h0_one` contraposed: given
two distinct effective divisors of one class, `h⁰` of that class cannot be `1`; it is positive
because an effective divisor has the section `1`; so it is at least `2`.  The passage between
"`h⁰` of `A`" and "`h⁰` of a class member" is `h0_divisorSheaf_eq_of_picClass_eq`. -/
theorem CurveDivisor.two_le_h0_iff_exists_two_effective
    [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule (X.moduleKSheaf K) 1)]
    (hO : Sheaf.h0 (X.moduleKSheaf K) = 1) {A : X.CurveDivisor} (hA : 0 ≤ A) :
    2 ≤ Sheaf.h0 (X.divisorSheaf K A) ↔
      ∃ D D' : X.CurveDivisor, 0 ≤ D ∧ 0 ≤ D' ∧ D ≠ D' ∧
        CurveDivisor.picClass K D = CurveDivisor.picClass K A ∧
        CurveDivisor.picClass K D' = CurveDivisor.picClass K A := by
  refine ⟨fun hh0 =>
    CurveDivisor.exists_two_effective_picClass_eq_of_two_le_h0 K hO hA hh0, ?_⟩
  rintro ⟨D, D', hD, hD', hne, hcl, hcl'⟩
  -- otherwise `h⁰(𝒪(D)) ≤ 1`; the keystone then needs it to be exactly `1`, and `h⁰ = 0` is
  -- refuted because `1` is a section of the effective `D`
  rcases Nat.lt_or_ge (Sheaf.h0 (X.divisorSheaf K A)) 2 with hlt | hge
  · exfalso
    have hD0 : Sheaf.h0 (X.divisorSheaf K D) = Sheaf.h0 (X.divisorSheaf K A) :=
      h0_divisorSheaf_eq_of_picClass_eq (K := K) hcl
    -- `h⁰(𝒪(D)) ≠ 0`: `1 ∈ H⁰(𝒪(D))` is a nonzero element, so the section space is nontrivial
    -- and a `finrank` of `0` over a field would make it a subsingleton
    have hne0 : Sheaf.h0 (X.divisorSheaf K D) ≠ 0 := by
      intro h0
      have hzero : Module.finrank K ↥(divisorSections K D ⊤) = 0 := by
        rw [finrank_divisorSections_top]; exact h0
      haveI hntriv : Nontrivial ↥(divisorSections K D ⊤) :=
        ⟨⟨⟨1, one_mem_divisorSections_top K hD⟩, 0, fun h =>
          one_ne_zero (congrArg Subtype.val h)⟩⟩
      exact ((Module.finrank_pos_iff_of_free (R := K)
        (M := ↥(divisorSections K D ⊤))).mpr hntriv).ne' hzero
    have hone : Sheaf.h0 (X.divisorSheaf K D) = 1 := by omega
    exact hne (CurveDivisor.eq_of_picClass_eq_of_h0_one K hD hD'
      (hcl.trans hcl'.symm) hone).symm
  · exact hge

end Scheme

end AlgebraicGeometry
