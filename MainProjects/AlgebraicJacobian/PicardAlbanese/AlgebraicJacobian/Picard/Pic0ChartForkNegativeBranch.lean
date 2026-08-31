/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartAbelForkReduce
import AlgebraicJacobian.Picard.DivisorFamilyFieldSurj
import AlgebraicJacobian.RiemannRoch.EffectiveNonUniqueness

/-!
# THE `abel-noninj` FORK'S NEGATIVE BRANCH, DISCHARGED AT ANY DEGREE WITH `h⁰ ≥ 2`

`Picard/Pic0ChartAbelForkReduce.lean` reduces the fork to one ring-level statement,
`RelPicSeparatesDivFamZar C π n A`, and closes with the dichotomy: either `n` is a degree
where `h⁰ = 1` (positive branch) or it is not (negative branch, "and a witness exists").
Its own words: *"Neither is decided here."*  Four other files repeat the same open question,
and `Pic0ChartAbelNonInjective.lean:50-56` states what is owed as

> for some curve, some test `T`, and some `n`: two *distinct* elements of `divFamZar C π n T`
> whose `chartValue` agree.

**This file produces that pair.**  It is the negative branch, discharged — not conditionally,
and not at a hand-picked curve: at *every* field test where some effective divisor of the
chart's degree has two sections.

## The chain, and the one link that was missing

Four steps, of which three were already landed and nobody had composed them:

1. **`2 ≤ h⁰` gives two distinct effective divisors of one class.**  This was the missing
   link, and it is now `Scheme.CurveDivisor.exists_two_effective_picClass_eq_of_two_le_h0`
   (`RiemannRoch/EffectiveNonUniqueness.lean`) — the converse of GAP-2's keystone.  It could
   not be got from `exists_effective_of_h0_pos`, which chooses its section inside the
   proof term and so cannot be applied twice to obtain two.
2. **Two distinct effective divisors of degree `n` are realized by divisor families.**
   `exists_divFam_divFamDivisor_eq` (`Picard/DivisorFamilyFieldSurj.lean`) — the surjectivity
   half of the field dictionary, unconditional over any field.  (The bundled
   `divFamFieldEquiv` sits in the same file and is *not* what the proofs below call: the
   realization equations carry distinctness by themselves.)
3. **`DivFam.toZar` is injective**, at an arbitrary commutative ring
   (`Picard/DivRepClassifyZarKit.lean`), so the two survive into the locally certified
   carrier.
4. **Equal classes give equal `chartValue`**, because `relPicMk` is a homomorphism — and
   conversely at a field test the two are the same statement, since `picFromBase` is trivial
   on a one-point space (`Tangent/RelPicPointTest.lean`).

**Citation discipline for this header.**  Five names below live *outside* this file's import
closure and are therefore cited by FILE, never bare: the `Tangent/RelPicPointTest.lean` fact
just mentioned, the two coverage-parameter results in `Picard/Pic0ChartLocusH0Rank.lean`, the
degree-zero producer in `Picard/DivisorFamilyDegreeZeroRep.lean`, and the threshold converse in
`Picard/Pic0ChartCoverageThreshold.lean`.  A name that cannot be `#check`ed from here is a name
this file must not spell as if it could.  Everything the *proofs* use is in closure:
`exists_divFam_divFamDivisor_eq`, `DivFam.toZar_injective`, `picClass_divFamDivisor`,
`deg_eq_deg_of_picClass_eq`, `h0_divisorSheaf_eq_of_picClass_eq`,
`exists_effective_of_h0_pos`, `relPicSeparates_of_injective_chartValue`,
`RelPicSeparatesDivFamZar` and the new brick.

**AND THIS PARAGRAPH ITSELF SHIPPED A PHANTOM, which is the part worth keeping.**  The list
above read `Scheme.exists_effective_of_h0_pos`; the constant has no `Scheme.` prefix.  So the
very sentence declaring that a name which cannot be `#check`ed must not be spelled bare
contained an unresolvable name — and the file failed to compile, because the *proof* used the
same wrong spelling.  A citation-discipline paragraph reads as the audited part of a header,
which is exactly why a phantom survives there: the rule has to be run against its own list.

Three further binder-level defects a fresh-context review found in the first version, all fixed:
`DivFam.toZar_injective`'s ring binder is `S`, not `R`; `picClass_divFamDivisor` needs
`[IsFinite π]`; and the two `Module.Finite` instances on the base-changed curve are not
synthesizable from this file's imports (their producers are out of closure), so they are
explicit binders below.

## What is refuted, and at which degrees

`RelPicSeparatesDivFamZar C π n K` is **false** at every field `K` admitting an effective
divisor of degree `n` with `2 ≤ h⁰`.  By the rank anchor that is every `n > g` on a curve with
vanishing `H¹` at that degree — and `n > g` is where the coverage half of the seam is landed:
`Picard/Pic0ChartLocusH0Rank.lean`'s genus-vs-parameter strictness result puts
`admissibleCoverageParameter` strictly above `g` **for `g ≠ 0`**, and
the same file's uniform admissible chart produces the `2 ≤ h⁰` witness there under the same
`hg : g ≠ 0`.

The `g ≠ 0` binder is not decoration and is stated rather than dropped: at `g = 0` the ledger
parameter can equal the genus (the converse statement is proved in
`Picard/Pic0ChartCoverageThreshold.lean` — cited by **file**, since it is outside this file's
import closure and a name I cannot `#check` here is a name I should not cite), `Pic⁰` is
trivial, and this file's conclusion is then uninteresting rather than false.

So this is not a fact about one row.  It says the two seam antecedents are pulling in
opposite directions along one parameter: antecedent 1 needs `h⁰ = 1`, i.e. `n ≤ g`;
the landed coverage needs `n > g`.

## The `hO` binder is FREE at this carrier, and a consumer should not pay it

Every theorem below carries `hO : h⁰(𝒪) = 1` on `relCurve C K`.  That is **not** an open
obligation and no consumer should treat it as one: `Picard/DivSchemeSeedUnivAssembleKappa.lean`
proves it at *every* field extension `K/k` from the standing curve package alone (proper,
smooth of relative dimension 1, geometrically irreducible), with no further hypothesis.  It is
carried as an explicit argument here only because that module is outside this file's import
closure; a consumer that already imports it can discharge `hO` by `inferInstance`-grade
citation rather than by proving anything.

Recorded because a binder that *looks* like a cohomological hypothesis is exactly the kind a
later round reprices as a gap.  Its cost here is zero at any curve site.

## What this does NOT do, stated at the strength proved

* It does **not** refute `IsChartUniv` or `IsChartLocusFibre` for the atlas the seam actually
  consumes.  The *conditional* `rep` producers of the `DivRep…` layer
  (`DivRepAffPullClause.lean:85`, `DivRepChartRange.lean:97`) each carry an `hchi` binder
  pinning their parameter to the genus, and at `n = g` the linear system is a single point —
  the positive branch.  What is refuted is the separation statement at degrees **above** the
  genus.

  **A correction to the natural way of saying that, which I first wrote and which is false.**
  It is *not* true that "every `rep` producer pins `n = genus C`": the one unconditional
  producer in the tree (the degree-zero representation of
  `Picard/DivisorFamilyDegreeZeroRep.lean`) is at `n = 0` and carries **no** `hchi` at all.
  The `hchi` claim is about the conditional producers only, and it is `n = 0` — the parameter
  where a producer actually exists — that this file says nothing about, since `2 ≤ h⁰` fails
  there (the degree-zero divisor functor is subsingleton-valued).
* It does **not** exhibit a divisor with `2 ≤ h⁰` for a specific curve; the `hh0` hypothesis
  of the theorems below is discharged elsewhere (see above) and is carried explicitly here.
* It does **not** settle the general-test question.  Every witness below lives at a **field**
  test, which is legal precisely because *refuting* injectivity needs one test — the standing
  caveat of `Pic0ChartAbelNonInjective.lean` (a fibrewise anchor cannot settle a general-test
  statement) binds the *positive* branch, where a statement must hold at every test.

## Main declarations

* `AlgebraicGeometry.exists_two_divFamZar_picClass_eq_of_two_le_h0` — the pair, in the
  locally certified carrier over a field.
* `AlgebraicGeometry.not_relPicSeparatesDivFamZar_of_two_le_h0` — **the fork's residue,
  REFUTED** at a field of that degree.
* `AlgebraicGeometry.not_injective_chartValue_of_two_le_h0` — hence `chartValue` is not
  injective at that field test, which is the fork's own statement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The pair in the locally certified carrier -/

/-- **TWO DISTINCT LOCALLY CERTIFIED FAMILIES WITH EQUAL CLASS.**

Steps 1–3 of the chain composed: the two effective divisors of
`exists_two_effective_picClass_eq_of_two_le_h0` are realized as divisor families by the
dictionary's surjectivity half (`exists_divFam_divFamDivisor_eq`), then pushed through
`DivFam.toZar`, injective at an arbitrary ring.  Classes agree by `picClass_divFamDivisor`.

**On which half of the dictionary is used.**  The `divFamFieldEquiv` bundle is not applied:
distinctness comes from the two realization *equations* `divFamDivisor Gᵢ = Dᵢ` directly (if
the `toZar`s agreed then `toZar_injective` would identify `G₁ = G₂`, hence `D₁ = D₂`), so only
surjectivity of `divFamDivisor` is consumed here and `divFamDivisor_injective` is not.  An
earlier version of this paragraph credited the equiv and its injectivity, which is a nearby
true statement about a lemma the proof never calls. -/
theorem exists_two_divFamZar_picClass_eq_of_two_le_h0
    [IsFinite π] {K : Type u} [Field K] [Algebra k K]
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (A : (relCurve C K).CurveDivisor) (hA : 0 ≤ A)
    (hdegA : Scheme.CurveDivisor.deg K A = (n : ℤ))
    (hh0 : 2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K A)) :
    ∃ F₁ F₂ : DivFamZar C K π n, F₁ ≠ F₂ ∧ F₁.picClass = F₂.picClass := by
  -- step 1: the pair of effective divisors
  obtain ⟨D₁, D₂, hD₁, hD₂, hne, hcl₁, hcl₂⟩ :=
    Scheme.CurveDivisor.exists_two_effective_picClass_eq_of_two_le_h0 K hO hA hh0
  -- their degrees are `n`, transported along the class equalities
  have hdeg₁ : Scheme.CurveDivisor.deg K D₁ = (n : ℤ) :=
    (deg_eq_deg_of_picClass_eq (K := K) hcl₁).trans hdegA
  have hdeg₂ : Scheme.CurveDivisor.deg K D₂ = (n : ℤ) :=
    (deg_eq_deg_of_picClass_eq (K := K) hcl₂).trans hdegA
  -- step 2: cross the field dictionary
  obtain ⟨G₁, hG₁⟩ := exists_divFam_divFamDivisor_eq (C := C) (π := π) (n := n) D₁ hD₁ hdeg₁
  obtain ⟨G₂, hG₂⟩ := exists_divFam_divFamDivisor_eq (C := C) (π := π) (n := n) D₂ hD₂ hdeg₂
  -- step 3: `toZar`, injective at an arbitrary ring
  refine ⟨G₁.toZar, G₂.toZar, ?_, ?_⟩
  · intro h
    exact hne (hG₁.symm.trans ((congrArg divFamDivisor
      (DivFam.toZar_injective (C := C) (S := K) (π := π) (n := n) h)).trans hG₂))
  · -- the classes agree, read through `picClass_divFamDivisor`
    rw [DivFamZar.picClass_toZar, DivFamZar.picClass_toZar,
      ← picClass_divFamDivisor (L := K) G₁, ← picClass_divFamDivisor (L := K) G₂, hG₁, hG₂,
      hcl₁, hcl₂]

/-! ## Effectivity is recoverable, so a chart-locus witness qualifies

`IsSplitWitness` — hence every chart-locus witness — carries **no** `0 ≤ W` clause; its own
docstring says so deliberately, because the GAP-6 dictionary it comes from cannot see
effectivity.  So a consumer holding `exists_splitting_two_le_h0_of_mem_chartLocus`'s output
cannot feed the theorems above directly.  It does not have to: `h⁰` and `deg` are both class
invariants, and `exists_effective_of_h0_pos` moves to an effective representative of the same
class, carrying both numbers along. -/

/-- **From a possibly-non-effective divisor with two sections to an effective one.**

The bridge a chart-locus consumer needs, so that the missing `0 ≤ W` clause of `IsSplitWitness`
costs nothing: replace `W` by an effective divisor of the same class, whose `h⁰` and degree are
the same numbers by `h0_divisorSheaf_eq_of_picClass_eq` and `deg_eq_deg_of_picClass_eq`. -/
theorem exists_effective_deg_two_le_h0_of_two_le_h0
    [IsFinite π] {K : Type u} [Field K] [Algebra k K]
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (W : (relCurve C K).CurveDivisor)
    (hdegW : Scheme.CurveDivisor.deg K W = (n : ℤ))
    (hh0 : 2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K W)) :
    ∃ A : (relCurve C K).CurveDivisor, 0 ≤ A ∧
      Scheme.CurveDivisor.deg K A = (n : ℤ) ∧
      2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K A) ∧
      Scheme.CurveDivisor.picClass K A = Scheme.CurveDivisor.picClass K W := by
  obtain ⟨A, hAe, hAcl⟩ := exists_effective_of_h0_pos K W (by omega)
  refine ⟨A, hAe, ?_, ?_, hAcl⟩
  · exact (deg_eq_deg_of_picClass_eq (K := K) hAcl).trans hdegW
  · rw [h0_divisorSheaf_eq_of_picClass_eq (K := K) hAcl]; exact hh0

/-! ## The residue, refuted -/

/-- **`RelPicSeparatesDivFamZar` IS FALSE at a field of a degree carrying two sections.**

`Pic0ChartAbelForkReduce.lean` names this `Prop` as the whole of what the fork's positive
branch owes, and proves it *equivalent* to injectivity of `chartValue`.  Two distinct families
with equal Čech class have equal `relPicMk`-image by `congrArg` — the quotient can only merge
more — so the separation fails.

**The `picFromBase` triviality is NOT used here, and saying so is the point.**  Step 4 of the
chain in the header describes the field test as the place where `relPicMk` is injective
(`Tangent/RelPicPointTest.lean`), which is true and is what makes the *converse*
direction available.  For the refutation it is not needed at all: passing to a quotient
preserves equality, and only equality is required.  So this refutation would survive a test
where `picFromBase` is nontrivial, which the earlier draft of this docstring implied it would
not. -/
theorem not_relPicSeparatesDivFamZar_of_two_le_h0
    [IsFinite π] {K : Type u} [Field K] [Algebra k K]
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (A : (relCurve C K).CurveDivisor) (hA : 0 ≤ A)
    (hdegA : Scheme.CurveDivisor.deg K A = (n : ℤ))
    (hh0 : 2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K A)) :
    ¬ RelPicSeparatesDivFamZar C π n K := by
  intro hsep
  obtain ⟨F₁, F₂, hne, hcl⟩ :=
    exists_two_divFamZar_picClass_eq_of_two_le_h0 (π := π) (n := n) hO A hA hdegA hh0
  exact hne (hsep (congrArg (relPicMk C (overSpec k K)) hcl))

/-- **THE FORK'S OWN STATEMENT: `chartValue` is NOT injective at that field test.**

`Pic0ChartAbelForkReduce.lean`'s `relPicSeparates_of_injective_chartValue` says injectivity of
`chartValue` at the affine test `Spec K` *gives* the residue at `K`.  The previous theorem
refutes the residue, so it refutes the injectivity — and non-injectivity of `chartValue` is
literally the hypothesis the fork's negative branch consumes
(`not_isChartLocusFibre_of_divFamZar` takes two distinct sections with equal `chartValue`).

Needs `[GeometricallyReduced C.hom]`, which is where the plus-unit step of that reduction lives;
the standing package of this file does not carry it, so it is an explicit binder here. -/
theorem not_injective_chartValue_of_two_le_h0 [GeometricallyReduced C.hom]
    [IsFinite π] {K : Type u} [Field K] [Algebra k K]
    [IsIntegral (relCurve C K)]
    [SmoothOfRelativeDimension 1 (relCurve C K ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (relCurve C K ↘ Spec (CommRingCat.of K))]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 0)]
    [Module.Finite K (Sheaf.HModule ((relCurve C K).moduleKSheaf K) 1)]
    (hO : Sheaf.h0 ((relCurve C K).moduleKSheaf K) = 1)
    (A : (relCurve C K).CurveDivisor) (hA : 0 ≤ A)
    (hdegA : Scheme.CurveDivisor.deg K A = (n : ℤ))
    (hh0 : 2 ≤ Sheaf.h0 ((relCurve C K).divisorSheaf K A))
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    ¬ Function.Injective (chartValue C π n m Z (overSpec k K)) := fun hinj =>
  not_relPicSeparatesDivFamZar_of_two_le_h0 (π := π) (n := n) hO A hA hdegA hh0
    (relPicSeparates_of_injective_chartValue C π n m Z K hinj)

end

end AlgebraicGeometry
