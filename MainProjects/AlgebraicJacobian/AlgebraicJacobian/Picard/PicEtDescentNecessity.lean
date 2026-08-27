/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import AlgebraicJacobian.Picard.PicEtInvariantMatch

/-!
# The descent route is NOT a detour, and one of its four inputs is not an input

`AJC.picrep.etale-rep.descent-necessity`.

## The question this file answers, and why nobody had asked it

Four lanes have spent four rounds supplying **inputs** of
`Scheme.PicScheme.seamClauseOne_of_isGaloisQuotient` — a `k'`-side representation
`rep`, a Galois quotient `hq`, the covering statement `hcov`, and local finiteness
`hlft` of the quotient. What had never been measured is whether those are the
**right** four: which of them the theorem's own *conclusion* already implies, and
which are therefore consequences rather than obligations.

Two answers, and they go in opposite directions.

**1. `rep` is NECESSARY, not merely sufficient.** Clause (1) field 1 over `k` — a
`k`-scheme representing `picEt C` — *produces* a `k'`-scheme representing
`picEt (C_{k'})`, namely the base change of that very scheme
(`representableBy_picEt_baseChangeField_of_representableBy`). So the campaign's
undischarged output is not one sufficient route among several: any solution of the
seam contains one. Nobody can close field 1 over `k` and leave `rep` unwitnessed.

**2. `hlft` may be TRADED for the `k'`-side condition — and that is a relabelling,
not a subtraction. THIS IS A CORRECTION OF WHAT THIS FILE FIRST PUBLISHED.** The first
revision said `hlft` "is NOT an independent input" and that the resulting form "owes
three inputs, not four". **Both sentences are false**, refuted by a fresh-context audit
(`I-1591`) and reproduced here before accepting: the converse of §3 closes in three
lines from the *same* destructuring of `hq`,

    obtain ⟨e, he, -, -⟩ := hq
    have h : X'.hom = e.inv ≫ pullback.snd Y.hom (specMapAlgebra k k') := by
      rw [← he, Iso.inv_hom_id_assoc]

so `LocallyOfFiniteType Y.hom` and `LocallyOfFiniteType X'.hom` are **interderivable
under `hq`**, and the four-input theorem is recoverable from §5's "three-input" one.

**Why the error was structural and not a slip.** `IsGaloisQuotient`'s *first field is
an isomorphism* `Y_{k'} ≅ X'`. Any property transported along it goes both ways by
construction, so a forward proof measures nothing except that the iso is there — which
the hypothesis already gave. The general rule, worth more than this file's result: when
a hypothesis swap runs through a structure that already contains an iso between the two
objects, prove the converse *before* publishing a reduction.

What survives is genuinely narrower: §5 is a **restatement at a different coordinate**,
useful only where a lane holds the `k'`-side condition and not the `k`-side one.
`locallyOfFiniteType_pullback_of_locallyOfFiniteType` (§3b) does not rescue the
stronger claim either — §5's `X'` is an arbitrary `k'`-object, not the base change of
anything, so §3b does not apply to it (type mismatch, measured).

## The direction that matters for a costing, stated precisely

These two facts are **not** the same shape and must not be quoted as one.

Fact 1 is an implication *out of* the conclusion, so it can only make the route look
better-aimed; it discharges nothing. In particular it is **not** a producer of
`rep`: its hypothesis is field 1 over `k`, which is exactly what the seam `sorry`
`Scheme.fgaPicardRepresentability` still owes and what no curve witnesses.

Fact 2 is **not** a subtraction — see the correction above. It is a change of
coordinate on one hypothesis, and the reusable part of it is the *lesson*, not the
lemma.

## What the two facts do together, and where the slack is

§7 shows the seam *implies* `rep`, at an arbitrary extension and so at `k^s`. That is
the durable half. **What it does NOT give is a two-way pinning of the route**, and the
first revision of this paragraph claimed one: §5's hypothesis list is the same length as
the landed theorem's (see §5), and the loop does not even typecheck at one field — §5
binds `[Module.Finite k k']`, which fails at `SeparableClosure k`, while §7 only runs
there. So the honest statement is one-directional: no `k`-side argument can bypass the
base change, because the base-changed representation is a consequence of the goal.

§4 was written as the boundary of that claim, and it is **weaker than first published**
(`I-1590`): it measures the pullback action, not the
`semilinearGalActionOfRepresentableBy` action every landed descent theorem consumes, and
the two are not interchangeable (type mismatch, measured). So §4 does not by itself
forbid the over-reading. What does forbid it is plainer: §2's conclusion is the `rep`
*input*, and `hq` at the consumed action is untouched by it — including a per-γ equality
that no lemma in the tree closes. "The inputs are equivalent to the conclusion" remains
**false**, but for that reason rather than §4's.

## What is NOT claimed

* **No `sorry` is closed.** `Scheme.fgaPicardRepresentability` is untouched and is
  used here only as an axiom control. Clause (1) field 1 is witnessed for no curve.
* **Fact 1 is not a converse of the descent theorem.** It says field 1 over `k`
  implies the `rep` *input*; it does not imply `hq`, and §4 measures exactly how much
  of `hq` it does give (clauses 1 and 2, not clause 3). So "the four inputs are
  equivalent to the conclusion" is **false** and is not asserted anywhere below.
* **`hcov` is untouched.** It is `AJC.picrep.etale-rep.hcov` (`pic-a`'s row).

## How generic the necessity step is — measured, not guessed

`representableByCompLeftAdjoint` is the whole content of fact 1 with **every**
geometric hypothesis deleted: an arbitrary adjunction `L ⊣ R` between arbitrary
categories, an arbitrary presheaf, no scheme, no field, no curve. The Picard
statement is that lemma at `Over.mapPullbackAdj (specMapAlgebra k k')`, and the
`picEt`-specific step is only `picEt_crossBaseIso`. Recorded at that generality on
purpose: a reader must not budget a descent or base-change argument for it.

Reference: Kleiman, "The Picard scheme", §4 Thm. `th:main` (arXiv:math/0504020).
-/

set_option autoImplicit false

universe v u w

open CategoryTheory Limits Opposite AlgebraicGeometry

/-! ## §1. The generic transport: representability along a left adjoint

No schemes, no fields, no Picard functor. If `L ⊣ R` and `F` is represented by `X`,
then `L.op ⋙ F` is represented by `R.obj X` — the adjunction bijection *is* the
required natural bijection, and its naturality clause is
`Adjunction.homEquiv_naturality_left_symm`.

This is stated first, and at this generality, because the descent-necessity theorem
of §2 is *nothing else*: reading it as a geometric fact about base change is the
mispricing this file exists to prevent. -/

namespace CategoryTheory

/-- **Representability transports along a left adjoint.**

Fully generic. **The reason this is not simply a mathlib citation is the VALUE
UNIVERSE, and the first revision of this docstring gave a wrong reason** (`I-1593`,
fresh-context audit; reproduced). It said mathlib's transports "transport along the
functor being represented, or represent a `yoneda.obj`", implying no mathlib route
exists. There is one, in a single line, for a `Type v`-valued presheaf:

    (adj.representableBy X).ofIso (Functor.isoWhiskerLeft L.op rep.toIso)

which elaborates (`EXIT=0`). What it cannot do is reach the site this file needs:
`Adjunction.representableBy` pins the presheaf's value universe to the hom universe,
while `picEt` is `Type (u+1)`-valued over `Scheme.{u}`, so both the
universe-independent form and the Picard instance fail there with universe mismatches.
The declaration is worth keeping for exactly that reason and for no other.

Declared in `CategoryTheory`, not `AlgebraicGeometry`: it mentions no scheme, and a
reader who finds it under the geometric namespace would reasonably assume it does. -/
noncomputable def Functor.representableByCompLeftAdjoint {C : Type u} {D : Type u}
    [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {F : Dᵒᵖ ⥤ Type w} {X : D} (rep : F.RepresentableBy X) :
    (L.op ⋙ F).RepresentableBy (R.obj X) where
  homEquiv {T} := (adj.homEquiv T X).symm.trans rep.homEquiv
  homEquiv_comp {T T'} f g := by
    simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_left_symm]
    exact rep.homEquiv_comp _ _

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §2. FACT 1 — the `k'`-side representation is NECESSARY -/

/-- **The restricted functor is represented by the base change**, for an arbitrary
field extension.

`restrictTest k k' = Over.map (specMapAlgebra k k')` is a left adjoint, with right
adjoint `Over.pullback (specMapAlgebra k k')`, so §1 applies verbatim. No hypothesis
on `k'/k`: not finite, not separable, not normal. -/
noncomputable def representableByRestrictTest_of_representableBy
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (picEt C).RepresentableBy X) :
    ((restrictTest k k').op ⋙ picEt C).RepresentableBy
      ((Over.pullback (specMapAlgebra k k')).obj X) :=
  Functor.representableByCompLeftAdjoint (Over.mapPullbackAdj (specMapAlgebra k k')) rep

/-- **THE NECESSITY THEOREM: field 1 of clause (1) over `k` PRODUCES the descent
route's `k'`-side input.**

Given a `k`-scheme `X` representing `picEt C`, the base change `X_{k'}` represents
`picEt (C_{k'})` — the Picard functor of the base-changed curve over `k'`, which is
exactly the `rep` hypothesis of
`Scheme.PicScheme.seamClauseOne_of_isGaloisQuotient` and of every theorem in
`Picard/PicEtDescentGoal.lean`.

**What this buys, and it is a statement about the ROUTE, not a discharge.** The
descent route is not one sufficient strategy among several that a cheaper `k`-side
argument might bypass: *any* solution of clause (1) field 1 carries a solution of
`rep` inside it. So `rep`'s 93 consumers and 0 producers is not a sign that the route
is badly chosen — the object it asks for is a consequence of the goal.

**What it does NOT buy.** Its hypothesis is the seam's own open obligation, so it
witnesses nothing. It also does not give `hq` at the action the route consumes: §4
measures the *pullback* action instead, and per `I-1590` the two are not interchangeable,
so `hq` is untouched here.

Two hypotheses it does *not* carry, both of which a reader would expect: no
finiteness and no separability of `k'/k`. Those are input 1's price
(`Scheme.picEt_ext_of_pullback_agrees`), and the same double-count has been corrected
twice in this cluster already. The proof is §1 plus `picEt_crossBaseIso`, and the
latter holds for an arbitrary field extension. -/
noncomputable def representableBy_picEt_baseChangeField_of_representableBy
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (picEt C).RepresentableBy X) :
    (picEt (Scheme.baseChangeField C k')).RepresentableBy
      ((Over.pullback (specMapAlgebra k k')).obj X) :=
  (representableByRestrictTest_of_representableBy (k' := k') C rep).ofIso
    (picEt_crossBaseIso C k').symm

/-! ## §3. FACT 2 — `hlft` is a consequence, not an input

`Scheme.PicScheme.seamClauseOne_of_isGaloisQuotient` carries
`(hlft : LocallyOfFiniteType Y.hom)` as a fourth hypothesis beside `rep`, `hq` and
`hcov`. It need not: the quotient's own isomorphism `e` identifies `Y_{k'}` with
`X'`, and `Picard/PicEtSeparated.lean`'s `locallyOfFiniteType_of_baseChange` descends
the property back to `Y`. So `hlft` is derivable from a condition on the object the
`k'`-side representation already names. -/

/-- **Local finiteness of the quotient is free from the `k'`-side.**

From the bundled `IsGaloisQuotient` — nothing else — plus
`LocallyOfFiniteType X'.hom`. Two steps: the quotient's `e` and `he` say `X'.hom`
*is* `pullback.snd Y.hom (specMapAlgebra k k')` up to a composition with an
isomorphism, hence that projection is locally of finite type; and
`locallyOfFiniteType_of_baseChange` (Mathlib's
`DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`) descends
it to `Y.hom`.

**This does NOT make `hlft` a non-obligation, and the first revision of this docstring
said it did.** The converse closes from the same `⟨e, he, -, -⟩` (see the module header's
correction, `I-1591`), so the two conditions are interderivable under `hq` and §5 is a
coordinate change. Dropping `hX'` entirely and closing by `infer_instance` **fails**, so
it is still a real hypothesis. Call `seamClauseOne_of_isGaloisQuotient_lftFree` only when
what you hold is the `k'`-side condition.

**Note the binder set, because the first draft of this lemma got it wrong in the
expensive direction.** It carried `[FiniteDimensional k k']` and `[IsGalois k k']`, on
the reading that `IsGaloisQuotient` needs them. It does not, and the reason is
sharper than "they come from elsewhere": `AlgebraicJacobian.GaloisDescent.SemilinearGalAction`
itself is declared under `variable (K L) [Field K] [Field L] [Algebra K L]` with **no**
Galois or finiteness binder, and `IsGaloisQuotient` adds none — so the word "Galois" in
both names is about the *intended* application, not about a hypothesis either carries.
(A first revision of this paragraph said the action "carries the Galois binders itself";
that is false, checked at the `variable` line, and it is the kind of plausible reason
that would have kept the trap alive.) Both are deleted here and the statement
re-elaborates (`lake env lean`, `EXIT=0`). Same double-count as
`Picard/PicEtSeparated.lean`'s field-2 theorem and the seam docstring's input 2: treat
a Galois binder on a descent-side lemma as unproven until checked without it. -/
theorem locallyOfFiniteType_of_isGaloisQuotient
    {X' : Over (Spec (CommRingCat.of k'))}
    {Y : Over (Spec (CommRingCat.of k))}
    (ρ : AlgebraicJacobian.GaloisDescent.SemilinearGalAction k k' X'.left X'.hom)
    (hq : AlgebraicJacobian.GaloisDescent.IsGaloisQuotient ρ Y.hom)
    (hX' : LocallyOfFiniteType X'.hom) :
    LocallyOfFiniteType Y.hom := by
  obtain ⟨e, he, -, -⟩ := hq
  refine locallyOfFiniteType_of_baseChange k' ?_
  have h2 : LocallyOfFiniteType (pullback.snd Y.hom (specMapAlgebra k k')) := by
    rw [← he]; exact MorphismProperty.comp_mem _ _ _ inferInstance hX'
  rw [← pullbackSymmetry_hom_comp_snd (specMapAlgebra k k') Y.hom]
  exact MorphismProperty.comp_mem _ _ _ inferInstance h2

/-! ### §3b. And the `k'`-side condition is free from the `k`-side one

§3 **is** a relocation (header, `I-1591`), and this section does not rescue it: these
two lemmas apply to the object §2 *produces*, i.e. to a base change, whereas §5's `X'`
is arbitrary. So what they buy is narrower than the first revision claimed — they say
the `k'`-side conditions hold at the §2 object, which is what a lane checking that §2
lands inside the campaign's `k'`-side endpoint needs, and nothing about §5's hypothesis
being free. -/

/-- **Local finiteness base-changes to the `k'`-side object of §2**, and so does
separatedness. Both by `MorphismProperty.pullback_snd`; neither needs a hypothesis on
`k'/k`. `infer_instance` does **not** find either (measured), because the goal is
stated at the `Over.pullback` spelling rather than at the projection. -/
theorem locallyOfFiniteType_pullback_of_locallyOfFiniteType
    {X : Over (Spec (CommRingCat.of k))} (h : LocallyOfFiniteType X.hom) :
    LocallyOfFiniteType ((Over.pullback (specMapAlgebra k k')).obj X).hom :=
  MorphismProperty.pullback_snd _ _ h

/-- The separatedness companion of the previous lemma. Recorded because clause (1)'s
third field is `IsSeparated`, so a lane checking that §2 lands *inside* the campaign's
`k'`-side endpoint needs both. -/
theorem isSeparated_pullback_of_isSeparated
    {X : Over (Spec (CommRingCat.of k))} (h : IsSeparated X.hom) :
    IsSeparated ((Over.pullback (specMapAlgebra k k')).obj X).hom :=
  MorphismProperty.pullback_snd _ _ h

/-! ## §4. How much of `hq` is free — and which clause is the residue

§2 could be over-read as "the four inputs are equivalent to the conclusion". They are
not, and this section was written to forbid it. At a `k`-scheme `Y` with the **pullback**
action, `IsGaloisQuotient`'s comparison isomorphism is `Iso.refl`, its two compatibility
clauses close by `simp`, and clause 3 — unique descent of an equivariant
`T_{k'}`-morphism — is the residue.

**AND THE ACTION HERE IS NOT THE ONE THE LANDED DESCENT THEOREMS CONSUME. CORRECTION
OF WHAT THIS SECTION FIRST CLAIMED** (`I-1590`, fresh-context audit; reproduced before
accepting). The first revision said "clauses 1 and 2 are free **at the object §2
produces**, clause 3 is the whole residue". Every landed `hq` is at
`semilinearGalActionOfRepresentableBy C rep`; this section concludes at
`pullbackSemilinearGalAction k k' Y.hom`. Those are **not** the same action — offering
one where the other is expected is a type mismatch, not a coercion (measured) — and they
are not defeq at the §2 object. So this section's output cannot be fed to §5, and at the
*consumed* action clause 2 is itself an open per-γ equality
(`pullbackGalMap … γ = ((semilinearGalActionOfRepresentableBy C rep).act γ).hom`), closed
by no lemma in the tree.

**Note this correction cuts against this file's own interests**, which is why it is
stated at the sentence that made the claim: the guardrail §2 was published with is
weaker than advertised, so §2 is *less* fenced against over-reading, not more. What
survives is a true statement about `Y` and its pullback action, and it locates the
residue **there** — not at the action the route uses. -/

/-- **Clauses 1 and 2 of `IsGaloisQuotient` are free at a base-changed object; clause
3 is the residue, isolated here as the single hypothesis.**

For an arbitrary `k`-scheme `Y`, `Y` is a Galois quotient of its own base change (with
the canonical pullback action) as soon as equivariant morphisms into `Y_{k'}` descend
uniquely. No Picard vocabulary, no curve, no representability: this is a statement
about `Y` alone, which is why it locates the residue rather than restating it.

**Read this as a NEGATIVE result about §2 — but a weaker one than first published.** It
was offered as "exactly what stops §2 from being a converse". It is not *exactly* that,
because it is stated at the pullback action while the descent theorems consume
`semilinearGalActionOfRepresentableBy` (`I-1590`, above). What it genuinely says: for a
`k`-scheme `Y` and its own pullback action, the quotient property reduces to unique
descent of equivariant morphisms, stated below at the identity comparison so that no
reader mistakes the free clauses for the content.

Like §3, this carries **no** `[FiniteDimensional k k']` and **no** `[IsGalois k k']`,
and for the same reason given there: neither `SemilinearGalAction` nor
`IsGaloisQuotient` binds either class. Measured by deleting both and re-elaborating. -/
theorem isGaloisQuotient_pullbackAction_of_uniqueDescent
    (Y : Over (Spec (CommRingCat.of k)))
    (hdesc : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k))
      (h : Limits.pullback t (specMapAlgebra k k') ⟶
        Limits.pullback Y.hom (specMapAlgebra k k')),
      h ≫ pullback.snd Y.hom (specMapAlgebra k k')
          = pullback.snd t (specMapAlgebra k k') →
      (AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k' t).IsEquivariant
        (AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k' Y.hom) h →
      ∃! u : {u : T ⟶ Y.left // u ≫ Y.hom = t},
        AlgebraicJacobian.GaloisDescent.pullbackBaseChange k k' Y.hom t u.1 u.2 = h) :
    AlgebraicJacobian.GaloisDescent.IsGaloisQuotient
      (AlgebraicJacobian.GaloisDescent.pullbackSemilinearGalAction k k' Y.hom) Y.hom := by
  refine ⟨Iso.refl _, by simp, by intro γ; simp, ?_⟩
  intro T t h hcomp heq
  simpa using hdesc T t h hcomp heq

/-! ## §5. The descent step with `hlft` deleted — the form a lane should aim at

§3 carried out on the landed theorem. `seamClauseOne_of_isGaloisQuotient_noMatch`
(`Picard/PicEtInvariantMatch.lean`) is the current minimal-input form: `rep`, `hq`,
`hcov`, `hlft`. Below it is again with `hlft` replaced by the `k'`-side condition,
which §3b shows is not a new obligation.

**It is NOT a three-input theorem, and calling it one was this file's main error**
(`I-1591`, reproduced). It has the same four hypotheses as
`seamClauseOne_of_isGaloisQuotient_noMatch` with the fourth stated at `X'` instead of
`Y`, and each is derivable from the other under `hq`. Use it when you hold the `k'`-side
condition; do not quote it as a shorter antecedent list. -/

/-- **Clause (1) of the seam with local finiteness stated on the `k'` side.**

Same four hypotheses as `seamClauseOne_of_isGaloisQuotient_noMatch`, with the last one
moved from `Y` to `X'`. **Not a shorter antecedent list** — the two are interderivable
under `hq`, whose first field is an iso `Y_{k'} ≅ X'` (module header, `I-1591`). Use
this form when the condition you hold is the `k'`-side one.

`Scheme.fgaPicardRepresentability` is untouched: `rep` is the campaign's undischarged
output and clause (1) field 1 is witnessed for no curve. -/
theorem seamClauseOne_of_isGaloisQuotient_lftFree
    [Algebra.IsSeparable k k'] [Module.Finite k k']
    {C : Over (Spec (CommRingCat.of k))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X')
    {Y : Over (Spec (CommRingCat.of k))}
    (hq : AlgebraicJacobian.GaloisDescent.IsGaloisQuotient
      (semilinearGalActionOfRepresentableBy C rep) Y.hom)
    (hcov : ∀ T : Over (Spec (CommRingCat.of k)), Sieve.generate (Presieve.ofArrows
        (fun _ : k' ≃ₐ[k] k' => (restrictTest k k').obj (baseTest (k' := k') T))
        (fun γ => coverSelfSection T γ)) ∈
      Scheme.etaleTopologyOver k (Limits.pullback (coverMap (k := k) (k' := k') T)
        (coverMap (k := k) (k' := k') T)))
    (hX' : LocallyOfFiniteType X'.hom) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom :=
  seamClauseOne_of_isGaloisQuotient_noMatch rep hq hcov
    (locallyOfFiniteType_of_isGaloisQuotient _ hq hX')

/-! ## §6. What §2 buys for the OTHER open rows: `rep` is a lower bound

§2's real use is not on the descent route at all — it is that `rep` may now be quoted
as a **necessary condition** anywhere in the tree. Two consequences worth naming,
because both are statements a lane could otherwise spend a session trying to avoid.

`not_representableBy_picEt_of_not_representableBy_baseChangeField` is §2
contrapositive: a refutation of `k'`-side representability refutes the seam. That is
the same *shape* as `Picard/PicEtSubcanonical.lean`'s
`not_exists_representing_picSharp_of_not_isIso`, but on the object the board's chosen
route actually holds, and with no comparison map in it.

And it forecloses one hope explicitly: no argument can close clause (1) field 1 over
`k` while leaving `picEt (C_{k'})` unrepresentable. A lane looking for a route that
"avoids the base change" is looking for something that does not exist.

**THE CAVEAT THESE TWO THEOREMS OWE, measured rather than argued.** Their hypothesis —
"no `k'`-scheme represents `picEt (C_{k'})`" — is **refutable inside this project**,
and a lane must know that before quoting them as live constraints. `instHasPicSchemeEt`
is an *unconditional* instance, its binders base-change (`baseChangeField` carries
`SmoothOfRelativeDimension 1`, `IsProper` and `GeometricallyIntegral` as named
instances), so `HasPicSchemeEt.has_pic_scheme_et` at `C_{k'}` produces a representing
object and contradicts the hypothesis. Reproduced in a scratch probe (since deleted):
the derivation of `False` elaborates.

**But it reports `sorryAx`, and the theorems below do not.** That is the whole
distinction, and it is the discipline the seam docstring records for this exact area:
near `HasPicSchemeEt`, provability is not a discriminating control and the axiom list
is. So the honest reading is that the hypothesis is *mathematically* open — Kleiman's
pointless real conic is where a failure would be sought, over `ℝ` rather than over an
extension — while *in-tree* it contradicts a projection of the very `sorry` these
theorems are about. Both statements below are therefore genuine implications whose
antecedent nobody can currently satisfy in Lean without first removing the seam's
unconditional gate instance. Do not present either as a refutation of anything, and do
not present the in-tree contradiction as evidence the hypothesis is false. -/

/-- **The contrapositive of §2: refuting `k'`-side representability refutes the seam.**

If `picEt (C_{k'})` is representable by *no* `k'`-scheme, then `picEt C` is
representable by no `k`-scheme, so clause (1) field 1 of
`Scheme.fgaPicardRepresentability` is false and the seam statement is false as a
whole. Stated for an arbitrary field extension.

This is the form in which §2 is a genuine constraint rather than an observation: it
converts any future non-representability result over an extension into a refutation of
the headline's representability input, exactly as
`not_exists_representing_picSharp_of_not_isIso` does for the `picSharp` endpoint — but
here on `picEt`, which is the object protection `I-0491` chose. -/
theorem not_representableBy_picEt_of_not_representableBy_baseChangeField
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (h : ∀ X' : Over (Spec (CommRingCat.of k')),
      ¬ Nonempty ((picEt (Scheme.baseChangeField C k')).RepresentableBy X')) :
    ∀ X : Over (Spec (CommRingCat.of k)), ¬ Nonempty ((picEt C).RepresentableBy X) :=
  fun _ hX => h _ (hX.map (representableBy_picEt_baseChangeField_of_representableBy C))

/-- **Clause (1) itself is refuted by `k'`-side non-representability.**

The seam's clause (1) is a three-field existential; this kills its first field, hence
the whole conjunct, for every candidate `Z`. Recorded separately from the previous
theorem because the seam consumes the existential, not the per-object statement, and a
lane checking whether a refutation "reaches the sorry" needs the existential form. -/
theorem not_seamClauseOne_of_not_representableBy_baseChangeField
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (h : ∀ X' : Over (Spec (CommRingCat.of k')),
      ¬ Nonempty ((picEt (Scheme.baseChangeField C k')).RepresentableBy X')) :
    ¬ ∃ Z : Over (Spec (CommRingCat.of k)),
        Nonempty ((picEt C).RepresentableBy Z) ∧
          LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom := by
  rintro ⟨Z, hZ, -, -⟩
  exact not_representableBy_picEt_of_not_representableBy_baseChangeField
    (k' := k') C h Z hZ

/-! ## §7. At the separable closure — and NOT the campaign's endpoint (see the correction)

§2 holds at an arbitrary extension, so it holds at `k^s`. That instance is worth its
own name because of *where* the Milne–Kollár campaign lives: cluster `J` is stated over
a separably closed field, which is exactly where a section is available
(`Curve/SeparablyClosedRationalPoint.lean`) and where `picSharp` and `picEt` agree.

**WHAT THIS SECTION MAY AND MAY NOT SAY — CORRECTION** (`I-1592`, fresh-context audit;
both points reproduced here). The first revision said the seam "implies the campaign's
own endpoint", pinning the relationship "in both directions". Two things are wrong with
that.

*First, the object.* Campaign cluster `J`'s stated target is
`Nonempty ((picSharpDeg C' r).RepresentableBy J'_r)` — a **graded `picSharp`**, and
`picSharpDeg` **has no carrier in this project at all** (`#check` returns
`unknownIdentifier`, measured). So §7 does not conclude the campaign's endpoint; it
concludes representability of `picEt (C_{k^s})`. The seam file itself says the milestone
bodies never mention `picEt`, which is the same fact from the other side. Whether the
two agree over `k^s` routes through the seam's *own* second conjunct, and closing it that
way reports `sorryAx` — so it is not available as an argument here.

*Second, the loop does not close at one field.* §5 binds `[Module.Finite k k']`, which
fails at `SeparableClosure k` (`infer_instance` fails, measured), while §7 only runs
there. So there is no field at which both directions are instantiable.

What survives is one-directional and still worth having: the seam implies
representability of the base-changed `picEt` at every extension, `k^s` included. A lane
must not read that as "the campaign is proving the right thing at `k^s`" — that
identification is unproved.

**This is not a discharge and the direction is the whole point.** §7's hypothesis is
clause (1) field 1 over `k`, i.e. what the seam owes. It says nothing about how to
produce either side. What it removes is the worry that the campaign might be proving
something stronger than needed at `k^s` — it is not: what it targets there is a
consequence of the goal. -/

/-- **The seam implies representability over the separable closure.**

The `k^s` instance of §2. `SeparableClosure k` is a `Type u` field with a `k`-algebra
structure, so no universe bridge and no extra hypothesis is involved: this is §2 with
`k' := SeparableClosure k` and nothing else.

Named because `k^s` is the field campaign cluster `J` works over, so a lane can cite
this instance without re-deriving the base change. **Not** because it is cluster `J`'s
target: that target is a graded `picSharp` with no carrier in this project, and the
section header above records why the identification is unproved. Do not cite this as
"the campaign's endpoint follows from the seam". -/
noncomputable def representableBy_picEt_separableClosure_of_representableBy
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (picEt C).RepresentableBy X) :
    (picEt (Scheme.baseChangeField C (SeparableClosure k))).RepresentableBy
      ((Over.pullback (specMapAlgebra k (SeparableClosure k))).obj X) :=
  representableBy_picEt_baseChangeField_of_representableBy C rep

end PicScheme

end Scheme

end AlgebraicGeometry
