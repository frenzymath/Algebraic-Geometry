/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import Mathlib
import AlgebraicJacobian.Picard.PicEtCrossBase
import AlgebraicJacobian.Picard.EtaleFieldCover

/-!
# The descent assembly — the theorem that CONSUMES the four repair inputs

`AJC.picrep.etale-rep.descent-assembly`.

## Why this file exists

The repaired route to the seam `sorry` `Scheme.fgaPicardRepresentability`
(`Picard/FGAPicRepresentability.lean`) is documented at that declaration as
having **four inputs**, and each of the four has either landed or is held by a
lane. What no declaration in this project stated is the theorem those four are
inputs *to*: the step that takes a representation over a larger field and
returns one over `k`.

Measured before this file was written, at HEAD with fresh oleans: the seam's
conclusion shape `Nonempty ((PicScheme.picEt C).RepresentableBy X)` occurs at
exactly three sites — `Picard/FGAPicRepresentability.lean` twice (the
`HasPicSchemeEt` class field, and the `sorry`-bodied seam itself) and
`Picard/PicEtSubcanonical.lean` once
(`hasPicSchemeEt_of_picSharp_representability`). All three are **same-field**:
the last takes a `picSharp` representation over the *same* `k` and transports it
along subcanonicity. None takes a `k'`-side representation and concludes over
`k`. Independently re-measured by `review-ajc` (`I-1256`) before this file
landed.

So the route's scoreboard was a list of antecedents with no goal attached, and an
input nobody held would have stayed invisible — the failure mode this file is
written to remove.

## What is proved here, and what is not

**Proved, `sorry`-free** (§2): the **uniqueness half** of the descent, at the
cover the repair uses. `picEt_injective_restrict_baseTest` says restriction along
the single morphism `T ×_k k' ⟶ T` is *injective* on `picEt`-classes, for every
`k`-test `T`. This is what makes a descended class unique once it exists.

**Proved, `sorry`-free** (§3): the transport that makes the `k'`-side hypothesis
statable in the right variables (`representableByRestrict_of_baseChange`, free from
input 2). The other half of the class-level descent — a compatible family has a
unique amalgamation — is `Scheme.isSheafFor_picEt_pullback_presieve`
(`Picard/EtaleFieldCover.lean`), cited in §3 rather than restated.

**Not proved, and named rather than hidden** (§4): `G1` invariance — producing the
compatible family from a Galois-invariant `k'`-class — and then the `G2` quotient
construction that turns descended classes into a representing `k`-scheme, gated on
`AlgebraicJacobian.GaloisDescent.HasGaloisQuotient` (affine half only). Neither is
sheaf-theoretic; this file does not weaken either, does not restate them more
cheaply, and does not close them.

**What this file deliberately does not contain.** An earlier draft stated the
assembly as a Lean implication whose antecedent was the seam's clause (1) and whose
conclusion was the same existential — i.e. `P → P`, the shape `I-0838` forbids and
the 2026-07-29 audit found 67 times. It was removed before committing rather than
dressed up: the remaining obligation is a *construction*, so its home is the gate
in `Picard/FiniteGaloisQuotient.lean`, not a hypothesis slot here. Nor is any
conclusion in this file class-valued: because `instHasPicSchemeEt` is
unconditional, instance search discharges a `HasPicSchemeEt`-valued conclusion by
projecting the seam `sorry` for every object in the gate's domain, so such a
statement would typecheck whatever its hypotheses said (`review-ajc`, `I-1251`).

## What this does NOT do

It closes no `sorry` in `Picard/FGAPicRepresentability.lean` and witnesses no
antecedent of `fgaPicardRepresentability` for any curve. §2 is a genuine theorem
about `picEt` on an arbitrary smooth proper curve over an arbitrary field, with no
hypothesis on `C(k)` per `I-0491`; the statements of §3 are unconditional, and what
§4 records as remaining has no producer.

## A route correction recorded here because it was nearly acted on

`review-ajc` proposed (and, once shown this, withdrew — `I-1256`) that the
assembly should conclude the `picSharp`-shaped endpoint
`∃ X, Nonempty ((picSharp C).RepresentableBy X) ∧ LocallyOfFiniteType X.hom ∧
IsSeparated X.hom`, on the strength of its own r5 measurement that this single
existential discharges *both* seam conjuncts with nothing left over. That
reduction is correct and is cited below at the **input** end. As a *conclusion*
over the headline's arbitrary `k` it is inadmissible, and this project already
proves why: `PicScheme.not_exists_representing_picSharp_of_not_isIso`
(`Picard/PicEtSubcanonical.lean`) says no scheme at all represents `picSharp C`
over such a `k` once `picEtComparison C` fails to be an isomorphism. Aiming the
assembly there would have produced a green, `sorry`-free theorem refutable from a
lemma two files away. The whole content of the repair is that the object crossing
the descent step is `picEt`.

## Measurement discipline

`lake build AlgebraicJacobian` EXIT=0 (8869 jobs) with **fresh** oleans before
every probe below — a stale-import environment reports every probe as succeeding
(`I-1057`), which would have made the §2 proof look free when it was not.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-! ## §1. The cover of a `k`-test by its base change, as an `Over`-morphism -/

/-- The base change `T ×_k Spec k'` of a `k`-test `T`, regarded as a `k'`-test
via the second projection.

This is the object the descent step's classes live on: a class over `k'` is a
class on `T_{k'}` for the tests `T` of interest, and `§2` shows a `k`-class is
determined by its restriction here. -/
noncomputable abbrev baseTest (T : Over (Spec (CommRingCat.of k))) :
    Over (Spec (CommRingCat.of k')) :=
  Over.mk (pullback.snd T.hom (specMapAlgebra k k'))

/-- **The covering morphism `T_{k'} ⟶ T`**, in the slice over `Spec k`.

Its underlying scheme map is exactly `pullback.fst`, which is the morphism
`Picard/EtaleFieldCover.lean` builds its covering sieve from — so the sheaf
axiom landed there applies to this morphism on the nose (checked by `rfl`:
`coverMap_left`). -/
noncomputable def coverMap (T : Over (Spec (CommRingCat.of k))) :
    (restrictTest k k').obj (baseTest (k' := k') T) ⟶ T :=
  Over.homMk (pullback.fst T.hom (specMapAlgebra k k'))
    (pullback.condition (f := T.hom) (g := specMapAlgebra k k'))

/-- The cover morphism's underlying scheme map **is** `pullback.fst`, definitionally.

This is the identification that lets `§2` feed
`Scheme.picEt_ext_of_pullback_agrees`, whose sieve is generated by
`Presieve.singleton (pullback.fst T.hom (specMapAlgebra k k'))`. -/
@[simp]
theorem coverMap_left (T : Over (Spec (CommRingCat.of k))) :
    (coverMap (k' := k') T).left = pullback.fst T.hom (specMapAlgebra k k') := rfl

/-! ## §2. The uniqueness half of the descent — PROVED -/

/-- **Restriction along `T_{k'} ⟶ T` is injective on `picEt`-classes.**

For a smooth proper curve `C` over an arbitrary field `k`, an arbitrary finite
separable `k'/k`, and an arbitrary `k`-test `T`: two classes in
`Pic_{(C/k)ét}(T)` that agree after restriction to `T ×_k Spec k'` are equal.

This is the *uniqueness* half of the descent step, and it is what makes a
descended class unique once one exists — so a consumer holding a single class,
rather than a compatible family, needs no separate uniqueness hypothesis.

**Where the content is, stated precisely.** The amalgamation property itself is
free: `Scheme.isSheafFor_picEt_of_mem` holds at *every* covering sieve of
`etaleTopologyOver k`, `⊤` included, because it is `PicSharp.etaleSheaf`'s own
`Sheaf.cond` pushed through the forgetful functor. What this lemma adds over
`Scheme.picEt_ext_of_pullback_agrees` is the reduction from that lemma's
*sieve-indexed* hypothesis — agreement after restriction along **every** arrow of
the generated sieve — to agreement along the **single** morphism `coverMap`. The
step is the factorisation: an arrow of the sieve factors through `pullback.fst`,
and lifting that factorisation to the slice over `Spec k` is where
`pullback.condition` is consumed.

**That the factorisation is not avoidable is measured, not assumed** — it is the
obvious refutation of this lemma ("the sheaf axiom gives injectivity directly, so
the hand proof is redundant"), so it was probed rather than argued. Two routes,
both `EXIT=1`:

* deriving it from the amalgamation statement
  (`Scheme.isSheafFor_picEt_pullback_presieve`) requires exhibiting a
  `Presieve.FamilyOfElements` on the *whole* sieve for which both classes are
  amalgamations, and constructing that family needs a value at every sieve arrow —
  i.e. the same factorisation, relocated;
* discharging the sieve-indexed goal from the single-morphism hypothesis with no
  factorisation work fails: `exact h`, `simpa using h`, `congrArg _ h` and `aesop`
  all leave the goal open (`aesop` reports exhaustive search).

So the content is the reduction, and only the reduction. Whoever re-checks this
should re-run those two probes rather than trust the paragraph.

**No hypothesis on `C(k)`** (`I-0491`), and none on `T`. The finite-separability
binders are inherited from the covering-sieve membership witness of
`Picard/EtaleFieldCover.lean`, which is where they are genuinely used; they are
*not* needed by the cross-base identification (`picEt_crossBaseIso` holds for an
arbitrary field extension). -/
theorem picEt_injective_restrict_baseTest
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (T : Over (Spec (CommRingCat.of k)))
    {t₁ t₂ : (picEt C).obj (Opposite.op T)}
    (h : (picEt C).map (coverMap (k' := k') T).op t₁
       = (picEt C).map (coverMap (k' := k') T).op t₂) :
    t₁ = t₂ := by
  refine AlgebraicGeometry.Scheme.picEt_ext_of_pullback_agrees k' C T ?_
  intro W g hg
  rw [Sieve.overEquiv_symm_iff] at hg
  obtain ⟨Z, a, b, hb, hfac⟩ := hg
  cases hb
  -- `g` factors through `coverMap` in the slice over `Spec k`.
  have hgfac : g = (Over.homMk a (by
      rw [← Over.w g]
      simp only [restrictTest, Over.map_obj_hom, baseTest, Over.mk_hom, ← hfac]
      rw [Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition.symm) :
        W ⟶ (restrictTest k k').obj (baseTest (k' := k') T))
      ≫ coverMap (k' := k') T := by
    apply Over.OverMorphism.ext
    change Over.Hom.left g = a ≫ pullback.fst T.hom (specMapAlgebra k k')
    exact hfac.symm
  rw [hgfac]
  simp only [op_comp, Functor.map_comp, CategoryTheory.comp_apply, h]

/-! ## §3. The input-side transport, and the sharp form of what remains -/

/-- **The `k'`-side input, transported: PROVED, and free.**

A representation of `picEt` of the **base-changed curve** `C_{k'}` by a
`k'`-scheme `X'` is the same thing as a representation of `picEt C` restricted to
`k'`-tests. This is `picEt_crossBaseIso` (input 2 of the repair, closed
unconditionally by `Picard/PicEtCrossBase.lean`) fed to
`Functor.RepresentableBy.ofIso`.

It is recorded because it is the step that makes the assembly's hypothesis
*statable in the right variables*: without it the `k'`-scheme that campaign `J5`
produces would represent `picEt` of the `k`-curve restricted to `k'`-tests rather
than `picEt` of `C_{k'}`, and there would be no functor for the Galois action to
act on — a mismatch no green build reveals.

No separability or finiteness hypothesis on `k'/k`: the cross-base identification
never needed one. -/
noncomputable def representableByRestrict_of_baseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X' : Over (Spec (CommRingCat.of k'))}
    (rep : (picEt (Scheme.baseChangeField C k')).RepresentableBy X') :
    ((restrictTest k k').op ⋙ picEt C).RepresentableBy X' :=
  rep.ofIso (picEt_crossBaseIso C k')

/-! ### The other half — free, and already in the tree

A *compatible family* of `picEt C`-classes on this cover has a **unique**
amalgamation, so descent of classes along the cover is settled outright and nothing
about it is owed. That is
`AlgebraicGeometry.Scheme.isSheafFor_picEt_pullback_presieve`
(`Picard/EtaleFieldCover.lean`), and it is cited rather than restated here.

**An earlier revision of this file restated it** as an
`existsUnique_amalgamation_picEt_fieldCover`, describing the restatement's value as
"the pricing consequence". A fresh-context audit measured the two `rfl`-equal —
*proposition and term* — and pointed at `EtaleFieldCover.lean`'s own `:289`/`:294`,
which already say "unique amalgamation" and "every covering sieve, `⊤` included,
free from sheafification" (`I-1312`). So the pricing fact was in the tree as prose
and the declaration added nothing; it is deleted rather than kept with a caveat, per
`I-1284`. The same audit deleted a second self-downgraded lemma from this file.

**The pricing fact itself stands**, and it is what a lane needs: the residue of the
descent step is **not** in the sheaf theory. It is in two places this file does not
reach —

1. producing the *compatible family* from a Galois-**invariant** `k'`-class, the
   Hilbert-90/invariance content of campaign `G1`, where the group action enters; and
2. the **scheme-level** quotient — turning descended classes into a `k`-scheme
   representing `picEt C` — campaign `G2`, gated on
   `AlgebraicJacobian.GaloisDescent.HasGaloisQuotient`.

Budget those two and *nothing* for the sheaf-theoretic halves.
-/


/-! ## §4. What still stands between this and the seam's clause (1)

The seam's clause (1) asks for a `k`-scheme representing `picEt C`. What `§3`
establishes is that the *class-level* descent along the field-extension cover is
**complete**: a compatible family has a unique amalgamation, both halves free from
sheafification once the covering-sieve witness of `Picard/EtaleFieldCover.lean` is
in hand. What this file does **not** supply, and therefore leaves open, is two
things, neither of them sheaf-theoretic:

* producing the compatible family from a Galois-invariant `k'`-class (the
  invariance content of campaign `G1`); and
* the passage from descended classes to a *representing scheme* over `k` — the
  quotient construction itself (campaign `G2`), which produces the `k`-scheme as a
  quotient of `X'` by the semilinear Galois action, gated on
  `AlgebraicJacobian.GaloisDescent.HasGaloisQuotient`. That gate now has a global
  instance on the **affine** locus (`Picard/GaloisQuotientAffineGeneral.lean`,
  `ajc-p1`), while the object this route descends is glued, so it still bites.

Deliberately **not** stated here as a Lean implication with that passage as a
hypothesis: an implication whose antecedent is its own conclusion is `P → P`, and
an implication whose antecedent is "the `k`-scheme exists with its properties" is
that. The route's remaining obligation is a *construction*, and the place for it is
`Picard/FiniteGaloisQuotient.lean`'s gate, where it already sits.

And clause (1) is a **one-conjunct** obligation, not three — measured by
`review-ajc` (`I-1286`) after this file's first revision, which priced only the
representability field and said nothing about the other two. Both side conjuncts
are free: `LocallyOfFiniteType` descends along exactly this cover (mathlib has a
`DescendsAlong` instance for it — do **not** quote a total number of such
instances here, which an earlier revision of this paragraph did: "exactly five"
was one file's count published as mathlib's and is withdrawn, `I-1315`/`I-1357`;
grep `DescendsAlong` and count), and `IsSeparated` never needs to descend at all
— `picEt` is group-valued, so any representing scheme is a group object by Yoneda
transport and a group scheme over a field is separated. Note the direction:
`IsSeparated` *cannot* descend in mathlib v4.31 (no `DescendsAlong` instance, and
the diagonal route needs one for `IsClosedImmersion`, also absent), so the free
route is the only route.

**Both fields are LANDED, so budget nothing for them.** An earlier revision of
this paragraph said "the one brick is a port of AJCR's
`AbelianVariety/GroupSeparated.lean`". That was true when written and is false at
HEAD: `ajc-p1` landed the port on 2026-07-30 as `Picard/PicEtSeparated.lean`
(`isSeparated_of_representableBy_picEt` for field 3,
`locallyOfFiniteType_of_baseChange` for field 2, plus
`seamClauseOne_of_representableBy_locallyOfFiniteType` restating clause (1) as the
two-field obligation). Flagged by a fresh-context audit (`I-1357`) and accepted
here: the correction had been made in `FGAPicRepresentability.lean` and not in this
file, which is the one a lane opens to read the scoreboard.

So the scoreboard this file was written to complete reads, at HEAD: inputs 1 (the
cover), 2 (cross-base), 4 (the `k^s` section) landed; input 3 (the Galois quotient)
open, gated, affine half only; the *goal* they feed now exists, with its
class-level half **closed**; and of the goal's three conjuncts only
representability is owed. The remaining cost is `G1` invariance and the `G2`
quotient — and `k'`-side representability itself, which is the campaign's
undischarged output and is not made cheaper by any of this.
-/

end PicScheme

end Scheme

end AlgebraicGeometry
