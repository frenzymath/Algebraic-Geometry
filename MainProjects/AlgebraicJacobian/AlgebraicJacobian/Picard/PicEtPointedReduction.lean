/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtGaloisQuotient
import AlgebraicJacobian.Picard.PicEtSubcanonical
import AlgebraicJacobian.Curve.GaloisLevelRationalPoint

/-!
# The arbitrary-field seam reduces to the POINTED Picard theorem

`Scheme.fgaPicardRepresentability` (`Picard/FGAPicRepresentability.lean`) is this
project's one open obligation. Its statement carries **no** hypothesis on `C(k)`,
by the owner decision `I-0491`, and that is exactly what makes it hard: the
classical FGA/Kleiman representability theorem, and the whole Milne–Kollár
campaign built to formalise it, produce a representing scheme only for a curve
that **has** a rational point.

This file removes that gap. It proves that **both** conjuncts of the seam, over an
**arbitrary** field, follow from the *pointed* statement — plus one geometric side
condition on the representing scheme, `FiniteInAffine`, which is the
action-free form of the EGA II 4.5.4 hypothesis and is true for quasi-projective
schemes.

## What is proved

* `seamClauseOne_of_pointedPicSharpRep` — clause (1), over an arbitrary `k`.
* `seamClauseTwo_of_pointedPicSharpRep` — clause (2). It needs the pointed
  antecedent **alone**: no Galois level, no quotient, no orbit hypothesis.
* `fgaPicardRepresentability_of_pointedPicSharpRep` — the seam statement itself,
  verbatim, as the conclusion of an implication.
* `seamClauseOne_of_hasGoodGaloisLevel` (§5) — clause (1) from the **weakest**
  antecedent the proof actually consumes: a *single* finite Galois extension over
  which `picSharp` is representable by a quasi-projective scheme. No rational
  point occurs in that statement, no uniformity in the field, and
  `[GeometricallyIntegral C.hom]` is not a binder. Price the remaining work
  against this one, not against `PointedPicSharpRep`.
* `nonempty_representableBy_picSharp_of_isIso` and
  `nonempty_representableBy_picSharp_of_hasRationalPoint` (§6) — the **converse**
  direction, which an earlier revision of §5 wrongly claimed did not exist. At a
  pointed curve the two representability notions are interderivable; §5 says
  precisely where the residual gap is.

## Why this is not a new hypothesis on the headline

`I-0491` forbids putting `[HasRationalPoint C]` on the headline. Nothing here
does: `PointedPicSharpRep` is a **closed** proposition quantifying over *all*
fields and *all* pointed curves, and the theorems below conclude about a curve
over an arbitrary `k` with no section. The rational point is produced, not
assumed — `Curve/GaloisLevelRationalPoint.lean`'s
`exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral` is
unconditional, so the curve reaches a finite Galois level carrying a point using
only the binders the seam already has. That is the step which turns a pointed
input into an arbitrary-field output, and it is where the descent machinery of
`Picard/PicEtGaloisQuotient.lean` is spent.

## The three landed facts this composes, and why nobody had composed them

Each was proved by a different lane for a different row; none of the three rows
mentions the other two.

1. `Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral`
   (`Curve/GaloisLevelRationalPoint.lean`) — every curve with the seam's own
   binders has a rational point over *some* finite **Galois** `k''/k`. Not merely
   separable: `IsGalois` is what the semilinear-action machinery needs, and the
   normal-closure step in that file is what supplies it.
2. `Scheme.PicScheme.seamClauseOne_of_hasGaloisQuotient_lftFree`
   (`Picard/PicEtGaloisQuotient.lean`) — the descent step with `hq` **and** `hcov`
   already discharged internally. This is the fact that changes the price: the
   board row `AJC.picrep.etale-rep.descent-assembly` lists *four* inputs, and at
   this spelling three of them are gone (`hcov` closed by `pic-f`'s
   `coverSelfSection_generate_mem_etaleTopology`, the quotient by the **global**
   instance `hasGaloisQuotient_of_orbitsInAffineOpen`
   (`GaloisDescent/GaloisQuotientOverlap.lean`), the `G1` predicate match by
   `isInvariantMatch_canonical`). The one remaining instance binder is
   `OrbitsInAffineOpen`.
3. `Scheme.picSharp_representableBy_picEt_transport` and
   `Scheme.isIso_picEtComparison_of_picSharp_representability`
   (`Picard/PicEtSubcanonical.lean`) — a scheme representing `picSharp` also
   represents `picEt`, and makes the comparison an iso, with no section anywhere.
   So the pointed **`picSharp`** theorem is enough; nothing needs an étale
   representability statement of its own.

## Correction to the seam docstring's own item 3, measured here

`Picard/FGAPicRepresentability.lean` item 3 says the quotient gate "bites only off
the affine locus" and that `inferInstance` for it at an abstract action carrying
the orbit hypothesis but not affineness **fails**. At HEAD that is stale for the
gate as a whole: `hasGaloisQuotient_of_orbitsInAffineOpen`
(`GaloisDescent/GaloisQuotientOverlap.lean`) is a global instance requiring
`[FiniteDimensional K L] [IsGalois K L] [ρ.OrbitsInAffineOpen]` and **no**
affineness, and `seamClauseOne_of_hasGaloisQuotient_lftFree` consumes it
successfully at the *glued* quotient (`gluedQuotientMap`). What survives of item 3
is the *orbit* hypothesis, which is the honest residue and is the one this file
carries.

**And my first attempt to hedge that correction was itself wrong, which is worth
more than the correction** (fresh-context audit, reproduced before accepting). It
said: "the sentence there is about `HasGaloisQuotient` at an action with **no**
orbit binder, where it is still true." The sentence in that file explicitly says
*with* the orbit hypothesis — "at an abstract action carrying the orbit hypothesis
but not affineness **fails** (measured, control both ways)" — and at HEAD that is
false: `infer_instance` **succeeds** at exactly that shape, and fails without the
orbit binder (control, both ways in one probe). So item 3 is stale as written, not
mis-scoped, and its downstream conclusion ("the remaining `G2(c)` work is exactly
the `Scheme.GlueData` assembly") is stale in the same cheap direction, since
`isGaloisQuotient_glued` is what discharges the instance. I have not edited that
file; the true nearby claim it may be confused with is item 3's *other*
measurement, about `HasStableAffineCover` at an action with no orbit binder.
Relocating a stale sentence to a shape it does not describe is worse than leaving
it, because it makes the staleness invisible.

## What this does NOT do

It does not close the seam. `PointedPicSharpRep` is **unproved in this project** —
it *is* the Milne–Kollár campaign's undischarged output — and no curve is exhibited
satisfying `FiniteInAffine` at its Picard scheme. Both are explicit antecedents
below, not hidden ones. What changes is the *shape* of what remains: the
arbitrary-field difficulty that `I-0491` deliberately put on the headline is now
**discharged**, and what is left is the classical pointed theorem plus
quasi-projectivity of the representing scheme.

And it is an equivalence **at pointed curves** — §6 proves the converse there, so
away from the pointless case this is a change of coordinates and not a discount.
§5 locates the residual gap: curves with no rational point, where
`¬ IsIso (picEtComparison C)` is quoted from Kleiman and unproved here.

Finally, per §7, `PointedPicSharpRep` is *derivable from the seam itself* up to
`FiniteInAffine`. So a claimed proof of it must be **axiom-checked**: on this seam
provability is not a discriminating control and the axiom list is.

`FiniteInAffine` is not free: `exact?` fails on it at an arbitrary scheme
(measured, control in the same probe as the results). It is also not vacuous — §3
inhabits it at an affine scheme.
-/

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicJacobian.GaloisDescent

universe u

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-! ## §1. The two hypotheses, named -/

/-- **Every finite subset lies in a single affine open** — the action-free,
scheme-level form of the EGA II 4.5.4 orbit hypothesis.

`SemilinearGalAction.OrbitsInAffineOpen` (`Picard/FiniteGaloisQuotient.lean`) is
stated *about an action*, so a consumer cannot discharge it before knowing which
action it will face. This form is a property of the scheme alone, and §2 shows it
implies the action form for **every** semilinear action of a finite Galois group.
That is what lets the antecedent of §4 be stated without mentioning the Galois
level, which is chosen inside the proof.

True for quasi-projective schemes (finite point sets of a quasi-projective scheme
lie in an affine open). Mathlib `v4.31` has no quasi-projectivity vocabulary at
this pin, which is why the hypothesis is carried in this elementary form rather
than derived. -/
def FiniteInAffine (X : Scheme.{u}) : Prop :=
  ∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.1

/-- **The pointed Picard theorem**: FGA/Kleiman representability of the relative
Picard functor, for curves that *have* a rational point, uniformly in the base
field, together with quasi-projectivity of the representing scheme.

This is the campaign's target, written as a closed proposition. Three things about
its shape are deliberate, and a fourth is deliberately **absent**.

* It quantifies over **all** base fields `K`, not just over `k`. That is
  essential and it is not a strengthening in any useful sense: §4 applies it at a
  finite Galois extension of `k` chosen by the curve, so a version fixed at `k`
  would not compose. Every formalisation route to FGA representability is uniform
  in the base field anyway.
* It is about `picSharp`, the **unsheafified** relative Picard functor — the object
  the Milne–Kollár modules target (`I-0907`). No étale-sheafified representability
  statement is needed on top of it; §3 of `Picard/PicEtSubcanonical.lean` supplies
  the transport for free.
* `FiniteInAffine X.left` is bundled rather than carried separately so that the
  results below have **one** antecedent. The *property* is perfectly stateable
  outside it — `HasGoodGaloisLevel` in §5 does exactly that, and §2 takes it as a
  free-standing hypothesis. What cannot be stated outside is the **witness**: no
  separate binder can name the scheme the antecedent itself produces. (An earlier
  revision of this bullet said the property "cannot be stated outside it", which
  two declarations in this same file refute.)
* **`IsSeparated X.hom` is NOT a conjunct**, and carrying it would have
  misreported the price of the reduction. It is *free* from the resulting `picEt`
  representation by `isSeparated_of_representableBy_picEt`
  (`Picard/PicEtSeparated.lean`) — Yoneda transports the `CommGrpCat`-valued
  functor's group structure onto any representing scheme, and a group scheme over
  a field is separated. That file's
  `picEtClauseOne_of_picSharp_representableBy_locallyOfFiniteType` already says
  in its own docstring that the form to hand the campaign asks "nothing about
  separatedness". A first revision of this file bundled it anyway; a
  fresh-context audit reproved every result with the conjunct deleted, so it is
  deleted. The seam's clause (1) still *concludes* separatedness — it is
  discharged, not dropped. -/
def PointedPicSharpRep : Prop :=
  ∀ {K : Type u} [Field K] (E : Over (Spec (CommRingCat.of K))),
    ∀ [SmoothOfRelativeDimension 1 E.hom] [IsProper E.hom] [GeometricallyIntegral E.hom],
      Scheme.HasRationalPoint E →
      ∃ X : Over (Spec (CommRingCat.of K)),
        Nonempty ((PicScheme.picSharp E).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ FiniteInAffine X.left

/-! ## §2. The scheme-level hypothesis implies the action-level one -/

/-- **`FiniteInAffine` discharges `OrbitsInAffineOpen`, for every semilinear
action of a finite Galois group.**

The orbit of a point is the range of a map indexed by `L ≃ₐ[K] L`, which is finite
because `L/K` is finite Galois (`Finite (L ≃ₐ[K] L)` by synthesis), so it is a
finite subset and the hypothesis applies directly.

Note where the finiteness of the group is consumed: only here. The quotient
machinery downstream binds `[FiniteDimensional K L] [IsGalois K L]` for its own
reasons. -/
theorem orbitsInAffineOpen_of_finiteInAffine
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of L)}
    (ρ : SemilinearGalAction K L X f) (h : FiniteInAffine X) :
    ρ.OrbitsInAffineOpen where
  exists_affineOpen x := by
    obtain ⟨U, hU⟩ :=
      h (Set.range fun γ : L ≃ₐ[K] L => (ρ.act γ).hom.base x) (Set.finite_range _)
    exact ⟨U, fun γ => hU ⟨γ, rfl⟩⟩

/-! ## §3. `FiniteInAffine` is inhabited, and is not free

Both directions are recorded as declarations rather than as docstring sentences,
per `I-0838`: a hypothesis whose satisfiability is unmeasured is how a vacuous
statement survives, and a hypothesis that is *free* would make the results below
empty. -/

/-- **Non-vacuity**: an affine scheme satisfies `FiniteInAffine`, with `⊤` as the
affine open. So the antecedent of §4 is not asserting something about no scheme.

This is the cheap witness, and it is the honest one to give: it is *not* a witness
at a Picard scheme, and no such witness exists in this project. What it rules out
is the failure mode where `FiniteInAffine` is unsatisfiable and the results below
are vacuously true. -/
theorem finiteInAffine_of_isAffine (X : Scheme.{u}) [IsAffine X] : FiniteInAffine X :=
  fun _ _ => ⟨⟨⊤, isAffineOpen_top X⟩, fun _ _ => trivial⟩

/-! ## §4. The reduction

Clause (2) first, because it needs strictly less. -/

/-- **Clause (2) of the seam, from the pointed antecedent alone.**

No Galois level, no quotient, no orbit hypothesis, and the `FiniteInAffine`
conjunct of the antecedent is discarded: given a section, the antecedent applies
to `C` *itself*, and subcanonicity of the étale topology turns a representation
into invertibility of the comparison map
(`isIso_picEtComparison_of_picSharp_representability`).

So of the seam's two conjuncts, this one costs nothing beyond the pointed theorem.
That is a sharper statement than the seam docstring's "clause (2) costs zero extra
work", which was said relative to a `picSharp`-shaped endpoint over the *same*
field; here it is said relative to the pointed antecedent, which is the thing
actually being assumed. -/
theorem seamClauseTwo_of_pointedPicSharpRep {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (H : PointedPicSharpRep.{u}) :
    Scheme.HasRationalPoint C → IsIso (PicScheme.picEtComparison C) := by
  intro hpt
  obtain ⟨X, ⟨rep⟩, -, -⟩ := H C hpt
  exact isIso_picEtComparison_of_picSharp_representability C rep

/-- **Clause (1) of the seam, over an ARBITRARY field, from the pointed
antecedent.** This is the theorem the file exists for.

The proof is the composition the module docstring describes, and each step is a
landed sorry-free theorem of a different lane:

1. `exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral` produces
   a finite **Galois** `k''/k` and a rational point on `C_{k''}` — unconditionally,
   from `[SmoothOfRelativeDimension 1]` and `[GeometricallyIntegral]` alone. This
   is the only step that uses `GeometricallyIntegral`.
2. The antecedent, applied at `k''` to the base-changed curve (all three binders
   are stable under field base change, by synthesis), gives a scheme representing
   `picSharp (C_{k''})` with the two side conjuncts and `FiniteInAffine`.
3. `picSharp_representableBy_picEt_transport` converts it to a `picEt`
   representation — the same scheme, so `LocallyOfFiniteType` rides along.
4. §2 turns `FiniteInAffine` into `OrbitsInAffineOpen` at the canonical semilinear
   action `semilinearGalActionOfRepresentableBy C rep`, which is the action the
   descent step uses.
5. `seamClauseOne_of_hasGaloisQuotient_lftFree` descends to `k`, discharging the
   quotient and the covering sieve internally.

The conclusion is over `k` with **no** section and **no** `k''` in sight, and no
hypothesis of the theorem mentions a representation of `picEt C` — so this is not
`P → P`, and it is not the refuted shape of `representableByRestrict_of_baseChange`
(`I-1312`), which concluded about a `k'`-object. -/
theorem seamClauseOne_of_pointedPicSharpRep {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (H : PointedPicSharpRep.{u}) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((PicScheme.picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom := by
  obtain ⟨k'', hfd, hgal, hpt⟩ :=
    Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral C
  letI := hfd
  letI := hgal
  obtain ⟨X', ⟨rep0⟩, hft, hfa⟩ := H (Scheme.baseChangeField C (k'' : Type u)) hpt
  letI rep :=
    picSharp_representableBy_picEt_transport (Scheme.baseChangeField C (k'' : Type u)) rep0
  letI := orbitsInAffineOpen_of_finiteInAffine
    (PicScheme.semilinearGalActionOfRepresentableBy C rep) hfa
  exact PicScheme.seamClauseOne_of_hasGaloisQuotient_lftFree rep hft

/-- **The seam, verbatim, as the conclusion of an implication.**

The conclusion is character-for-character the statement of
`Scheme.fgaPicardRepresentability`, so a lane that proves `PointedPicSharpRep`
closes the project's central `sorry` by `exact`. Stated as a named theorem rather
than left to the reader to assemble, because "the two clauses are available
separately" is not the same as "the seam follows", and the difference is exactly
the kind of joint that goes unchecked. -/
theorem fgaPicardRepresentability_of_pointedPicSharpRep {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (H : PointedPicSharpRep.{u}) :
    (∃ X : Over (Spec (CommRingCat.of k)),
        Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ IsSeparated X.hom)
      ∧ (Scheme.HasRationalPoint C → IsIso (PicScheme.picEtComparison C)) :=
  ⟨seamClauseOne_of_pointedPicSharpRep C H, seamClauseTwo_of_pointedPicSharpRep C H⟩

/-! ## §5. The weakest antecedent clause (1) actually needs

§4 states the reduction against `PointedPicSharpRep`, which is the shape a
*campaign* delivers: uniform in the field, stated with a rational-point
hypothesis. That is the right form for a hand-off, and it is deliberately
stronger than the proof consumes. This section writes down what clause (1) really
needs, because a reduction priced against an over-strong antecedent misreports
what is left.

Three things fall away, and each is a fact about the proof rather than a
restatement.

* **The uniformity in the field.** Only ONE extension is used. Not "all
  fields", not even "all finite Galois levels of `k`" — a single good level
  suffices, so the antecedent is an existential.
* **The rational point.** It does not occur in `HasGoodGaloisLevel` at all. In §4
  it is the *route* by which the level is produced (via
  `exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral`), but the
  descent step never looks at it. A lane that can represent `picSharp` over some
  finite Galois extension by any other means owes no section.
* **`[GeometricallyIntegral C.hom]` and `IsSeparated`.** The former is used in §4
  *only* to produce the level, so with the level assumed it is not a binder here
  — this theorem holds for a smooth proper `C` with no integrality hypothesis at
  all. The latter is not an input in either form: it comes from the group
  structure of the represented object (`PicEtSeparated`, consumed inside
  `seamClauseOne_of_hasGaloisQuotient_lftFree`).

**On the converse — and this paragraph is a CORRECTION of what stood here.** The
first revision said the converse "fails even at the trivial extension `k' = k`",
evidenced by `exact?` failing on
`Nonempty ((picSharp C).RepresentableBy Z)` from `(picEt C).RepresentableBy Z`,
and gave as the reason that the `PicEtSubcanonical.lean` transport "runs
`picSharp → picEt` only, because it is the sheafification unit". **The reason was
false and the probe was inadequate** (fresh-context audit, reproduced here before
accepting). The comparison is a *morphism*; once it is an iso,
`RepresentableBy.ofIso` runs both ways, and

  `converseOfIsIso : IsIso (picEtComparison C) → (picEt C).RepresentableBy Z →`
  `  Nonempty ((picSharp C).RepresentableBy Z)`

is the three-line term below — the same term already landed inside
`picSchemeOfHasRationalPoint` (`Picard/FGAPicRepresentability.lean`), i.e. in this
file's own import closure, which the withdrawn paragraph did not mention. And the
hypothesis it needs is supplied by **clause (2) of this file's own antecedent**:
under `PointedPicSharpRep`, `seamClauseTwo_of_pointedPicSharpRep` gives
`IsIso (picEtComparison C)` at every curve *with a section*.

So the honest statement is narrower than "not equivalent" and sharper than
"equivalent": the two representability notions are **interderivable at every
pointed curve**, and the gap is confined exactly to curves with **no** rational
point — where `¬ IsIso (picEtComparison C)` is Kleiman's pointless real conic,
quoted in `Picard/PicEtSubcanonical.lean` and *not proved* in this project. That
is still a genuine gap and this is still not a change of coordinates, but the
reason is the pointless case, not the direction of the unit. Contrast
`coverCompatibleEquiv_of_representableBy`
(`Picard/PicEtDescentRepresentability.lean`), whose converse is unconditional. -/
def HasGoodGaloisLevel {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] : Prop :=
  ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
    ∃ (_ : FiniteDimensional k k') (_ : IsGalois k k')
      (X : Over (Spec (CommRingCat.of k'))),
      Nonempty ((PicScheme.picSharp (Scheme.baseChangeField C k')).RepresentableBy X) ∧
        LocallyOfFiniteType X.hom ∧ FiniteInAffine X.left

/-- **Clause (1) from a single good Galois level** — the weakest form, with no
rational point, no integrality binder and no uniformity in the field.

Compare `seamClauseOne_of_pointedPicSharpRep`: same conclusion, and the binder
list has lost `[GeometricallyIntegral C.hom]`. -/
theorem seamClauseOne_of_hasGoodGaloisLevel {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (H : HasGoodGaloisLevel C) :
    ∃ Z : Over (Spec (CommRingCat.of k)),
      Nonempty ((PicScheme.picEt C).RepresentableBy Z) ∧
        LocallyOfFiniteType Z.hom ∧ IsSeparated Z.hom := by
  obtain ⟨k', _, _, hfd, hgal, X', ⟨rep0⟩, hft, hfa⟩ := H
  letI rep := picSharp_representableBy_picEt_transport (Scheme.baseChangeField C k') rep0
  letI := orbitsInAffineOpen_of_finiteInAffine
    (PicScheme.semilinearGalActionOfRepresentableBy C rep) hfa
  exact PicScheme.seamClauseOne_of_hasGaloisQuotient_lftFree rep hft

/-- **The strong antecedent implies the weak one**, so §4 factors through §5 and
the two are not independent routes.

This is the declaration that makes the "deliberately stronger" claim above
checkable instead of asserted: it exhibits the good level, and the exhibition is
exactly the step §4's proof performs. `[GeometricallyIntegral C.hom]` reappears
here because producing the level is what needs it. -/
theorem hasGoodGaloisLevel_of_pointedPicSharpRep {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (H : PointedPicSharpRep.{u}) :
    HasGoodGaloisLevel C := by
  obtain ⟨k'', hfd, hgal, hpt⟩ :=
    Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral C
  letI := hfd
  letI := hgal
  obtain ⟨X', hrep, hft, hfa⟩ := H (Scheme.baseChangeField C (k'' : Type u)) hpt
  exact ⟨(k'' : Type u), inferInstance, inferInstance, hfd, hgal, X', hrep, hft, hfa⟩

/-! ## §6. The converse, as a theorem rather than a docstring sentence

§5's paragraph on the converse is a correction of a claim that was wrong twice
over — false reason, inadequate probe. The lesson is not to state the repaired
version in prose either, so both halves are declarations here. -/

/-- **The converse direction, given invertibility of the comparison.** A scheme
representing `picEt C` also represents `picSharp C` as soon as
`picEtComparison C` is an isomorphism.

This is the term the withdrawn §5 paragraph asserted did not exist. It is not new
mathematics — the same one-liner is inside `picSchemeOfHasRationalPoint`
(`Picard/FGAPicRepresentability.lean`) — but it was not available under a name,
which is exactly how the false prohibition survived. -/
theorem nonempty_representableBy_picSharp_of_isIso {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (hiso : IsIso (PicScheme.picEtComparison C))
    {Z : Over (Spec (CommRingCat.of k))}
    (rep : (PicScheme.picEt C).RepresentableBy Z) :
    Nonempty ((PicScheme.picSharp C).RepresentableBy Z) :=
  ⟨rep.ofIso (asIso (PicScheme.picEtComparison C)).symm⟩

/-- **At a pointed curve the two representability notions are interderivable**,
under the antecedent of §4.

So the reduction of §4/§5 is a change of coordinates *at pointed curves* and a
genuine implication only away from them. Stating this costs nothing and it is the
claim a reviewer would otherwise have to reconstruct from two docstrings; leaving
it unstated is what let the withdrawn version of §5 read as measured. -/
theorem nonempty_representableBy_picSharp_of_hasRationalPoint {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (H : PointedPicSharpRep.{u}) (hpt : Scheme.HasRationalPoint C)
    {Z : Over (Spec (CommRingCat.of k))}
    (rep : (PicScheme.picEt C).RepresentableBy Z) :
    Nonempty ((PicScheme.picSharp C).RepresentableBy Z) :=
  nonempty_representableBy_picSharp_of_isIso C
    (seamClauseTwo_of_pointedPicSharpRep C H hpt) rep

/-! ## §7. The gate-reachability control, and what it says about the price

`HasPicSchemeEt`'s instance `instHasPicSchemeEt` is a projection of the seam
`sorry` and is **unconditional**, so every statement in its domain is provable and
provability is not a discriminating control on this seam — the seam docstring says
so itself. That warning applies to this file's own antecedent and the first
revision ran no such control. It does now.

**MEASURED** (fresh-context audit, reproduced): three of the four conjuncts of
`PointedPicSharpRep` — the `picSharp` representation, local finiteness, and (in
the withdrawn revision) separatedness — are *already derivable from the seam* at a
pointed curve, via `picSchemeOfHasRationalPoint`. A scratch theorem

  `(∀ X : Scheme.{u}, FiniteInAffine X) → PointedPicSharpRep.{u}`

typechecks and reports `[propext, sorryAx, Classical.choice, Quot.sound]`.

**So the honest decomposition of the price is**: relative to the seam taken as
assumed, the only conjunct of `PointedPicSharpRep` that is not a projection of it
is `FiniteInAffine`. That does **not** make the reduction empty — the seam is
`sorry`, so "derivable from the seam" is not a proof of anything — but it does
mean a lane must **axiom-check** any claimed proof of `PointedPicSharpRep` rather
than accept a green build. A proof that routes through `instHasPicSchemeEt`
discharges nothing and will fire `sorryAx`.

The control is recorded here rather than landed as a declaration on purpose: a
`sorryAx`-firing theorem in a rooted module would make this file's own axiom
audit read dirty, which is the opposite of what the measurement is for. -/

/-! ## §8. Producers for `FiniteInAffine`

§7 identifies `FiniteInAffine` as the one conjunct of the antecedent that is not a
projection of the seam — so it is the part a lane must actually build, and the
lemmas it will need to move it around belong here rather than in that lane. -/

/-- **`FiniteInAffine` transports along an isomorphism of schemes.**

This is not a convenience lemma: `RepresentableBy` determines the representing
object only **up to isomorphism**, so the scheme a lane produces and the scheme
the antecedent names need not be the same one, and without this the hypothesis
could be discharged at the wrong object. -/
theorem finiteInAffine_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (h : FiniteInAffine X) :
    FiniteInAffine Y := by
  intro s hs
  obtain ⟨U, hU⟩ := h (e.hom.base ⁻¹' s) (hs.preimage
    (TopCat.homeoOfIso ((Scheme.forgetToTop).mapIso e)).injective.injOn)
  refine ⟨⟨e.hom ''ᵁ U.1, U.2.image_of_isOpenImmersion e.hom⟩, ?_⟩
  intro y hy
  exact ⟨e.inv.base y, hU (by simpa using hy), by simp⟩

/-- **The relative producer**: an object of `Over (Spec k)` whose structure
morphism is affine satisfies `FiniteInAffine`.

Weaker than it looks useful for — the Picard scheme is *not* affine over `k` — but
it is the form a chart-by-chart argument would consume, and it makes the
hypothesis satisfiable at named objects in the slice category the antecedent
actually lives in, not merely at bare affine schemes. -/
theorem finiteInAffine_left_of_isAffineHom {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffineHom X.hom] :
    FiniteInAffine X.left :=
  haveI := isAffine_of_isAffineHom X.hom
  finiteInAffine_of_isAffine _

end AlgebraicGeometry.Scheme
