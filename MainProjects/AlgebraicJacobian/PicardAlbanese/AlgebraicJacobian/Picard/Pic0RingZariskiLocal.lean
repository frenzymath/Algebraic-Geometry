/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0RigidityAffineReduction
import AlgebraicJacobian.Picard.PicEtAffZariskiSep

/-!
# THE RING CASE OF THE `pic⁰` VANISHING IS ZARISKI-LOCAL ON THE TEST RING

The surviving obligation of the whole vanishing route to a `JacobianData` is a statement at
an **arbitrary** `k`-algebra `A`, in either of two interderivable spellings:

* `Subsingleton (pic0Subgroup C (overSpec k A))` — consumed by
  `jacobianData_of_overSpec_subsingleton` (`Pic0VanishingAffineReduction.lean:269`);
* ring-level field-point rigidity `hrigAff` — consumed by `jacobianData_of_rigidityAff`
  (`Pic0RigidityAffineReduction.lean:190`).

This file attacks the **quantifier** rather than the content: both spellings are Zariski-local
on `Spec A`.  The input is the *separation* half of the landed Zariski sheaf property of the
plus construction, `PicEtAff.eq_of_away_eq` (`PicEtAffZariskiSep.lean:137`) — nothing is glued,
so the gluing half (`PicEtAffZariskiGlue.lean`) is not used.

## What this is and is not — READ THIS BEFORE PRICING ANYTHING BELOW

It is a reduction of the *test algebra*, not of the geometry, and it does **not** prove the ring
case.  Two things are load-bearing and were wrong in an earlier version of this header; both were
found by a fresh-context audit (`I-1657`, `I-1660`) and independently reproduced here.

**1. AT A FIXED `A` the reduction is real: the ring case at `A` follows from the ring case at the
members of any finite covering family of localizations of `A`, and there is no route back.**  That
is what `PicEtAff.subsingleton_of_away` and `rigidity_of_away` say, and it is the usable content
of the file.

**2. UNDER THE OUTER `∀ A` IT IS NOT A WEAKENING AT ALL.**  The two `JacobianData` producers at
the bottom quantify their pointwise hypothesis over *every* test algebra — and
`Localization.Away f` **is** a test algebra, so the outer `∀ A` already covers it.  The converse
is one line with the trivial witness `f = 1`: `Ideal.eq_top_of_isUnit_mem` says `1 ∉ p`, and the
hypothesis at `Localization.Away 1` is an instance of the global statement.  So

> `jacobianData_of_forall_prime_subsingleton`'s hypothesis is **logically equivalent** to
> `jacobianData_of_affine_subsingleton`'s (`Pic0VanishingRoute.lean:296`), and
> `jacobianData_of_forall_prime_rigidity`'s to `jacobianData_of_rigidityAff`'s
> (`Pic0RigidityAffineReduction.lean:190`).

Those two producers are therefore **restatements, not repricings**.  They are kept because the
pointwise *shape* is what a local computation delivers, but a lane must not read them as having
reduced the obligation.  The general lesson, which cost this session a false claim: before
pricing a localisation-or-pointwise reduction as progress, try the converse with the trivial
witness — if it closes, the reduction only helps at a **fixed** base object, and the consumer's
quantifier decides whether that is any help.

**3. The interface is NOT a local-ring interface**, contrary to what this header first said.  The
hypothesis is about `Localization.Away f`, and `IsLocalRing (Localization.Away f)` does not hold
(verified: instance synthesis fails; a basic open of `Spec A` is not a point).  A lane with a
genuinely local computation holds `Localization.AtPrime p`, and **nothing here bridges `AtPrime`
to `Away`** — that bridge is spreading-out, it is unbuilt, and it is the real remaining work on
this side.

Seminormality is the other half of the story and it does not go away: see the measurement at the
end of this docstring.

## The degenerate test ring: the site is not a counterexample, and that is ALL it is

`hrigAff`'s antecedent is **vacuous** at a subsingleton `A` (there is no `k`-algebra map from
the zero ring to a field), so the hypothesis demands `q = 1` for free there.  That made the
subsingleton ring the cheapest potential *refutation* site for the affine spelling, and it was
recorded as genuinely unchecked (inbox `I-1655`, author addendum).  It is now checked:
`PicEtAff.subsingleton_of_subsingleton` proves the plus construction **is** trivial there,
unconditionally and with no genus or curve input.  So the site is **not a counterexample**.

**CORRECTED after a fresh-context audit (`I-1658`), and the correction is the honest reading.**
An earlier version of this paragraph said this "settles the open question of `I-1655`".  It does
not.  At a subsingleton `A` the antecedent, the conclusion, *and* this file's own pointwise-local
hypothesis are all vacuous together — the section is the vacuous-hypothesis instance of
`PicEtAff.subsingleton_of_forall_prime` below, since `Spec A` is empty.  So it tells a reader
nothing about whether `hrigAff` is inhabitable at any `A` with a **nonempty** spectrum, which is
what the `I-1655` addendum was actually asking.  Inhabitability stays open.  What the section
does buy is that a specific attack is closed, and the four steps below are reusable.

The chain is four steps, each of which is about the vehicle rather than the curve: `Spec` of a
subsingleton ring has empty carrier (`PrimeSpectrum.isEmpty_iff_subsingleton`), hence so does
the product `C ⊗ overSpec k A` (project along `snd`), hence its Čech Picard group is trivial
(the landed `Scheme.CechPic.subsingleton_of_subsingleton`, `Pic.lean:257`) and so is the
quotient `relPic`; and every étale cover of a subsingleton ring is again subsingleton, because
its spectrum maps *onto* the empty spectrum.

## Main declarations

* `AlgebraicGeometry.PicEtAff.subsingleton_of_away` — **the reduction, `Subsingleton`
  spelling**: triviality of the plus construction at each member of a finite covering family
  of localizations gives it at `A`.
* `AlgebraicGeometry.PicEtAff.rigidity_of_away` — **the reduction, rigidity spelling**: the
  `hrigAff` clause at each member of the family gives it at `A`.  Note the direction the field
  points travel: a field point of a localization `S i` restricts to one of `A` by composing
  with `A → S i`, so the antecedent at `A` supplies the antecedent at `S i` and no lifting of
  field points is needed.
* `AlgebraicGeometry.subsingleton_pic0Subgroup_overSpec_of_away` — the same reduction
  transported to the `pic0Subgroup` carrier the producers consume.
* `AlgebraicGeometry.PicEtAff.subsingleton_of_forall_prime` — **the pointwise form, and the
  one a consumer wants**: no covering family in the statement, only a basic-open neighbourhood
  at each prime.  With `subsingleton_pic0Subgroup_overSpec_of_forall_prime` on the `pic⁰`
  carrier, and `span_eq_top_of_forall_prime` as the `Spec`-level step (a mathlib lemma
  re-spelled, not new).
* `AlgebraicGeometry.PicEtAff.subsingleton_of_subsingleton` /
  `subsingleton_relPic_of_subsingleton` / `Algebra.EtaleCover.subsingleton_carrier` — the
  degenerate-test-ring chain, unconditional.

## What was measured and did NOT work, so nobody re-runs it

The obvious hope is that "local" is enough on its own.  It is not, and the reason is worth
recording: `Subsingleton (CommRing.Pic A)` **is** available for a local `A` (mathlib's
`CommRing.Pic.instSubsingletonOfFiniteMaximalSpectrum`), but the obligation involves the
polynomial ring, and `Subsingleton (CommRing.Pic (Polynomial A))` does **not** follow from
`IsLocalRing A` — measured, `exact?` fails.  Traverso–Swan is the reason (that identity holds
exactly for seminormal rings) and a local ring need not be seminormal.  So at a FIXED `A` these
lemmas move the obligation to basic opens of `Spec A`; they do not discharge it there, and the
remaining content is seminormality-flavoured rather than quantifier-flavoured.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

noncomputable section

/-! ## The degenerate test ring -/

/-- Every étale cover of a subsingleton ring has subsingleton carrier: the carrier's spectrum
maps **onto** `Spec A`, which is empty, so the carrier's spectrum is empty too. -/
theorem Algebra.EtaleCover.subsingleton_carrier {A : Type u} [CommRing A] [Subsingleton A]
    (E : Algebra.EtaleCover A) : Subsingleton E.Carrier := by
  haveI : IsEmpty (PrimeSpectrum A) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr ‹_›
  haveI : IsEmpty (PrimeSpectrum E.Carrier) :=
    ⟨fun p => isEmptyElim (PrimeSpectrum.comap (algebraMap A E.Carrier) p)⟩
  exact PrimeSpectrum.isEmpty_iff_subsingleton.mp ‹_›

/-- **The relative Picard group is trivial over a subsingleton test ring.**

`Spec A` is empty, so the product `C ⊗ overSpec k A` is empty (project along `snd`), so its
Čech Picard group is trivial by the landed `Scheme.CechPic.subsingleton_of_subsingleton`; the
quotient by `picFromBase` inherits it.

Uses none of the curve's geometry — this is a statement about the vehicle. -/
theorem subsingleton_relPic_of_subsingleton (A : Type u) [CommRing A] [Algebra k A]
    [Subsingleton A] : Subsingleton (relPic C (overSpec k A)) := by
  haveI : IsEmpty ↥((overSpec k A).left) := by
    change IsEmpty (PrimeSpectrum A)
    exact PrimeSpectrum.isEmpty_iff_subsingleton.mpr ‹_›
  haveI : Subsingleton ↥((C ⊗ overSpec k A).left) :=
    ⟨fun x _ => isEmptyElim ((snd C (overSpec k A)).left.base x)⟩
  haveI := Scheme.CechPic.subsingleton_of_subsingleton ((C ⊗ overSpec k A).left)
  exact ⟨fun x y => by
    induction x using relPic.ind with | mk L =>
    induction y using relPic.ind with | mk M =>
    exact congrArg (relPicMk C (overSpec k A)) (Subsingleton.elim L M)⟩

/-- The `A`-algebra map into a subsingleton `A`-algebra: everything goes to `0`.  Needed
because two plus-class representatives over a subsingleton base live on *different* covers,
and `mk_eq_mk_iff` wants a common refinement. -/
def toSubsingletonAlgHom (A : Type u) [CommRing A] (R S : Type u)
    [CommRing R] [CommRing S] [Algebra A R] [Algebra A S] [Subsingleton S] :
    R →ₐ[A] S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- **THE PLUS CONSTRUCTION IS TRIVIAL OVER A SUBSINGLETON TEST RING**, unconditionally.

This is a **non-counterexample only** (audit `I-1655`/`I-1676`): the subsingleton ring is the
site at which `hrigAff`'s antecedent is vacuous, and therefore its cheapest potential
refutation site.  The conclusion holds there anyway, so the affine spelling is **not refuted**
at that site — but this does NOT settle `hrigAff`'s inhabitability, which remains open on
nonempty spectra (see the module header).  It rules out one degenerate refutation, nothing
more.

No genus hypothesis, no curve input beyond the standing section variable. -/
theorem PicEtAff.subsingleton_of_subsingleton {A : Type u} [CommRing A] [Algebra k A]
    [Subsingleton A] : Subsingleton (PicEtAff C A) := by
  refine ⟨fun x y => ?_⟩
  induction x using PicEtAff.ind with | _ E ξ =>
  induction y using PicEtAff.ind with | _ F ζ =>
  haveI : Subsingleton E.Carrier := Algebra.EtaleCover.subsingleton_carrier E
  haveI : Subsingleton (relPic C (overSpec k E.Carrier)) :=
    subsingleton_relPic_of_subsingleton C E.Carrier
  refine (PicEtAff.mk_eq_mk_iff C).mpr
    ⟨E, AlgHom.id A _, toSubsingletonAlgHom A F.Carrier E.Carrier, ?_⟩
  exact Subtype.ext (Subsingleton.elim _ _)

/-- The `pic⁰` form at a subsingleton test ring: a subgroup of a subsingleton group. -/
theorem subsingleton_pic0Subgroup_overSpec_of_subsingleton
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Subsingleton A] :
    Subsingleton (pic0Subgroup C (overSpec k A)) := by
  haveI hplus : Subsingleton (PicEtAff C A) :=
    PicEtAff.subsingleton_of_subsingleton C (A := A)
  haveI : Subsingleton (picEt C (overSpec k A)) :=
    @Equiv.subsingleton _ _ (picEtAffineEquiv C A).toEquiv hplus
  exact ⟨fun s t => Subtype.ext (Subsingleton.elim _ _)⟩

/-! ## The reduction: both spellings are Zariski-local on the test ring -/

section Local

variable {A : Type u} [CommRing A] [Algebra k A]
variable {ι : Type u} [Finite ι] (g : ι → A)
variable (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra k (S i)]
  [∀ i, Algebra A (S i)] [∀ i, IsScalarTower k A (S i)]
  [∀ i, IsLocalization.Away (g i) (S i)]

/-- **THE REDUCTION, `Subsingleton` spelling**: if the plus construction is trivial at every
member of a finite covering family of localizations of `A`, it is trivial at `A`.

One application of the landed separation half `PicEtAff.eq_of_away_eq`: two classes over `A`
have equal restrictions because the target is a subsingleton. -/
theorem PicEtAff.subsingleton_of_away (hg : Ideal.span (Set.range g) = ⊤)
    (hloc : ∀ i, Subsingleton (PicEtAff C (S i))) :
    Subsingleton (PicEtAff C A) :=
  ⟨fun _ _ => PicEtAff.eq_of_away_eq C g S hg fun i => @Subsingleton.elim _ (hloc i) _ _⟩

/-- **THE REDUCTION, rigidity spelling**: the `hrigAff` clause at every member of a finite
covering family of localizations of `A` gives it at `A`.

Note which way the field points travel, because it is what makes this cheap: a field point of a
localization `S i` restricts to a field point of `A` by composing with `A → S i`, so the
antecedent **at `A`** supplies the antecedent at each `S i` — no lifting of field points along
the localization is required, and no compatibility between the members is used.  The classes
then agree with `1` after each localization, and separation finishes. -/
theorem PicEtAff.rigidity_of_away (hg : Ideal.span (Set.range g) = ⊤)
    (hloc : ∀ i, ∀ q : PicEtAff C (S i),
      (∀ (K : Type u) [Field K] [Algebra k K] (φ : S i →ₐ[k] K),
        PicEtAff.mapAlg C φ q = 1) → q = 1)
    (q : PicEtAff C A)
    (hq : ∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
      PicEtAff.mapAlg C φ q = 1) :
    q = 1 := by
  refine PicEtAff.eq_of_away_eq C g S hg (x := q) (y := 1) fun i => ?_
  rw [map_one]
  refine hloc i _ fun K _ _ φ => ?_
  rw [← PicEtAff.mapAlg_comp]
  exact hq K (φ.comp (IsScalarTower.toAlgHom k A (S i)))

/-- **The reduction on the `pic⁰` carrier the producers consume**: `Subsingleton
(pic0Subgroup C (overSpec k A))` from triviality of the plus construction at each member of a
finite covering family.

Transported through the affine comparison `picEtAffineEquiv`, then restricted to the subgroup.
Stated separately because `jacobianData_of_overSpec_subsingleton`
(`Pic0VanishingAffineReduction.lean:269`) takes exactly this carrier. -/
theorem subsingleton_pic0Subgroup_overSpec_of_away
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (hg : Ideal.span (Set.range g) = ⊤)
    (hloc : ∀ i, Subsingleton (PicEtAff C (S i))) :
    Subsingleton (pic0Subgroup C (overSpec k A)) := by
  haveI hplus : Subsingleton (PicEtAff C A) :=
    PicEtAff.subsingleton_of_away C g S hg hloc
  haveI : Subsingleton (picEt C (overSpec k A)) :=
    @Equiv.subsingleton _ _ (picEtAffineEquiv C A).toEquiv hplus
  exact ⟨fun s t => Subtype.ext (Subsingleton.elim _ _)⟩

end Local

/-! ## The pointwise form: a hypothesis at each prime, no cover supplied

The reductions above take the covering family as an argument, which is the wrong interface for
a consumer: a lane computing `Pic` locally knows something *at each prime*, not a finite cover.
This section removes the cover from the statement.  Two elementary steps do it, and both are
about `Spec` rather than about the curve:

* if a set of elements meets the complement of every prime, it generates the unit ideal
  (otherwise it sits inside a maximal ideal);
* the unit ideal is spanned by a **finite** subset (`Ideal.span_eq_top_iff_finite`), which is
  the compactness of `Spec A` in the form the sheaf property wants.

The localizations are then the canonical `Localization.Away f`, so no family of test algebras
has to be threaded through the statement either. -/

section Pointwise

/-- An indexed family of ring elements whose basic opens cover `Spec A` generates the unit ideal.

**This is mathlib's `PrimeSpectrum.iSup_basicOpen_eq_top_iff` in another spelling**, and it is
written through it rather than re-proved — the audit finding `I-1659`.  An earlier version proved
it directly (a set in no prime is in no maximal ideal) because plain `exact?` fails on this goal;
`exact?` failing is not absence, and the mathlib lemma is stated as an `iSup` of basic opens over
an *indexed family*, which is exactly the shape the use site below has.

Kept as a named lemma only because the `Set.range`/`iSup` translation is two tactic lines that
would otherwise be inlined twice. -/
theorem span_eq_top_of_forall_prime {A : Type u} [CommRing A] {ι : Type*} (f : ι → A)
    (h : ∀ p : PrimeSpectrum A, ∃ i, f i ∉ p.asIdeal) :
    Ideal.span (Set.range f) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  ext p
  simpa using h p

variable {A : Type u} [CommRing A] [Algebra k A]

/-- **THE POINTWISE REDUCTION**: if every prime of `A` has *some* basic open neighbourhood on
which the plus construction is trivial, it is trivial at `A`.

No covering family in the statement: the witnesses are chosen at the primes, shown to span,
cut down to a finite subfamily by `Ideal.span_eq_top_iff_finite`, and fed to
`PicEtAff.subsingleton_of_away`.  The hypothesis is about `Localization.Away f`, a BASIC OPEN and
NOT a local ring (`IsLocalRing (Localization.Away f)` does not hold); a lane holding a genuinely
local computation has `Localization.AtPrime p`, and the `AtPrime`-to-`Away` bridge is spreading
out and is unbuilt.  So this is the interface for a computation over basic opens, which is a
weaker thing than the header of this file originally claimed. -/
theorem PicEtAff.subsingleton_of_forall_prime
    (h : ∀ p : PrimeSpectrum A, ∃ f : A, f ∉ p.asIdeal ∧
      Subsingleton (PicEtAff C (Localization.Away f))) :
    Subsingleton (PicEtAff C A) := by
  classical
  choose f hf hsub using h
  have hspan : Ideal.span (Set.range f) = ⊤ :=
    span_eq_top_of_forall_prime f fun p => ⟨p, hf p⟩
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite (Set.range f)).mp hspan
  refine PicEtAff.subsingleton_of_away C (ι := {x // x ∈ t}) (fun i => i.1)
    (fun i => Localization.Away i.1) ?_ ?_
  · rwa [show (Set.range fun i : {x // x ∈ t} => i.1) = (↑t : Set A) from by
      ext x; exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩]
  · intro i
    obtain ⟨p, hp⟩ := hts i.2
    exact hp ▸ hsub p

/-- The pointwise reduction on the `pic⁰` carrier the producers consume. -/
theorem subsingleton_pic0Subgroup_overSpec_of_forall_prime
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (h : ∀ p : PrimeSpectrum A, ∃ f : A, f ∉ p.asIdeal ∧
      Subsingleton (PicEtAff C (Localization.Away f))) :
    Subsingleton (pic0Subgroup C (overSpec k A)) := by
  haveI hplus : Subsingleton (PicEtAff C A) :=
    PicEtAff.subsingleton_of_forall_prime C h
  haveI : Subsingleton (picEt C (overSpec k A)) :=
    @Equiv.subsingleton _ _ (picEtAffineEquiv C A).toEquiv hplus
  exact ⟨fun s t => Subtype.ext (Subsingleton.elim _ _)⟩

/-- **THE POINTWISE REDUCTION, rigidity spelling**: the `hrigAff` clause at a basic open around
each prime gives it at `A`.

Same three steps as `PicEtAff.subsingleton_of_forall_prime` (choose, span, cut to finite), fed
to `PicEtAff.rigidity_of_away`.  Stated separately because `jacobianData_of_rigidityAff`
consumes the rigidity clause and not a `Subsingleton`, and because the rigidity form is the one
that carries no degree apparatus. -/
theorem PicEtAff.rigidity_of_forall_prime
    (h : ∀ p : PrimeSpectrum A, ∃ f : A, f ∉ p.asIdeal ∧
      ∀ q : PicEtAff C (Localization.Away f),
        (∀ (K : Type u) [Field K] [Algebra k K] (φ : Localization.Away f →ₐ[k] K),
          PicEtAff.mapAlg C φ q = 1) → q = 1)
    (q : PicEtAff C A)
    (hq : ∀ (K : Type u) [Field K] [Algebra k K] (φ : A →ₐ[k] K),
      PicEtAff.mapAlg C φ q = 1) :
    q = 1 := by
  classical
  choose f hf hrig using h
  have hspan : Ideal.span (Set.range f) = ⊤ :=
    span_eq_top_of_forall_prime f fun p => ⟨p, hf p⟩
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite (Set.range f)).mp hspan
  refine PicEtAff.rigidity_of_away C (ι := {x // x ∈ t}) (fun i => i.1)
    (fun i => Localization.Away i.1) ?_ ?_ q hq
  · rwa [show (Set.range fun i : {x // x ∈ t} => i.1) = (↑t : Set A) from by
      ext x; exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩]
  · intro i
    obtain ⟨p, hp⟩ := hts i.2
    exact hp ▸ hrig p

end Pointwise

/-! ## The composition to the goal object

The reductions above are worth nothing if they do not reach `JacobianData`.  These two
declarations are that check, and they are what makes this file usable by the representability
headline rather than local to its own row: the *pointwise-local* hypothesis, quantified over
every test algebra, produces the datum through the landed producers with no atlas, no chart
certificate, no coverage clause, no divisor representability and no rational point.

Both carry the genus-`0` hypothesis of the producer they compose with, and neither adds anything
else. -/

section Datum

variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **`JacobianData` from the pointwise-local vanishing.**

`subsingleton_pic0Subgroup_overSpec_of_forall_prime` at every test algebra, fed to
`jacobianData_of_overSpec_subsingleton` (`Pic0VanishingAffineReduction.lean:269`).  The
hypothesis mentions no test object, no open and no morphism of schemes: only `k`-algebras, their
primes, and the plus construction at the canonical localizations. -/
def jacobianData_of_forall_prime_subsingleton
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A],
      ∀ p : PrimeSpectrum A, ∃ f : A, f ∉ p.asIdeal ∧
        Subsingleton (PicEtAff C (Localization.Away f))) :
    JacobianData C :=
  jacobianData_of_overSpec_subsingleton C fun A _ _ =>
    subsingleton_pic0Subgroup_overSpec_of_forall_prime C (h A)

/-- **`JacobianData` from the pointwise-local rigidity**, at genus `0`.

The rigidity analogue, through `jacobianData_of_rigidityAff`
(`Pic0RigidityAffineReduction.lean:190`).  This is the shortest statement of the whole vanishing
route's remaining debt IN SHAPE, though — per point 2 of the module docstring — not in
strength: this hypothesis is logically equivalent to `jacobianData_of_rigidityAff`'s own. -/
def jacobianData_of_forall_prime_rigidity (hg : genus C = 0)
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A],
      ∀ p : PrimeSpectrum A, ∃ f : A, f ∉ p.asIdeal ∧
        ∀ q : PicEtAff C (Localization.Away f),
          (∀ (K : Type u) [Field K] [Algebra k K] (φ : Localization.Away f →ₐ[k] K),
            PicEtAff.mapAlg C φ q = 1) → q = 1) :
    JacobianData C :=
  jacobianData_of_rigidityAff C hg fun A _ _ => PicEtAff.rigidity_of_forall_prime C (h A)

/-! ### The equivalence, proved rather than asserted

Point 2 of the module docstring says the two producers above are restatements.  A docstring
saying so is a claim nobody checks, so here it is as a theorem: the converse direction, with the
trivial witness `f = 1`.  Together with `PicEtAff.subsingleton_of_forall_prime` (which is the
forward direction) the two hypotheses are interderivable, and the same argument works verbatim for
the rigidity spelling.

This is the check that should be run on *any* localisation-or-pointwise reduction before it is
priced as progress. -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
/-- **The converse, with the trivial witness**: the global hypothesis implies the pointwise-local
one, because `Localization.Away 1` is itself a test algebra and `1` lies outside every prime.

So under the outer `∀ A` the pointwise form is *not* weaker — the content of the audit finding
`I-1660`, kept in the file so the equivalence cannot be lost again. -/
theorem forall_prime_subsingleton_of_forall
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A], Subsingleton (PicEtAff C A))
    (A : Type u) [CommRing A] [Algebra k A] (p : PrimeSpectrum A) :
    ∃ f : A, f ∉ p.asIdeal ∧ Subsingleton (PicEtAff C (Localization.Away f)) :=
  ⟨1, fun hc => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hc isUnit_one),
    h (Localization.Away (1 : A))⟩

end Datum

end

end AlgebraicGeometry
