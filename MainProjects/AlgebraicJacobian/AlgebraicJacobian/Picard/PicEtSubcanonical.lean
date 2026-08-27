/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.FGAPicRepresentability

/-!
# Subcanonicity of the étale site, and the section-free transport `picSharp → picEt`

This file settles a **route** question about the project's central obligation
`Scheme.fgaPicardRepresentability` (`Picard/FGAPicRepresentability.lean`), and
it settles it in the direction opposite to what that file's docstring and the
board row `AJC.picrep.etale-rep` currently assert.

## The claim this file refutes

Clause (1) of the seam asks for representability of the étale-sheafified
functor `PicScheme.picEt C`, while every milestone of the Milne–Kollár campaign
targets the *unsheafified* `PicScheme.picSharp C`. The seam docstring and the
board row both say the gap between them **cannot be bridged without a
`k`-rational point**, on the grounds that the comparison
`PicScheme.picEtComparison C` is Kleiman §2 Thm 2.5 — an isomorphism only under
a section — and that a section is exactly what the owner decision `I-0491`
forbids the headline to carry.

That reasoning is wrong, and the error is a direction confusion. Kleiman §2
Thm 2.5 is the statement that a section makes the comparison an isomorphism
*with no hypothesis on the presheaf*. But there is a second, entirely
independent, route to the same conclusion: the comparison is the sheafification
unit, and a unit is an isomorphism **exactly when its source is already a
sheaf** (`CategoryTheory.isIso_toSheafify`). A representable functor is a sheaf
for any subcanonical topology. So *if* the campaign delivers representability of
`picSharp`, the source is a sheaf for that reason alone, the unit is an
isomorphism, and no section is involved anywhere.

The consequence for the route, stated precisely because the board row is
currently priced on its negation: the campaign's endpoint **is** transportable
to clause (1). `picSharp_representableBy_picEt_transport` below is that
transport, proved with no rational-point hypothesis of any kind.

## What is actually still open

This file does **not** close the seam. It removes an alleged obstruction, which
is a different thing, and the honest statement of what remains is:

* the antecedent of every theorem here is representability of `picSharp C`
  over an arbitrary field — campaign milestones J1–J5, G3, G4, B1/B4/B6,
  D2′–D4′, P5 — and **not one of those is discharged**. No theorem in this file
  is applied to a curve anywhere in the project, and none should be reported as
  progress on the existence question;
* what changes is the *shape* of the remaining work. Before this file, a reader
  of the seam docstring concluded that finishing the campaign leaves a further
  unpriced obligation ("represent `picEt` directly, or restate the headline").
  After it, no supplementary étale-representability theorem is needed: `picEt`
  representability follows from `picSharp` representability by `Subcanonical` +
  `isIso_toSheafify`, both already in Mathlib.

**But the antecedent must not be read as reachable over `k`, and §4 is why.**
The same subcanonicity that powers the transport also proves that a
representable `picSharp` is a *Zariski* sheaf
(`PicScheme.picSharp_isSheaf_zariski_of_representableBy`).

**But the falsity of `picSharp` representability is quoted from Kleiman, NOT
derived from that theorem** — corrected 2026-07-29 (`review-ajc` / `I-0970`,
after two successive citations in this slot turned out not to support it).
Kleiman L5105–L5108: for the conic `u²+v²+w²=0` in `ℙ²_ℝ` — smooth, proper,
geometrically integral, no rational point, i.e. exactly these binders —
`Pic_{X/ℝ}` is **not representable**, while `Pic_{(X/ℝ)ét}` is by §4 `th:main`.
That is direct. The Zariski route would need "`picSharp` is not a Zariski
sheaf", which no source establishes: `ex:Pfs` compares the two *sheafifications*
`zar` and `ét` (both already sheaves), and `th:cmp` part 1 gives
`picSharp ↪ Pic_{(X/S)zar}` here, so `picSharp` is Zariski-*separated* and any
failure could only be gluing. Do **not** rebuild the argument that way.
Contrapositive of the quoted fact: representability of `picSharp C` over an
arbitrary field is **unproved, with a refutation route mapped out** — the
antecedent that route needs is quoted from Kleiman, not formalised. So the campaign
milestones that conclude representability of `picSharp`/`picSharpDeg` over `k`
itself — G3 (Galois descent of `picSharp` points) and G4 (the coproduct
assembly) — aim at a statement this project cannot currently prove, and expects to
be false.

**Read §3's closing paragraphs (`:390`–`:400`) before acting on that sentence**, and
read them as qualifying it rather than elaborating it. Four sentences in this file,
this one included, formerly said "**false in general**" / "genuinely uninhabitable",
and that is a stronger claim than anything established: the refutation
(`not_representableBy_picSharp_of_not_isIso_picEtComparison`) is *conditional* on
`¬ IsIso (picEtComparison C)`, which is Kleiman L5105–L5108 quoted, not proved here.
The four sites are corrected (`I-1354`); the distinction is not pedantry, because a
reader who takes "false in general" at face value concludes the campaign is dead,
where what is true is that its endpoint must be delivered over `k^s` and descended
as `picEt` — a route decision taken on a word.

This is not an argument against the Milne–Kollár route. Everything through J5
runs over a separably closed `k'`, where a section is available *mathematically*
and the obstruction is absent; the break is precisely at the descent step where
the conclusion returns to `k`.

**That availability is UNFORMALISED, and this is the one place it is load-bearing
(`review-ajc`, 2026-07-30, controlled probe).** The sentence above is what keeps
the §3/§4 refutation from sinking the whole route, so it is worth stating exactly
what backs it: nothing, yet. `Scheme.HasRationalPoint C` for a smooth proper
geometrically integral `C` over a *separably* closed field has **no producer** in
this project — `exact?` fails on it, while the same probe with `[IsAlgClosed k]`
closes outright by `hasRationalPoint_of_isAlgClosed`
(`Albanese/AlbaneseUP.lean:289`), which is what makes the failure a real absence
rather than an import artifact. And the algebraically closed producer is *not* a
substitute: the campaign pins `k^s`, never `k̄` (G1, and P4(c)/(d) are marked
"separably closed only — never generalize"), because `k̄` breaks the char-`p`
discipline the J-cluster needs. The other candidate,
`hasRationalPoint_baseChangeField` (`RiemannRoch/CurveBaseChange.lean:285`), only
*propagates* a point down a tower — it assumes `[HasRationalPoint C]` upstairs,
which `I-0491` forbids the headline to carry.

The statement is true and the gap is real, but **the cheap proof route I first
suggested for it is FALSE, and the correction matters more than the gap**
(`ajc-p3`/`ajc-p4`, refuting `review-ajc`'s own hint, 2026-07-30). I had written
that the campaign names its own proof at P4(d) — "closed points of a smooth curve
over a separably closed field are rational, since smoothness makes the residue
fields separable" — so that one need only weaken `IsAlgClosed` to `IsSepClosed`
in the last step of `hasRationalPoint_of_isAlgClosed`. That is wrong: a
separably closed field need **not** be perfect, so over an imperfect separably
closed `K` the affine line already has closed points with residue field
`K(a^{1/p})`, an *inseparable* extension. Machine-checked in both directions:
`IsAlgClosed K → PerfectField K` exists in mathlib
(`IsAlgClosed.perfectField`), while `IsSepClosed K` — even with `CharP K p` — does
**not** give it. So `pointEquivClosedPoint` has no separable analogue and that
route targets a false intermediate. Two further corrections from the same pair:
bare `[Smooth]` is not enough (the relative-dimension *numeral* is load-bearing,
because the chart argument needs étale-over-`𝔸¹`), and my "zero lemmas" was true
of AJC but false of the workspace.

The real route is a **port**: the sibling project proves it, sorry-free, as
`exists_rationalPoint_of_smoothOfRelativeDimension_one`
(`Curve/SeparablyClosedPoints.lean:62`, with `Curve/SeparablyClosedFibre.lean`
importing only `Mathlib`), via a standard-smooth chart and an étale
`K[X]`-algebra — not via residue-field separability. Its conclusion is this
project's `HasRationalPoint` field verbatim (`∃ p, p ≫ f = 𝟙`) on a *bare*
`Scheme` over `Spec K`, so unlike the `picEt` case there is no carrier mismatch
to price. Tracked as `I-1135`; owned by `AJC.picrep.sepclosed-section`.

The repair the results here name is that the object
descended to `k` must be `picEt` and not `picSharp`. Over `k'` the two agree, by
`isIso_picEtComparison_of_isSheaf` applied to the representability available
there — so J5's output is already a `picEt`-representing scheme after base
change.

**§4 makes the constraint a reduction rather than a quotation**, which is the
one place this file goes beyond restating Kleiman.
`not_representableBy_picSharp_of_not_isIso_picEtComparison` proves: if the
comparison fails to be an isomorphism then NO scheme represents `picSharp C`.
That is Kleiman's own inference at L5105–L5108 ("the two functors differ, so
`Pic_{X/ℝ}` is not representable") supplied with a proof, and it is the
contrapositive of §3 — no sheaf step, no topology. So a hypothetical proof of
G3/G4 as written would prove `picEtComparison` is an isomorphism for *every*
curve over *every* field, including pointless ones.

What is **not** formalised, and is the whole residue of the argument: that the
comparison genuinely fails for that conic. Kleiman's `φ*O(1)` witness runs
through `h⁰` on `ℙ¹_ℂ` and flat base change. Producing it in Lean is bounded,
well-specified work, and §4's theorems are the interface it plugs into. Until
then "G3/G4 target a false statement" rests on that one quotation — and on
nothing else, which is the improvement.

There is one genuine subtlety, and it is not a section. The transport proves
that the *same* scheme represents both functors, so it does not produce
`picSharp` representability out of nothing — it consumes it. Read
`Scheme.picSharp_representableBy_picEt_transport` as: the campaign does not
need a supplementary étale-representability theorem, only the subcanonicity
lemma proved here.

## Main results

* `AlgebraicGeometry.Scheme.subcanonical_etaleTopology` — the big étale
  topology on schemes is subcanonical. Absent from Mathlib `v4.31` as an
  instance; obtained from `proetaleTopology` (which has one) along
  `Scheme.etaleTopology_le_proetaleTopology` by
  `GrothendieckTopology.Subcanonical.of_le`.
* `AlgebraicGeometry.Scheme.subcanonical_etaleTopologyOver` — its localisation
  to `(Sch/k)`, the site the relative Picard presheaf actually lives on.
* `Scheme.PicScheme.isIso_picEtComparison_of_isSheaf` — the section-free
  criterion: if `PicSharp.relPresheaf C` is an étale sheaf then
  `picEtComparison C` is an isomorphism.
* `Scheme.PicScheme.relPresheaf_isSheaf_of_representableBy` — representability
  of `picSharp C` makes `relPresheaf C` an étale sheaf (subcanonicity, then
  reflection along the forgetful functor).
* `Scheme.picSharp_representableBy_picEt_transport` — the transport: a scheme
  representing `picSharp C` also represents `picEt C`, with **no**
  `[HasRationalPoint C]`.
* `Scheme.hasPicSchemeEt_of_picSharp_representability` — the same statement in
  the seam's own packaging: clause (1) of `fgaPicardRepresentability` follows
  from its `picSharp` analogue.
* `Scheme.isIso_picEtComparison_of_picSharp_representability` — and clause (2)
  follows too, *unconditionally*, which is strictly stronger than the seam's
  own `HasRationalPoint C → IsIso …`.
* `Scheme.PicScheme.picSharp_isSheaf_zariski_of_representableBy` — §4: a
  representable `picSharp` is a Zariski sheaf. True and clean, but only half of
  the seam's prose argument; see its docstring for why the other half is not
  sourced (`I-0970`).
* `Scheme.PicScheme.not_representableBy_picSharp_of_not_isIso_picEtComparison`
  and `not_exists_representing_picSharp_of_not_isIso` — §4's actual payload:
  if the comparison is not an isomorphism then NO scheme represents `picSharp C`.
  This is Kleiman's non-representability inference (L5105–L5108) as a theorem,
  and it needs no sheaf step — only §3.

## References

Kleiman, "The Picard scheme" (arXiv:math/0504020), §2 Thm 2.5 (`th:comp`) — the
section route, which this file does not use — and §4 Thm `th:main`.
Board: `AJC.picrep.etale-rep`. Decision: `I-0491`.
-/

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. The étale site is subcanonical -/

/-- **The big étale topology on schemes is subcanonical**, i.e. every
representable presheaf is an étale sheaf.

Mathlib `v4.31` supplies this instance for the Zariski, coherent, regular,
extensive and *pro*-étale topologies, but not for the étale one. It costs
nothing: `Scheme.etaleTopology_le_proetaleTopology` and
`GrothendieckTopology.Subcanonical.of_le` (a subtopology of a subcanonical
topology is subcanonical, since the canonical topology is an upper bound).

This is the lemma that makes the transport of §3 possible, and its absence is
why the seam's route analysis concluded a section was needed. -/
instance subcanonical_etaleTopology : Scheme.etaleTopology.{u}.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology

/-- Subcanonicity descends to the localisation `(Sch/k)`, which is the site the
relative Picard presheaf lives on (`Scheme.etaleTopologyOver`,
`Picard/PicEtSheaf.lean`).

Supplied by `GrothendieckTopology.subcanonical_over` from
`subcanonical_etaleTopology`; recorded as a named theorem because the
`etaleTopologyOver` abbreviation is what every statement downstream mentions. -/
theorem subcanonical_etaleTopologyOver (k : Type u) [Field k] :
    (etaleTopologyOver k).Subcanonical :=
  inferInstance

namespace PicScheme

/-! ## §2. The comparison is an isomorphism when the source is a sheaf -/

/-- **The section-free criterion for the sheafification comparison.**

`PicScheme.picEtComparison C` is by construction the sheafification unit
`PicSharp.toEtaleSheaf C` whiskered with the forgetful functor. A unit of the
sheafification adjunction is an isomorphism exactly when its source is already
a sheaf (`CategoryTheory.isIso_toSheafify`), so the étale sheaf property of
`PicSharp.relPresheaf C` suffices — and nothing about `C(k)` enters.

Contrast `picEtComparison_isIso_of_hasRationalPoint`
(`Picard/FGAPicRepresentability.lean`), which reaches the same conclusion from
Kleiman §2 Thm 2.5 via a section. The two routes are independent; this one is
the one available under the owner decision `I-0491`. -/
theorem isIso_picEtComparison_of_isSheaf {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (h : Presheaf.IsSheaf (etaleTopologyOver k) (PicSharp.relPresheaf C)) :
    IsIso (picEtComparison C) :=
  haveI : IsIso (PicSharp.toEtaleSheaf C) := isIso_toSheafify _ h
  Functor.isIso_whiskerRight _ _

/-- **Representability makes the relative Picard presheaf an étale sheaf.**

Two steps, both structural. A functor represented by a scheme is a sheaf for
the subcanonical étale topology
(`GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`, using
`subcanonical_etaleTopologyOver`); and the sheaf property of the
`AddCommGrpCat`-valued `relPresheaf C` is *equivalent* to that of its
underlying type-valued functor `picSharp C = relPresheaf C ⋙ forget _`, because
the forgetful functor of a concrete algebraic category preserves limits and
reflects isomorphisms (`Presheaf.isSheaf_iff_isSheaf_forget`).

The hypothesis is a `RepresentableBy` for an arbitrary `X`, not for
`PicScheme C`, so this does not silently consume the seam. -/
theorem relPresheaf_isSheaf_of_representableBy {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (picSharp C).RepresentableBy X) :
    Presheaf.IsSheaf (etaleTopologyOver k) (PicSharp.relPresheaf C) := by
  haveI : (picSharp C).IsRepresentable := ⟨X, ⟨rep⟩⟩
  have hsh : Presieve.IsSheaf (etaleTopologyOver k) (picSharp C) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat.{u+1}),
    CategoryTheory.isSheaf_iff_isSheaf_of_type]
  exact hsh

end PicScheme

/-! ## §3. The transport, with no rational point anywhere -/

/-- **The transport: a scheme representing `picSharp C` also represents
`picEt C`, with no hypothesis on `C(k)`.**

This is the statement the seam docstring and the board row `AJC.picrep.etale-rep`
declare impossible without a section. The proof composes §1 and §2: the
representing scheme makes `relPresheaf C` an étale sheaf
(`relPresheaf_isSheaf_of_representableBy`, i.e. subcanonicity), being a sheaf
makes the sheafification unit an isomorphism
(`isIso_picEtComparison_of_isSheaf`), and `Functor.RepresentableBy.ofIso`
carries the representation across it.

Note what is and is not proved. `X` is *given* here — the theorem consumes
`picSharp` representability rather than producing it, and that antecedent is
exactly the undischarged output of the Milne–Kollár campaign. What the theorem
establishes is that no *further* representability theorem is needed on top of
the campaign, contradicting the "eleventh item" pricing. -/
noncomputable def picSharp_representableBy_picEt_transport {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (PicScheme.picSharp C).RepresentableBy X) :
    (PicScheme.picEt C).RepresentableBy X :=
  rep.ofIso (@asIso _ _ _ _ (PicScheme.picEtComparison C)
    (PicScheme.isIso_picEtComparison_of_isSheaf C
      (PicScheme.relPresheaf_isSheaf_of_representableBy C rep)))

/-- **Clause (1) of the seam follows from its `picSharp` analogue.**

Same content as `picSharp_representableBy_picEt_transport`, packaged in the
seam's own existential shape so the comparison with
`Scheme.fgaPicardRepresentability` is direct: the local-finiteness and
separatedness conjuncts are carried across unchanged, because the transport
does not move the representing scheme — it is the *same* `X`.

The hypothesis is stated as the `picSharp`-shaped existential rather than as
`[HasPicScheme C]`, deliberately: `HasPicScheme` pins the witness to
`PicScheme C` and has no instance, so quantifying over it would make this
theorem consume an uninhabited class. Here the witness is universally
quantified and the statement is a genuine implication. -/
theorem hasPicSchemeEt_of_picSharp_representability {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (h : ∃ X : Over (Spec (CommRingCat.of k)),
        Nonempty ((PicScheme.picSharp C).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ IsSeparated X.hom) :
    ∃ X : Over (Spec (CommRingCat.of k)),
      Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
        LocallyOfFiniteType X.hom ∧ IsSeparated X.hom := by
  obtain ⟨X, ⟨rep⟩, hft, hsep⟩ := h
  exact ⟨X, ⟨picSharp_representableBy_picEt_transport C rep⟩, hft, hsep⟩

/-- **Clause (2) follows too, and unconditionally** — which is strictly stronger
than the seam's own second conjunct `HasRationalPoint C → IsIso …`.

Given representability of `picSharp C`, the comparison
`PicScheme.picEtComparison C` is an isomorphism outright, with no section. So
under the campaign's endpoint the rational-point hypothesis of Kleiman §2
Thm 2.5 becomes redundant *for this curve*: it was buying a sheaf property that
representability already supplies.

This is not a proof of Kleiman 2.5 — that theorem asserts the comparison is an
isomorphism from the section alone, with no representability input, and remains
unformalised. -/
theorem isIso_picEtComparison_of_picSharp_representability {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (PicScheme.picSharp C).RepresentableBy X) :
    IsIso (PicScheme.picEtComparison C) :=
  PicScheme.isIso_picEtComparison_of_isSheaf C
    (PicScheme.relPresheaf_isSheaf_of_representableBy C rep)

/-! ## §4. The limit on the antecedent: representable implies *Zariski* sheaf

The transport of §3 says the campaign needs no supplementary étale
representability theorem. This section says where the campaign may not put its
conclusion, and the two together are what actually price the board row.

Attribution: this direction was pointed out by `review-ajc` on the §1–§3
commit, as a corollary of `relPresheaf_isSheaf_of_representableBy`. -/

namespace PicScheme

/-- **A representable `picSharp` is a Zariski sheaf.**

Immediate from subcanonicity of the *Zariski* topology on `(Sch/k)`
(`Scheme.subcanonical_zariskiTopology` through
`GrothendieckTopology.subcanonical_over`) — the étale route of §1 is not even
needed, though `zariskiTopologyOver_le_etaleTopologyOver` (`Picard/PicEtSheaf.lean`)
would also transport it from there.

**What this rules out.** The seam docstring
(`Picard/FGAPicRepresentability.lean`, "Why sheafifying is what makes an
unconditional statement possible") argued *in prose* that an unconditional
`RepresentableBy` against `picSharp` is FALSE rather than unproved, because
some curve has a `picSharp` that is not a Zariski sheaf, while a representable
functor is a sheaf for any subcanonical topology. That seam docstring **no longer
says "FALSE"**: it now reads "unproved with a refutation route mapped out", so the
sentence being ruled out here is a historical one, retained because the *shape* of
the mistake is what this paragraph is about.

**That prose argument does not close, and this theorem is only its first half**
(`I-0970`). Its second half — a curve whose `picSharp` fails Zariski descent —
is not established by any source in the workspace: the seam's original citation
(§2 L1292–L1302) is about the *absolute* functor, its first replacement
(`ex:Pfs`) compares the two *sheafifications*, and `th:cmp` part 1 in fact gives
`picSharp ↪ Pic_{(X/S)zar}` on these binders. What IS established, and needs no
sheaf step, is Kleiman's own L5105–L5108: for the real conic `u²+v²+w²=0`
(smooth, proper, geometrically integral, no rational point) `Pic_{X/ℝ}` is not
representable while `Pic_{(X/ℝ)ét}` is. So the conclusion — over an arbitrary
field, no scheme represents `picSharp C` in general — stands on that quotation,
not on this theorem.

The campaign milestones G3 and G4 conclude exactly that (G3: `J_r := J'_r/Γ`
represents `picSharpDeg C r` over `k`; G4 assembles `picSharpDeg`), so as written
they target a statement that is unproved with a refutation route mapped out — and
they need restating against `picEt` either way, because a milestone whose
conclusion this project expects to be refutable is not one to spend rounds on. That
restatement is the content of the board row `AJC.picrep.etale-rep`, and it is
what makes the row a *route repair* rather than a missing theorem.

**The binder check, which the earlier text here left open, now closes**: the
witness is a smooth plane conic over `ℝ`, hence smooth, proper and
geometrically integral — this file's exact binders — and it has no `ℝ`-point,
which is what makes the two functors differ. So the refutation route is not
blocked on a binder mismatch, which is all the binder check can settle.

**It does NOT show the antecedent is uninhabitable.** An earlier revision of this
sentence said "genuinely uninhabitable in general, not merely unproved", and that
was the strongest and least supported of this file's four overclaims (`I-1354`):
whether `¬ IsIso (picEtComparison C)` holds *is* the unformalised residue, quoted
from Kleiman and not constructed in Lean. Worse, it is self-defeating — if the
antecedent were uninhabitable then
`not_representableBy_picSharp_of_not_isIso_picEtComparison` would be *vacuous*
rather than a refutation route, contradicting the value ascribed to it two
paragraphs above. A binder census answers "could this witness satisfy the
hypotheses"; it cannot answer "does the hypothesis hold".

What remains unformalised is the *counterexample itself* (that `Pic_{X/ℝ}` of
that conic is not representable); it is quoted from Kleiman rather than
constructed in Lean. `not_representableBy_picSharp_of_not_isIso_picEtComparison`
below isolates exactly what a Lean version of it would have to supply. -/
theorem picSharp_isSheaf_zariski_of_representableBy {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    {X : Over (Spec (CommRingCat.of k))}
    (rep : (picSharp C).RepresentableBy X) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of k)))
      (picSharp C) := by
  haveI : (picSharp C).IsRepresentable := ⟨X, ⟨rep⟩⟩
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- **Kleiman's non-representability argument, as a Lean theorem: if the
comparison is not an isomorphism then `picSharp` is not representable.**

This is the honest replacement for the Zariski-sheaf mechanism above, and it is
strictly better: it needs no sheaf step and no topology, only §3.

Kleiman's own reasoning at L5105–L5108 and L5126–L5129 is exactly this. For the
real conic he shows `Pic_{X/ℝ}` and `Pic_{(X/ℝ)ét}` *differ*, and concludes
"`Pic_{X/ℝ}` is not representable" — with `Pic_{(X/ℝ)ét}` representable by the
Main Theorem. The inference from "they differ" to "the unsheafified one is not
representable" is not stated as needing an argument in the source; here it is
one, and it is the contrapositive of
`isIso_picEtComparison_of_picSharp_representability`: representability of
`picSharp` forces the comparison to be an isomorphism, so the two functors
cannot differ.

**This is what converts the route claim from a quotation into a reduction.**
Combined with §3, the campaign's tail is constrained as follows: any proof that
some scheme represents `picSharp C` over a general field `k` would prove that
`picEtComparison C` is an isomorphism for every such `C` — including curves with
no `k`-point, where Kleiman exhibits it as non-surjective. So G3 and G4 cannot
be proved as written, and the repair is to descend `picEt`.

**The one thing still quoted rather than proved**: that the comparison genuinely
fails to be an isomorphism for that conic. Formalising it means producing a
class in `picEt C (Spec ℝ)` outside the image — Kleiman's `φ*O(1)`, whose
argument runs through `h⁰` on `ℙ¹_ℂ` and flat base change. That is a bounded,
well-specified piece of work, and this theorem is the interface it would plug
into. -/
theorem not_representableBy_picSharp_of_not_isIso_picEtComparison {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (hne : ¬ IsIso (picEtComparison C)) (X : Over (Spec (CommRingCat.of k))) :
    IsEmpty ((picSharp C).RepresentableBy X) :=
  ⟨fun rep => hne (Scheme.isIso_picEtComparison_of_picSharp_representability C rep)⟩

/-- The same statement in the shape the seam's clause (1) uses: if the
comparison fails to be an isomorphism, the `picSharp` analogue of clause (1) is
FALSE — no scheme at all represents `picSharp C`, with or without the
finiteness and separatedness conjuncts.

This is the precise sense in which the campaign's endpoint is not merely
unproved. Note the quantifier: `X` ranges over all `k`-schemes, so this refutes
the existential, not just the pinned witness `PicScheme C`. -/
theorem not_exists_representing_picSharp_of_not_isIso {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    (hne : ¬ IsIso (picEtComparison C)) :
    ¬ ∃ X : Over (Spec (CommRingCat.of k)),
        Nonempty ((picSharp C).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ IsSeparated X.hom := by
  rintro ⟨X, ⟨rep⟩, -, -⟩
  exact (not_representableBy_picSharp_of_not_isIso_picEtComparison C hne X).false rep

end PicScheme

end Scheme

end AlgebraicGeometry
