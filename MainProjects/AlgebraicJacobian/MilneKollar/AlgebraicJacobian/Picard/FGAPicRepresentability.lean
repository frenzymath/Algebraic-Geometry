/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RelPicFunctor
import AlgebraicJacobian.Picard.PicEtSheaf
import AlgebraicJacobian.Picard.DivFunctorDef
import AlgebraicJacobian.Picard.HasRationalPoint
import AlgebraicJacobian.Picard.CurveProjectivity

/-!
# FGA representability of the Picard scheme

This file states the FGA representability of the relative Picard functor of a
smooth proper geometrically integral curve `C/k`, following Kleiman, "The
Picard scheme", §2 and §4 (cf. FGA Explained Ch. 9; arXiv:math/0504020).

The relative Picard functor is

```
picSharp C := PicSharp.relPresheaf C ⋙ forget AddCommGrpCat
```

the set-valued shadow of the `H_T`-coset carrier
`T ↦ Pic(C ×_k T)/π_T^* Pic(T)` of `Picard/RelPicFunctor.lean` (Kleiman §2
Def. `df:Pfs`; blueprint `def:rel_pic_sharp`). A `RepresentableBy` witness
against it is a natural bijection
`(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)`, which is what the downstream
tangent-space computation (`AJC.pic0av`, `Pic0.tangentSpaceIso`) attaches to.

## The étale-sheafification route (owner decision of 2026-07-28)

Kleiman §4 represents the **étale-sheafified** functor `Pic_{(C/k)ét}`, and
that is what this file's obligation is stated against —
`fgaPicardRepresentability`, over an **arbitrary** base field, with **no
hypothesis on `C(k)`**. The functor is built and its sheaf property proved in
`Picard/PicEtSheaf.lean` (`PicScheme.picEt`, `picEt_isSheaf_forget`), by
sheafifying the relative Picard presheaf for Mathlib's big étale topology
localised at `Spec k`.

Why the sheafification is not optional. The plain relative functor
`picSharp C = T ↦ Pic(C ×_k T)/π_T^* Pic(T)` is not representable over a
general field, so an unconditional `RepresentableBy` against `picSharp` is a
**false** statement, not merely an unproved one.

**CITATION CORRECTED 2026-07-29 (`review-ajc`), by reading the source. The
conclusion above is right; the reason previously given for it was not.** This
paragraph used to say `picSharp` "is not even a Zariski sheaf (Kleiman §2
L1292–L1302)". Those lines
(`references/kleiman-picard-src/kleiman-picard.tex`, the full paper) say
something else: "The **absolute** Picard functor `Pic_X` is never a separated
presheaf in the Zariski topology", proved with the `ℙ¹_X`/`O(1)` argument. That
is about `Pic_X`, **not** about the relative `Pic_{X/S} = picSharp`, which is
*defined* by quotienting out `Pic(T)` precisely to defeat that argument. What
Kleiman actually asserts about the relative functor is weaker (L1330): "Since
`Pic_{X/S}` is not *a priori* a sheaf, it is remarkable that it is representable
so often in practice." Not-a-priori is not never — indeed L1600–L1605 proves
`Pic_{X/S} ≅ Pic_{(X/S)zar}` whenever `f` has a section.

**The witness, and it satisfies exactly this file's binders.** Kleiman
L5105–L5108 (repeated L5126–L5129): take `X : u² + v² + w² = 0` in `ℙ²_ℝ`, a
smooth plane conic — hence smooth, proper, and geometrically integral, since
`X_ℂ ≅ ℙ¹_ℂ` — over a field where it has **no** rational point. `Pic_{(X/ℝ)ét}`
is representable by §4 `th:main`, the two functors differ (Exercise `ex:Pfs`),
and Kleiman concludes `Pic_{X/ℝ}` is not representable.

**That last step is now a Lean theorem rather than a quotation**, which is the
right state for something this load-bearing:
`PicScheme.not_exists_representing_picSharp_of_not_isIso`
(`Picard/PicEtSubcanonical.lean`, `ajc-p1`) derives *from* `¬ IsIso
(picEtComparison C)` that **no** scheme represents `picSharp C` — the existential
of clause (1), not merely the pinned `PicScheme C`. No topology and no sheaf step
enter. So the falsity of the `picSharp` analogue of clause (1) is reduced to the
single residue that the comparison really does fail for that conic (via
`φ^* O(1)` and `h⁰` on `ℙ¹_ℂ`), which is where Kleiman's own argument lives and
is not yet formalised.

**Do not route this through a Zariski-sheaf claim** (corrected again the same
day, after `work-reviewer` refuted the first repair — see `I-0970`). It is
tempting to argue "representable ⟹ Zariski sheaf, and `picSharp` is not one";
the second half is *not* what the sources say. `ex:Pfs` compares
`Pic_{(X/ℝ)zar}` with `Pic_{(X/ℝ)ét}` — both already sheaves — so it witnesses
`zar ≠ ét`, not a failure of Zariski descent for the unsheafified functor. And
Kleiman `th:cmp` part 1 (L1391–L1393) proves `Pic_{X/S} ↪ Pic_{(X/S)zar}`
whenever `O_S ≅ f_* O_X` holds universally, which is automatic on these binders —
i.e. `picSharp` *is* Zariski-separated here, and any failure could only be
gluing. The non-representability above needs no sheaf step at all, so take it
directly. Kleiman §2 **Thm 2.5** repairs it only under a
**section**: given one (and `O_S = f_* O_X` universally, automatic for our
proper geometrically integral `C/k`), the comparisons

```
Pic_{X/S}(T) → Pic_{(X/S)ét}(T) → Pic_{(X/S)fppf}(T)
```

are bijective. That conditional route survives here as
`picEtComparison_isIso_of_hasRationalPoint` and `picSchemeOfHasRationalPoint`,
both clearly labelled as **strictly weaker than the challenge**. They are not
the headline and must not be reported as progress toward it. (Earlier revisions
of this file named a class `PicEtComparisonIso` in these four places; no such
declaration exists or ever landed — the comparison is supplied by the theorem
`picEtComparison_isIso_of_hasRationalPoint`, which is clause (2) of
`fgaPicardRepresentability` applied to the section. Corrected 2026-07-29.)

The two interfaces, and which one to build against:

* `HasPicSchemeEt` / `PicSchemeEt` / `representableEt` / `groupSchemeStructureEt`
  — **unconditional**, the étale formulation, the target. New work goes here.
* `HasPicScheme` / `PicScheme` / `representable` / `groupSchemeStructure` — the
  legacy `picSharp`-shaped interface, whose only producer is now the
  conditional `picSchemeOfHasRationalPoint`. Consumers quantifying over
  `[HasPicScheme C]` as a hypothesis remain valid and kernel-clean; they are
  simply conditional statements until restated against `picEt`.

## Main results

* `fgaPicardRepresentability` — **the project's central open obligation**:
  representability of `Pic_{(C/k)ét}` over an arbitrary field, no rational
  point. The file's only `sorry`.
* `HasPicSchemeEt`, `PicSchemeEt`, `representableEt`,
  `instPicSchemeEtLocallyOfFiniteType`, `instPicSchemeEtIsSeparated`,
  `groupSchemeStructureEt` — the unconditional étale interface derived from it.
* `picEtComparison_isIso_of_hasRationalPoint`, `picSchemeOfHasRationalPoint` —
  the **conditional** Kleiman §2 Thm 2.5 route, strictly weaker than the
  challenge, not the headline.
* `picSharp` — the relative Picard functor `Pic^♯_{C/k}`.
* `divFunctor` — the relative-divisor functor `Scheme.DivFunctor C.hom` of
  `Picard/DivFunctorDef.lean` (Kleiman §3 Def. `df:div`, invertible-kernel
  quotient encoding).
* `PicScheme`, `representable`, `instPicSharpRepresentable` — the representing
  scheme and the natural bijection
  `(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)` it induces.
* `instPicSchemeLocallyOfFiniteType`, `isSeparated` — `Pic_{C/k}` is locally
  of finite type and separated over `k` (Kleiman §4 Thm `th:main`(1)); over a
  field, Cor `cor:algsch` refines it to a disjoint union of open
  quasi-projective `k`-subschemes.
* `groupSchemeStructure` — `Pic_{C/k}` is a commutative `k`-group scheme, by
  Yoneda transport (`CommGrpObj.ofRepresentableBy`) of the abelian-group
  structure of `PicSharp.relPresheaf`.
* `abelMapWitness`, `abelMap`, `abelMap_app_mk` — the Abel map
  `Div_{C/k} ⟶ Pic^♯_{C/k}`, `[D] ↦ [O(D)] = -[ker q]` (Kleiman §3
  Def. `dfn:Abel`), assembled as `abelKernelNatTrans C ≫ picNeg C`.
* `smoothProperQuotient` — the Altman–Kleiman quotient lemma (Kleiman §4
  Lem. `lm:qt`), relative to the use-site hypothesis class
  `HasSmoothProperQuotient`.

## Remaining obligations

**Exactly one** statement in this file is `sorry`: `fgaPicardRepresentability`,
the existence of a scheme representing the étale-sheafified relative Picard
functor `Pic_{(C/k)ét}` and separated and locally of finite type over `k`, for
an arbitrary field `k` and **no** hypothesis on `C(k)`. Mathematically this is
Kleiman §4 Thm `th:main`(1) together with Cor `cor:algsch`. It is the project's
central open obligation and is **expected to stay open**. Its inputs are the
Milne–Kollár ones — `Div^d` through the Grassmannian and a finite Galois
quotient — *not* Quot and *not* `smoothProperQuotient`; see the "Which route
discharges it" paragraph on `fgaPicardRepresentability` below, which corrects an
earlier claim here that the inputs were blocked on Quot. Everything else here —
the representing scheme,
its representability, local finiteness, separatedness and group-scheme
structure, and the conditional `picSchemeOfHasRationalPoint` — is derived from
that one existence statement.

`smoothProperQuotient` is stated against an explicit hypothesis class rather
than proved outright, because the hypothesis list expressible here is weaker
than Kleiman §4 Lem. `lm:qt`: it omits quasi-projectivity of the representing
scheme `Y`, for which Mathlib has no vocabulary at the pinned revision.
Without that hypothesis the statement is false — a Hironaka-type free
`ℤ/2`-action on a smooth proper non-projective 3-fold gives a smooth proper
equivalence relation whose quotient étale sheaf is an algebraic space that is
not a scheme. The class must therefore be supplied at the use site, where
quasi-projectivity of the Abel-map slice is available.

## References

Blueprint: `blueprint/src/chapters/Picard_FGAPicRepresentability.tex`.
Kleiman, "The Picard scheme" (arXiv:math/0504020): §2 Thm 2.5
(`th:comp` comparison under a section), §3 Def `dfn:Abel` + Thm `th:repDiv`,
§4 Thm `th:main` + Cor `cor:algsch` + Lem `lm:qt`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace PicScheme

/-! ## §0. The relative Picard functor and the divisor functor

`picSharp` is the honest relative Picard functor of sibling
`Picard/RelPicFunctor.lean` (Kleiman §2 Def `df:Pfs`), with the group
structure forgotten (representability is a statement about the underlying
set-valued functor; the group structure is transported back onto the
representing scheme by `groupSchemeStructure` below).

`divFunctor` (the relative-effective-divisor functor `Div_{C/k}`, Kleiman §3
Def `df:div`) is the functor `Scheme.DivFunctor C.hom` of sibling
`Picard/DivFunctorDef.lean`. -/

/-- **The relative Picard functor** `Pic^♯_{C/k} : (Sch/k)^op ⥤ Type (u+1)`,
`T ↦ Pic(C ×_k T)/π_T^* Pic(T)` — the set-valued shadow of the group-valued
presheaf `PicSharp.relPresheaf` of `Picard/RelPicFunctor.lean` (the honest
`H_T`-coset carrier of Kleiman §2 Def `df:Pfs`).

Universe note: the values live in `Type (u+1)` because the line-bundle
carrier `LineBundle.OnProduct` is a quotient of (large) sheaves of modules.
`Functor.RepresentableBy` is universe-polymorphic, so representability by a
(`Type u`-homed) scheme remains a well-formed — and, under a rational point,
true — statement. -/
noncomputable def picSharp {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1) :=
  PicSharp.relPresheaf C ⋙ CategoryTheory.forget AddCommGrpCat.{u+1}

/-- Typeclass asserting existence of the relative-divisor functor `Div_{C/k}`.
The instance `instHasDivFunctor` below discharges it, with witness
`divFunctor C = DivFunctor C.hom`; the class survives as the blueprint-pinned
existence carrier (`def:has_div_functor`).

**Vacuity warning.** The field
`has_div_functor : Nonempty ((Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1))` does not
mention `C` at all: any functor (e.g. a constant functor) witnesses it, so
the class is vacuously true and carries no mathematical content. It must
never be cited as evidence that the relative-divisor functor of `C` exists —
use `Scheme.DivFunctor C.hom` (`Picard/DivFunctorDef.lean`) directly, as
`divFunctor` below does. -/
class HasDivFunctor {k : Type u} [Field k] (C : Over (Spec (.of k))) : Prop where
  has_div_functor : Nonempty ((Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1))

/-- **The relative-divisor functor** `Div_{C/k} : (Sch/k)^op ⥤ Type (u+1)`,
sending a `k`-scheme `T` to the set of relative effective Cartier divisors on
`C ×_k T` flat over `T` (Kleiman §3 Def. `df:div`).

It is defined as

```
divFunctor C := Scheme.DivFunctor C.hom
```

with `Scheme.DivFunctor` from sibling `Picard/DivFunctorDef.lean`: `T`-flat
invertible-kernel quotients of `O_{C ×_k T}` modulo `ker q = ker q'`, i.e.
Kleiman's set of relative effective divisors. The definition does not route
through the `HasDivFunctor` carrier class above. -/
noncomputable def divFunctor {k : Type u} [Field k]
    (C : Over (Spec (.of k))) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u+1) :=
  DivFunctor C.hom

/-- Existence instance for `HasDivFunctor`: the relative-divisor functor
`divFunctor C = Scheme.DivFunctor C.hom` witnesses the existential. -/
instance instHasDivFunctor {k : Type u} [Field k]
    (C : Over (Spec (.of k))) : HasDivFunctor C :=
  ⟨⟨divFunctor C⟩⟩

end PicScheme

/-! ## §1. The Picard scheme

The Picard scheme `Pic_{C/k}` of a smooth proper geometrically integral curve
`C/k` **with a `k`-rational point** is the `k`-scheme representing the
relative Picard functor `picSharp C` (which, under the rational point, agrees
with the étale-sheafified functor of Kleiman §4 Thm `th:main` by Kleiman §2
Thm 2.5). The scheme is separated, locally of finite type over `k`, and a
disjoint union of open quasi-projective `k`-subschemes; the
abelian-group-scheme structure is `groupSchemeStructure` below.

Blueprint reference: `def:pic_scheme` (Kleiman §4 Def. `df:Psch`). -/

/-- Typeclass asserting existence of a scheme over `Spec k` that represents
the **unsheafified** relative Picard functor `picSharp C` and is separated and
locally of finite type over `k`.

**This is the legacy, conditional interface, not the headline target.** Its only
producer is `picSchemeOfHasRationalPoint`, which needs `[HasRationalPoint C]`
(from which it derives the comparison via
`picEtComparison_isIso_of_hasRationalPoint`), and
there is deliberately **no instance**: without a section the plain relative
functor is not representable in general, so an unconditional instance would
assert a false statement. The unconditional étale target is `HasPicSchemeEt`.

Consumers that quantify over `[HasPicScheme C]` as a hypothesis remain
kernel-clean and valid; what they prove are conditional statements until
restated against `picEt`.

Representability, local finiteness and separatedness are bundled into a single
existential because Kleiman §4 Thm `th:main`(1) delivers them as one package:
`Pic_{C/k}` is a separated scheme locally of finite type over `k`. Over a
field, Kleiman Cor `cor:algsch` further writes it as a disjoint union of open
quasi-projective `k`-subschemes. Bundling therefore adds no strength beyond
representability, and lets the carriers
`PicScheme.instPicSchemeLocallyOfFiniteType` and `PicScheme.isSeparated` be
obtained by extraction. -/
class HasPicScheme {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : Prop where
  has_pic_scheme : ∃ (X : Over (Spec (.of k))),
    Nonempty ((PicScheme.picSharp C).RepresentableBy X) ∧
      LocallyOfFiniteType X.hom ∧ IsSeparated X.hom

/-- The **Picard scheme** `Pic_{C/k}` of a smooth proper geometrically
integral curve `C/k`, encoded as an object of `Over (Spec (.of k))`.

Extracted (`Classical.choose`) from the `HasPicScheme` existence field, so it
carries the identity "this scheme represents the relative Picard functor
`picSharp C`" through `representable` below — a natural bijection onto
`Pic(C ×_k T)/π_T^* Pic(T)`. -/
noncomputable def PicScheme {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    Over (Spec (.of k)) :=
  (HasPicScheme.has_pic_scheme (C := C)).choose

/-- The projectivity premise of Kleiman §4 `th:main`(1), discharged from the
curve hypotheses used by `fgaPicardRepresentability`.

This closes only the geometric premise of the published theorem.  Constructing
the representing Picard scheme remains the central open obligation below. -/
theorem isProjective_for_kleimanClauseOne {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : C.hom.IsProjective :=
  Adelic.isProjective_of_smoothProperGeometricallyIntegral C

/-- **THE PROJECT'S CENTRAL OPEN OBLIGATION — expected to stay open.**

Kleiman §4 Thm `th:main` + Cor `cor:algsch`: for a smooth proper geometrically
integral curve `C` over an *arbitrary* field `k`, the **étale-sheafified**
relative Picard functor `Pic_{(C/k)ét}` (`PicScheme.picEt`,
`Picard/PicEtSheaf.lean`) is representable by a `k`-scheme that is separated
and locally of finite type — a disjoint union of open quasi-projective
`k`-subschemes. All three conjuncts are parts of that one theorem, which is
why they are bundled.

**There is no hypothesis on `C(k)`, and that is the point.** This statement is
the one the challenge asks for: `AlgebraicJacobian/Challenge.lean` binds
`Jacobian C` for a curve with no rational point, so a representability input
carrying `[HasRationalPoint C]` answers a different question. The conditional
form survives beside this one as `picSchemeOfHasRationalPoint` below, clearly
labelled as strictly weaker.

**Why sheafifying is what makes an unconditional statement possible.** The
unsheafified functor `picSharp C = T ↦ Pic(C ×_k T)/π_T^* Pic(T)` is *not*
representable over a general field, so an unconditional `RepresentableBy`
against `picSharp` would be a FALSE statement, not merely an unproved one. The
witness is Kleiman L5105–L5108: the real conic `u²+v²+w²=0` in `ℙ²_ℝ`, smooth
proper geometrically integral with no rational point, for which he states
`Pic_{X/ℝ}` is not representable while `Pic_{(X/ℝ)ét}` is. (**Two citations have
been wrong in this slot** — "§2 L1292–L1302", which is about the *absolute*
functor, and then `ex:Pfs`, which compares the two *sheafifications*. Neither
shows `picSharp` failing Zariski descent, and `th:cmp` part 1 says it is in fact
Zariski-separated on these binders. Take the non-representability directly; see
the module docstring.) Against `picEt` it is Kleiman's own
theorem. `PicScheme.picEt_isSheaf_forget` records the sheaf property that makes
the difference, and it is proved rather than assumed.

**Expected to stay open, and that is the honest state rather than a defect.**
The project reaches this statement rather than proving it, and it is the single
named `sorry` that the whole Jacobian headline rests on. Do not replace it with
a weaker conditional statement to make a count go down.

**Which route THIS PROJECT takes — and the 2026-07-29 version of this paragraph
overstated, corrected 2026-07-30 (`review-ajc`, by reading Kleiman rather than
the board).** That version said the previous text "named the inputs of a route
this project does not take", listing `Div` representability (Kleiman §3 Thm
`th:repDiv`) and the Altman–Kleiman quotient lemma `smoothProperQuotient`, and
concluded the prescription was *simply wrong* because both belong to the
Grothendieck/Kleiman quotient route, `rejected` on the board
(`AJC.picrep.quot`, `AJC.picrep.serre`).

**Right about which route AJC CHOSE; wrong as a statement about what discharging
this `sorry` NEEDS.** Read from the source
(`references/kleiman-picard-src/kleiman-picard.tex`): `th:main` L2155–L2166 is
clause (1)'s **conclusion** verbatim — "Assume `f : X → S` is projective Zariski
locally over `S`, and is flat with integral geometric fibers. (1) Then
`Pic_{X/S}` exists, is separated and locally of finite type over `S`, and
represents `Pic_{(X/S)ét}`" — with no rational-point hypothesis. And Kleiman's
proof reduces (1) to (2) and then runs exactly the two named inputs: the Abel map
`Div_{X/S} → P` with `Div_{X/S}` an open subscheme of the **Hilbert** scheme by
`th:repDiv`, descended by `lm:qt`. So the original text was naming the inputs of
the published proof of this file's own conclusion.

**The projectivity gap identified by the fresh-context audit is now closed
(2026-07-30, `pic-b`).** `th:main`'s hypothesis is `f` **projective**
Zariski-locally and flat with integral geometric fibres. This file's binders are
`[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
[GeometricallyIntegral C.hom]` over a field. The rooted theorem
`Scheme.isProjective_for_kleimanClauseOne` proves exactly the previously missing
implication, by constructing a finite map to `ℙ¹`, embedding the two pulled-back
Laurent charts into relative projective space, and applying properness to the
resulting immersion. It adds no rational-point or projectivity hypothesis.
Thus projectivity is no longer an open antecedent in the comparison with
Kleiman's clause (1); the representability construction itself remains the
obligation described below.

Two things follow, and both matter for planning. `th:repDiv` is **Hilb, not
Quot** (its statement: "`Div_{X/S}` is representable by an open subscheme of the
Hilbert scheme `Hilb_{X/S}`"), so rejecting `AJC.picrep.quot` never rejected it.
And the campaign below is **one** route to clause (1); Kleiman's is a second,
whose `lm:qt` interface this project already pins as `smoothProperQuotient`
(§4 below — currently `P → P`, zero instances) while building its `Div` side
through the Grassmannian instead of Hilb. Nobody has priced Hilb-vs-Grassmannian,
because the board filed this docstring as stale rather than as an alternative.
That is a comparison worth making before more work commits to D′; it is *not* a
recommendation to switch, since Hilb's availability in Mathlib is unmeasured.
Full detail: `I-1360`.

The committed route is **Milne–Kollár** (`informal/pic-representability-campaign.md`,
alternative D3), and it needs neither of Kleiman's two:

* `Div^d` representability comes through the **Grassmannian**, not Quot:
  degree slices of `Scheme.DivFunctor` (`Picard/DivDegree.lean`, landed), an
  embedding into `Scheme.Grassmannian` of the section module, locally closed
  carving, and `Grassmannian.representable`
  (`Picard/GrassmannianRepresentability.lean`, proved) — campaign milestones
  D1′–D4′. D4′ also delivers the locally closed immersion into `Gr` that serves
  as the quasi-projectivity certificate.
* the quotient is the **finite Galois** quotient of a semilinear action whose
  finite orbits lie in affine opens — campaign G2, in
  `Picard/FiniteGaloisQuotient.lean` (`sorry`-free) with Speiser descent under
  `Picard/GaloisDescent/`. It is *not* `smoothProperQuotient`, which is false as
  stated in Lean (see the §4 note below) and must not be built against.
  **`sorry`-free is not gate-free here**: the affine case is proved
  (`isGaloisQuotientSpec`, `Picard/FiniteGaloisQuotientAffine.lean`) and the
  gluing substrate exists, but the general existence statement is still the
  instance-free class `AlgebraicJacobian.GaloisDescent.HasGaloisQuotient`
  (`FiniteGaloisQuotient.lean`, not imported here), whose
  only producer is a single-field non-vacuity witness
  (`Picard/GaloisQuotientNonVacuity.lean`). So G2 is *substantially* built, not
  discharged.

What remains is those campaign modules — uniform `H¹` vanishing (P5, the open
`AJC.rr.extuniform` leaf), the `picSharp` Zariski-sheaf/degree/separatedness
devices (B1, B4, B6), the `Div^d` chain (D2′–D4′), the Milne glue over a
separably closed field (J1–J5, which also needs a universe bridge since
`picSharp` is `Type (u+1)`-valued while Mathlib's 01JJ engine wants `Type u`),
Galois descent of `picSharp` points (G3), and the coproduct assembly (G4) —
**plus one further item that no campaign milestone covers**, recorded next.

**THE ELEVENTH ITEM — every campaign milestone targets `picSharp`, while clause
(1) above is about `picEt`. CORRECTED 2026-07-29 (`ajc-p1`): the gap is a route
repair, NOT a missing representability theorem.** The campaign
(`informal/pic-representability-campaign.md`) was written on 2026-07-09 for the
`picSharp`-shaped obligation, before the étale decision of 2026-07-28
(protection `I-0491`). Its J-cluster represents `picSharpDeg C' r`, G3 descends
`picSharp` points, and G4 assembles `picSharpDeg`; the word `picEt` does not
occur in any milestone body.

The previous text here concluded that the gap "cannot be closed by composing
with `picEtComparison`", because that comparison is an isomorphism only under a
section (Kleiman §2 Thm 2.5), and hence that representability of the sheafified
functor is a *genuine additional obligation*. **That inference was wrong**, and
it is a direction confusion. Kleiman 2.5 makes the comparison an isomorphism
from a section with no hypothesis on the presheaf; but the comparison is the
sheafification *unit*, and a unit is an isomorphism exactly when its source is
already a sheaf — and a representable functor is a sheaf for any subcanonical
topology. `Picard/PicEtSubcanonical.lean` proves this chain
(`subcanonical_etaleTopology`, absent from Mathlib `v4.31` for the étale
topology but free from `proetaleTopology`), and
`picSharp_representableBy_picEt_transport` transports a `picSharp`
representation to a `picEt` one with **no** rational-point hypothesis, the same
scheme serving both. So no supplementary étale-representability theorem is
needed.

**What the correction costs instead, and it is a sharper constraint.**
Representability of `picSharp` over an arbitrary field is **FALSE**, so **G3 and
G4 target a false statement as written**, not a hard one. The source says so
directly: Kleiman L5105–L5108 on the conic `u²+v²+w²=0` in `ℙ²_ℝ` — smooth,
proper, geometrically integral, no rational point — `Pic_{X/ℝ}` is not
representable while `Pic_{(X/ℝ)ét}` is.

**This does not go through the Zariski-sheaf theorem, and an earlier revision of
this paragraph wrongly said it did** (`I-0970`). The Lean statement
`PicScheme.picSharp_isSheaf_zariski_of_representableBy` is true and useful, but
its contrapositive needs "`picSharp` is not a Zariski sheaf", which no source
here establishes — `ex:Pfs` compares the two *sheafifications*, and `th:cmp`
part 1 shows `picSharp ↪ Pic_{(X/S)zar}` on these binders, so it is
Zariski-*separated*. The route that does work is
`not_exists_representing_picSharp_of_not_isIso` (see the sheafification paragraph
above): comparison-failure alone refutes representability, with no topology in
the argument. Everything through J5 runs over a separably closed
`k'` where a section is available and the obstruction absent; the break is the
descent step where the conclusion returns to `k`, and the repair is that the
object descended must be `picEt` (which has the sheaf property that carries
descent) rather than `picSharp`. Over `k'` the two agree. Restating G3/G4 that
way reaches clause (1) with no false intermediate.

Not formalised, and named as such: that Kleiman's non-sheaf curve satisfies this
file's binders (smooth, proper, geometrically integral) is quoted from the
reference rather than proved. Tracked as `AJC.picrep.etale-rep`; the board node
`AJC.picrep` carries the landed/absent split.

**How many inputs the repair has, and which are now in hand** — the count has
moved twice, so it is stated here as a history rather than as a fact.
"Descend `picEt` instead of `picSharp`" was priced at two inputs (2026-07-29
`ajc-p1`), then three (`review-ajc`, adding the cross-base identification), and
is now **four** (`review-ajc`, `I-1135`, adding the section over separably closed
fields that everything else silently assumes) — **plus a fifth entry added
2026-07-30 which is a subtraction, not an input**: all four price the
`RepresentableBy` field of clause (1), and the *other two fields of that same
clause* are free (item 5 below, `I-1286`).

**And a list of inputs is not a route — corrected 2026-07-30 (`ajc-p2`), because
for four rounds this paragraph was one.** Every entry below is an *antecedent*.
For four rounds there was **no declaration anywhere in this project stating the
theorem they are antecedents *of***, and an earlier revision of this paragraph —
written by the lane that added `Picard/PicEtDescentAssembly.lean` — claimed that
file supplied one. **It does not** (refuted by a fresh-context audit, `I-1312`,
reproduced and accepted by its author): none of that file's declarations takes a
`k'`-side representation and concludes over `k`. Its
`representableByRestrict_of_baseChange` concludes a `RepresentableBy` for a
`k'`-**object**, i.e. it restates the `k'`-side input in the right variables rather
than crossing the descent step.

**THAT GAP IS NOW CLOSED, 2026-07-30 (`pic-e`), and the sentence above is kept in
the past tense rather than deleted** because the census it rests on is still the
right way to check this: `Picard/PicEtDescentGoal.lean`'s
`PicScheme.representableBy_picEt_of_galoisQuotient` takes a representation of
`picEt (C_{k'})` over `k'` plus a Galois quotient of its canonical semilinear
action plus `hcov` plus a named `G1` predicate match (`IsInvariantMatch`), and
concludes `(picEt C).RepresentableBy Y` over `k`;
`seamClauseOne_of_isGaloisQuotient` is clause (1) in full through the free side
conjuncts. `sorry`-free and axiom-clean against this theorem as a `sorryAx`
control. **It closes nothing here**, and what changed is that the goal is now a
statement a lane can aim an input at, not that any input is in hand.

**AND ONE OF THE FOUR IS SINCE GONE — proved free, not supplied** (`pic-e`, same
day; this sentence replaces "all four of its inputs are explicit undischarged
hypotheses", which that commit falsified).
`PicScheme.isInvariantMatch_canonical` (`Picard/PicEtInvariantMatch.lean`) proves
the `G1` predicate match at the canonical action for every test, with **no**
hypothesis beyond the representation and the curve's own binders — no finiteness,
no separability, no `IsGalois`, no condition on `Gal(k'/k)`. It is free because the
canonical action's `γ`-component *is* `twistMor γ`, which is defined by
transporting the functor action along `rep`, so equivariance and invariance are two
readings of one equation and naturality converts between them. So the route from a
`k'`-side representation to clause (1) field 1 carries **two** named antecedents:
the Galois quotient at a glued non-affine `X'`, and `hcov`. Consumers should call
`seamClauseOne_of_isGaloisQuotient_noMatch`. **Still nothing here is discharged**:
the `k'`-side representation is the campaign's undischarged output, and clause (1)
field 1 is witnessed for no curve.

**ONE CORRECTION TO THE COUNT, AND IT IS SMALLER THAN THIS PARAGRAPH FIRST SAID**
(`pic-e`, 2026-07-30, `Picard/PicEtDescentNecessity.lean`; the first revision of this
box claimed a *third* antecedent "was never one", and that claim is **withdrawn** —
`I-1591`, reproduced by its author). The genuine point is only that the paragraph above
counts the *named* inputs and `seamClauseOne_of_isGaloisQuotient_noMatch` also takes
`hlft : LocallyOfFiniteType Y.hom`, so a consumer supplies four things, not two.

`hlft` can be *restated* at the `k'` side — but that is a **relocation, not a
subtraction**, and the reason is structural: `IsGaloisQuotient`'s first field is an
isomorphism `Y_{k'} ≅ X'`, so any property transported along it goes both ways, and the
four-input form is recoverable from the relocated one in three lines. Do not budget
`hlft` as free. The transferable rule: when a hypothesis swap runs through a structure
that already contains an iso between the two objects, prove the converse before
publishing a reduction.

What *is* clean: the Galois binders a first draft of that lemma carried are deletable —
neither `SemilinearGalAction` nor `IsGaloisQuotient` binds `[IsGalois]` or
`[FiniteDimensional]`, checked at the `variable` line, so the word "Galois" in both
names is about the intended application and not about a hypothesis.

**AND `rep` IS NECESSARY, WHICH CHANGES WHAT ITS "0 PRODUCERS" MEANS.**
`PicScheme.representableBy_picEt_baseChangeField_of_representableBy` derives a
`k'`-side representation *from* clause (1) field 1 over `k` — the base change of the
representing scheme, for an **arbitrary** field extension, and hence
(`representableBy_picEt_separableClosure_of_representableBy`) at `k^s`, where campaign
cluster `J` lives. So this route is not one sufficient strategy that a cheaper `k`-side
argument might bypass: every solution of clause (1) field 1 contains a solution of
`rep`. The step is generic — an arbitrary adjunction, no scheme, no field, no curve
(`CategoryTheory.Functor.representableByCompLeftAdjoint`) — plus `picEt_crossBaseIso`;
do not budget a descent argument for it.

**It does NOT say the campaign's endpoint is a consequence of the seam, and the first
revision of this box did say that** (withdrawn, `I-1592`). What follows at `k^s` is
representability of `picEt (C_{k^s})`. Cluster `J`'s stated target is
`picSharpDeg C' r`, a graded `picSharp` which **has no carrier in this project** —
`#check picSharpDeg` returns `unknownIdentifier` — which is the same fact the
"eleventh item" paragraph above records from the other side. Identifying the two over
`k^s` routes through this theorem's own second conjunct, so it is not available as an
argument.

**What that does NOT license, since it is the natural over-reading.** It discharges
nothing: its hypothesis is this very `sorry`. And it is **not** a converse of the
descent theorem: `hq` at the action these theorems consume
(`semilinearGalActionOfRepresentableBy C rep`) is untouched by it, including a per-γ
equality no lemma in the tree closes. So "the inputs are equivalent to the conclusion"
is false. (`isGaloisQuotient_pullbackAction_of_uniqueDescent` was first published here
as the measurement establishing that; it is stated at the *pullback* action instead, not
interchangeable with the consumed one — `I-1590`, withdrawn as the guardrail while
remaining true of what it does state.)

**Every name in the two paragraphs above lives DOWNSTREAM of this file** — in
`Picard/PicEtDescentNecessity.lean`, which imports the seam through
`Picard/PicEtInvariantMatch.lean`. So a bare `#check` for any of them *here* fails with
`unknownIdentifier` (verified, not assumed), and that failure is import direction, not
absence. Same trap the `HasGaloisQuotient`/`HasStableAffineCover` note in item 3 below
records; import the module before probing.

Two measurements from building it that a consumer needs.
`quotientHomEquiv_uniform`'s `Nonempty` cannot carry the naturality
square a `RepresentableBy` needs, so clause 3 had to be re-derived with its
forward map pinned to a named morphism. And there is an asymmetry in what
`Classical.choice` is spent on: the `RepresentableBy` form needs it, while
clause (1), being an existential, eliminates the quotient's `∃` into a `Prop` and
needs none — which is why `seamClauseOne_of_isGaloisQuotient` is a `theorem` and
not a `noncomputable def`. (An earlier revision of this paragraph gave a *stronger*
reason — that the `Prop`-valued `IsGaloisQuotient` "cannot be destructured" into the
`Type`-valued conclusion, so the `Nonempty` form was forced. That was withdrawn at
`PicEtDescentGoal.lean` §6 the day it was written: `Exists.choose` elaborates
directly, only the `obtain` *tactic* cannot, and the same paragraph was already
invoking choice. The asymmetry is what survived.) The conclusion shape
`Nonempty ((PicScheme.picEt C).RepresentableBy X)` occurred at exactly three sites
— the `HasPicSchemeEt` class field and the seam `sorry` below, plus
`hasPicSchemeEt_of_picSharp_representability` — and all three are **same-field**,
none taking a representation over a larger field and concluding over `k`
(measured by `ajc-p2`, re-measured independently by `review-ajc`, `I-1256`). With
the goal unwritten, an input nobody held would not have shown up as missing.

What *is* settled, and it is a pricing fact rather than a step: do **not** budget
effectivity of `picEt`-**classes** along the field-extension cover. Both halves are
free from sheafification — `Picard/EtaleFieldCover.lean` already says so in prose at
its own §4 (`:289`, `:294`: "unique amalgamation", "every covering sieve, `⊤`
included, free from sheafification"), and `PicEtDescentAssembly.lean`'s
`existsUnique_amalgamation_picEt_fieldCover` is that lemma `rfl`-equal, proposition
and term (`I-1312`). Its `picEt_injective_restrict_baseTest` is the
sieve-to-single-morphism reduction; that step is unavoidable, but it is **not
geometric** — the same statement closes in an arbitrary category with pullbacks,
with every geometric hypothesis deleted (`I-1312`, `I-1316`). So what remains is the
**scheme-level** quotient (`G2`, item 3), the covering statement `hcov`, and
`k'`-side representability itself. `I-1280` states the pricing consequence and
`I-1312` corrects that item's overclaims.

**This sentence used to begin with the invariance step** — "producing a compatible
family from a Galois-invariant `k'`-class (`G1`, where the group action enters)" —
and that item is **gone as of 2026-07-30** (`pic-e`): the predicate match `G1` owed
is free at the canonical action (`PicScheme.isInvariantMatch_canonical`,
`Picard/PicEtInvariantMatch.lean`), for an arbitrary extension, so the group action
does not enter as an obligation here at all. The clause is removed rather than
struck because it was a list of what remains, and it no longer does.

**AND THE SENTENCE THREE PARAGRAPHS UP IS NOW STALE TOO, in the same cheap
direction** (`pic-e`, 2026-07-31). It says what remains is "the **scheme-level**
quotient (`G2`, item 3), the covering statement `hcov`, and `k'`-side
representability itself". Of those three, `hcov` is **closed**
(`coverSelfSection_generate_mem_etaleTopology`, `pic-f`), and the scheme-level
quotient is discharged from the orbit hypothesis alone — see the withdrawal in
item 3 below. So at the spelling
`PicScheme.seamClauseOne_of_hasGaloisQuotient_lftFree`
(`Picard/PicEtGaloisQuotient.lean`) the descent step's remaining *instance* binder
is **one**: `OrbitsInAffineOpen`. The list is left standing rather than rewritten
because each entry is corrected at its own item; what a costing should read
instead is the reduction below.

**THE WHOLE OF THIS SEAM NOW HAS A NAMED SUFFICIENT CONDITION, and it is the
classical pointed theorem** (`pic-e`, 2026-07-31,
`Picard/PicEtPointedReduction.lean`, 11 declarations, `sorry`-free, all
axiom-clean against this theorem as a control).
`fgaPicardRepresentability_of_pointedPicSharpRep` derives **both** conjuncts
below, verbatim, over an **arbitrary** `k`, from `Scheme.PointedPicSharpRep`:
`picSharp`-representability for curves that *have* a rational point, uniform in
the base field, plus `FiniteInAffine` of the representing scheme. So the
arbitrary-field difficulty that `I-0491` deliberately put on this statement — the
thing that makes it harder than FGA/Kleiman as classically proved — is
**discharged**, and a lane proving that antecedent closes this `sorry` by `exact`.
The rational point is *produced*, not assumed
(`exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral` is
unconditional at these very binders), so nothing here carries `[HasRationalPoint C]`
and `I-0491` is respected. Price against the weaker
`seamClauseOne_of_hasGoodGaloisLevel`: it needs **one** finite Galois level, has no
rational point in its statement, and does not bind `[GeometricallyIntegral]`.
**Two cautions from that file, both measured there**: `PointedPicSharpRep` is
derivable *from this very `sorry`* up to `FiniteInAffine`, so axiom-check any
claimed proof rather than trusting a green build; and no curve is exhibited
satisfying `FiniteInAffine` at its Picard scheme.

Present state of the four:

1. **the descent test — LANDED.** `Picard/EtaleFieldCover.lean` proves
   `Spec k' ⟶ Spec k` is an étale cover for `k'/k` finite separable and that
   `picEt` satisfies the sheaf axiom at that cover.
2. **the cross-base identification — CLOSED** (`Picard/PicEtCrossBase.lean`,
   `PicScheme.picEt_crossBaseIso`, `sorry`-free and axiom-clean). Without it the
   scheme `J5` produces over `k'` would represent `picEt` *of the curve over `k`,
   restricted to `k'`-tests* rather than `picEt` of the base-changed curve, and
   there would be no functor for the descent datum to be a datum *for* — a
   mismatch no green build would reveal. **Note the hypotheses it does NOT
   carry**: earlier revisions of this paragraph, and the board row, both stated
   the obligation for `k'/k` *finite separable*; the theorem needs neither
   hypothesis and holds for an arbitrary field extension, because the argument is
   about pullback projections rather than about étale covers. Finite-separability
   is item 1's constraint and was double-counted here. Do not budget a
   separability argument for a cross-base step.
3. **the Galois action and quotient — G1/G2, substantially built; the gate now
   bites only off the affine locus.** Updated 2026-07-30 (`ajc-p1`): the class
   `AlgebraicJacobian.GaloisDescent.HasGaloisQuotient` is **no longer
   instance-free**. `hasGaloisQuotient_of_isAffine`
   (`Picard/GaloisQuotientAffineGeneral.lean`, global `instance`, `sorry`-free and
   axiom-clean against a control that still reports `sorryAx` on this very
   theorem) discharges it for **every** semilinear action on an affine total
   space — not just for the affine *model* `specSemilinearGalAction`, which is
   what `isGaloisQuotient_spec` had covered. The step was
   `isGaloisQuotient_congr`, transport of `IsGaloisQuotient` along an equivariant
   isomorphism over `Spec L`, applied to `X.isoSpec`; it subsumes the former
   single-object witness `hasGaloisQuotient_specF4` by `inferInstance`.
   **THE PARAGRAPH THAT STOOD HERE IS WITHDRAWN — IT WAS FALSE, AND FALSE IN THE
   EXPENSIVE DIRECTION** (`pic-e`, 2026-07-31, measured with controls both ways;
   reproduced from a fresh-context audit before editing). It said: "the campaign
   consumer `J'_r` is a *glued* scheme, hence non-affine, and `inferInstance` for
   the gate at an abstract action carrying the orbit hypothesis but not affineness
   **fails** (measured, control both ways). So the remaining `G2(c)` work is
   exactly the `Scheme.GlueData` assembly of the per-chart quotients."
   `inferInstance` **SUCCEEDS** at exactly that shape — an abstract `ρ` with
   `[FiniteDimensional K L] [IsGalois K L] [ρ.OrbitsInAffineOpen]` and no
   affineness — and fails only without the orbit binder. The producer is
   `hasGaloisQuotient_of_orbitsInAffineOpen`
   (`Picard/GaloisDescent/GaloisQuotientOverlap.lean`), a **global** instance
   built from `isGaloisQuotient_glued`, i.e. the `Scheme.GlueData` assembly that
   this paragraph called the remaining work **is already done**. Both stale
   sentences told a lane to budget work that exists, which is worse than an
   optimistic error because nobody re-tests a prohibition.
   **What survives**: the gate's price is the *orbit* hypothesis, and that is a
   real one — `[ρ.OrbitsInAffineOpen]` at the Picard scheme is unproved here, and
   it is where quasi-projectivity and the Hironaka trap actually enter.
   `Picard/PicEtPointedReduction.lean` carries it as the scheme-level
   `FiniteInAffine` (`orbitsInAffineOpen_of_finiteInAffine`) and shows it is
   neither free nor vacuous. So still do not read "the gate has an instance" as
   "input 3 is closed" — but the reason is the orbit hypothesis, not gluing.
   `AlgebraicJacobian.GaloisDescent.HasStableAffineCover` is **not** a second
   gate, but the reason stated here until now was false (`review-ajc`,
   2026-07-29 → corrected 2026-07-30 with controls both ways). It said the cover
   class "has had a global instance since G2(a) landed"; that instance,
   `hasStableAffineCover_of_orbitsInAffineOpen`, requires
   `[ρ.OrbitsInAffineOpen]`, and `inferInstance` for `HasStableAffineCover` at an
   **abstract** semilinear action carrying only `[FiniteDimensional K L]`
   `[IsGalois K L]` **fails** with `synthInstanceFailed` (control: with the orbit
   hypothesis in scope it succeeds). What is true is that the orbit hypothesis is
   free *at the action this route uses*: `instOrbitsInAffineOpen_pullback`
   discharges it for `pullbackSemilinearGalAction` over an arbitrary
   `Spec K`-scheme, so the cover class synthesises there outright — while
   `HasGaloisQuotient` at that same action does **not** (both measured in one
   probe). That separation is what makes G2 one gate rather than two, and it is a
   sharper statement than the absolute it replaces. **Both names are fully
   qualified on purpose**: they live in `Picard/FiniteGaloisQuotient.lean`, which
   this file does *not* import, so a bare `#check HasGaloisQuotient` here fails
   and would read as absence. That is the recorded "cited names need `#check`,
   not `grep`" trap; import that module before probing either class.
4. **a section over separably closed `k'` — LANDED 2026-07-30, this item is
   CLOSED.** (Read item 5 below first if you are pricing the descent: the
   four-input list prices clause (1)'s *first* field only.) This entry read "NO
   PRODUCER IN THIS PROJECT" and that is no longer
   the state: `Curve/SeparablyClosedRationalPoint.lean`
   (`hasRationalPoint_of_isSepClosed`, `sorry`-free, axiom-clean) is exactly the
   producer it said was absent. What survives, and is the reason the descent step
   is still open here, is narrower and was found on that closed item: campaign G1
   consumes the section at a **finite** Galois level, where `IsSepClosed` is
   false, so the `k^s` producer does not reach the step that needs it. That
   residue is a filtered-colimit-of-schemes argument tracked as
   `AJC.picrep.sepclosed-finite`. The old absolute is kept visible here because
   the `[IsAlgClosed]` half of it is still true and still the trap: `k^s`, never
   `k̄`, and `hasRationalPoint_baseChangeField` only *propagates* a section that
   `I-0491` forbids the headline to carry.
   This one is upstream of the other three.
5. **THE TWO SIDE CONJUNCTS OF CLAUSE (1) ARE FREE, AND BOTH ARE NOW
   DISCHARGED IN-TREE** — found 2026-07-30 (`review-ajc`, `I-1286`) because items
   1–4 above priced the *first* field of clause (1); landed the same day
   (`ajc-p1`, `Picard/PicEtSeparated.lean`, roadmap
   `AJC.picrep.etale-rep.separated`). Clause (1) is a three-field existential, and
   no roadmap row under `AJC.picrep.etale-rep` mentions either side conjunct.
   **The stronger claim first published here — that they were "never mentioned"
   anywhere — is FALSE and is withdrawn** (`review-ajc`, corrected by a
   fresh-context audit): they were priced a day earlier, as *free by transport
   from the `picSharp` endpoint*, on the board row `AJC.picrep` ("SAME scheme, so
   `LocallyOfFiniteType` and `IsSeparated` ride along unchanged") and in
   `Picard/PicEtSubcanonical.lean`, in the docstring of
   `hasPicSchemeEt_of_picSharp_representability` ("the local-finiteness and
   separatedness conjuncts are carried across unchanged, because the transport
   does not move the representing scheme"). What is genuinely new here is a
   *different* route — free from a bare `picEt` representation, with no `picSharp`
   detour — and the descent-unavailability fact below. That distinction is
   load-bearing: on the **field-descent** route this board actually holds, the
   transport argument is not available, so there the two conjuncts really were
   live and unpriced. So **clause (1) is now a two-field obligation**, and a
   lane closing the descent step should target
   `seamClauseOne_of_representableBy_locallyOfFiniteType`. Measured, `lake env
   lean` EXIT=0, axiom-clean against a control that fires `sorryAx` here:
   * `LocallyOfFiniteType` **descends** across the cover. At `k'/k` with
     `[Module.Finite k k']` `[Algebra.IsSeparable k k']`,
     `Spec.map (algebraMap k k')` is `Surjective`, `Flat` and `QuasiCompact` all
     by `inferInstance`, and Mathlib's
     `DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
     (`Morphisms/LocalFlatDescent.lean`) then closes it via
     `of_pullback_fst_of_descendsAlong`.
   * `IsSeparated` **cannot** descend with Mathlib `v4.31` — and does not need
     to. There is no `DescendsAlong @IsSeparated` instance, and the diagonal
     route through `IsSeparated.isSeparated_eq_diagonal_isClosedImmersion` fails
     too, because `DescendsAlong @IsClosedImmersion` is *also* absent
     (`IsClosedImmersion` is not a `HasRingHomProperty`, so
     `HasRingHomProperty.descendsAlong_flat` does not apply).
     **So do not budget a separatedness-descent argument: the lemma it would cite
     does not exist.** (A previous revision of this sentence added "Mathlib has
     exactly five such scheme instances", listing the five in
     `Morphisms/LocalFlatDescent.lean`. **That count was FALSE and is withdrawn**
     — `review-ajc`, corrected by a fresh-context audit, `I-1315`.
     `Morphisms/FlatDescent.lean` registers six more, all of which synthesise on
     probe: `Surjective`, `UniversallyClosed`, `UniversallyOpen`,
     `UniversallyInjective`, `isomorphisms Scheme`, `IsOpenImmersion` — eleven,
     not five. It was one file's count published as Mathlib's, three lines below
     this file's own method note warning about exactly that. The absence of the
     two properties above is unaffected: it was measured by failed synthesis, not
     inferred from any list. Do not quote a total here; grep
     `DescendsAlong` and count.) Separatedness instead comes from the *group structure of
     the represented object*: `picEt` is `CommGrpCat`-valued (`picEtCommGrp`), so
     ANY scheme representing it is a group object over `Spec k` by Yoneda
     transport (`CommGrpObj.ofRepresentableBy _ (picEtCommGrp C)
     (rep.ofIso (picEtCommGrpForgetIso C))`), and a group scheme over a field is
     separated. From a bare `(PicScheme.picEt C).RepresentableBy X` this is a
     theorem — it does not even use `[GeometricallyIntegral C.hom]`.
   **BOTH ARE NOW LANDED, 2026-07-30 (`ajc-p1`), in
   `Picard/PicEtSeparated.lean`** — so this item is no longer a costing, and the
   sentence that stood here ("the one brick is a **port** … none of those three
   names exists in this project") is false at HEAD and replaced. Mathlib still
   does not have "group scheme over a field is separated" (re-measured both ways
   in one probe: `IsClosedImmersion η[G].left` synthesises for `[GrpObj G]` over
   `Spec K` while `IsSeparated G.hom` does **not**), and the argument is
   transcribed from `Algebraic-Jacobian-Challenge-Rebuild`'s
   `AbelianVariety/GroupSeparated.lean`; all three names now exist here.
   * field 3: `isSeparated_of_representableBy_picEt` — `IsSeparated X.hom` from a
     bare `(PicScheme.picEt C).RepresentableBy X`, arbitrary field, and
     `seamClauseOne_of_representableBy_locallyOfFiniteType` restates clause (1) as
     the **two-field** obligation. Aim a descent step at *that*.
   * field 2: `locallyOfFiniteType_of_baseChange` — the descent above, carried
     out, so the contrast is compiler-checked rather than asserted. **The two side
     conjuncts are free for opposite reasons**, which is the part a costing gets
     wrong: one is a descent argument and the other is free precisely because
     descent is unavailable for it. Field 2 descends at an **arbitrary** field
     extension: its theorem formerly carried `[Algebra.IsSeparable k k']` and
     `[Module.Finite k k']` and consumed neither, and both are now deleted
     (`I-1356`). Finite separability is **input 1's** price —
     `picEt_ext_of_pullback_agrees` genuinely needs it — so this is the *same*
     double-count the input-2 note below corrects, and it was live in two files.
   Both `sorry`-free and axiom-clean against this theorem as a control; gate-free
   (no `HasPicSchemeEt` binder on any of them, checked by full signature per
   `I-1292`, not by header). Non-vacuity measured: dropping `rep` leaves
   `IsSeparated X.hom` for an arbitrary `X` and `infer_instance` **fails**.
   **This is not a discount on the seam**: `k'`-side representability is still
   the campaign's undischarged output, and field 1 is witnessed for no curve. It
   removes two obligations nobody had counted, and forecloses one dead end.

Method note for whoever re-checks any absence claim in this area: a bare
`horizon search picEt` returns ten hits, **all from the sibling project**, because
the result set is capped — reading that as absence in AJC would be a false
negative. Query a specific name (`picEtComparison`) or scan declaration headers
in-tree. Two earlier revisions of this paragraph offered lists called "the
complete list" and **both were wrong** (`I-1075`, and a fresh-context audit that
found six omissions); neither error touched the conclusion, which is why a token
scan rather than a census is what such a claim should rest on.

Item 2 was **not** portable from the sibling project, which was the trap, and the
outcome recorded it: `AJCR` proves a cross-base comparison as a `MulEquiv`
(`picEtCrossBaseEquiv`, `Picard/PicEtCrossBase.lean:316`, 468 lines), but its
`picEt` is a hand-built affine-opens limit of plus-classes (`PicEt.lean:105`)
while this file's is a categorical sheafification (`PicEtSheaf.lean:238`) —
different objects, no `lake` edge. Most of that length is a section-ring scalar
tower which a *sheafification*-based `picEt` does not need, because for it the
whole sheafification layer collapses to one Mathlib lemma
(`Functor.pushforwardContinuousSheafificationCompatibility`, applicable because
restriction along `Over.map` is continuous for the two localised étale topologies
by pure synthesis). Reading the sibling as a design lead rather than transcribing
it was the cheaper move.

This is the **sole** `sorry` of the seam: everything else below — the
representing scheme `PicSchemeEt`, its representability, local finiteness,
separatedness and group-scheme structure, the comparison theorem
`picEtComparison_isIso_of_hasRationalPoint` and the conditional
`picSchemeOfHasRationalPoint` — is derived from it.

**Why the second conjunct is bundled here rather than given its own `sorry`.**
Clause (1) is Kleiman §4; clause (2) is Kleiman §2 Thm 2.5 (`th:comp`): given a
section, the comparison `picSharp C → Pic_{(C/k)ét}` is an isomorphism. Both are
theorems of the same paper and neither is formalised. They are stated as one
named obligation on purpose: the `picSharp`-shaped consumer interface
(`HasPicScheme`, and through it the tangent-space chain and the `k̄` Albanese
witness) needs clause (2) to exist at all, and splitting it out would report the
Jacobian headline as resting on *six* open obligations where the mathematics has
five. The bundling adds no strength — clause (2) is conditional on a section, so
it says nothing about a pointless curve — and it keeps the frontier count honest
in both directions. `scripts/axiom-frontier.lean` measures the result rather
than asserting it.

**"Adds no strength" is now MEASURED, and the measurement is sharper than the
claim** (`review-ajc`, 2026-07-30; `lake env lean` EXIT=0 in a scratch file,
since deleted). Both conjuncts of this theorem follow, *together*, from the
single hypothesis

  `∃ X, Nonempty ((PicScheme.picSharp C).RepresentableBy X) ∧`
  `      LocallyOfFiniteType X.hom ∧ IsSeparated X.hom`

— i.e. from the `picSharp`-shaped endpoint that the Milne–Kollár campaign's ten
modules are built to produce, with **nothing left over**. Clause (1) is
`hasPicSchemeEt_of_picSharp_representability` and clause (2) is
`isIso_picEtComparison_of_picSharp_representability` (both
`Picard/PicEtSubcanonical.lean`), the second discarding the section it is handed.
Axiom-clean `[propext, Classical.choice, Quot.sound]`. The two halves existed
separately; what had not been measured is that their conjunction is exactly this
statement, so no reader had to take "adds no strength" on trust.

**The control here has a trap in it, and the trap is worth more than the
result.** The obvious control — "does the conclusion close *without* the campaign
hypothesis?" — **succeeds**, so read naively it says the reduction is empty.
`exact?` closes clause (1) hypothesis-free via
`HasPicSchemeEt.has_pic_scheme_et`, and clause (2) via
`picEtComparison_isIso_of_hasRationalPoint`. Both are legitimate terms; both
route through `instHasPicSchemeEt`, which *is* a projection of the `sorry` below.
Measured: the hypothesis-free version reports
`[propext, sorryAx, Classical.choice, Quot.sound]` while the version above
reports no `sorryAx`. So on this seam **provability is not a discriminating
control and the axiom list is** — because an unconditional gate instance makes
every statement in its domain provable. Anyone probing a reduction anywhere near
`HasPicSchemeEt` should compare axiom lists, not success and failure.

**What this does NOT mean, since it is the natural misreading.** It does not
bring the seam closer. The hypothesis is the campaign's *undischarged output*,
and over an arbitrary `k` there is a refutation waiting for it —
`PicScheme.not_exists_representing_picSharp_of_not_isIso`
(`Picard/PicEtSubcanonical.lean`) turns any failure of
`IsIso (picEtComparison C)` into a refutation of the existential, and Kleiman's
pointless real conic is where that failure is expected.

**Stated precisely, because the first version of this paragraph overstated it**
(`review-ajc`, corrected within the same session): that refutation is
*conditional* on `¬ IsIso (picEtComparison C)`, which is **quoted from Kleiman,
not proved in this project** — `PicEtSubcanonical.lean` says so itself, and
formalising it means exhibiting `φ*O(1)` in `picEt C (Spec ℝ)` outside the image
via `h⁰` on `ℙ¹_ℂ`. So the honest word for the campaign's `picSharp` endpoint
over arbitrary `k` is **unproved with a refutation route mapped out**, not
"FALSE" — the reduction above is a theorem, its trigger is not. Writing "FALSE"
here would be the same error the board row was corrected for in the opposite
direction.

Either way the consequence for planning is unchanged: whatever the campaign
delivers must be delivered over a field where `picSharp` is representable (a
separably closed one, or under a section), and the descent to `k` must carry
`picEt` points — and if it does deliver that, this bundled statement is fully
discharged, with clause (2) costing zero extra work. -/
theorem fgaPicardRepresentability {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    (∃ (X : Over (Spec (.of k))),
        Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
          LocallyOfFiniteType X.hom ∧ IsSeparated X.hom)
      ∧ (HasRationalPoint C → IsIso (PicScheme.picEtComparison C)) :=
  sorry

/-- **The étale representability gate**, as a `Prop`-class so that consumers can
quantify over it as a hypothesis.

Unlike the legacy `HasPicScheme`, this class carries **no** hypothesis on
`C(k)`: its unique producer `instHasPicSchemeEt` is unconditional. It is the
carrier of the project's central open obligation.

**It is not a gate, and quantifying over it does not keep a consumer
kernel-clean** — the previous sentence here promised that and it is
undeliverable (`review-ajc`, 2026-07-29). Because `instHasPicSchemeEt` is
unconditional, instance search discharges this class for every object in its own
domain, so a consumer that binds it is `sorryAx`-reachable the moment it is
applied; there is no `C` in the domain for which the binder is a real
restriction. Contrast `HasPicScheme`, which has no instance at all and for which
the binder genuinely is a hypothesis. What this class does buy is the shape:
statements quantified over it read as implications and are stated for an
arbitrary base field, per `I-0491`. See `PicSchemeEt` below for the
measurement. -/
class HasPicSchemeEt {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : Prop where
  has_pic_scheme_et : ∃ (X : Over (Spec (.of k))),
    Nonempty ((PicScheme.picEt C).RepresentableBy X) ∧
      LocallyOfFiniteType X.hom ∧ IsSeparated X.hom

/-- The étale gate fires for **every** smooth proper geometrically integral
curve, with no rational-point hypothesis — which is the whole content of the
owner decision of 2026-07-28. Its mathematics is
`fgaPicardRepresentability`, the one open obligation. -/
instance instHasPicSchemeEt {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : HasPicSchemeEt C :=
  ⟨(fgaPicardRepresentability C).1⟩

/-- **The Picard scheme `Pic_{C/k}` over an arbitrary base field**: the scheme
representing the étale-sheafified relative Picard functor.

This is the honest `Pic_{C/k}` of the project — available for every smooth
proper geometrically integral curve, with no hypothesis on `C(k)`. The legacy
`PicScheme` (representing the unsheafified `picSharp`) exists only under a
rational point and is retained for the consumers written against it.

**WHAT "AVAILABLE" DOES AND DOES NOT MEAN — read this before reporting anything
on this side of the seam as landed** (`review-ajc`, 2026-07-29, kernel-measured;
the same distinction is stated correctly at `Picard/Pic0EtTangentSpace.lean:59`
and in `scripts/axiom-frontier.lean`, but this is the file a reader arrives at
first, and it did not say it).

`PicSchemeEt` and everything extracted from it (`representableEt`,
`instPicSchemeEtLocallyOfFiniteType`, `instPicSchemeEtIsSeparated`,
`picEtCommGrp`, `groupSchemeStructureEt`) has axiom list
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. That is a fact about
each declaration *as an implication*, and it holds only because each **binds**
`[HasPicSchemeEt C]`; Lean never unfolds a bound instance.

At a **use site** the picture is different, and this is the honest state:
`[HasPicSchemeEt C]` is not a gate. Its instance `instHasPicSchemeEt` is
unconditional, so instance search discharges the class for **every** object in
its own domain — including an abstract `C` carrying only
`[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
[GeometricallyIntegral C.hom]`, with the gate *not* assumed. Measured:
`etGateAbstract` and `representableEt C` at such a `C` both report
`[propext, sorryAx, Classical.choice, Quot.sound]`. The control is what makes
this meaningful rather than a tautology about sorries: in the same probe,
`(inferInstance : HasPicScheme C)` **fails** with `synthInstanceFailed`. So the
legacy class is genuinely instance-free — a hypothesis a consumer must supply —
while `HasPicSchemeEt` is a hypothesis that supplies itself from the bare `sorry`
at `fgaPicardRepresentability`.

So the étale migration bought exactly one thing, and it is the thing the owner
decision `I-0491` asked for: these statements are about an **arbitrary field**
with no rational-point binder. It did not buy a discharged obligation, and no
count of `sorry`-free declarations on this side is evidence that it did. -/
noncomputable def PicSchemeEt {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    Over (Spec (.of k)) :=
  (HasPicSchemeEt.has_pic_scheme_et (C := C)).choose

/-- **Representability of `Pic_{(C/k)ét}` by `Pic_{C/k}`, over an arbitrary
field**: the natural bijection `(T ⟶ Pic_{C/k}) ≃ Pic_{(C/k)ét}(T)`.

The étale-formulation replacement for `PicScheme.representable`. Consumers of
the tangent-space chain should compose with *this* `homEquiv`; the `picSharp`
version is available only under `[HasRationalPoint C]`. -/
noncomputable def representableEt {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    (PicScheme.picEt C).RepresentableBy (PicSchemeEt C) :=
  Classical.choice (HasPicSchemeEt.has_pic_scheme_et (C := C)).choose_spec.1

/-- `Pic_{C/k}` is locally of finite type over `k` (Kleiman §4 Thm `th:main`(1)),
extracted from the étale existence package.

**"Unconditional" here means unconditional on `C(k)`, NOT available today.**
Measured (`review-ajc`, 2026-07-29): this declaration's own axiom list is
`[propext, Classical.choice, Quot.sound]` only because it *binds*
`[HasPicSchemeEt C]`, and a bound instance is never unfolded. But that class is
not a gate — `instHasPicSchemeEt` discharges it by instance search for **every**
object in its own domain, so at any use site (even an abstract `C` carrying only
the three geometric binders) it synthesises and the result fires `sorryAx`.
Control in the same probe: `[HasPicScheme C] := inferInstance` fails with
`synthInstanceFailed`, so the legacy class really is instance-free while this one
is not. See `PicSchemeEt` above for the full statement of the distinction. -/
instance instPicSchemeEtLocallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    LocallyOfFiniteType (PicSchemeEt C).hom :=
  (HasPicSchemeEt.has_pic_scheme_et (C := C)).choose_spec.2.1

/-- `Pic_{C/k}` is separated over `k` (Kleiman §4 Thm `th:main`), extracted from
the étale existence package.

"Unconditional" in the same restricted sense as
`instPicSchemeEtLocallyOfFiniteType` above: unconditional on `C(k)`, and
`sorryAx`-reachable at every use site. -/
instance instPicSchemeEtIsSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    IsSeparated (PicSchemeEt C).hom :=
  (HasPicSchemeEt.has_pic_scheme_et (C := C)).choose_spec.2.2

/-- The multiplicative avatar of the étale-sheafified relative Picard functor,
to feed the (multiplicative) `CommGrpObj.ofRepresentableBy` API. -/
noncomputable def picEtCommGrp {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u+1} :=
  (PicSharp.etaleSheaf C).obj ⋙ AddCommGrpCat.toCommGrp

/-- The set-valued shadows of `picEtCommGrp` and `picEt` agree up to the
carrier-preserving `Multiplicative.ofAdd` bijection. -/
noncomputable def picEtCommGrpForgetIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    PicScheme.picEt C ≅ picEtCommGrp C ⋙ CategoryTheory.forget CommGrpCat.{u+1} :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Multiplicative.ofAdd
      (α := (((PicSharp.etaleSheaf C).obj).obj T : Type (u+1)))))
    (fun _ => rfl)

/-- **`Pic_{C/k}` is a commutative `k`-group scheme, over an arbitrary base
field.** Yoneda transport (`CommGrpObj.ofRepresentableBy`) of the abelian-group
structure of the étale Picard sheaf along `representableEt`.

The group structure survives sheafification because `PicSharp.etaleSheaf` is
`AddCommGrpCat`-valued by construction, so this needs no rational point — in
contrast with `groupSchemeStructure`, its `picSharp` counterpart. -/
noncomputable instance groupSchemeStructureEt {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicSchemeEt C] :
    CommGrpObj (PicSchemeEt C) :=
  CommGrpObj.ofRepresentableBy (PicSchemeEt C) (picEtCommGrp C)
    ((representableEt C).ofIso (picEtCommGrpForgetIso C))

/-- **The comparison that transports representability of `Pic_{(C/k)ét}` to the
`picSharp`-shaped consumer interface**, and the one place where the étale
formulation costs something.

`HasPicScheme` is stated against `picSharp C` because that is the shape every
downstream consumer uses — the tangent-space chain of
`Picard/Pic0AbelianVariety.lean` composes with `representable`'s `homEquiv` to
turn scheme points into line-bundle classes. The obligation above is about
`picEt C`. Bridging them is exactly the assertion that the sheafification
comparison `PicScheme.picEtComparison C` is an isomorphism of functors, which is
Kleiman §2 Thm 2.5 (`th:comp`): **sufficient** under a section, and **not known
to require one**.

**Corrected 2026-07-30 (`review-ajc`): this passage said the comparison is
"TRUE under a section, and FALSE in general without one". The second half is
false as an assertion about this project, and it is contradicted by a theorem in
this file's own import closure.** `Scheme.isIso_picEtComparison_of_picSharp_representability`
(`Picard/PicEtSubcanonical.lean:310`, axiom-clean) proves `IsIso
(PicScheme.picEtComparison C)` from representability of `picSharp C` alone, with
**no** hypothesis on `C(k)`; the mechanism is that the comparison is the
sheafification *unit*, a unit is an iso exactly when its source is a sheaf, and a
representable presheaf is a sheaf for a subcanonical topology. So a section is one
sufficient condition among others, and "FALSE in general" was a sufficient
condition misread as necessary. The two sites that had *already* retracted this
same sentence — `Jacobian.lean:484` and `Picard/Pic0EtTangentSpace.lean:32`, both
naming it as a mispricing of the dimension leaf — left it standing here, in the
file a reader arrives at first.

What IS true and is the real cost: the comparison is not known to be an iso
*unconditionally*, and over an arbitrary field it cannot be, since
`Scheme.PicScheme.not_exists_representing_picSharp_of_not_isIso`
(`PicEtSubcanonical.lean:427`) turns any failure of it into a refutation of
`picSharp` representability — which Kleiman's pointless real conic exhibits. The
honest statement of the cost is therefore about `picSharp` representability, not
about sections.

This statement is therefore **NOT** given a `sorry`-bodied carrier of its own:
the seam has exactly one open obligation (`fgaPicardRepresentability`), of which
this theorem is clause (2), and adding a second carrier would misreport the
frontier.

**Corrected 2026-07-29 (`review-ajc`): there is no class here, and the two
sentences that said there was are gone.** This passage described the bridge as
"a hypothesis class that a consumer must supply explicitly at the use site",
following "the same discipline `HasSmoothProperQuotient` follows", and then told
a consumer to "either supply this class or be restated against `picEt`". No such
class exists — `PicEtComparisonIso` never landed, as `:100` of this same file
already admits three paragraphs above. The bridge is the **theorem** below,
derived from clause (2) of the seam applied to the section, so a consumer does
not supply it: a consumer supplies `[HasRationalPoint C]` and gets it. The
`HasSmoothProperQuotient` analogy was wrong in the same stroke — that *is* a
real class with a use-site-only discipline, which is why citing it made the
absent class sound routine.

The consequence for the headline, which is the part that survives unchanged:
over an arbitrary field the project reaches representability of the *étale*
functor (`representableEt`), and a consumer wanting the `picSharp` shape must
either carry `[HasRationalPoint C]` — strictly weaker than the challenge, and
forbidden as a headline by `I-0491` — or be restated against `picEt`. That
restatement is downstream work in `Picard/Pic0AbelianVariety.lean` (a lane this
file does not own), not a defect here, and it is the bulk of what the étale
decision still implies: 70 declarations bind the `picSharp`-shaped
`HasPicScheme` against 27 on the étale side. -/
theorem picEtComparison_isIso_of_hasRationalPoint {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasRationalPoint C] :
    IsIso (PicScheme.picEtComparison C) :=
  (fgaPicardRepresentability C).2 inferInstance

/-- **The conditional milestone: the Picard scheme of a curve WITH a rational
point.** Kleiman §4 Thm `th:main` combined with §2 Thm 2.5: given a section,
the comparison `picSharp C → Pic_{(C/k)ét}` is bijective, so the scheme
representing the étale sheaf represents the plain relative functor too.

**This is strictly weaker than the challenge and is not the headline.** It is
retained (owner decision of 2026-07-28, clause 4) because it is true, because
it records what a rational point buys, and because the group-scheme /
tangent-space development is stated against the `picSharp` shape. It is
deliberately **not an instance**: nothing may pick up a rational-point
hypothesis by synthesis, and any consumer wanting this must name it.

It carries **no `sorry` of its own**: both inputs are clauses of the seam's
single open obligation `fgaPicardRepresentability` — clause (1) for the
representing scheme, clause (2) for the Kleiman §2 Thm 2.5 comparison — composed
with `Functor.RepresentableBy.ofIso`. -/
theorem picSchemeOfHasRationalPoint {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasRationalPoint C] :
    HasPicScheme C := by
  obtain ⟨X, ⟨rep⟩, hft, hsep⟩ := (fgaPicardRepresentability C).1
  haveI := picEtComparison_isIso_of_hasRationalPoint C
  exact ⟨X, ⟨rep.ofIso (asIso (PicScheme.picEtComparison C)).symm⟩, hft, hsep⟩

namespace PicScheme

/-! ## §2. The Abel map — line-bundle / Quot correspondence

The bridge from line bundles on `C ×_k T` to the Quot scheme is the **Abel
map**: a relative effective divisor `D ⊆ C ×_k T` over `T` determines a
`T`-point of `Div_{C/k}`, and the dual ideal sheaf
`O_{C ×_k T}(D) := I_D⁻¹` represents a class in `Pic^♯_{C/k}(T)`.

Blueprint reference: `lem:line_bundle_quot_correspondence` (Kleiman §3
Def. `dfn:Abel` + Thm. `th:repDiv`). -/

/-! ### The Abel map

The class `HasAbelMap` carries the map itself (a data field `abel`), so that
`abelMap` has the defining property `abelMap_app_mk` below; the instance
supplies the explicit natural transformation `abelMapWitness C`.

Construction of `abelMapWitness C : Div_{C/k} ⟶ Pic^♯_{C/k}`, `[D] ↦ [O(D)]`:
a relative effective divisor family `⟨F, q⟩` on `C ×_k T` has invertible ideal
`I_D = ker q`; the Abel map sends its class to
`[O(D)] = [I_D⁻¹] = -[I_D]`, the additive inverse (in the group-valued target
`Pic^♯_{C/k}(T)`) of the class of the ideal sheaf.  It is assembled as the
composite `abelKernelNatTrans C ≫ picNeg C`, where `abelKernelNatTrans` is the
substantive `[D] ↦ [I_D]` transformation and `picNeg` is the (natural)
negation on the group-valued functor.

Naturality of `abelKernelNatTrans` is the mathematical heart: for a test map
`g : T' ⟶ T` the base-change square is cartesian (`quotBaseSquare`), and the
**kernel–pullback comparison** `g_C^*(ker q) ⟶ ker(g_C^* q)` is an isomorphism
under the divisor conditions (`Modules.isIso_pullbackKernelComparison`, whose
side hypotheses — epi `q`, quasi-coherent source, finitely-presented `F`,
`T`-flat `F`, invertible kernel — are exactly the fields of `DivFamily`), so
`ker` commutes with base change and the class `[ker q]` is natural.  Negation
is natural because `Pic^♯`'s pullback maps are group homomorphisms.

The `dual` route (`Modules.dual (ker q)` as an explicit inverse) is available
for the *object-level* invertibility (`dual_isLocallyTrivial`) but is not used
here: the group-inverse `-[ker q]` is the canonical `[I_D⁻¹]` and makes
naturality rest only on the kernel–pullback comparison, avoiding the
not-yet-formalised sheaf-level dual-pullback commutation.

Blueprint reference: `lem:line_bundle_quot_correspondence` (Kleiman §3
Def. `dfn:Abel`); this instance is the **natural-transformation half** — `Div`
representability (Kleiman §3 Thm. `th:repDiv`) is NOT claimed here. -/

/-- Well-definedness of the ideal-class assignment `⟨F, q⟩ ↦ [ker q]` on the
divisor equivalence relation `DivFamily.Rel`: an equivalence `f : x.F ≅ y.F`
with `x.q ≫ f.hom = y.q` gives `ker x.q ≅ ker y.q` (`kernelCompMono` at the
iso `f.hom`), hence equal `H_T`-coset classes (`relPicRel_of_iso`). -/
private theorem abelKernel_welldef {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (T : (Over (Spec (.of k)))ᵒᵖ) {x y : DivFamily C.hom T.unop} (h : x.Rel y) :
    Quotient.mk (PicSharp.relPicSetoid C.hom T.unop.hom)
        (⟨kernel x.q, x.kerLocallyTrivial⟩ : LineBundle.OnProduct C.hom T.unop.hom) =
      Quotient.mk (PicSharp.relPicSetoid C.hom T.unop.hom)
        (⟨kernel y.q, y.kerLocallyTrivial⟩ : LineBundle.OnProduct C.hom T.unop.hom) := by
  obtain ⟨f, hf⟩ := h
  exact Quotient.sound (PicSharp.relPicRel_of_iso
    ⟨(kernelCompMono x.q f.hom).symm ≪≫ Limits.kernelIsoOfEq hf⟩)

/-- **Kernel commutes with base change for a divisor family** (the mathematical
heart of Abel-map naturality).  For a test map `g : T ⟶ T'` and a divisor family
`x` over `T`, the ideal of the pulled-back family is the pullback of the ideal:
`ker((g_C^* x).q) ≅ g_C^*(ker x.q)`.  Proof: `(pullbackAlong g.unop x).q` is
`triangleIso.inv ≫ g_C^*(x.q)`, so its kernel agrees with `ker(g_C^* x.q)`
(`kernelIsIsoComp`, precomposition by the iso `triangleIso.inv`); the
**kernel–pullback comparison** `g_C^*(ker q) ⟶ ker(g_C^* q)` is an isomorphism
under the divisor conditions (`Modules.isIso_pullbackKernelComparison`, whose
side hypotheses are exactly the `DivFamily` fields `epi`, quasi-coherent source,
`isFinitePresentation`, `flat`, `kerLocallyTrivial` over the cartesian
`quotBaseSquare`). -/
private noncomputable def abelKernelBaseChangeIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    {T T' : (Over (Spec (.of k)))ᵒᵖ} (g : T ⟶ T') (x : DivFamily C.hom T.unop) :
    kernel ((DivFamily.pullbackAlong g.unop x).q) ≅
      (Scheme.Modules.pullback (quotBaseMap C.hom g.unop)).obj (kernel x.q) := by
  haveI hiso : IsIso (Modules.pullbackKernelComparison (quotBaseMap C.hom g.unop) x.q) :=
    Modules.isIso_pullbackKernelComparison (quotBaseSquare C.hom g.unop) x.q x.epi
      (pullback_isQuasicoherent_hom (pullback.fst C.hom T.unop.hom)
        (SheafOfModules.unit C.left.ringCatSheaf) inferInstance)
      x.isFinitePresentation x.flat x.kerLocallyTrivial
  exact kernelIsIsoComp
      (pullbackTriangleIso (quotBaseMap_fst C.hom g.unop)
        (SheafOfModules.unit C.left.ringCatSheaf)).inv
      ((Scheme.Modules.pullback (quotBaseMap C.hom g.unop)).map x.q) ≪≫
    (asIso (Modules.pullbackKernelComparison (quotBaseMap C.hom g.unop) x.q)).symm

/-- **The ideal-class transformation** `[D] ↦ [I_D] = [ker q]`
(`Div_{C/k} ⟶ Pic^♯_{C/k}`), the additive negative of the Abel map.  On
objects it is `⟦⟨F, q⟩⟧ ↦ ⟦ker q⟧`; naturality is the invertible
kernel–pullback comparison over the cartesian base-change square
(`abelKernelBaseChangeIso`, fed by the `DivFamily` fields).  Well-definedness on
`DivFamily.Rel` is `abelKernel_welldef`. -/
noncomputable def abelKernelNatTrans {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    divFunctor C ⟶ picSharp C where
  app T := TypeCat.ofHom (Quotient.lift
    (fun x : DivFamily C.hom T.unop =>
      Quotient.mk (PicSharp.relPicSetoid C.hom T.unop.hom)
        (⟨kernel x.q, x.kerLocallyTrivial⟩ : LineBundle.OnProduct C.hom T.unop.hom))
    (fun _ _ h => abelKernel_welldef C T h))
  naturality {T T'} g := by
    ext a
    induction a using Quotient.ind with | _ x => ?_
    apply Quotient.sound
    apply PicSharp.relPicRel_of_iso
    exact ⟨abelKernelBaseChangeIso C g x⟩

/-- **Negation on the group-valued relative Picard presheaf**
`PicSharp.relPresheaf C ⟶ PicSharp.relPresheaf C`.  Pointwise it is the group
homomorphism `a ↦ -a` (`-AddMonoidHom.id`, valid since `Pic^♯_{C/k}(T)` is
abelian); naturality is `map_neg` of the group-homomorphism pullback maps of
`Pic^♯` (`PicSharp.relFunctorial`).  Building the negation at the
`AddCommGrpCat`-valued level (rather than on the forgotten set-valued
`picSharp`) keeps the group structure directly available — the forget-composite
`(picSharp C).obj T` does not expose its `AddGroup` to instance search. -/
noncomputable def relPresheafNeg {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    PicSharp.relPresheaf C ⟶ PicSharp.relPresheaf C where
  app T := AddCommGrpCat.ofHom (-AddMonoidHom.id _)
  naturality {T T'} g := by
    ext a
    exact (map_neg (PicSharp.relFunctorial C.hom T.unop.hom T'.unop.hom
      g.unop.left (Over.w g.unop).symm) a).symm

/-- **Negation on the relative Picard functor**, as a natural transformation
`Pic^♯_{C/k} ⟶ Pic^♯_{C/k}`.  Pointwise it is `a ↦ -a` in the group
`Pic^♯_{C/k}(T)`; it is the set-valued shadow (`whiskerRight … (forget _)`) of
the group-presheaf negation `relPresheafNeg`, so its naturality is inherited
for free. -/
noncomputable def picNeg {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    picSharp C ⟶ picSharp C :=
  Functor.whiskerRight (relPresheafNeg C) (CategoryTheory.forget AddCommGrpCat.{u+1})

/-- **The Abel map witness** `A_{C/k} : Div_{C/k} ⟶ Pic^♯_{C/k}`,
`[D] ↦ [O(D)] = [I_D⁻¹] = -[ker q]`, the substantive natural transformation
underlying the line-bundle / Quot correspondence (Kleiman §3 Def. `dfn:Abel`).
Assembled as `abelKernelNatTrans C ≫ picNeg C`. -/
noncomputable def abelMapWitness {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    divFunctor C ⟶ picSharp C :=
  abelKernelNatTrans C ≫ picNeg C

/-- Class **carrying the Abel map** `Div_{C/k} ⟶ Pic^♯_{C/k}`.  It is a
data-carrying class with field `abel`; the instance `instHasAbelMap` supplies
the witness `abelMapWitness C`.

**PROPERTY-FREE DATA SLOT — corrected 2026-07-29 (`review-ajc`, from a
fresh-context vacuity sweep). The previous text claimed that `abelMap :=
HasAbelMap.abel` "inherits the concrete construction and the defining property
`abelMap_app_mk`". Both halves are false under the class binder**, and the
second is provably so.

The single field constrains nothing beyond the *type* of `abel`. Machine-checked:
the constant-zero transformation inhabits the class — its naturality is
`map_zero` of the pullback group hom, so it is free — and under that instance
`abelMap C` is identically `0`, sending every divisor class to `0`. Probing
`abelMap_app_mk`'s conclusion against it, `rfl` **fails**. So `abelMap_app_mk`
is a statement about `instHasAbelMap` alone, never about the class: a consumer
quantifying over `[HasAbelMap C]` gets an arbitrary natural transformation with
no Abel-map content. This is the `ClassDegree` collapse
(`IdentityComponent.lean:1450-1461`) one level up, and it is the
property-free-data-field sibling of the `HasDivFunctor` vacuity recorded in this
file's §2 caveat.

Blast radius is small at HEAD and this is a documentation fix, not a repair: the
only declaration taking `[HasAbelMap C]` is `abelMap` itself, and every real
consumer routes through `abelMapWitness` directly (`DivDegree.lean:678-703`,
`IdentityComponent.lean:1539`). **Do not write a new consumer against this
class.** The cheap repair, for whoever owns this file, is to delete the class and
use `abelMapWitness`; the alternative is to add the pin as a field, as
`ClassDegreePinned` did after its own collapse. Recorded as inbox `I-0953`. -/
class HasAbelMap {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] where
  /-- The Abel map itself (data). -/
  abel : divFunctor C ⟶ picSharp C

/-- The **Abel map** `A_{C/k} : Div_{C/k} ⟶ Pic^♯_{C/k}`, sending a relative
effective Cartier divisor `D ⊆ C ×_k T` over `T` to its associated invertible
sheaf `[O_{C ×_k T}(D)] = [I_D⁻¹]`.

It is the map carried by `HasAbelMap`; the instance `instHasAbelMap` fixes it
to `abelMapWitness C`, and `abelMap_app_mk` is its defining property **at that
instance**.

**Not under an arbitrary `[HasAbelMap C]` binder** — that class is a
property-free data slot, inhabited by the constant-zero transformation, and
`abelMap_app_mk` provably fails there (see the class docstring, and `I-0953`).
Read this definition as "the Abel map" only when the instance in scope is
`instHasAbelMap`. -/
noncomputable def abelMap {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasAbelMap C] :
    divFunctor C ⟶ picSharp C :=
  HasAbelMap.abel

/-- Existence instance for `HasAbelMap`: the Abel map `abelMapWitness C`
witnesses the carrier. -/
noncomputable instance instHasAbelMap {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] : HasAbelMap C :=
  ⟨abelMapWitness C⟩

/-- **Defining property of the Abel map** (Kleiman §3 Def. `dfn:Abel`): on the
class of a relative divisor family `⟨F, q⟩` it returns `[O(D)] = [I_D⁻¹]`, the
additive inverse of the class of the ideal sheaf `I_D = ker q`. -/
theorem abelMap_app_mk {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (T : (Over (Spec (.of k)))ᵒᵖ) (x : DivFamily C.hom T.unop) :
    (abelMap C).app T (Quotient.mk (DivFamily.setoid C.hom T.unop) x) =
      - Quotient.mk (PicSharp.relPicSetoid C.hom T.unop.hom)
        (⟨kernel x.q, x.kerLocallyTrivial⟩ : LineBundle.OnProduct C.hom T.unop.hom) := by
  rfl

/-! ## §3. The smooth-proper quotient lemma — Altman–Kleiman descent

The structural lemma underlying Step 4 of Kleiman §4 Thm. `th:main`: given a
surjection `α : Z ⟶ P` of étale sheaves with `R := Z ×_P Z` representable,
`Z` representable **by a quasi-projective scheme**, and the first projection
`R ⟶ Z` smooth and proper, the quotient `P` is representable.

The hypothesis list expressible here is strictly weaker than Kleiman §4 Lem
`lm:qt`: it lacks **quasi-projectivity of `Y`**, for which Mathlib has no
vocabulary at the pinned revision. Without it the statement is false: a
Hironaka-type free `ℤ/2`-action on a smooth proper non-projective 3-fold
gives a smooth proper equivalence relation satisfying hypotheses (1)–(4)
whose quotient étale sheaf is an algebraic space that is not a scheme. In
particular there is no global instance of `HasSmoothProperQuotient`; such an
instance would assert that every presheaf receiving any natural
transformation is representable.

`HasSmoothProperQuotient α` is therefore an **explicit use-site hypothesis**:
the intended consumer (the FGA assembly, Step 4 of `th:main`) instantiates it
for the Abel-map slice `Z ⟶ P^{φ_0}_0`, where `Z` is a quasi-projective open
of `Div_{C/k}` and Altman–Kleiman descent genuinely applies. Supplying that
instance is part of the `fgaPicardRepresentability` obligation, not a standalone
global fact.

Blueprint reference: `lem:smooth_proper_quotient` (Kleiman §4 Lem. `lm:qt`). -/

/-- Hypothesis class packaging the CONCLUSION of the Altman–Kleiman
smooth-proper quotient lemma for a specific étale-sheaf surjection `α`:
that the target presheaf is representable.

There is deliberately no global instance: an unconditional one would be a
false statement (see the section header). The class is supplied at the use
site, where the Kleiman `lm:qt` hypotheses — including quasi-projectivity of
the representing scheme, which the `smoothProperQuotient` statement below
cannot express — actually hold.

**`α` IS A DECORATIVE INDEX — recorded 2026-07-29 (`review-ajc`), from a
fresh-context vacuity sweep, and it limits the use-site argument just made.**
Neither `α` nor `Z` occurs in the field `is_representable : P.IsRepresentable`;
only `P` does. Machine-checked consequences: from
`[HasSmoothProperQuotient α]` one derives `HasSmoothProperQuotient α'` for *any*
other `α' : Z' ⟶ P` with the same target, and `[HasSmoothProperQuotient (id P)]`
discharges the class for every `α` into `P` — where no equivalence relation, no
smoothness and no properness is in sight. So this class **cannot** express "this
quotient presentation is smooth and proper"; it says only "`P` is
representable", indexed by an argument it ignores. The scoping paragraph above
should be read as describing where the *mathematics* applies, not as a property
the Lean statement enforces: a use site could satisfy it with an unrelated map
and nothing would complain.

Nothing is unsound at HEAD — the class has zero instances and zero call sites —
but do not treat the index as a guard. Recorded as inbox `I-0954`, alongside the
`P → P` labelling on `smoothProperQuotient` below.

The class is kept as the blueprint-pinned record of the Altman–Kleiman
`lm:qt` interface. A route to `fgaPicardRepresentability` that takes only finite
Galois quotients with an orbit-in-affine hypothesis sidesteps the
Hironaka-type counterexample above, and so needs neither this class nor
`smoothProperQuotient`. -/
class HasSmoothProperQuotient {k : Type u} [Field k]
    {Z P : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1)}
    (_α : Z ⟶ P) : Prop where
  is_representable : P.IsRepresentable

/-- **The smooth-proper quotient lemma — Altman–Kleiman descent of an
étale-sheaf surjection** (Kleiman §4 Lem. `lm:qt`).

Let `Z, P : (Sch/k)^op ⥤ Type (u+1)` be presheaves and `α : Z ⟶ P` a natural
transformation with: (1) `Z` representable by `Y`; (2) `R := Z ×_P Z`
representable by `R`; (3) the first projection `π : R ⟶ Y` smooth and proper;
(4) `α` an étale-local surjection (every `T`-point of `P` lifts along some
test morphism). Then, granting the use-site hypothesis
`[HasSmoothProperQuotient α]` (which additionally encodes Kleiman's
quasi-projectivity of `Y` — see the section header for why it cannot yet be
stated internally), `P` is representable.

The Lean body extracts the conclusion from the hypothesis class; the
mathematical content (Altman–Kleiman effective-equivalence-relation descent
+ EGA IV 8.11.5) lives at the use site supplying the instance.

**WHAT THIS THEOREM PROVES, stated flatly (`review-ajc`, 2026-07-29), because
the paragraphs above explain the situation without ever naming it.** Since
`HasSmoothProperQuotient α` is by definition `P.IsRepresentable`, this theorem
is `P.IsRepresentable → P.IsRepresentable`. All four numbered hypotheses are
unused in the body — they are named `_hZ`, `_hR`, `_hα` for exactly that
reason — as are `Y`, `R`, `π` and both instance binders on `π.left`. The class
has **zero instances** and this theorem has **zero call sites** in the project.
It is a blueprint-pinned record of the `lm:qt` interface and nothing more.
Do not cite it as evidence that a quotient is a scheme, do not write a consumer
against it, and do not claim its `\leanok` in the blueprint as a proof of
Kleiman `lm:qt`. The committed Milne–Kollár route does not need it at all
(finite Galois quotients with an orbit-in-affine hypothesis instead). -/
theorem smoothProperQuotient {k : Type u} [Field k]
    {Z P : (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1)}
    (α : Z ⟶ P)
    (Y : Over (Spec (.of k)))
    (_hZ : Z.RepresentableBy Y)
    (R : Over (Spec (.of k)))
    (_hR : (Limits.pullback α α).RepresentableBy R)
    (π : R ⟶ Y)
    [Smooth π.left] [IsProper π.left]
    (_hα : ∀ ⦃T : (Over (Spec (.of k)))ᵒᵖ⦄ (p : P.obj T),
        ∃ (T' : (Over (Spec (.of k)))ᵒᵖ) (e : T ⟶ T') (z : Z.obj T'),
          α.app T' z = P.map e p)
    [HasSmoothProperQuotient α] :
    P.IsRepresentable :=
  HasSmoothProperQuotient.is_representable (_α := α)

/-! ## §4. The FGA representability theorem

Grothendieck's existence theorem for the Picard scheme (Kleiman §4 Thm.
`th:main`, specialised via Cor. `cor:algsch` to `S = Spec k`, `X = C`),
transported through Kleiman §2 Thm 2.5 to the plain relative functor under
the rational-point hypothesis: `picSharp C` is representable by `PicScheme C`.

Blueprint reference: `thm:fga_pic_representability`. -/

/-- Typeclass asserting that `picSharp C` is representable by `PicScheme C`.

It follows from `HasPicScheme` — the representing witness is
`Classical.choose`-extracted, so its `choose_spec` is exactly this statement.
The class survives to preserve the blueprint-pinned consumer signature of
`representable`.

**THIS CLASS IS A SELF-PROJECTION AND CARRIES NO MATHEMATICS** (`review-ajc`,
2026-07-30). The paragraph above states the mechanism and stops short of the
conclusion, exactly as `PicSchemeLocallyOfFiniteType` below did until it was
labelled: these are the *same* defect at two carriers, and labelling only one of
them made the other look audited. `instPicSharpRepresentable` is
`choose_spec.1` of the `[HasPicScheme C]` binder it assumes, so the class is
definitionally whatever its own hypothesis already said — `P → P`. Discharging
it is not a step toward anything.

As with `PicSchemeLocallyOfFiniteType`: **do not write a new consumer against
it** (binding `[PicSharpRepresentable C]` on top of `[HasPicScheme C]` is no
more general — instance search discharges it from the first), and it is
nonetheless **harmless to keep**, since `HasPicScheme` is `Prop`-valued so the
projection is unique and the blueprint pins `representable`'s signature. The
honest content is upstream: `HasPicScheme` has zero instances and over an
arbitrary field cannot get one. -/
class PicSharpRepresentable {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] : Prop where
  has_representable : Nonempty ((picSharp C).RepresentableBy (PicScheme C))

/-- Existence instance for `PicSharpRepresentable`: `PicScheme C` is
`Classical.choose` of the `HasPicScheme` existential, and the first component
of `Exists.choose_spec` says precisely that the chosen scheme represents
`picSharp C` (the remaining components are local finiteness and
separatedness). The FGA content lives upstream in `fgaPicardRepresentability`. -/
instance instPicSharpRepresentable {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] : PicSharpRepresentable C :=
  ⟨(HasPicScheme.has_pic_scheme (C := C)).choose_spec.1⟩

/-- **FGA representability of the Picard scheme.**

Let `k` be a field and `C` a smooth proper geometrically integral curve over
`k` (with, through the `HasPicScheme` hypothesis chain, a `k`-rational
point). Then the relative Picard functor `Pic^♯_{C/k}` is representable by
the Picard scheme `PicScheme C`: there is a natural bijection

```
(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)
```

for every `k`-scheme `T`. This `RepresentableBy` structure is a comparison
against the relative Picard functor itself, so downstream consumers
(tangent-space computation at the identity, `Pic⁰` degree theory) can compose
with its `homEquiv` to transfer line-bundle data to scheme points. -/
noncomputable def representable {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] [PicSharpRepresentable C] :
    (picSharp C).RepresentableBy (PicScheme C) :=
  Classical.choice (PicSharpRepresentable.has_representable (C := C))

/-! ## §5. The abelian group-scheme structure

The Picard scheme `Pic_{C/k}` inherits an abelian group-scheme structure from
the tensor product of invertible sheaves on `C ×_k T`: the relative Picard
presheaf is group-valued (`PicSharp.relPresheaf`), and a representing object
of (the set-valued shadow of) a group-valued presheaf is canonically a group
object, by Yoneda transport (`GrpObj.ofRepresentableBy`).

Since `picSharp` is by definition `relPresheaf ⋙ forget`, the transport
applies directly.

Blueprint reference: `thm:pic_is_group_scheme` (Kleiman §2 Def. `df:Pfs` +
§4 Def. `df:Psch`). -/

/-- The multiplicative (`CommGrpCat`-valued) avatar of the relative Picard
presheaf, used to feed `GrpObj.ofRepresentableBy` (whose API is
multiplicative). Carrier-level it is the same functor: `Multiplicative` is a
type synonym. -/
noncomputable def picSharpCommGrp {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u+1} :=
  PicSharp.relPresheaf C ⋙ AddCommGrpCat.toCommGrp

/-- The set-valued shadows of `picSharpCommGrp` and `picSharp` agree up to
the canonical `Multiplicative.ofAdd` bijection (a natural isomorphism, since
`Multiplicative` is carrier-preserving). -/
noncomputable def picSharpCommGrpForgetIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] :
    picSharp C ≅ picSharpCommGrp C ⋙ CategoryTheory.forget CommGrpCat.{u+1} :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Multiplicative.ofAdd
      (α := ((PicSharp.relPresheaf C).obj T : Type (u+1)))))
    (fun _ => rfl)

/-- **The Picard scheme is a commutative `k`-group scheme** — a canonical
`CommGrpObj` structure (i.e. `GrpObj` + `IsCommMonObj`) on `PicScheme C`,
obtained by Yoneda transport (`CommGrpObj.ofRepresentableBy`) of the
abelian-group structure of the relative Picard presheaf
`PicSharp.relPresheaf` along the representability witness `representable C`.
Concretely: `[L] + [M] = [L ⊗ M]`, `-[L] = [L⁻¹]`, unit `[O_{C ×_k T}]`,
transported through `(T ⟶ Pic_{C/k}) ≃ Pic(C ×_k T)/π_T^* Pic(T)`.

Commutativity comes for free from the transport, so this is the full
abelian-group-scheme statement of the blueprint
(`thm:pic_is_group_scheme`). -/
noncomputable instance groupSchemeStructure {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    CommGrpObj (PicScheme C) :=
  CommGrpObj.ofRepresentableBy (PicScheme C) (picSharpCommGrp C)
    ((representable C).ofIso (picSharpCommGrpForgetIso C))

/-! ## §6. Local finiteness of the Picard scheme

Kleiman §4 Thm `th:main`(1): the Picard scheme is separated and locally of
finite type over the base. `HasPicScheme` packages local finiteness together
with the representability existential (one existence package, as in Kleiman's
theorem), so the carrier below is obtained by extraction. It is what the
identity-component substrate (`Picard/IdentityComponent.lean`,
`GroupScheme.IdentityComponent`) consumes to specialise to
`G = PicScheme C`. -/

/-- Typeclass asserting that the structural morphism of the Picard scheme is
  locally of finite type (Kleiman §4 Thm `th:main`(1)). Over a field, Cor
  `cor:algsch` further writes `Pic_{C/k}` as a disjoint union of open
  quasi-projective `k`-subschemes. The `HasPicScheme` existential carries local
  finiteness, so the property of the `Classical.choose` witness is its second
  `choose_spec` component; the class survives to preserve the blueprint-pinned
  consumer signature.

**THIS CLASS IS A SELF-PROJECTION AND CARRIES NO MATHEMATICS** (`review-ajc`,
2026-07-30 — the paragraph above states the mechanism but never draws the
conclusion, and 57 binder sites read it as content). Its sole producer
`instPicSchemeLocallyOfFiniteType` below is `choose_spec.2.1` of the very
`[HasPicScheme C]` binder it assumes, so the class is *definitionally* whatever
its hypothesis already said: it proves nothing that naming `HasPicScheme` does
not. Discharging it is not a step toward anything.

Two consequences worth stating separately, because they pull in opposite
directions:

* **Do not write a new consumer against it.** A statement binding
  `[PicSchemeLocallyOfFiniteType C]` on top of `[HasPicScheme C]` is not more
  general than one binding `[HasPicScheme C]` alone — the extra binder is
  discharged by instance search from the first. It costs a reader a lookup and
  buys nothing.
* **It is nonetheless harmless to keep**, which is why it is labelled rather
  than deleted: 57 signatures name it, `HasPicScheme` is `Prop`-valued so the
  projection is unique, and the blueprint pins the consumer shape. Deleting it
  is a 57-site edit for zero mathematical gain.

The honest content is upstream: `HasPicScheme` itself has **zero** instances,
and over an arbitrary field it cannot get one (see `HasPicSchemeEt` below and
`PicScheme.not_exists_representing_picSharp_of_not_isIso` in
`Picard/PicEtSubcanonical.lean`). So neither this class nor its **57** consumers
currently speaks about any curve.

(That figure said "61" until 2026-07-30 — the stale survivor of the correction
that fixed the two figures fourteen lines above it, which is the caveat-pass
failure this project keeps reproducing: the pass that fixes a number leaves its
own copies behind. Re-measured at HEAD by the declaration-block method: 57
signatures, in Pic0AbelianVariety 33, Pic0Dimension 6, IdentityComponent 6,
GroupSchemeHomogeneity 5, Jacobian 4, HomogeneityOrbitCollapse 2, and one here.
The line anchor formerly given for the refutation is dropped in favour of the
declaration name, for the same reason.) -/
class PicSchemeLocallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] : Prop where
  locallyOfFiniteType : LocallyOfFiniteType (PicScheme C).hom

/-- Existence instance for `PicSchemeLocallyOfFiniteType`: Kleiman §4 Thm
`th:main`(1) makes local finiteness part of the same existence package as
representability, so the `HasPicScheme` existential carries it and the
property of the chosen witness is the second component of its `choose_spec`.
The instance hypothesis is `[HasPicScheme C]` rather than
`[HasRationalPoint C]`: the rational-point conditionality lives entirely in
`picSchemeOfHasRationalPoint` (the sole producer of `HasPicScheme C`), and any consumer able
to name `PicScheme C` already quantifies over `[HasPicScheme C]`. -/
instance instPicSchemeLocallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    PicSchemeLocallyOfFiniteType C :=
  ⟨(HasPicScheme.has_pic_scheme (C := C)).choose_spec.2.1⟩

/-- Projection of `PicSchemeLocallyOfFiniteType` to the Mathlib morphism
property, so that instance search finds `LocallyOfFiniteType (PicScheme
C).hom` whenever the carrier class is in scope (as the identity-component
substrate requires). -/
instance {k : Type u} [Field k] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicSchemeLocallyOfFiniteType C] :
    LocallyOfFiniteType (PicScheme C).hom :=
  PicSchemeLocallyOfFiniteType.locallyOfFiniteType

/-- **`Pic_{C/k}` is separated over `k`.**

Kleiman §4 Thm `th:main` packages separatedness together with representability
and local finite type for `Pic_{C/k}` ("Then `Pic_{X/k}` is separated, ..."):
one existence package, as in the theorem. As with
`instPicSchemeLocallyOfFiniteType`, we extract this property from the
strengthened `HasPicScheme.has_pic_scheme` existential — its third
component — so downstream files (`Picard/Pic0AbelianVariety.lean`) can consume
`IsSeparated (PicScheme C).hom` as a normal instance without opening the axiom
layer. The conditionality on `[HasRationalPoint C]` lives entirely upstream in
`picSchemeOfHasRationalPoint` (the sole producer of `HasPicScheme C`); this extraction only
names `[HasPicScheme C]`, as every consumer able to name `PicScheme C`
already does. -/
instance isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    IsSeparated (PicScheme C).hom :=
  (HasPicScheme.has_pic_scheme (C := C)).choose_spec.2.2

end PicScheme

end Scheme

end AlgebraicGeometry
