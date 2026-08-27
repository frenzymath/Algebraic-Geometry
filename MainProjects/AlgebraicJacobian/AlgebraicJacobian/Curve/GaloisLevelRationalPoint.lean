/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Curve.FiniteLevelRationalPoint
import AlgebraicJacobian.Picard.RigidPushforwardP1Witness
import AlgebraicJacobian.Jacobian
import AlgebraicJacobian.Picard.GaloisQuotientAffineGeneral

/-!
# A rational point at a finite *Galois* level, with no hypothesis on `C(k)`

Campaign `G1` (`informal/pic-representability-campaign.md`) spreads `J5`'s datum from `k^s` down
to a **finite Galois** extension `k'/k`, because the object it hands `G2` is a *semilinear
`Gal(k'/k)`-action* — and `Gal(k'/k)` is only the right group when `k'/k` is Galois. Two
neighbouring files stop one step short of that:

* `Curve/SeparablyClosedRationalPoint.lean` gives a section over `k^s` itself, where
  `IsSepClosed` holds; `IsSepClosed k'` is false at every finite level, so it does not reach `G1`.
* `Curve/FiniteLevelRationalPoint.lean` (`exists_finiteSeparable_level_hasRationalPoint`) gives
  one at a finite **separable** level. A finite separable extension need not be Galois, and its
  own docstring says so: "Still not Galois. … That remains open, by a normal-closure argument
  (`IntermediateField.normalClosure`), and this theorem must not be read as closing it."

This file closes exactly that step, and the roadmap row `AJC.picrep.sepclosed-galois` that
recorded it as open and **unpriced**.

## What is proved here

* `Scheme.hasRationalPoint_baseChangeField_of_pullbackSection` — a section of the base-changed
  curve's structure morphism yields a `κ`-point of `C` over `Spec k`, at the pullback spelling.
* `Scheme.exists_finiteGalois_level_hasRationalPoint` — from a `k^s`-point of `C` over `k`, a
  finite **Galois** `k''/k` with `Scheme.HasRationalPoint (Scheme.baseChangeField C k'')`.
* `Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIrreducible` — the same
  conclusion with **no antecedent at all** beyond the curve binders the headline
  `AlgebraicGeometry.picardJacobianWitness` (`AlgebraicJacobian/Jacobian.lean:840`) already
  carries. This is the form a consumer binds.

## The price the row quoted, and what it actually cost

The row (and my own `r4` release note) left this "unpriced". Measured: the normal closure of a
finite separable `k' ⊆ k^s` is again inside `k^s`, is again finite over `k`, and *is* Galois —
all three by mathlib instances that synthesise (`normalClosure.is_finiteDimensional`,
`IsGalois.normalClosure`, `IntermediateField.le_normalClosure`), with no separability argument
re-run and no `Algebra.IsSeparable` hypothesis needed in the conclusion. Pushing the point up the
inclusion `k' ≤ k''` is `Spec.map_comp` plus one `congr 1`, the same two-line triangle as the
sibling file's `specMap_val_comp_specMap_algebraMap`. So the step is cheap, and saying so is part
of the result: a lane sent to build a filtered-colimit or a descent argument here would build
nothing.

## What this does **not** do

It does not close the seam `Scheme.fgaPicardRepresentability`, and it does not close campaign
`G1`. `G1` also needs the *datum* — the finitely many `J^Σ ↪ Gr`, the gluing isomorphisms, the
universal families — spread to that level; this supplies only the **section**, which is input (4)
of the four-input descent repair. The `k'`-side representability output of cluster `J` and the
glued (non-affine) half of `G2(c)` are untouched and remain open.

It also carries **no** hypothesis on `C(k)`, per protection `I-0491`: the point appears only after
a separable base extension. `Scheme.HasRationalPoint C` itself is never assumed, and nothing here
may be read as progress toward a headline that carries it.

**And the level is existentially quantified, which is the shape a consumer will trip on.** The
conclusion is `∃ k'', …`, and that `k''` is manufactured *from the point*: it is the normal closure
of whichever finite level the `k^s`-point happens to factor through. So what is proved is "there
**exists** a finite Galois level carrying a rational point", **not** "at *your* level there is
one". A consumer whose cover, splitting, or `Gal`-indexed family already lives at some fixed
`k''₀` cannot simply `obtain` from here and proceed: it owes either that its construction runs at
whatever level it is handed, or an enlargement step up a further extension. Which of those is
needed depends on the consumer and **neither is measured here**.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace AlgebraicGeometry.Scheme

/-! ## §1. A section of the base-changed curve is a point over the extension

`Scheme.baseChangeField C κ` is `Over.mk (pullback.snd C.hom (Spec.map (algebraMap k κ)))`, so a
`Scheme.HasRationalPoint` for it is a section `σ` of that second projection. Composing with the
*first* projection gives a morphism `Spec κ ⟶ C.left`, and the pullback square turns the section
equation into the over-`Spec k` equation that §2 consumes.

The statement is deliberately at the **pullback** spelling rather than at `baseChangeField`:
`baseChangeField` is semireducible, so a goal phrased through it is not type-correct at
`instances` transparency and `rw [pullback.condition]` reports "did not find an occurrence" on a
goal that visibly contains the pattern. Stating it at the pullback and letting the caller's
`obtain` supply the section is what makes the proof two lines instead of a transport. -/

/-- **A section of the base change is a point over the extension field.** For `κ/k` any field
extension and `σ` a section of `pullback.snd C.hom (Spec.map (algebraMap k κ))` — i.e. a
`Scheme.HasRationalPoint` witness for `Scheme.baseChangeField C κ` — the composite
`σ ≫ pullback.fst` is a `κ`-point of `C` lying over `Spec.map (algebraMap k κ)`.

Pure pullback bookkeeping: `pullback.condition` swaps the two legs and the section equation
cancels. No finiteness, no separability, no curve hypothesis. -/
theorem hasRationalPoint_baseChangeField_of_pullbackSection {k κ : Type u} [Field k] [Field κ]
    [Algebra k κ] (C : Over (Spec (CommRingCat.of k)))
    (σ : Spec (CommRingCat.of κ) ⟶
      Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))))
    (hσ : σ ≫ Limits.pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ))) = 𝟙 _) :
    (σ ≫ Limits.pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k κ)))) ≫ C.hom
      = Spec.map (CommRingCat.ofHom (algebraMap k κ)) := by
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hσ, Category.id_comp]

/-! ## §2. Separable to Galois: the normal closure

The sibling file produces a finite **separable** level `k'`. Its normal closure `k''` inside `k^s`
is finite over `k` and Galois, and contains `k'`, so the point pushes up the inclusion. The three
facts are mathlib instances; the push-up is one triangle. -/

/-- **The section at a finite GALOIS level.** For a smooth curve `C` over an arbitrary field `k`
and a `k^s`-point of `C` over `k`, there is a finite **Galois** `k''/k` inside `k^s` such that the
base-changed curve `C_{k''}` has a `k''`-rational point.

This is what campaign `G1` consumes: `G2`'s quotient engine takes a semilinear
`Gal(k''/k)`-action, and `[IsGalois k k'']` is the hypothesis that makes that group the right one.
`exists_finiteSeparable_level_hasRationalPoint` supplies a finite *separable* level only, which
is one hypothesis short.

`k''` is `IntermediateField.normalClosure k k' (SeparableClosure k)` for the `k'` the sibling
file produces. `FiniteDimensional k k''` is `normalClosure.is_finiteDimensional`, `IsGalois k k''`
is `IsGalois.normalClosure` (available because `SeparableClosure k` is normal over `k`), and
`k' ≤ k''` is `IntermediateField.le_normalClosure`; the point is transported along
`IntermediateField.inclusion` and the two base triangles agree by `Spec.map_comp`.

**The curve binder is stronger than this proof needs, measured.** `[SmoothOfRelativeDimension 1]`
is carried here only so that §3 and the sibling file's `level_factorization_of_curve` line up on
one spelling. The argument itself runs at `[LocallyOfFiniteType C.hom]`: substituting it and going
through `exists_finiteSeparable_level_factorization` directly closes the same goal (`lake env lean`
EXIT=0), while dropping every finiteness binder makes the first step fail to synthesise (control,
both ways in one probe). So this is a statement about locally-finite-type `k`-schemes wearing a
curve's clothes, and a consumer that only has finite type may use
`Scheme.exists_finiteGalois_level_hasRationalPoint_of_locallyOfFiniteType` below instead.

Note the conclusion does **not** carry `Algebra.IsSeparable k k''`: it is true (a Galois extension
is separable) but no consumer of a `Gal`-action needs it stated, and `IsGalois` already implies it
by `IsGalois.to_isSeparable`. -/
theorem exists_finiteGalois_level_hasRationalPoint_of_locallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType C.hom]
    (p : Spec (CommRingCat.of (SeparableClosure k)) ⟶ C.left)
    (hp : p ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))) :
    ∃ (k'' : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k k'')
      (_ : IsGalois k k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField C k'') := by
  obtain ⟨k', hfd, hsep, q, hq⟩ :=
    Scheme.exists_finiteSeparable_level_factorization C.hom p hp
  have hqf : q ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k k')) :=
    Scheme.comp_eq_specMap_algebraMap_of_factorization C.hom p hp k' q hq
  have hle : k' ≤ IntermediateField.normalClosure k k' (SeparableClosure k) :=
    IntermediateField.le_normalClosure k'
  refine ⟨IntermediateField.normalClosure k k' (SeparableClosure k), inferInstance, inferInstance,
    Scheme.hasRationalPoint_baseChangeField_of_comp_eq C _
      (Spec.map (CommRingCat.ofHom ((IntermediateField.inclusion hle).toRingHom)) ≫ q) ?_⟩
  rw [Category.assoc, hqf, ← Spec.map_comp]
  congr 1

/-- The curve-shaped form, at the spelling §3 and the sibling file use. `LocallyOfFiniteType`
follows from `[SmoothOfRelativeDimension 1 C.hom]` by synthesis, so this is the general theorem
above with no work — recorded because every consumer in this project carries the smooth binder. -/
theorem exists_finiteGalois_level_hasRationalPoint {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    (p : Spec (CommRingCat.of (SeparableClosure k)) ⟶ C.left)
    (hp : p ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))) :
    ∃ (k'' : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k k'')
      (_ : IsGalois k k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField C k'') :=
  exists_finiteGalois_level_hasRationalPoint_of_locallyOfFiniteType C p hp

/-! ## §3. The antecedent is discharged: the unconditional form

§2 still takes a `k^s`-point as a hypothesis. It need not: `Curve/SeparablyClosedRationalPoint.lean`
**produces** one for every curve satisfying the headline's binders, and §1 converts
its section into exactly the `hp` §2 wants. So the conclusion holds with no antecedent beyond the
curve hypotheses — which is what makes it a theorem about curves rather than an implication. -/

/-- **The unconditional form — no antecedent, no hypothesis on `C(k)`.** For a smooth
geometrically irreducible curve `C` over an *arbitrary* field `k`, there is a finite **Galois**
`k''/k` with `Scheme.HasRationalPoint (Scheme.baseChangeField C k'')`.

Every antecedent of §2 is witnessed here rather than assumed:
`hasRationalPoint_baseChangeField_separableClosure_of_geometricallyIrreducible` produces the
`k^s`-section from `[SmoothOfRelativeDimension 1 C.hom]` and `[GeometricallyIrreducible C.hom]`
alone, and §1 turns it into the over-`Spec k` equation. `GeometricallyIrreducible` is the binder
the headline `picardJacobianWitness` (`AlgebraicJacobian/Jacobian.lean:840`) actually carries, so
a consumer needs no bridging instance — and this file needs one binder *fewer* than the headline,
which also carries `[IsProper C.hom]`. (Four sibling files, including the seam
`Picard/FGAPicRepresentability.lean:345`, attribute this binder to
`AlgebraicJacobian/Challenge.lean`. **There is no such file in this project** — `find` returns
nothing and `RiemannRoch/Ledger/ChiCurve.lean:11` already says so — and the correct site is
`Jacobian.lean:840`. Filed as `I-1373`. An earlier revision of this file said the dead pointer
"is not repeated here" and then repeated it three times below; the audit that caught that is
`I-1375`.)

There is **no** `[HasRationalPoint C]`, and there must not be (`I-0491`): the point exists only
after the separable base extension. -/
theorem exists_finiteGalois_level_hasRationalPoint_of_geometricallyIrreducible {k : Type u}
    [Field k] (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] :
    ∃ (k'' : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k k'')
      (_ : IsGalois k k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField C k'') := by
  obtain ⟨⟨σ, hσ⟩⟩ :=
    (Scheme.hasRationalPoint_baseChangeField_separableClosure_of_geometricallyIrreducible
      C).nonempty_section
  exact exists_finiteGalois_level_hasRationalPoint C _
    (hasRationalPoint_baseChangeField_of_pullbackSection C σ hσ)

/-- The same, at the `GeometricallyIntegral` spelling. Both spellings have callers in this
project (`GeometricallyIntegral` is what `FGAPicRepresentability.lean`'s classes bind,
`GeometricallyIrreducible` what the headline `picardJacobianWitness` does), so both are recorded
rather than one being left to a bridging instance the caller has to find. -/
theorem exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral {k : Type u}
    [Field k] (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIntegral C.hom] :
    ∃ (k'' : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k k'')
      (_ : IsGalois k k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField C k'') := by
  obtain ⟨⟨σ, hσ⟩⟩ :=
    (Scheme.hasRationalPoint_baseChangeField_separableClosure C).nonempty_section
  exact exists_finiteGalois_level_hasRationalPoint C _
    (hasRationalPoint_baseChangeField_of_pullbackSection C σ hσ)

end AlgebraicGeometry.Scheme

/-! ## §4. Non-vacuity, compiler-checked rather than asserted

Two ways §3 could have been true-about-nothing, both refuted here by a declaration rather than by
a docstring sentence.

* The binder set could have been empty. It is not: it is satisfied **at the headline's own
  hypotheses with nothing added** — indeed with one binder *fewer*, since the headline also carries
  `[IsProper C.hom]` and §3 does not use it (`galoisLevel_at_headline_binders`).

  **This one is a real guard, and an earlier revision's was not.** A fresh-context audit
  (`I-1375`) found that the first version of this section merely *retyped* the headline's binder
  list: `picardJacobianWitness` was an unknown identifier in this file's import closure, so nothing
  linked the two and a drift in the headline's binders would have broken no build, under a section
  heading promising "compiler-checked rather than asserted". Fixed by importing
  `AlgebraicJacobian.Jacobian` and taking a hypothesis whose *type* is
  `Nonempty (AlgebraicGeometry.JacobianWitness C)` — that type is only well-formed under the
  headline's own binders (control: dropping `[IsProper C.hom]` makes it fail to synthesise), so
  the link is now checked. The hypothesis is **not** used in the proof and must not be: the
  headline `picardJacobianWitness` is `sorryAx`-reachable (measured), so putting its *term* in a
  proof here would contaminate this file. A binder mentioning its type does not.
* The binder set could have been inhabited only by variables. It is not: `ℙ¹` over `ℚ` is a
  concrete object of the domain and the conclusion holds for it
  (`galoisLevel_p1Over_rat`). `ℚ` is chosen because it is *not* separably closed, so this is not
  the degenerate case `k^s = k` where every level is `k` — though note that inference is about
  this one field, not about the domain as a whole: getting from `¬ IsSepClosed k` to `k^s ≠ k` in
  general needs a converse this project does not have (`I-1310`), and no such general claim is
  made here.
-/

namespace AlgebraicJacobian.NonVacuity

open AlgebraicGeometry.Adelic

/-- **Non-vacuity 1: the headline's binders suffice, with one to spare.** The conclusion of §3
holds for every curve satisfying the hypotheses of `AlgebraicGeometry.picardJacobianWitness`
(`AlgebraicJacobian/Jacobian.lean:840`), with no hypothesis added — and `[IsProper C.hom]`, which
the headline carries, is present here only to make the match visible; the proof does not use it.

The `_hw` binder is what makes this a **checked** match rather than a retyped one: the type
`AlgebraicGeometry.JacobianWitness C` is well-formed only under the headline's own binder set, so
if that set drifts this declaration stops elaborating. It is deliberately unused in the proof —
`picardJacobianWitness` is `sorryAx`-reachable, so its term must not enter a proof here, and
`Nonempty` of its type is a `Prop` that costs nothing. -/
theorem galoisLevel_at_headline_binders {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (_hw : Nonempty (AlgebraicGeometry.JacobianWitness C)) :
    ∃ (k'' : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k k'')
      (_ : IsGalois k k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField C k'') :=
  Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIrreducible C

/-- **Non-vacuity 2: a concrete inhabitant.** `ℙ¹` over `ℚ` satisfies the binders and the
conclusion holds for it, so §3 is not a statement about an empty class of curves. -/
theorem galoisLevel_p1Over_rat :
    ∃ (k'' : IntermediateField ℚ (SeparableClosure ℚ)) (_ : FiniteDimensional ℚ k'')
      (_ : IsGalois ℚ k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField (p1Over ℚ) k'') :=
  Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIntegral (p1Over ℚ)

end AlgebraicJacobian.NonVacuity

/-! ## §5. Why the Galois hypothesis is the point: composing with the `G2` quotient engine

§3's whole advance over `Curve/FiniteLevelRationalPoint.lean` is `[IsGalois k k'']` rather than
`Algebra.IsSeparable k k'`. That is worth a *declaration* rather than a docstring claim, because
"the stronger hypothesis is the one the consumer wants" is exactly the sentence a costing gets
wrong. `G2`'s quotient engine takes a `SemilinearGalAction K L X f`, whose group is `L ≃ₐ[K] L`,
and its discharge `hasGaloisQuotient_of_isAffine` binds `[FiniteDimensional K L] [IsGalois K L]` —
both of which §3 now supplies at a level a curve over an arbitrary field actually reaches.

**Read the scope of §5 precisely.** It composes §3 with the **affine** half of `G2`, which is the
half that is proved (`GaloisQuotientAffineGeneral.lean`). The campaign's actual consumer `J'_r` is
a *glued* scheme, hence non-affine, and the gate there is open — `G2(c)`, the `Scheme.GlueData`
assembly, with the Hironaka trap. So §5 is evidence that the Galois strengthening reaches a real
engine, **not** evidence that `G2` is closed. And it is still the existential level of §3: the
quotient clause is universally quantified over affine `X` *at that* `k''`.
-/

namespace AlgebraicJacobian.GaloisLevel

open AlgebraicJacobian.GaloisDescent

/-- **The Galois level reaches `G2`'s quotient engine.** For a smooth geometrically irreducible
curve over an arbitrary field `k` there is a finite Galois level `k''/k` which simultaneously
carries a rational point for `C_{k''}` and admits a Galois quotient for *every* semilinear
`Gal(k''/k)`-action on an **affine** `k''`-scheme.

The second conjunct is `exists_isGaloisQuotient_of_isAffine`, whose `[FiniteDimensional k k'']` and
`[IsGalois k k'']` binders are precisely what §3 delivers and what the finite *separable* level of
the sibling file does not: over a non-Galois `k'`, `k' ≃ₐ[k] k'` is the wrong group and the action
type is not the campaign's.

Axiom-clean, and note what that means here: the affine half of `G2` is genuinely proved, so this
composite does not pass through the seam. The **non-affine** case is untouched and is `G2(c)`. -/
theorem exists_level_with_point_and_affineQuotients {k : Type u} [Field k]
    (C : Over (Spec (CommRingCat.of k))) [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] :
    ∃ (k'' : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k k'')
      (_ : IsGalois k k''),
      Scheme.HasRationalPoint (Scheme.baseChangeField C k'') ∧
      ∀ (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (CommRingCat.of (k'' : Type u)))
        (ρ : SemilinearGalAction k (k'' : Type u) X f),
        ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of k)), IsGaloisQuotient ρ g := by
  obtain ⟨k'', hfd, hgal, hpt⟩ :=
    Scheme.exists_finiteGalois_level_hasRationalPoint_of_geometricallyIrreducible C
  letI := hfd
  letI := hgal
  refine ⟨k'', hfd, hgal, hpt, ?_⟩
  intro X _ f ρ
  exact exists_isGaloisQuotient_of_isAffine ρ

end AlgebraicJacobian.GaloisLevel
