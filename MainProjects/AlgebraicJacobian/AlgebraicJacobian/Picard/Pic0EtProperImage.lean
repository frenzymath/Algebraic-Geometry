/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.Pic0EtStructure

/-!
# Headline obligation 3: four spellings of one transfer lemma, and why none of
# them reduces it

Headline obligation 3 is `Scheme.Pic0Et.universallyClosed` (`Picard/Pic0Et.lean:228`,
a bare `sorry`): universal closedness of `Pic⁰_{C/k}` over an arbitrary base field.
`Picard/Pic0EtStructure.lean` reduced properness to that single residue and proved
three of its formulations equivalent (`valuativeCriterion_existence_iff_universallyClosed`),
recording the **topological** `SpecializingMap` route as a genuinely different
attack that was never costed.

This file was written to cost that route. **The answer is negative on every count,
and the negative results are the content.** A first revision of this header claimed
§1 as a gain; a fresh-context audit refuted both of its claims and the claims are
replaced here rather than hedged (`I-1199`, `I-1200`, `I-1201`).

## 1. The topological route stays uncosted, because the factor I freed is a
## CONSEQUENCE of the obligation

`specializingMap` proves `SpecializingMap` of `(Pic⁰_{C/k}).hom`'s underlying map
unconditionally, because the base `Spec k` is a one-point space. That is true and
it is nearly free.

**It localises nothing, and the first revision of this header had the implication
backwards.** `MorphismProperty.universally_le : P.universally ≤ P` says the
un-quantified factor *follows from* `ValuativeCriterion.Existence`, so proving it
free removes no part of the obligation. Machine-checked: `SpecializingMap f.base`
follows from `ValuativeCriterion.Existence f` for an **arbitrary** scheme
morphism, with no one-point base anywhere. And no consumer wanted it — mathlib's
`ValuativeCriterion.Existence.of_specializingMap`, already wired at
`Pic0EtStructure.lean:387`, takes the `universally` form as its hypothesis.
`specializingMap` is a convenience name for a triviality, nothing more.

`compactSpace` is likewise **not new information**: over an affine base
`CompactSpace ↥X` and `QuasiCompact f` are interderivable in one mathlib lemma each
way (`HasAffineProperty.iff_of_isAffine`), and `QuasiCompact` was already landed as
`Pic0EtStructure.lean:189`. By the rule this file applies to §2 below, that makes it
a renaming of a landed fact. A name search missed it only because the other
spelling is the one in the tree.

The claim that it "makes the ambient refutation's escape compiler-checked" is also
withdrawn: `Picard/AmbientPicNotProper.lean`'s theorems turn on an **infinite
disjoint open cover**, not on compactness, and that file says at `:136` that the
project does not have the cover, so the refutation is never instantiated at any
Picard object. The refuted route is on the legacy `picSharp` tower under the
instance-free `[HasPicScheme C]`; there was no étale-side ambient route to escape,
and `Pic0EtStructure.lean:288-292` had already written the escape in Lean.

## 2–3. Sections 2 and 3 are ONE lemma in FOUR spellings

All four of the following are `UniversallyClosed.of_comp_surjective` (plus, for two
of them, `ValuativeCriterion.Existence.eq`) at the étale identity component, and
each collapses existentially by the **identity** witness as soon as `Pic⁰` is
universally closed. Two are shipped with their converses; the audit supplied the
third and fourth collapse. None is a reduction, and none may be reported as
progress:

* `universallyClosed_of_universally_specializing` /
  `universally_specializing_of_universallyClosed` — the arbitrary-base-change form;
* `universallyClosed_of_proper_cover` / `exists_proper_cover_of_universallyClosed`
  — "some proper `k`-scheme surjects onto `Pic⁰`";
* `universallyClosed_of_surjective_source`, `proper_of_surjective_source` — the
  named-cover forms. A first revision claimed the explicit cover argument is what
  keeps these from collapsing. It is not: the existential closure of *these* also
  closes with the identity, and §2's cover is an explicit argument in the same
  position. The only difference between §2 and §3 is existential versus
  non-existential phrasing.

Both pairs in §2 were additionally derivable from `Pic0EtStructure` in three or
four lines each. They are kept as named entry points, not as results.

## What the named-cover interface is waiting on (corrected)

The intended source for §3 is Kleiman's Abel map `Div^d_{C/k} → Pic^d_{C/k}`.
`Scheme.abelMapWitness` (`Picard/FGAPicRepresentability.lean:950`) is a natural
transformation of *functors*, `divFunctor C ⟶ picSharp C`; promoting it to a
morphism of schemes needs representability of `Div^d`.

A first revision attributed that to "the Quot input the board marks `rejected`".
**Wrong, and it re-introduced an error `FGAPicRepresentability.lean:371-390` was
written to correct**: `Div^d` representability goes through the **Grassmannian**,
not Quot, and the live rows are `AJC.picrep.divgrassmannian` (active) and
`AJC.picrep.divlocallyclosed` (pending). So the interface waits on open-but-live
work, not on a rejected route — a real handoff.

## Honest accounting

`Pic0Et.universallyClosed` is **untouched**; nothing here witnesses it for any
curve, and this file makes no progress towards it. Every declaration binds
`[HasPicSchemeEt C]`, whose instance projects the seam `sorry`
`fgaPicardRepresentability`, so all of it is sorry-*reachable* on instantiation
even though the file adds no `sorry`. The residue is bounding the **base-changed**
maps `Pic⁰ ×_k T → T`, and neither this file nor `Pic0EtStructure.lean` touches
that.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Pic0Et

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIntegral C.hom] [HasPicSchemeEt C]

/-! ### §1. Two facts that are free — and are not gains -/

/-- **`Pic⁰_{C/k}` has a compact underlying space**, from the already-proved
`Pic0Et.quasiCompact` (`Pic0EtStructure.lean:189`) plus compactness of `Spec k`.

**This is a renaming of that landed fact, not new information.** Over an affine
base the two are interderivable in one mathlib lemma each way: the converse is
`HasAffineProperty.iff_of_isAffine.mpr (compactSpace C) : QuasiCompact _`,
machine-checked. Kept as a convenience spelling for consumers that want the
topological form.

**Two claims about this theorem are WITHDRAWN** (refuted by a fresh-context audit,
`I-1199`; the wording is replaced rather than hedged). It does *not* make
`Picard/AmbientPicNotProper.lean`'s escape compiler-checked: that file's theorems
turn on an **infinite disjoint open cover**, not on compactness, it says at `:136`
that the project does not have such a cover, and the route it refutes is on the
legacy `picSharp` tower under the instance-free `[HasPicScheme C]`. There was no
étale-side ambient route to escape, and `Pic0EtStructure.lean:288-292` had already
written the escape in Lean. -/
theorem compactSpace : CompactSpace (Pic0SchemeEt C).left := by
  haveI := quasiCompact C
  exact QuasiCompact.compactSpace_of_compactSpace (Pic0SchemeEt C).hom

/-- **Specialization-lifting for `Pic⁰_{C/k} → Spec k` is free**, because the base
is a one-point space.

Every specialization `x ⤳ y` in `Spec k` is trivial (`Subsingleton ↥(Spec k)`), so
the given point lifts itself. No hypothesis on `C` is used beyond what names the
object.

**IT LOCALISES NOTHING, and a first revision of this docstring had the implication
backwards** (refuted by a fresh-context audit, `I-1200`). That revision argued: since
`ValuativeCriterion.Existence = (topologically @SpecializingMap).universally`, and
this factor is free, the whole obligation must live in the `universally`. But
`MorphismProperty.universally_le : P.universally ≤ P` says this factor is a
**consequence** of the obligation, so proving it free removes nothing. Two
confirmations, both machine-checked: `SpecializingMap f.base` follows from
`ValuativeCriterion.Existence f` for an **arbitrary** scheme morphism, with no
one-point base anywhere; and no consumer wanted the un-quantified factor, since
`ValuativeCriterion.Existence.of_specializingMap` — already wired at
`Pic0EtStructure.lean:387` — takes the `universally` form as its hypothesis.

So the topological route recorded as uncosted at `Pic0EtStructure.lean:387`
**remains uncosted**. This theorem is a convenience name for a triviality. -/
theorem specializingMap : SpecializingMap (Pic0SchemeEt C).hom.base := by
  intro x y _
  exact ⟨x, specializes_rfl, Subsingleton.elim _ _⟩

/-- The `MorphismProperty` spelling of `specializingMap`, for composing with
mathlib's `universally` API. -/
theorem topologically_specializingMap :
    (topologically @SpecializingMap) (Pic0SchemeEt C).hom :=
  specializingMap C

/-! ### §2. Two renamings, each with its converse -/

/-- Universal closedness from specialization-lifting on **every** base change.

This is `ValuativeCriterion.Existence.eq` composed with the free `QuasiCompact`
(`Pic0Et.quasiCompact`), so it needs no valuation rings. It is **not** a
reduction — see `universally_specializing_of_universallyClosed` for the converse,
which makes the pair an equivalence. -/
theorem universallyClosed_of_universally_specializing
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Spec (.of k)),
      SpecializingMap (pullback.fst g (Pic0SchemeEt C).hom).base) :
    UniversallyClosed (Pic0SchemeEt C).hom := by
  haveI := quasiCompact C
  refine UniversallyClosed.of_valuativeCriterion _ ?_
  rw [ValuativeCriterion.Existence.eq]
  exact MorphismProperty.universally_mk' _ _ (fun {T} g _ => h g)

/-- **The converse**: universal closedness gives specialization-lifting back on
every base change, so the hypothesis of
`universallyClosed_of_universally_specializing` is *equivalent* to the conclusion
and that lemma is a change of vocabulary, not a discharge of anything. -/
theorem universally_specializing_of_universallyClosed
    (h : UniversallyClosed (Pic0SchemeEt C).hom)
    {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) :
    SpecializingMap (pullback.fst g (Pic0SchemeEt C).hom).base := by
  haveI := h
  haveI hpb : UniversallyClosed (pullback.fst g (Pic0SchemeEt C).hom) := inferInstance
  have hcm : IsClosedMap (pullback.fst g (Pic0SchemeEt C).hom).base :=
    MorphismProperty.universally_le (topologically @IsClosedMap) _
      (universallyClosed_eq ▸ hpb)
  exact hcm.specializingMap

/-- Universal closedness from a proper `k`-scheme surjecting onto `Pic⁰` over `k`.

Sound, and **not** a reduction in its existential form: see
`exists_proper_cover_of_universallyClosed`, where the identity supplies the cover
as soon as `Pic⁰` is universally closed.

It is also `universallyClosed_of_surjective_source` (§3) plus `rw [hover]`, and §3
collapses existentially by the same identity witness — so "useful only with a
*named* source, which is what §3 is for" (a first revision) does not distinguish
them either. All four spellings in §2–§3 are one transfer lemma (`I-1201`). -/
theorem universallyClosed_of_proper_cover
    {W : Over (Spec (.of k))} [IsProper W.hom]
    (a : W.left ⟶ (Pic0SchemeEt C).left)
    (hsurj : Surjective a)
    (hover : a ≫ (Pic0SchemeEt C).hom = W.hom) :
    UniversallyClosed (Pic0SchemeEt C).hom := by
  haveI := hsurj
  haveI : UniversallyClosed (a ≫ (Pic0SchemeEt C).hom) := by
    rw [hover]; infer_instance
  exact UniversallyClosed.of_comp_surjective a (Pic0SchemeEt C).hom

/-- **The converse, and the reason the existential proper-cover form must not be
reported as progress**: if `Pic⁰` is universally closed then it is itself proper
(its other two conjuncts are theorems), so the **identity** is a proper surjection
onto it. Hence "there exists a proper cover" is *equivalent* to obligation 3. -/
theorem exists_proper_cover_of_universallyClosed
    (h : UniversallyClosed (Pic0SchemeEt C).hom) :
    ∃ (W : Over (Spec (.of k))) (_ : IsProper W.hom)
      (a : W.left ⟶ (Pic0SchemeEt C).left), Surjective a ∧
        a ≫ (Pic0SchemeEt C).hom = W.hom := by
  haveI := h
  haveI := isSeparated C
  haveI := locallyOfFiniteType C
  exact ⟨Pic0SchemeEt C, ⟨⟩, 𝟙 _, inferInstance, Category.id_comp _⟩

/-! ### §3. The named-cover interface (waiting on `Div^d` representability) -/

/-- **Transfer of universal closedness along a named surjection onto `Pic⁰`.**

Mathlib's `UniversallyClosed.of_comp_surjective`, instantiated at the étale
identity component.

**A first revision claimed this "does not collapse, unlike §2's existential form,
because the cover `a` is an explicit argument". That is false** (`I-1201`): the
existential closure of *this* lemma also closes with the identity witness, and
§2's cover is an explicit argument in the same position. §2 and §3 differ only in
existential versus non-existential phrasing; all four spellings are one transfer
lemma and none is a reduction.

The intended `a` is Kleiman's Abel map `Div^d_{C/k} → Pic^d_{C/k}`, which is **not
available at HEAD**: `Scheme.abelMapWitness` (`FGAPicRepresentability.lean:950`) is
a natural transformation of functors (`divFunctor C ⟶ picSharp C`), and promoting it
to a scheme morphism requires representability of `Div^d`. That representability
goes through the **Grassmannian**, not Quot — the same revision wrote "the Quot
input the board marks `rejected`", re-introducing the error
`FGAPicRepresentability.lean:371-390` exists to correct. The live rows are
`AJC.picrep.divgrassmannian` (active) and `AJC.picrep.divlocallyclosed` (pending),
so this interface waits on open work rather than on a rejected route. -/
theorem universallyClosed_of_surjective_source
    {W : Scheme.{u}} (a : W ⟶ (Pic0SchemeEt C).left)
    (hsurj : Surjective a)
    (huc : UniversallyClosed (a ≫ (Pic0SchemeEt C).hom)) :
    UniversallyClosed (Pic0SchemeEt C).hom :=
  UniversallyClosed.of_comp_surjective a (Pic0SchemeEt C).hom

/-- Properness of `Pic⁰` from a named surjection with universally closed
composite: the other two conjuncts of `IsProper` are `Pic0Et.isSeparated` and
`Pic0Et.locallyOfFiniteType`, both theorems, so the cover supplies **two** things
and neither is free — universal closedness of the composite *and* surjectivity of
`a`. (A first revision said "the cover only has to supply universal closedness",
which drops the `hsurj` binder a consumer must also discharge; corrected per
`I-1201`.) -/
theorem proper_of_surjective_source
    {W : Scheme.{u}} (a : W ⟶ (Pic0SchemeEt C).left)
    (hsurj : Surjective a)
    (huc : UniversallyClosed (a ≫ (Pic0SchemeEt C).hom)) :
    IsProper (Pic0SchemeEt C).hom := by
  haveI := hsurj
  haveI := huc
  haveI : IsSeparated (Pic0SchemeEt C).hom := isSeparated C
  haveI : LocallyOfFiniteType (Pic0SchemeEt C).hom := locallyOfFiniteType C
  haveI : UniversallyClosed (Pic0SchemeEt C).hom :=
    UniversallyClosed.of_comp_surjective a (Pic0SchemeEt C).hom
  constructor

end AlgebraicGeometry.Scheme.Pic0Et
