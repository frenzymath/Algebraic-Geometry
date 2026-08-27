/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0AbelianVariety

/-!
# Universal closedness is incompatible with an infinite disjoint cover

## Why this file exists: a landed reduction of this project reduced nothing

`Picard/Pic0AbelianVariety.lean` carries two theorems that move properness of
`Pic⁰_{C/k}` onto the **ambient** Picard scheme:

* `Pic0.universallyClosed_of_ambient` — `UniversallyClosed (PicScheme C).hom`
  implies `UniversallyClosed (Pic0Scheme C).hom`, because `Pic⁰ ↪ Pic` is a
  *closed* immersion;
* `Pic0.proper_of_ambient_universallyClosed` — hence properness of `Pic⁰`.

Both are true, sorry-free and axiom-clean, and the roadmap row
`AJC.pic0av.structure` recommended that route as "a SECOND, INDEPENDENT reduction
… worth trying first", on the reading that Kleiman §5 Thm.~`th:qpp&p` is a
theorem about `Pic_{C/k}` and so the ambient object is where the argument lives.

**The hypothesis those two theorems consume cannot hold.** `UniversallyClosed` is
strictly stronger than one expects over an affine base: mathlib derives
`QuasiCompact` from it (`Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean`,
the `priority := 900` instance — this is exactly *why* `IsProper` has only three
fields and omits quasi-compactness), and `Spec R` is a compact space, so
`QuasiCompact.compactSpace_of_compactSpace` upgrades it to `CompactSpace X`.

But `Pic_{C/k}` is a **disjoint union over `deg ∈ ℤ`** — that is the second clause
of Kleiman §4 Thm.~`th:main`(1), the very clause `HasPicScheme` bundles ("a
disjoint union of open quasi-projective `k`-subschemes"). An infinite family of
pairwise disjoint nonempty opens covering a space has no finite subcover. So
`Pic_{C/k}` is not quasi-compact, hence not universally closed, and
`universallyClosed_of_ambient` is an instance of **trap (c)**: a `P → Q` whose
antecedent is unsatisfiable in the intended setting. It passes every axiom probe
and every `sorry` census, because it is a theorem.

## What this file adds, and what survives

The three results below are the general statements, at scheme generality and with
no Picard vocabulary, that make the refutation checkable rather than argued:

* `not_compactSpace_of_infinite_disjoint_open_cover` — pure topology.
* `Scheme.compactSpace_of_universallyClosed` — the mathlib chain, as one name.
* `Scheme.not_universallyClosed_of_infinite_disjoint_open_cover` — the two
  composed: a scheme with an infinite disjoint open cover is not universally
  closed over an affine base.

`Scheme.not_isProper_of_infinite_disjoint_open_cover` records the same conclusion
for `IsProper`, since `UniversallyClosed` is one of its fields.

**What survives untouched.** The properness route through `Pic⁰` *itself*:
`Pic0.proper_of_valuativeCriterion` and
`Pic0.universallyClosed_of_valuativeCriterion` quantify over
`(Pic0Scheme C).hom`, whose source **is** quasi-compact (`Pic0.quasiCompact`,
landed run 0009 from Kleiman §5 Lem.~`lem:agps`(3)), so nothing here touches
them. The same holds for `Pic0.universallyClosed_of_baseChange`: base change to
`k̄` does not leave the identity component. What the roadmap called the fallback
was in fact the only route, and the "second, independent reduction" was never a
reduction.

Note this says nothing against `Pic0.universallyClosed_of_ambient` as a
*theorem*, and it is retained: if some future development produces a single
`Pic^d` or a finite union as the ambient object, the closed-immersion transport
is exactly right. It is the *satisfiability* at `PicScheme C` that fails.
-/

universe u v

open AlgebraicGeometry CategoryTheory Set

/-- **An infinite disjoint open cover obstructs compactness.** If a space is
covered by an infinite family of pairwise disjoint *nonempty* opens, it is not
compact: a finite subcover omits some index `j`, and any point of `U j` then lies
in some `U i` with `i ≠ j`, contradicting disjointness.

Nonemptiness is essential (an infinite family of copies of `∅` covers nothing and
obstructs nothing), and so is disjointness — without it a finite subfamily can
perfectly well cover. -/
theorem not_compactSpace_of_infinite_disjoint_open_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Infinite ι]
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hdisj : Pairwise (Function.onFun Disjoint U))
    (hcov : (univ : Set X) ⊆ ⋃ i, U i) :
    ¬ CompactSpace X := by
  intro _
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover U hopen hcov
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset t
  obtain ⟨x, hx⟩ := hne j
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact (hdisj (fun hh : i = j => hj (hh ▸ hi))).le_bot ⟨hxi, hx⟩

namespace AlgebraicGeometry.Scheme

/-- **Universal closedness over an affine base forces a compact space.**

The chain, all mathlib: `UniversallyClosed f` gives `QuasiCompact f` (the
`priority := 900` instance of `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean`
— the reason `IsProper` omits a quasi-compactness field), `Spec R` is a compact
space (`PrimeSpectrum.compactSpace`), and a quasi-compact morphism to a compact
base has compact source (`QuasiCompact.compactSpace_of_compactSpace`).

Stated as its own name because the implication is easy to miss and it is what
refutes the ambient-Picard properness route: `UniversallyClosed` is *not* merely
"closed under all base changes", it carries finiteness of the source. -/
theorem compactSpace_of_universallyClosed {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [UniversallyClosed f] : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f

/-- **A scheme with an infinite disjoint open cover is not universally closed over
an affine base.** Composite of `compactSpace_of_universallyClosed` with
`not_compactSpace_of_infinite_disjoint_open_cover`.

This is the checkable form of the refutation described in this file's header: it
applies to `Pic_{C/k}`, whose decomposition into the degree pieces `Pic^d` for
`d ∈ ℤ` is a cover of exactly this shape (Kleiman §4 Thm.~`th:main`(1)). Supplying
that decomposition as an actual `ℤ`-indexed family of opens is a separate
obligation, and this project does **not** have it: it has the degree map
(`PicScheme.degree`) but no fibrewise decomposition of the *scheme*. So this file
deliberately stops at the general statement and does not assert the instance at
`PicScheme C`; what it establishes is that the ambient route is
unsatisfiable-in-principle, which is enough to retract it as a reduction. -/
theorem not_universallyClosed_of_infinite_disjoint_open_cover
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {ι : Type v} [Infinite ι] (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hdisj : Pairwise (Function.onFun Disjoint U))
    (hcov : (univ : Set X) ⊆ ⋃ i, U i) :
    ¬ UniversallyClosed f := fun _ =>
  not_compactSpace_of_infinite_disjoint_open_cover U hopen hne hdisj hcov
    (compactSpace_of_universallyClosed f)

/-- **The same obstruction for `IsProper`.** `UniversallyClosed` is a field of
`IsProper` (`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`), so a scheme with
an infinite disjoint open cover is not proper over an affine base either — no
separatedness or finite-type input is used. -/
theorem not_isProper_of_infinite_disjoint_open_cover
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {ι : Type v} [Infinite ι] (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hdisj : Pairwise (Function.onFun Disjoint U))
    (hcov : (univ : Set X) ⊆ ⋃ i, U i) :
    ¬ IsProper f := fun h =>
  not_universallyClosed_of_infinite_disjoint_open_cover f U hopen hne hdisj hcov
    h.toUniversallyClosed

end AlgebraicGeometry.Scheme
