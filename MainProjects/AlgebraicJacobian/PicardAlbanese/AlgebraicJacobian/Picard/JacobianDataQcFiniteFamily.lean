/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataQcFromRep

/-!
# DAT-J's `quasiCompact` field from a FINITE FAMILY of carriers

`Picard/JacobianDataQcFromRep.lean` reduces DAT-J's `quasiCompact` field to one statement,
`hcl`: *every point of the representing object has its class pulled back from a fixed
degree-zero class `lam` along some field point of `divSchemeOver …`*.  That statement is
**single-carrier**: one divisor scheme, one class, quantified before the point.

**QUALIFIER, and it is not optional** (audit `I-1436`; ajcr-p3's `I-1430`): `hcl` is the route to
the `quasiCompact` field **at an infinite atlas**.  At a *finite* atlas that field is discharged
outright by `quasiCompact_jacobianDataOfFiniteMixedParamCharts`
(`Picard/Pic0AtlasCompactNoetherian.lean`) with no `hcl`, no Abel morphism, and — the
`IsLocallySurjective` binder there being idle — not even DAT-B coverage.  Any sentence in this
file reading "the qc field has no producer" is to be read with "at an infinite atlas" attached.
The class-indexed atlas the tree plans to build is the infinite one, which is why `hcl` is still
the live route.

The heterogeneous atlas the tree actually plans to build is not single-carrier.
`mixedParamChart` (`Picard/Pic0ChartAtlasParamFree.lean`) carries a *per-index* parameter
`nn i` with its own representing object `D i`, precisely so that different points may use
different charts — `Pic0ChartCoveragePointwise.lean` says so in as many words, and
ajcr-p4's `I-1389` records that collapsing the atlas to a single index asks for something
**stronger** than DAT-B coverage rather than weaker.  So `hcl` as stated is not the shape a
heterogeneous atlas can supply, and a producer trying to satisfy it would first have to
prove single-chart coverage, which this project expects to be false.

This file removes that mismatch.  The quasi-compactness argument never needed one carrier:

* `AlgebraicGeometry.compactSpace_of_finite_family_surjective` — if every point of `Y` is
  hit by one of **finitely many** morphisms out of compact sources, `Y` is compact.  Pure
  topology, no schemes-specific input beyond continuity.
* `AlgebraicGeometry.quasiCompact_of_finite_family_pic0_class` — hence the `quasiCompact`
  field from a **finite family** of divisor schemes, each with its own class `lam i`, and the
  per-point statement *"some index `i` and some field point of the `i`-th scheme carries
  `lam i` to the class of `y`"*.

`quasiCompact_of_pic0_class_surjective` is the one-element case
(`finite_family_pic0_class_of_single` below), so nothing is weakened: this is the same obligation
with the index quantifier moved inside, which is where the atlas puts it.  (An earlier draft of
this line cited that lemma as
`quasiCompact_of_finite_family_pic0_class_of_single`, **which does not exist** — caught by audit
`I-1436`.  A `#check` in a file that imports this one reports unknown identifier; grep found only
the docstring citing itself.  This project's recurring "grep resolves it, the import closure does
not" failure, in its worst form.)

## What this does NOT do

**No antecedent is discharged and no `JacobianData` is produced.**  `rep`, the classes
`lam i` and the per-point statement are all hypotheses.  What changes is the *shape* a
producer must exhibit: it may now answer point-by-point with a different chart each time,
which is what a heterogeneous atlas gives, instead of committing to one divisor scheme in
advance.

Two honest limits, both measured rather than assumed:

* **the `[∀ i, CompactSpace (X i)]` binder is discharged here but NOT at the atlas's chart
  objects** (ajcr-p3, `I-1443`/`I-1391`).  In `quasiCompact_of_finite_family_pic0_class` the
  sources are the `DivScheme …` themselves, where `compactSpace_divScheme` is an instance, so the
  binder costs nothing.  A consumer that reshapes them into the atlas's chart sources is asking
  about `(V i : Scheme)`, an **open** of the representing object, and `CompactSpace` of an open is
  *not* an instance — three sites priced it as free by citing the ambient object.  The fix is
  `compactSpace_isOpen_divSchemeOver` (`Picard/Pic0AtlasCompactNoetherian.lean`), which proves it
  for every open by local noetherianity; `compactSpace_of_representableBy` in that file transports
  it between any two representations of `divFunctor C π n`, so a consumer need not land at
  `divSchemeOver` to get it.
* **finiteness of the index is a real hypothesis here**, and it is *not* the same as
  `[Finite ι]` on the atlas: this family indexes the *carriers a producer chooses to answer
  with*, not the atlas.  A producer answering with one scheme per point needs the point set
  finite, which it is not; a producer answering from the finitely many chart parameters the
  campaign fixes needs nothing further.  Which of the two applies is the producer's business
  and is not settled here.
* **the fibrewise input is unchanged.**  `exists_effective_deg_eq_of_pic0_at_point`
  (`Picard/JacobianDataAbelEffectivePoint.lean`) still produces its divisor over a finite
  separable *splitting field* of `κ(y)`, not over `κ(y)`; the extension-tolerant form
  `quasiCompact_of_extensionTolerant_lift` (`Picard/JacobianDataQcFromRep.lean`) is what
  absorbs that, and the same widening applies verbatim here — it is orthogonal to the index
  quantifier this file moves.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-! ## The topological step -/

/-- **A scheme covered by finitely many compact images is compact.**

If every point of `Y` is in the image of one of the finitely many `g i`, and each source is
a compact space, then `Y` is a compact space: the images are compact (continuous image of a
compact space) and they cover.

This is the generalisation of `quasiCompact_of_surjective`
(`Picard/CompactImageQc.lean`, used with the *single* `DivScheme g`) that the heterogeneous
atlas needs.  Nothing about divisors, Picard functors or the base field enters. -/
theorem compactSpace_of_finite_family_surjective {Y : Scheme.{u}} {ι : Type u} [Finite ι]
    (X : ι → Scheme.{u}) [∀ i, CompactSpace (X i)] (g : ∀ i, X i ⟶ Y)
    (hsurj : ∀ y : Y, ∃ i, ∃ x : X i, (g i).base x = y) :
    CompactSpace Y := by
  rw [← isCompact_univ_iff]
  have hcover : (Set.univ : Set Y) = ⋃ i, Set.range (g i).base := by
    refine Set.eq_of_subset_of_subset (fun y _ => ?_) (fun _ _ => Set.mem_univ _)
    obtain ⟨i, x, hx⟩ := hsurj y
    exact Set.mem_iUnion.mpr ⟨i, x, hx⟩
  rw [hcover]
  refine isCompact_iUnion fun i => ?_
  rw [← Set.image_univ]
  exact (isCompact_univ (X := X i)).image (g i).base.hom.continuous

/-! ## The `quasiCompact` field at a finite family of carriers -/

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

section FiniteFamily

variable {ι : Type u} [Finite ι]
variable {X : ι → Scheme.{u}} [∀ i, (X i).Over (Spec (CommRingCat.of k))]
  [∀ i, SmoothOfRelativeDimension 1 ((X i) ↘ Spec (CommRingCat.of k))]
  [∀ i, IsIntegral (X i)]
variable {A B : ∀ i, (X i).CurveDivisor} {g r₁ r₂ : ι → ℕ}
variable {b₁ : ∀ i, Module.Basis (Fin (r₁ i)) k ↥(Scheme.divisorSections k (B i) ⊤)}
variable {b₂ : ∀ i, Module.Basis (Fin (r₂ i)) k
  ↥(Scheme.divisorSections k (A i + B i) ⊤)}

/-- **DAT-J's `quasiCompact` field from a finite family of divisor schemes.**

The hypothesis is `hcl` with its index quantifier *inside* the point quantifier: for each
point `y` of the representing object there is **some** index `i` and a field point of the
`i`-th divisor scheme carrying that scheme's class `lam i` to the class of `y`.

Compare `quasiCompact_of_pic0_class_surjective`
(`Picard/JacobianDataQcFromRep.lean`), which is the one-index case: there a single carrier
and a single class are fixed before `y`.  This form is the one a *heterogeneous* atlas can
answer, since `mixedParamChart` gives each index its own representing object and different
points may use different charts (`Pic0ChartCoveragePointwise.lean`; and per ajcr-p4's
`I-1389` a single-index coverage hypothesis is strictly stronger than DAT-B coverage, not
weaker).

**Discharges nothing**: `rep`, `lam` and `hcl` are hypotheses.  The finiteness is on the
family of carriers a producer answers with, which is not the atlas index — see the module
docstring. -/
theorem quasiCompact_of_finite_family_pic0_class {J : Over (Spec (.of k))}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : ∀ i, pic0Subgroup C (divSchemeOver k (A i) (B i) (g i) (r₁ i) (r₂ i)
      (b₁ i) (b₂ i)))
    (hcl : ∀ y : J.left, ∃ (i : ι)
      (q : overSpec k (Over.testPointField y) ⟶
        divSchemeOver k (A i) (B i) (g i) (r₁ i) (r₂ i) (b₁ i) (b₂ i)),
      pic0Map C q (lam i) = rep.homEquiv (Over.testPoint y)) :
    QuasiCompact J.hom := by
  refine HasAffineProperty.iff_of_isAffine.mpr ?_
  refine compactSpace_of_finite_family_surjective
    (fun i => DivScheme k (A i) (B i) (g i) (r₁ i) (r₂ i) (b₁ i) (b₂ i))
    (fun i => (abelOfPic0Class rep (lam i)).left) fun y => ?_
  obtain ⟨i, q, hq⟩ := hcl y
  refine ⟨i, q.left.base (Nonempty.some inferInstance), ?_⟩
  have h := congrArg (fun m : overSpec k (Over.testPointField y) ⟶ J => m.left.base
    (Nonempty.some inferInstance)) (comp_abelOfPic0Class_eq_testPoint rep (lam i) y q hq)
  exact h.trans (Over.testPoint_base y _)

/-- The single-carrier form is the one-index case — recorded so the generalisation is
visibly not a weakening of the conclusion, only a relaxation of the hypothesis.

Compare `extensionTolerant_of_kappaPinned` (`Picard/JacobianDataQcFromRep.lean`), which
records the same relationship for the *other* relaxation of `hcl` (the residue-field pin).
The two are independent: this one moves the index quantifier, that one the test object. -/
theorem finite_family_pic0_class_of_single {J : Over (Spec (.of k))}
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of k))] [IsIntegral Y]
    {A' B' : Y.CurveDivisor} {g' r₁' r₂' : ℕ}
    {b₁' : Module.Basis (Fin r₁') k ↥(Scheme.divisorSections k B' ⊤)}
    {b₂' : Module.Basis (Fin r₂') k ↥(Scheme.divisorSections k (A' + B') ⊤)}
    (rep : (pic0TypeFunctor C).RepresentableBy J)
    (lam : pic0Subgroup C (divSchemeOver k A' B' g' r₁' r₂' b₁' b₂'))
    (hcl : ∀ y : J.left,
      ∃ q : overSpec k (Over.testPointField y) ⟶ divSchemeOver k A' B' g' r₁' r₂' b₁' b₂',
        pic0Map C q lam = rep.homEquiv (Over.testPoint y))
    (y : J.left) :
    ∃ (_ : PUnit.{u + 1})
      (q : overSpec k (Over.testPointField y) ⟶
        divSchemeOver k A' B' g' r₁' r₂' b₁' b₂'),
      pic0Map C q lam = rep.homEquiv (Over.testPoint y) :=
  ⟨PUnit.unit, hcl y⟩

end FiniteFamily

end AlgebraicGeometry
