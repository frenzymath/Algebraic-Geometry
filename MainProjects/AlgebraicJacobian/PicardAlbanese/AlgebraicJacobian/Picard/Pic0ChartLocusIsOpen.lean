/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartShiftedDatum

/-!
# CHART-U(b): the openness of `chartLocus` (dat-b row B-4, the assembly)

`informal/w4-datb-worksheet.md` §1.6 (b-amendment) fixes the openness route of record as a
chain with THREE transports on top of the engine, and reserves `isOpen_chartLocus` as its
keystone.  This file is that assembly, and its central purpose is to make the *shape* of the
assembly checkable now that `chartLocus` exists (`Picard/Pic0ChartLocus.lean`), so that the
remaining obligation is a single named hypothesis rather than a fog.

## What the route of record is, and which links are landed

Reading the (b-amendment) against the tree at HEAD:

| link | statement | status |
|---|---|---|
| (0) class-indexation | `isOpen_cechWitnessLocus` (`Pic0ChartLocusClass:123`) | **landed** (c9a) |
| engine | `datumRigidEngine_isOpen_vanishing` (`GluedSheafEngine:221`) | **landed** |
| dictionary | `subsingleton_h1_tensor_iff_exists_witness` (`H1Locus:182`) | **landed** |
| RE-5 | `exists_fg_isNoetherianRing_baseChange_eq` (`DatumDescent:514`) | **landed** |
| datum openness | `isOpen_setOf_exists_witness_h1_vanishing` (`LocusOpen:80`) | **landed** |
| fibre-field | `hasWitnessH1Vanishing_iff_of_separable` (`FibreField:157`) | **landed** |
| GAP-1 inverse | `BasicOpenCocycleDatum.invDatum` (`Pic0ChartShiftedDatum`) | **landed** |
| carrier/field translation | `isOpen_setOf_hasWitnessH1Vanishing_testPointField` | **landed** |
| twist collapse | `chartTwist_collapse` (`Pic0ChartTwistCollapse`) | **landed** |
| ~~GAP-1 mul~~ | ~~a datum for a *product*, on a common cover refinement~~ | **NOT NEEDED** |
| honesty over the étale carrier | `PicEtAff.map_mk_eq_unit_self` (`Pic0ChartHonest`) | **landed** |
| pointwise presentation | `IsChartDatumPresentation` (below) | **HALF landed** (see note) |
| `cechPicClass_inv` | the class law of `invDatum` | **NOT landed**, and off the path |

(The engine is Noetherian-free; the GAP-1 inverse and the carrier/field translation landed
2026-07-28.)

**The GAP-1 mul row is struck, and this paragraph is a correction of what stood here.**  It
used to say the residue was the shifted-datum presentation and that "producing it needs the
mul/tensor half of GAP-1, which needs a common refinement of two basic-open covers".  That is
false (`Picard/Pic0ChartTwistCollapse.lean`): the twist is ONE `thetaFamily`, since
`sigmaFamily` *is* a `thetaFamily` and `thetaFamily` is multiplicative in its class, so Σ and
`θᵐ` fuse in `CechPic` over the fixed base before any datum is extracted; and
`exists_cechPicClass_eq` presents an arbitrary class, product or not, outright.

**What genuinely remains, stated without under-pricing it** (this is the correction the
reviewer of I-0558 asked for).  Two things, and neither is bookkeeping:

1. ~~**Honesty over a general affine base.**~~  **LANDED** (`Picard/Pic0ChartHonest.lean`).  This
   row read: `exists_datum_cechPicClass_chartTwistClass` takes an honest Čech class `c` over `B`
   as a *hypothesis*, and nothing supplies one, because the splitting theorem
   (`exists_splitting_of_picEt`) needs `[Field K]` — its engine is étale field-cofinality — and
   the only other plus-unit surjectivity is field-only too.  All of that is accurate about the
   tree and none of it matters: **a cover splits over its own carrier.**
   `PicEtAff.map_mk_eq_unit_self` gives `PicEtAff.map C E.Carrier (mk C E x) = unit C E.Carrier x`
   over an ARBITRARY affine base, because the map cofinality was being asked to produce is the
   *identity* `E.Carrier →ₐ[A] E.Carrier`.  This is exactly the (b-amendment)'s "over the étale
   carrier `B := E.Carrier` the class is honest" step, so it was never a general-`A` obligation
   in the first place.
2. **The pointwise presentation itself** — now the ONLY residue.  `IsChartDatumPresentation` asks
   for ONE datum over
   `A` whose fibre predicate matches, at every residue field simultaneously, a split predicate
   whose splitting field `L` varies from point to point (`IsSplitWitness` quantifies `L`
   existentially *per point*).  Calling that "a `cechPicClass` base-change statement, not a
   construction" — as an earlier draft of this header did — prices a construction as
   bookkeeping, which is precisely the mis-pricing the twist-collapse retraction was written
   to correct one level up.

Everything downstream of a presenting datum is landed.

**UPDATE 2026-07-28 (`de63abac6`): the residue of row 2 is now HALF discharged, and the half
that fell was the one this paragraph did not expect.**
`Picard/Pic0ChartPresentationHalf.lean` proves the **forward** direction of
`IsChartDatumPresentation` from a hypothesis containing no witness, no `H¹` and no divisor:
`IsChartDatumPlusFibre`, which says only that the datum presents `μ` at every residue field *as
plus classes*.  The move is to take the splitting extension to be `κ(t)` **itself** — the datum's
witness divisor is already in the right class over `κ(t)` with vanishing `H¹`, so nothing needs
transporting.  That trivial splitting `L := K` had been recorded as unelaborable (memory I-0564);
it is one line since that record's partial retraction (see
`isSplitWitness_of_presenting_witness` in `Picard/Pic0ChartTwistSplit.lean`).

What is still owed is the **converse**, and the per-point quantification of `L` this paragraph
warns about is exactly where it bites: one receives a witness over some `L_t` varying with `t`,
lying in `μ`'s class there rather than visibly in `D`'s at `κ(t)`.
`isChartDatumPresentation_of_plusFibre_of_converse` assembles the `↔` from the two halves, so a
lane closing this row faces one obligation instead of two.

## The shape of this file

`IsChartDatumPresentation` names exactly that residue as a hypothesis — a *per-field*
presentation of the twisted fibre class by a datum — and `isOpen_chartLocus_of_presentation`
derives the openness from it over an affine test.  This is the honest factorisation: the
theorem is real mathematics (it is the three transports plus the dictionary), and the
hypothesis is a single, precisely stated obligation.  (An earlier draft said the GAP-1
mul/tensor brick would discharge it; see the struck table row for why that was wrong.)

Writing it the other way round — stating `isOpen_chartLocus` unconditionally with a `sorry`
— would hide the fact that the missing input is a *construction*, not a proof.

**This file is sorry-free as of 2026-07-28.**  Its earlier single `sorry` (the carrier/field
translation) was not a mathematical gap: it was an artifact of taking the `Algebra A` /
`IsScalarTower k A` structures on `κ(t)` as explicit `alg`/`tow` *arguments*, which both made
the statement FALSE for some regradings — `HasWitnessH1Vanishing` reads its `Algebra` instance
inside `relCurveMap C B L`, so a non-canonical `alg` names a different base-change map and a
different set — and forced every consumer to carry two dead parameters.  (No refuting
`A`, `alg` was exhibited, so the honest verdict is "wrong shape, false for some regradings",
not "no proof can exist"; recorded per I-0559.)  With the canonical
instances of `Picard/Pic0ChartTestPoint.lean` the whole translation is
`hasWitnessH1Vanishing_iff_of_fieldExtension` across `Spec.residueFieldIso`, and the carrier
identification `↥(overSpec k A).left = PrimeSpectrum A` is definitional.  The general lesson
is recorded on the `chart-u` roadmap node.

## Main declarations

* `AlgebraicGeometry.IsChartDatumPresentation` — the residue, named.
* `AlgebraicGeometry.chartLocus_eq_cechWitnessLocus_of_presentation` — the identification of
  `chartLocus` over an affine test with the landed class-indexed witness locus.  This is
  transports (0) and (iii) discharged.
* `AlgebraicGeometry.isOpen_chartLocus_of_presentation` — **the keystone, conditionally**:
  `chartLocus` is open over an affine test given the presentation.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The residue of the chain, named -/

variable (C π) in
/-- **The shifted-datum presentation hypothesis** — the one link of the CHART-U(b) route of
record that is not landed, stated exactly.

Over an affine test `Spec A`, for a class `μ : picEt C (overSpec k A)` (in practice the
twisted family `chartTwist C m Z _ λ` restricted to the test), a presentation is a
`BasicOpenCocycleDatum` over `A` whose fibre witness predicate at every residue field agrees
with the split witness predicate of `μ` at the corresponding point.

Two remarks on the shape, both deliberate:

* it is stated as an **agreement of predicates at every point**, not as a class equality.
  That is weaker than "the datum's class is `μ`", and it is all the openness argument
  consumes — which matters, because the class equality is what needs `cechPicClass_inv` and
  a class-level identification, whereas a lane that can produce the pointwise agreement by any
  other route may use this theorem immediately;
* the split predicate is read at `Over.testPoint`, i.e. at the canonical residue-field point
  of the affine test, so no choice of affine chart enters;
* the `Algebra A (testPointField t)` / `IsScalarTower k A (testPointField t)` instances the
  datum predicate needs are the **canonical** ones of `Picard/Pic0ChartTestPoint.lean`.  An
  earlier draft of this file carried them as explicit `alg`/`tow` arguments; that was strictly
  worse — it made the statement false for some regradings (`HasWitnessH1Vanishing` reads its
  `Algebra` instance inside `relCurveMap`, so a non-canonical `alg` names a different set) as
  well as unusable. -/
def IsChartDatumPresentation {A : Type u} [CommRing A] [Algebra k A]
    (μ : picEt C (overSpec k A)) (D : BasicOpenCocycleDatum C A π) : Prop :=
  ∀ t : (overSpec k A).left,
    D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t)
      ↔ IsSplitWitness C (picEtMap C (Over.testPoint t) μ)

/-! ## The carrier translation: `testPointField` on `Spec A` versus `Ideal.ResidueField`

The engine's open set lives in `PrimeSpectrum A` and is indexed by `q.asIdeal.ResidueField`;
`chartLocus` lives in `(overSpec k A).left = Spec A` and is indexed by `Over.testPointField`.
The two carriers are the same space, but the two *fields* are only canonically isomorphic
(mathlib's `Spec.residueFieldIso`), so the witness predicate has to be carried across that
isomorphism.  That is what this section does, and it is the transport the (b-amendment) folds
into "affine pieces glue by (V1c)-style locality". -/

/-- **The residue-field comparison at a point of an affine test, as an algebra map.**

`Over.testPointField t` is the *scheme* residue field `(Spec A).residueField t`, while every
engine-facing predicate reads the *algebraic* residue field `t.asIdeal.ResidueField` of the
prime.  Mathlib's `Spec.residueFieldIso` identifies them; this records the identification in
the form the tower needs, namely that the canonical `A`-algebra structure on the scheme
residue field (`Over.instAlgebraTestPointFieldAffine`) factors through the algebraic one.

Proof: both sides are `Spec.preimage` of a morphism out of `Spec κ(t)`, and `Spec.map` is
injective on homs, so it suffices to compare after applying `Spec.map` — where the identity is
mathlib's `Spec.map_residueFieldIso_inv_eq_fromSpecResidueField`. -/
lemma algebraMap_testPointFieldAffine_factors {A : Type u} [CommRing A] [Algebra k A]
    (t : (overSpec k A).left) :
    algebraMap A (Over.testPointField (T := overSpec k A) t)
      = ((Scheme.Spec.residueFieldIso (.of A) t).inv).hom.comp
          (algebraMap A (t : PrimeSpectrum A).asIdeal.ResidueField) := by
  rw [Over.algebraMap_testPointFieldAffine]
  have h : Spec.preimage ((overSpec k A).left.fromSpecResidueField t)
      = CommRingCat.ofHom (algebraMap A (t : PrimeSpectrum A).asIdeal.ResidueField)
          ≫ (Scheme.Spec.residueFieldIso (.of A) t).inv := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp]
    exact (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) t).symm
  rw [h]
  rfl

/-- **The witness predicate at a scheme-residue field agrees with the one at the prime's
residue field, and the resulting locus is open.**

`Over.testPointField t` is `(Spec A).residueField t` and the engine reads
`t.asIdeal.ResidueField`; `Spec.residueFieldIso` identifies them, and the witness predicate
transfers along any field extension in the `A`-tower
(`hasWitnessH1Vanishing_iff_of_fieldExtension`, `Pic0ChartLocusFibreField.lean:142`), in
particular along an isomorphism.

Three points about the proof, each of which was a suspected wall and is not:

* the **carrier identification** `↥(overSpec k A).left = PrimeSpectrum A` is *definitional*
  (`Scheme.Spec`'s carrier is `PrimeSpectrum` on the nose), so the two index sets need no
  transport and the two topologies agree by `rfl`.  The set equality below is therefore a
  pointwise `Iff`, not a homeomorphism argument;
* the `Algebra A (testPointField t)` and `IsScalarTower k A (testPointField t)` instances the
  predicate needs are **already canonical** (`Over.instAlgebraTestPointFieldAffine`,
  `Over.instIsScalarTowerTestPointFieldAffine`), so nothing has to be passed in as an
  argument.  An earlier draft of this file took `alg`/`tow` as explicit hypotheses and left
  the conclusion as a `sorry`; that was a statement-shape artifact, not a gap — and worse,
  the hypothesis form is *false for some regradings*, since an arbitrary `alg` need not be the
  canonical instance and the predicate is not invariant under regrading the field over `A`;
* the only genuine content is the transport across `Spec.residueFieldIso`, which is
  `hasWitnessH1Vanishing_iff_of_fieldExtension` applied to the isomorphism, in the tower
  `A → κ(q) → (Spec A).residueField t` supplied by
  `algebraMap_testPointFieldAffine_factors`. -/
theorem isOpen_setOf_hasWitnessH1Vanishing_testPointField
    (hπ : π ≫ P1.structureMap k = C.hom) {A : Type u} [CommRing A] [Algebra k A]
    (D : BasicOpenCocycleDatum C A π) :
    IsOpen {t : (overSpec k A).left |
      D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t)} := by
  -- The two loci are the SAME set of the SAME type: `↥(overSpec k A).left` is
  -- `PrimeSpectrum A` definitionally, so only the fibre field differs, and the predicate is
  -- invariant under the isomorphism between the two readings of it.
  have hset : {t : (overSpec k A).left |
        D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t)}
      = {q : PrimeSpectrum A |
          ∃ W : ((C ⊗ overSpec k q.asIdeal.ResidueField).left).CurveDivisor,
            Scheme.CurveDivisor.picClass q.asIdeal.ResidueField W
                = Scheme.CechPic.map (relCurveMap C A q.asIdeal.ResidueField)
                    D.cechPicClass
              ∧ Subsingleton (Sheaf.HModule
                  ((C ⊗ overSpec k q.asIdeal.ResidueField).left.divisorSheaf
                    q.asIdeal.ResidueField W) 1)} := by
    refine Set.ext fun t => ?_
    -- the comparison iso as an algebra structure, and its tower over `A`
    letI : Algebra (t : PrimeSpectrum A).asIdeal.ResidueField
        (Over.testPointField (T := overSpec k A) t) :=
      ((Scheme.Spec.residueFieldIso (.of A) t).inv).hom.toAlgebra
    haveI : IsScalarTower A (t : PrimeSpectrum A).asIdeal.ResidueField
        (Over.testPointField (T := overSpec k A) t) :=
      IsScalarTower.of_algebraMap_eq' (algebraMap_testPointFieldAffine_factors t)
    exact (D.hasWitnessH1Vanishing_iff_of_fieldExtension
      (t : PrimeSpectrum A).asIdeal.ResidueField
      (Over.testPointField (T := overSpec k A) t)).symm
  rw [hset]
  exact D.isOpen_setOf_exists_witness_h1_vanishing hπ

/-! ## Transports (0) and (iii): the identification with the landed locus -/

/-- **`chartLocus` over an affine test is the witness locus of a presenting datum.**

This is transport (0) (the class-indexation, landed as `cechWitnessLocus`) composed with
transport (iii) (locality on the affine test, here trivial because the test *is* affine),
run against the presentation hypothesis.  The content is entirely the translation between
the two ways the tree indexes a fibre — by a point of the test object's space
(`Over.testPoint`, the `chartLocus` side) and by a prime of the test algebra
(`q.asIdeal.ResidueField`, the engine side).

The translation is available precisely because `Over.testPointField` at a point of
`(overSpec k A).left = Spec A` and `q.asIdeal.ResidueField` at the corresponding prime are
the same field up to the canonical `Spec.residueFieldIso`, and the witness predicate is
invariant under field isomorphism over the base (`hasWitnessH1Vanishing_iff_of_fieldExtension`
applied to an isomorphism). -/
theorem mem_chartLocus_iff_hasWitnessH1Vanishing
    {A : Type u} [CommRing A] [Algebra k A]
    {μ : picEt C (overSpec k A)} {D : BasicOpenCocycleDatum C A π}
    (hpres : IsChartDatumPresentation C π μ D) (t : (overSpec k A).left) :
    IsSplitWitness C (picEtMap C (Over.testPoint t) μ)
      ↔ D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t) :=
  (hpres t).symm

/-! ## The keystone, conditionally -/

variable (C π) in
/-- **`isOpen_chartLocus`, given the shifted-datum presentation** (dat-b row B-4's keystone,
over an affine test).

The proof is the route of record with the one missing link supplied as `hpres`: rewrite
membership of `chartLocus` as the datum's witness predicate at the residue field of the
point (the presentation), then quote the landed datum-level openness
`BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing` — itself the engine
`datumRigidEngine_isOpen_vanishing` read through the GAP-6 dictionary.

The general-test statement follows from this one by the affine-piece locality of the
(b-amendment)'s transport (iii): `chartLocus` over `T` meets each affine open `U ⊆ T.left` in
`chartLocus` over `Spec Γ(T.left, U)` (by `picEtMap_chartTwist` along
`Over.fromSpecAffine T U`), and a set that is open in every member of an open cover is open.
That last step is `isOpen_iff_forall_isOpen_inter`-style bookkeeping and needs no new
mathematics; it is not stated here only because it would need the presentation hypothesis
*per affine piece*, which is a statement about the general test and therefore belongs with
the honesty/presentation obligations named in the header table. -/
theorem isOpen_setOf_isSplitWitness_of_presentation (hπ : π ≫ P1.structureMap k = C.hom)
    {A : Type u} [CommRing A] [Algebra k A]
    {μ : picEt C (overSpec k A)} {D : BasicOpenCocycleDatum C A π}
    (hpres : IsChartDatumPresentation C π μ D) :
    IsOpen {t : (overSpec k A).left |
      IsSplitWitness C (picEtMap C (Over.testPoint t) μ)} := by
  -- The engine's open set is indexed by primes of `A`; the locus is indexed by points of
  -- `Spec A`.  These carriers are the same type, so the presentation rewrites one into the
  -- other pointwise.
  have hset : {t : (overSpec k A).left |
        IsSplitWitness C (picEtMap C (Over.testPoint t) μ)}
      = {t : (overSpec k A).left |
          D.HasWitnessH1Vanishing (Over.testPointField (T := overSpec k A) t)} :=
    Set.ext fun t => mem_chartLocus_iff_hasWitnessH1Vanishing hpres t
  rw [hset]
  exact isOpen_setOf_hasWitnessH1Vanishing_testPointField hπ D

end

end AlgebraicGeometry
