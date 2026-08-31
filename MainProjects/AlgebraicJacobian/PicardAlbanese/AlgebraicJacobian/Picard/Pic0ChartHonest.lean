/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartTwistCollapse

/-!
# A plus class becomes honest over its own étale carrier — over an ARBITRARY affine base

This closes the obligation the CHART-U(b) header table names "honesty over a general affine
base" (issue I-0558), and it needs no field.

## The obligation, and why it looked hard

`Picard/Pic0ChartLocusIsOpen.lean`'s route needs a `BasicOpenCocycleDatum` over an affine base
whose class is the (collapsed) twisted class.  `exists_datum_cechPicClass_chartTwistClass`
(`Picard/Pic0ChartTwistCollapse.lean`) supplies the datum — but it takes an **honest Čech
class** `c` over the base as a *hypothesis*, and a plus class over `Spec A` is not honest: it is
`PicEtAff.mk E x` for an étale cover `E` of `A`.

The tree's only route from a plus class to an honest one was
`Picard/Pic0ChartSplit.lean`'s `exists_splitting_of_picEt`, which requires `[Field K]` — its
engine is étale field-cofinality (`Algebra.EtaleCover.exists_finiteSeparableField_algHom`),
false over a general base.  So the obligation read as: find a *substitute* for cofinality over
`Spec A`.

## Why it is in fact free

There is no substitute needed, because **a cover splits over its own carrier**.  The
field-cofinality theorem is used to produce an `A`-algebra map `E.Carrier →ₐ L` into something
where the class becomes a unit; but the identity `E.Carrier →ₐ[A] E.Carrier` is already such a
map, and it exists for every cover over every base.  Restricting the plus class along
`A → E.Carrier` therefore makes it honest, with no finiteness, separability, or field
hypothesis anywhere.

Concretely `PicEtAff.map C E.Carrier (PicEtAff.mk C E x) = PicEtAff.unit C E.Carrier x` — the
transported class is presented by `x` itself.  The proof is the general-base analogue of
`PicEtAff.map_mk_eq_unit_of_algHom` (`Picard/PicEtAffFieldCollapse.lean:79`), which is stated
only for fields; the field hypotheses there are inherited from *its* consumer (the degree seam,
which reads a degree and so needs a field), not required by the argument.  The one substantive
step is the same in both: the descent condition `x.2`, fed to `relPicAlgMap_congr`, identifies
the two ways of transporting `x` to the base-changed carrier.

## What this does and does not give

It gives honesty **over `Spec E.Carrier`**, not over `Spec A`.  That is exactly what the
(b-amendment) asks for — its step is "over the étale carrier `B := E.Carrier` the class is
honest", after which the engine fires on `Spec B` and transport (ii) pushes the open locus down
to `Spec A` along the (open, surjective) carrier map.  Nothing here performs that descent; the
topological core of it is landed as `isOpen_of_isOpen_comap_preimage`
(`Picard/Pic0ChartLocusOpen.lean:129`).

So after this file the CHART-U(b) route has ONE remaining obligation, the pointwise
`IsChartDatumPresentation` — and, unlike the previous "one remaining obligation" claims on this
lane, that one is a genuine statement about matching two fibre predicates, not a missing
construction.

## Main declarations

* `AlgebraicGeometry.PicEtAff.map_mk_eq_unit_self` — **a plus class is honest over its own
  cover carrier**, over an arbitrary affine base.
* `AlgebraicGeometry.exists_honest_of_picEtAff` — the existential form.
* `AlgebraicGeometry.exists_datum_cechPicClass_twist` — the payoff, in the engine's shape: over
  a base where the class is honest, a datum presenting it twisted by any chart index exists.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsFinite π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## Honesty over the cover's own carrier -/

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
variable (C) in
/-- **A plus class becomes the plus-unit of an honest class over its own cover carrier**, over
an ARBITRARY affine base `A` — no field, no finiteness, no separability.

`PicEtAff.map C E.Carrier (PicEtAff.mk C E x) = PicEtAff.unit C E.Carrier x`: the class
presented by `x` on the cover `E` restricts, along `A → E.Carrier`, to the tautological plus
unit of `x` itself.

This is the general-base analogue of `PicEtAff.map_mk_eq_unit_of_algHom`
(`Picard/PicEtAffFieldCollapse.lean:79`) at `ℓ := AlgHom.id`.  That lemma carries `[Field K]`,
`[Field L]` because *its* consumer (the degree seam) reads a degree; the argument itself uses
neither.  The substantive content, identical in both, is the **descent condition** `x.2`: the
two ways of carrying `x` into the base-changed carrier — along `E.baseChangeInclude` and along
`Algebra.ofId` — agree on a descent class, which is what `relPicAlgMap_congr` consumes.

Why this matters: the tree's only previous route from a plus class to an honest one was étale
field-cofinality (`Picard/Pic0ChartSplit.lean`), which is field-only, so "honesty over a general
affine base" was recorded as an unlanded *construction*.  It is not a construction at all — a
cover splits over its own carrier, and the identity map is the splitting. -/
theorem PicEtAff.map_mk_eq_unit_self {A : Type u} [CommRing A] [Algebra k A]
    (E : Algebra.EtaleCover A) (x : descentClasses C E) :
    PicEtAff.map C E.Carrier (PicEtAff.mk C E x)
      = PicEtAff.unit C E.Carrier (x : relPic C (overSpec k E.Carrier)) := by
  rw [PicEtAff.map_mk, PicEtAff.unit_eq_mk C (E.baseChange E.Carrier)]
  refine congrArg (PicEtAff.mk C (E.baseChange E.Carrier)) (Subtype.ext ?_)
  rw [descentBaseChange_coe]
  exact relPicAlgMap_congr C (E.baseChangeInclude E.Carrier)
    ((Algebra.ofId E.Carrier (E.baseChange E.Carrier).Carrier).restrictScalars A) x.2

omit [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] in
variable (C) in
/-- **Every plus class over an affine base is honest over some affine base above it** — the
existential form of `PicEtAff.map_mk_eq_unit_self`, which is how a consumer meets it: it does
not get to choose `B`, it gets a `B` from the class's own presentation.

Compare `exists_splitting_of_picEt` (`Picard/Pic0ChartSplit.lean`): that gives a *field*
extension and requires the base to be a field; this gives an étale extension and requires
nothing.  The two are the field and general-base halves of the same move, and the chart layer
needs both — the field one to read the split witness predicate at a point, this one to run the
engine over a base. -/
theorem exists_honest_of_picEtAff {A : Type u} [CommRing A] [Algebra k A]
    (a : PicEtAff C A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : Algebra A B)
        (_ : IsScalarTower k A B) (z : relPic C (overSpec k B)),
      PicEtAff.map C B a = PicEtAff.unit C B z := by
  induction a using PicEtAff.ind with
  | mk E x =>
    refine ⟨E.Carrier, inferInstance, inferInstance, inferInstance, inferInstance,
      (x : relPic C (overSpec k E.Carrier)), ?_⟩
    exact PicEtAff.map_mk_eq_unit_self C E x

/-! ## The payoff: the engine's input, with honesty discharged -/

variable (C π) in
/-- **The engine input, assembled**: for any plus class over any affine base `A` and any chart
index `(m, Z)`, once the class is read honestly over a base `B` above `A` by a Čech class `c`,
a `BasicOpenCocycleDatum` over `B` presenting `c` twisted by the chart index exists.

This composes the two halves that were previously recorded as separate gates:

* honesty over `B := E.Carrier` — `exists_honest_of_picEtAff` above, which needs no field;
* presentation of the twisted class by a datum — `exists_cechPicClass_eq`, applied at the
  *product* class, which is why no `BasicOpenCocycleDatum.mul` is needed
  (`Picard/Pic0ChartTwistCollapse.lean`).

The conclusion is exactly the input of
`BasicOpenCocycleDatum.isOpen_setOf_exists_witness_h1_vanishing`, so the openness of the witness
locus over `Spec B` is available for every plus class and every chart index.  What is *not* here
is the identification of that locus with `chartLocus` — that is `IsChartDatumPresentation`, the
one genuine remaining obligation of CHART-U(b).

Stated with `c` as a hypothesis rather than bundled into the existential: bundling it forces the
elaborator to unify the tower instances on `B` while `B` is still a metavariable, which is the
hazard recorded at `Picard/Pic0ChartSplit.lean`'s closing note.  A consumer obtains `B` and `c`
from `exists_honest_of_picEtAff` plus `relPicMk_surjective`, then applies this. -/
theorem exists_datum_cechPicClass_twist {B : Type u} [CommRing B] [Algebra k B]
    (c : (relCurve C B).CechPic) (m : ℕ)
    (Z : (C ⊗ overSpec k k).left.CurveDivisor) :
    ∃ D : BasicOpenCocycleDatum C B π,
      D.cechPicClass
        = c * Scheme.CechPic.map (relCurveMap C k B) (chartTwistClass C m Z) :=
  exists_datum_cechPicClass_chartTwistClass c m Z

end

end AlgebraicGeometry
