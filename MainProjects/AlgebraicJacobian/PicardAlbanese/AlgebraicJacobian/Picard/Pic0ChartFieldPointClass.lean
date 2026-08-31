/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartFieldTestSurjective
import AlgebraicJacobian.Picard.Pic0ChartRestrictedFibre
import AlgebraicJacobian.Picard.JacobianDataQcFromRep

/-!
# The per-point field-point statement of DAT-J is FREE from DAT-B coverage

`Picard/JacobianDataQcFromRep.lean` and `Picard/Pic0AtlasCompactFromClass.lean` reduce DAT-J's
`quasiCompact` field to `hcl`, and both record that it has **no producer of any shape**.  The
routes they name are the Abel image and finite-separable descent.

This file measures that pricing and finds the *per-point* half of it free.  Two results, and the
second is the one that reprices the row:

* `AlgebraicGeometry.pic0Map_lamOfDivRep` — the **class-coordinate bridge**: restricting
  `lamOfDivRep` (`Picard/JacobianDataQcFromRep.lean`) along any test morphism `q : T ⟶ D` gives
  the *chart value* of the `D`-point `q`.  Pure naturality — `chartValueTrans`'s own naturality
  plus `RepresentableBy.homEquiv_comp` at `q ≫ 𝟙`.  So the class `hcl` speaks about is, at every
  test, the chart value; nothing in `hcl` is about a class one still has to construct.
* `AlgebraicGeometry.exists_chart_field_point_of_chartsCoverLocally` — **the per-point statement,
  discharged from coverage alone**: given DAT-B coverage for a chart family and *any* Σ-sheaf
  section over the field point of `y`, there is an index and an honest `Spec κ(y)`-point of that
  chart's source whose chart value **is** that section.  No descent, no Abel image, no refinement
  to a neighbourhood.  The section may be the one the representation names for `y`
  (`section_of_rep_at_field_point` below), which is what makes this bear on `hcl`.

The engine is `app_surjective_of_isLocallySurjective_of_subsingleton`
(`Picard/Pic0ChartFieldTestSurjective.lean`): at a one-point test, Zariski-local surjectivity
*is* surjectivity, so the "local" in B-5/B-6 costs nothing at exactly the tests `hcl`
quantifies over.

## What is NOT discharged — read this before quoting the file

**`hcl` is not proved here, and no antecedent of `pic0RepresentableByOfCharts` is discharged.**
The results above are implications whose antecedent is DAT-B coverage, which has no producer at
any `V` (`Pic0ChartRestrictedFibre.lean`, `Pic0ChartBotRefute.lean` for the `⊥` end).  Trading an
unproduced hypothesis for another unproduced hypothesis is not progress, and this file does not
claim it is.  What it claims is narrower and checkable: **given coverage, the per-point half of
`hcl` costs nothing**, so a lane pricing DAT-J should not schedule it as separate work.

**THE GAP LIST BELOW WAS WRONG TWICE, BOTH TIMES IN MY OWN FAVOUR** — found by a fresh-context
adversarial audit of this file and reproduced by me before accepting (`I-1434`, `I-1436`; lesson
`I-1437`: a gap list written as the honest-ledger section reads as already-audited, so nobody
probes it).  The original list had three items; item 1 was smaller than stated and item 3 had
been closed fifteen minutes before this file landed.  Corrected list:

1. **ONE Σ-TRANSPORT, not a carrier mismatch.**  The original text said the point produced lands
   in `(V i : Scheme)`, "an *open of* `(D i).left`", while `hcl` wants a point of the divisor
   scheme.  That clause is **idle**: `restrictChart` *is* `yoneda.map V.ι ≫ f`, so composing the
   produced `x` with `(V i).ι` and packaging by `Over.homMk` against
   `(congrArg Sigma.fst hx).trans (Over.testPoint y).w` gives an honest `⟶ D i` — measured, it
   elaborates.  What genuinely remains is the Σ *second* component: `Over.sigmaExtension_snd_eq`
   leaves `(pic0TypeFunctor C).map (Over.mkCongr hfst).op`, and `mkCongr hfst` is not `rfl`-provably
   the identity.  `Over.sigmaExtension_map_mk_eq_iff` (`Picard/OverSigmaExtension.lean`) is the
   seam built for exactly this.  So: **one transport lemma**, named, not a carrier problem.
2. **The index varies with the point.**  This item stands, and it is the one real residue.  See
   `Picard/JacobianDataQcFiniteFamily.lean`, which moves the qc field's index quantifier inside
   for exactly this reason, and ajcr-p4's `I-1389`, which shows a *fixed*-index coverage
   hypothesis is strictly **stronger** than DAT-B coverage.  The finite-family form needs the
   family of answering carriers finite, and coverage supplies no bound on how many indices the
   points of `J` use.
3. **WITHDRAWN — compactness of the chart sources is NOT owed.**  The original item cited
   ajcr-p3's `I-1391` for the negative half (`CompactSpace` of an open does not follow by
   instance resolution — true) and missed the *positive* half from that lane's same commit:
   `compactSpace_isOpen_divSchemeOver` (`Picard/Pic0AtlasCompactNoetherian.lean`) proves
   `CompactSpace (V : Scheme)` for **every** open of `divSchemeOver`, which is exactly the chart
   sources.  Verified by `#check`.

**AND A PREMISE THIS FILE INHERITED THAT NEEDS A QUALIFIER.**  The opening paragraph's "no
producer of any shape" is, at HEAD, false as an unqualified sentence:
`quasiCompact_jacobianDataOfFiniteMixedParamCharts` (`Picard/Pic0AtlasCompactNoetherian.lean`)
discharges the `quasiCompact` field outright at a **finite** atlas, with no `hcl` and no Abel
morphism — and per ajcr-p3's `I-1430` that route does not even need DAT-B coverage, the
`IsLocallySurjective` binder there being idle.  `hcl` is the route for the **infinite**
(class-indexed) atlas, which is the one the tree plans to build.  Read every "no producer"
sentence in this file and in `Picard/JacobianDataQcFiniteFamily.lean` with that qualifier.

So the corrected ledger: DAT-J's qc field, **at an infinite atlas**, owed one statement.  Its
per-point half is free given coverage; what remains owed is one named Σ-transport and the index
quantifier.  Not a geometric input either way — a repricing in the cheap direction, twice over.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The class-coordinate bridge -/

/-- **`lamOfDivRep` restricted along a test morphism IS the chart value there.**

`lamOfDivRep n divRep m Z hdeg` is the universal element of `divRep` pushed through
`chartValueTrans` (`Picard/JacobianDataQcFromRep.lean`).  Restricting it along `q : T ⟶ D` gives
the chart value of the `D`-point `q` — two naturality steps and nothing else:
`picEtMap_chartValue` moves the restriction inside `chartValue`, and
`RepresentableBy.homEquiv_comp` at `q ≫ 𝟙 D` identifies the restricted universal element with
`divRep.homEquiv q`.

**Why it matters for `hcl`.**  `hcl`'s equation is `pic0Map C q lam = rep.homEquiv (testPoint y)`
with `lam` a class a producer must supply.  At `lam := lamOfDivRep …` — the class the chart layer
already carries, per that file's own "`lam` is PRODUCED, not assumed" section — the left side is
*the chart value of `q`*.  So `hcl` at that `lam` says exactly: **the class of `y` is a chart
value at some field point**, with no reference to an Abel morphism or a compatibility square. -/
theorem pic0Map_lamOfDivRep {D : Over (Spec (.of k))}
    (divRep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {T : Over (Spec (.of k))} (q : T ⟶ D) :
    ((pic0Map C q (lamOfDivRep n divRep m Z hdeg)).1 : picEt C T)
      = chartValue C π n m Z T (divRep.homEquiv q) := by
  rw [pic0Map_coe, lamOfDivRep, chartValueTrans_app_coe, picEtMap_chartValue]
  refine congrArg (chartValue C π n m Z T) ?_
  have h := divRep.homEquiv_comp q (𝟙 D)
  rw [Category.comp_id] at h
  exact h.symm

/-! ## The section a representation names at a field point -/

variable (C) in
/-- **The Σ-sheaf section named by a point of a representing object.**

For `prep` a representation of `pic0TypeFunctor C` by `J` and `y : J.left`, the field point
`Over.testPoint y` composed into the Σ-extension of `prep` is a section of the Σ-sheaf over
`Spec κ(y)`.  Available from `prep` alone — no divisor data, no chart, no coverage.

This is the section the next theorem is applied to, and the reason `hcl` is a statement about
coverage rather than about constructing a class. -/
def sectionOfRepAtFieldPoint {J : Over (Spec (.of k))}
    (prep : (pic0TypeFunctor C).RepresentableBy J) (y : J.left) :
    (pic0SigmaSheaf C).1.obj (op ((overSpec k (Over.testPointField y)).left)) :=
  (prep.toSigmaExtension).app
    (op ((overSpec k (Over.testPointField y)).left)) (Over.testPoint y).left

/-! ## The per-point statement, from coverage -/

variable (C) in
/-- **DAT-J's per-point field-point statement is free given DAT-B coverage.**

Given a chart family that covers Zariski-locally, and any section `s` of the Σ-sheaf over the
field point of `y`, there is an index `i` and a genuine morphism `Spec κ(y) ⟶ X i` whose chart
value is `s` **on the nose** — no restriction to a neighbourhood, no refinement, no finite
separable descent.

The whole content is `app_surjective_of_isLocallySurjective_of_subsingleton`
(`Picard/Pic0ChartFieldTestSurjective.lean`): `Spec κ(y)` has one point, and there local
surjectivity is surjectivity.  Applied at `s := sectionOfRepAtFieldPoint C prep y` this is the
per-point half of `hcl`, at the chart carriers.

**Antecedent open.**  `ChartsCoverLocally` is antecedent 2 of `pic0RepresentableByOfCharts` and
has no producer at any `V`; this is an implication, not a discharge.  See the module docstring
for the three surviving gaps between this and `hcl` as `JacobianDataQcFromRep.lean` states it —
the carrier, the index quantifier, and compactness of the chart sources. -/
theorem exists_chart_field_point_of_chartsCoverLocally {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (hcov : ChartsCoverLocally C f)
    {T : Over (Spec (.of k))} (y : T.left)
    (s : (pic0SigmaSheaf C).1.obj (op ((overSpec k (Over.testPointField y)).left))) :
    ∃ (i : ι) (x : (overSpec k (Over.testPointField y)).left ⟶ X i),
      (f i).app (op ((overSpec k (Over.testPointField y)).left)) x = s :=
  exists_chart_section_of_chartsCoverLocally_of_subsingleton f hcov
    (Nonempty.some inferInstance) s

variable (C π) in
/-- **The same statement at the mixed-parameter atlas and the atlas's own class.**

The form a DAT-J producer reads: for every point `y` of a `Pic⁰`-representing object, coverage
supplies an index and a `Spec κ(y)`-point of the `i`-th chart source carrying the class of `y`.

Stated separately because the mixed-parameter atlas is the family the tree plans to build, and
because its chart sources `(V i : Scheme)` are the carriers the three gaps of the module
docstring are about. -/
theorem exists_mixedParamChart_field_point {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hcov : ChartsCoverLocally C (mixedParamChart C π nn D rep m Z hdeg V))
    {J : Over (Spec (.of k))} (prep : (pic0TypeFunctor C).RepresentableBy J) (y : J.left) :
    ∃ (i : ι) (x : (overSpec k (Over.testPointField y)).left ⟶ ((V i : Scheme.{u}))),
      (mixedParamChart C π nn D rep m Z hdeg V i).app
          (op ((overSpec k (Over.testPointField y)).left)) x
        = sectionOfRepAtFieldPoint C prep y :=
  exists_chart_field_point_of_chartsCoverLocally C
    (mixedParamChart C π nn D rep m Z hdeg V) hcov y _

end

end AlgebraicGeometry
